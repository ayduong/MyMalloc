#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
  inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
  #include <assert.h>
#endif

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t object_left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);
static inline void add_chunk();
static inline void insert_last_freelist(header * b);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);
static inline size_t get_index(header * block);
static inline void remove_from_freelist(header * block, size_t index);
static inline void update_left_size(header * block);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);
static inline size_t find_block_size(size_t raw_size);
static inline header * ptr_to_freelist(size_t size);
static inline header * split(header * block, size_t size);
static inline void insert_freelist(header * block);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_object_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->object_left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param object_left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t object_left_size) {
	set_object_state(fp,FENCEPOST);
	set_object_size(fp, ALLOC_HEADER_SIZE);
	fp->object_left_size = object_left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);
  
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_object_state(hdr, UNALLOCATED);
  set_object_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->object_left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
  // TODO implement allocation
  /*(void) raw_size;
  assert(false);
  exit(1);*/
	
    if (raw_size == 0) {
		return NULL;
    } 
	// Calculating the required block size
	size_t size = find_block_size(raw_size);

	// Finding the appropriate free list
	header * ptr = ptr_to_freelist(size);
	while (ptr == NULL) {
		add_chunk();
		ptr = ptr_to_freelist(size);
	}
	set_object_state(ptr, ALLOCATED);
	return (header*)ptr->data;
	//return ptr;
}

/**
 * Will return a pointer to the appropriate free list. Handles splitting the block if 
 * necessary.
 */
static inline header * ptr_to_freelist(size_t size) {
	size_t index = (size - ALLOC_HEADER_SIZE) / sizeof(size_t) - 1;
	if (index >= N_LISTS) {
		index = N_LISTS - 1;
	}
	
	header * sentinelNode;
	
	// Iterate through the free list until a block is found. If the block is too big,
	// allocate the extra memory or split it if the remining memory is enough to go in another
	// free list
	for (int i = (int) index; i < N_LISTS; i++) {
		sentinelNode = &freelistSentinels[i];		
		header * cur = sentinelNode->next;
		// if this freelist is empty, iterate to the next freelist
		if (cur == sentinelNode) {
			continue;
		}
		
		while (cur != sentinelNode) {
			/* There are 2 cases:
				1. Block size matches. In this case, remove the block from the freelist and allocate
				2. Block is bigger. In this case, if the extra size is >= to the sizeof a header,
				   split the block. Else, just allocate the entire block
			*/
			//print_object(cur);
			if (get_object_size(cur) == size) {
				cur->prev->next = cur->next;
				cur->next->prev = cur->prev;
				//cur->next->object_left_size = get_object_size(cur->prev);
				set_object_state(cur, ALLOCATED);
				return cur;
			} else if (get_object_size(cur) > size) {
				// if the chunk is big enough to split
				if (get_object_size(cur) - size >= sizeof(header)) {
					return split(cur, size);
				// if chunk is too small to split, just allocate it entirely
				} else {
					cur->prev->next = cur->next;
					cur->next->prev = cur->prev;
					//cur->next->object_left_size = get_object_size(cur->prev);
					set_object_state(cur, ALLOCATED);
					return cur;
				}
			}
			cur = cur->next;
		}

	}
	// if we reach this point, then we must add more memory from the OS
	//add_chunk();
	//return ptr_to_freelist(size);
	return NULL;
}

/**
 * Will add more memory from the OS into the freelist, coallescing if necessary
 */
/*static inline void add_chunk() {
	header * chunk = allocate_chunk(ARENA_SIZE); // the new chunk
	if (chunk == NULL) {
		return;
	}
	header * fencepost = (header *)((char *)chunk - ALLOC_HEADER_SIZE); // the fencepost of the chunk
	// pointer to the left chunk
	header * prev = (header *)((char *)lastFencePost - lastFencePost->object_left_size);
	header * rightFencePost = (header *)((char *)chunk + get_object_size(chunk));

	//lastFencePost = rightFencePost;
	// check if the chunks are adjacent
	if ((header *)((char *)fencepost - ALLOC_HEADER_SIZE) == lastFencePost) {
		// if adjacent, coallesce
		// make a new block starting at the last fencepost, set it as allocated,
		// then add it into the freelist
		header * new_block = lastFencePost;
		set_object_size(new_block, get_object_size(chunk) + 2 * ALLOC_HEADER_SIZE);
		rightFencePost->object_left_size = get_object_size(new_block);
		set_object_state(new_block, ALLOCATED);
		new_block->object_left_size = lastFencePost->object_left_size;
		deallocate_object((header*)((char*)new_block + ALLOC_HEADER_SIZE));
	} else {
		// if not adjacent, add the chunk to the freelist
		insert_os_chunk(fencepost);
		insert_freelist(chunk);
		//print_object(chunk);
		rightFencePost->object_left_size = get_object_size(chunk);
	}
	lastFencePost = rightFencePost;
}*/


/**
 * Will add more memory from the OS into the freelist, coallescing if necessary
 */
static inline void add_chunk() {
	header * chunk = allocate_chunk(ARENA_SIZE); // the new chunk
	header * fencepost = (header *)((char *)chunk - ALLOC_HEADER_SIZE); // the fencepost of the chunk
	// pointer to the left chunk
	header * prev = (header *)((char *)lastFencePost - lastFencePost->object_left_size);
	header * rightFencePost = (header *)((char *)chunk + get_object_size(chunk));

	//lastFencePost = rightFencePost;
	// check if the chunks are adjacent
	if ((header *)((char *)fencepost - ALLOC_HEADER_SIZE) == lastFencePost) {
		if (get_object_state(prev) == UNALLOCATED) {
			size_t id = get_index(prev);
			header * b = get_header_from_offset(lastFencePost, -get_object_size(prev));
			set_object_size(b, get_object_size(prev) + get_object_size(chunk) + 2*ALLOC_HEADER_SIZE);
			rightFencePost->object_left_size = get_object_size(b);
			set_object_state(b, UNALLOCATED);
			if (id != N_LISTS-1) { 
				//insert_freelist(b);
				remove_from_freelist(b, id);
				insert_last_freelist(b);
			}	
		} else {
			// if the prev chunk is allocated, remove the fenceposts
			header * b = lastFencePost;
			set_object_size(b, get_object_size(chunk) + 2*ALLOC_HEADER_SIZE);
			rightFencePost->object_left_size = get_object_size(b);
			set_object_state(b, UNALLOCATED);
			insert_last_freelist(b);
		}
	} else {
		insert_os_chunk(fencepost);
		insert_last_freelist(chunk);
	}
	lastFencePost = rightFencePost;
}

/**
 * Will insert the block into the last freelist
 */
static inline void insert_last_freelist(header * b) {
	header * sentinel = &freelistSentinels[N_LISTS-1];
	b->next = sentinel->next;
	sentinel->next = b;
	b->next->prev = b;
	b->prev = sentinel;
}

/**
 * Will split a block based on the size parameter and place it in the correct freelist
 */
static inline header * split(header * block, size_t size) {
	// The block will but split in two. The left side will be the allocated memory,
	// the right side will be moved to the appropriate freelist
	// First, set the next/prev pointers of the headers on either side of the block
	//block->prev->next = block->next;
	//block->next->prev = block->prev;
	// Now, set the left and right pointers to the correct spot
	header * left = block;
	header * right = (header *) ((char*)block + (get_object_size(block) - size));
	set_object_size(left, get_object_size(block) - size);
	set_object_size(right, size);

	// Next, update the left size of the right block and the next block
	right->object_left_size = get_object_size(left);
	header * next = (header *)((char *)right + size);
	next->object_left_size = size;
	
	// Insert into the freelist and return
	if (get_index(left) < N_LISTS-1) {
		left->prev->next = left->next;
		left->next->prev = left->prev;
		insert_freelist(left);
	}
	return right;    		
}

/**
 * Will insert the block into the front of the correct freelist
 *
 */
static inline void insert_freelist(header * block) {
	size_t size = get_object_size(block);

	// finding the right freelist index
	size_t index = (size - ALLOC_HEADER_SIZE)/ sizeof(size_t) - 1;
	if (index >= N_LISTS) {
		index = N_LISTS - 1;
	}
	index = get_index(block);
	
	// insert
	header * sentinelNode = &freelistSentinels[index];
	block->prev = sentinelNode;
	block->next = sentinelNode->next;
	sentinelNode->next->prev = block;
	sentinelNode->next = block;	
}

/**
 * Helper to find correct block size
 */
static inline size_t find_block_size(size_t raw_size) {
	size_t rounded_size = ((raw_size + 7)/8) * 8; // round up to nearest 8
	size_t size = rounded_size + ALLOC_HEADER_SIZE;
	
	// if the size is less than the header size, we need to allocate the size of the header
	if (size < sizeof(header)) {
		size = sizeof(header);
	}
	return size;
}

/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  // TODO implement deallocation
  /*(void) p;
  assert(false);
  exit(1);*/
	if (p == NULL) return;
	header * block = ptr_to_header(p);
	if (get_object_state(block) == UNALLOCATED) {
		fprintf(stderr, "Double Free Detected\n");
		assert(0);
		exit(1);
	}

	set_object_state(block, UNALLOCATED);

	// get pointers to the neighboring blocks
	header * right = (header *) ((char *)block + get_object_size(block));
	header * left = (header *) ((char *)block - block->object_left_size);

	/*
		4 cases to check:
			- both left and right are unallocated, so coallesce all
			- just left or just right is unallocated, so just coallesce that one
			- neither are unallocated, so just insert block into freelist
	*/
	// if both are unallocated
	if (get_object_state(left) == UNALLOCATED && get_object_state(right) == UNALLOCATED) {
		// get the size of the coallesced block
		size_t newsize = get_object_size(left) + get_object_size(block) + get_object_size(right);
		header * next = get_right_header(right);
		next->object_left_size = newsize;
		// get the index of the freelists they are in
		size_t idLeft = (get_object_size(left) - ALLOC_HEADER_SIZE)/ sizeof(size_t) - 1;
		size_t idRight = (get_object_size(right) - ALLOC_HEADER_SIZE)/ sizeof(size_t) - 1;
		if (idLeft > N_LISTS - 1) idLeft = N_LISTS-1;
		if (idRight > N_LISTS - 1) idRight = N_LISTS-1;
		// we want to check if either is in the last freelist. If so, don't delete it from the freelist	
		// if the left block is in the last freelist
		if (idLeft == N_LISTS - 1) {
			// remove the right from its freelist, coallesce with the left
			remove_from_freelist(right, idRight);
			set_object_size(left, newsize);
		} else if (idRight == N_LISTS - 1) {
			// remove the left from its freelist, then coallesce the blocks and keep it in the
			// same spot that the right block is in the freelist
			remove_from_freelist(left, idLeft);
			set_object_size(left, newsize);
			left->next = right->next;
			left->prev = right->prev;
			right->next->prev = left;
			right->prev->next = left;
		} else {
			// remove both, add into appropriate freelist
			remove_from_freelist(left, idLeft);
			remove_from_freelist(right, idRight);
			set_object_size(left, newsize);
			insert_freelist(left);
		}
		//update_left_size(left);
	} else if (get_object_state(left) == UNALLOCATED) {
		//print_object(left);
		//print_object(block);
		size_t idLeft = get_index(left);
		size_t newsize = get_object_size(left) + get_object_size(block);
		right->object_left_size = newsize;
		if (idLeft == N_LISTS - 1) {
			// if the left is in the last freelist, just coallesce
			set_object_size(left, newsize);
		} else {
			// if not, delete, coallesce, and reinsert
			remove_from_freelist(left, idLeft);
			set_object_size(left, newsize);
			insert_freelist(left);
		}
		//update_left_size(left);
	} else if (get_object_state(right) == UNALLOCATED) {
		size_t idRight = get_index(right);
		size_t newsize = get_object_size(block) + get_object_size(right);
		header * next = get_right_header(right);
		next->object_left_size = newsize;
		if (idRight == N_LISTS - 1) {
			// if the right is in the last freelist, just coallesce
			set_object_size(block, newsize);
			block->next = right->next;
			block->prev = right->prev;
			right->next->prev = block;
			right->prev->next = block;
			//update_left_size(block);
		} else {
			// if not, just delete, coallesce, and reinsert
			remove_from_freelist(right, idRight);
			set_object_size(block, newsize);
			insert_freelist(block);
			//update_left_size(block);
		}
	} else {
		// nothing to coallesce with, just reinsert
		insert_freelist(block);
	}
}

/**
 * Will update the left size of the block to the right of the block passed in
 */
static inline void update_left_size(header * block) {
	header * next = (header *)((char*)block + get_object_size(block));
	next->object_left_size = get_object_size(block);
}

/**
 * Returns the freelist index of a block
 */
static inline size_t get_index(header * block) {	
	size_t idx = (get_object_size(block) - ALLOC_HEADER_SIZE)/ sizeof(size_t) - 1;
	if (idx > N_LISTS - 1) idx = N_LISTS-1;
	return idx;
}

/**
 * Will remove the block from the specified freelist
 */
static inline void remove_from_freelist(header * block, size_t index) {
	header * sentinelNode = &freelistSentinels[index];
	header * cur = sentinelNode->next;
	while (cur != block) {
		cur = cur->next;
	}
	cur->prev->next = cur->next;
	cur->next->prev = cur->prev;
}

/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
         fast != freelist; 
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_object_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}
	
	for (; get_object_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_object_size(chunk)  != get_right_header(chunk)->object_left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}
	
	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_object_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem; 
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}
