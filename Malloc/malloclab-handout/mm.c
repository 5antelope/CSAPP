/*
 * mm.c
 * Yang Wu
 * 
 * Data Structure to organize block:
 *     Segregated free lists
 *     | prologue | free list table | blocks | epilogue |
 * ----------------------------------------------------------------------------- 
 *
 * Algorithms to scan free blocks:
 *     First fit
 *
 * -----------------------------------------------------------------------------
 *
 * Block Design:
 *     | header | payload |                             -[allocated]
 *     | header | prev free | next free | footer |      -[free]: at least 16 bytes
 *
 * -----------------------------------------------------------------------------
 *
 */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include "contracts.h"

#include "mm.h"
#include "memlib.h"


// Create aliases for driver tests
// DO NOT CHANGE THE FOLLOWING!
#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif

/*
 *  Logging Functions
 *  -----------------
 *  - dbg_printf acts like printf, but will not be run in a release build.
 *  - checkheap acts like mm_checkheap, but prints the line it failed on and
 *    exits if it fails.
 */

#ifndef NDEBUG
#define dbg_printf(...) printf(__VA_ARGS__)
#define checkheap(verbose) do {if (mm_checkheap(verbose)) {  \
                             printf("Checkheap failed on line %d\n", __LINE__);\
                             exit(-1);  \
                        }}while(0)
#else
#define dbg_printf(...)
#define checkheap(...)
#endif

/*
 *  Helper functions
 *  ----------------
 */

/*
 * some basic macros from CSAPP
 * ----------------------------
 */
#define WSIZE       8       /* Word and header/footer size (bytes) */
#define DSIZE       16       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */
#define SEGLEVEL    16	    /* 16 groups for different sizes */
#define MAX(x, y) ((x) > (y)? (x) : (y))
/* alignment */
#define ALIGNMENT   8
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)
/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))
#define SUPER_PACK(size, prev_free, alloc)  ((size) | (prev_free) | (alloc)) 


static char *heap_listp = 0;  /* Pointer to first block */
static char *heap_endp  = NULL; /* Pointer to last free block in heap */
static char *free_table = NULL;  /* Pointer to free table */


// Align p to a multiple of w bytes
static inline void* align(const void const* p, unsigned char w) {
    return (void*)(((uintptr_t)(p) + (w-1)) & ~(w-1));
}

// Check if the given pointer is 8-byte aligned
static inline int aligned(const void const* p) {
    return align(p, 8) == p;
}

// Return whether the pointer is in the heap.
static inline int in_heap(const void* p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 *  Block Functions
 *  ---------------
 *  TODO: Add your comment describing block functions here.
 *  The functions below act similar to the macros in the book, but calculate
 *  size in multiples of 4 bytes.
 */

/*
 * macro to inline
 */
static inline unsigned get(const void *p) {
    /*
     * #define GET(p)       (*(unsigned int *)(p))
     * ------------------------------------
     * read a word at address p 
     */
    return (*(unsigned *)(p));
}

static inline void put(void *p, unsigned val) {
    // #define PUT(p, val)  (*(unsigned int *)(p) = (val))
    *(unsigned *)(p) = val;
}
      
// Return the size of the given block in multiples of the word size
static inline unsigned int block_size(const void* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    // #define GET_SIZE(p)  (GET(p) & ~0x3)
    return (get(block) & ~0x03);
}

// Return true if the block is allocated, false otherwise
static inline int block_alloc(const void* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    // #define GET_ALLOC(p) (GET(p) & 0x1)
    return (get(block) & 0x01);
}
/* Given block ptr bp, compute address of its header and footer */
static inline char* block_header(void *block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));                             
    // #define HDRP(bp)       ((char *)(bp) - WSIZE)
    return ((char *)(block) - 4);
} 

// ALARM: this only works for free block
static inline char* block_footer(void *block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));                             
    // #define (bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
    return ((char *)(block) + block_size(block_header(block)) - WSIZE);
}

static inline char* block_next(void* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    // #define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
    return ((char *)(block) + block_size(block_header(block)));
}

// Return the header to the previous block
static inline char* block_prev(void* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    // #define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
    return ((char *)(block) - block_size(((char *)(block) - WSIZE)));
}
static inline void set_aloc(void *block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));                             
    // flag indicate free/allocate of this block
    put(block, (get(block) | 1));
}

static inline void set_free(void *block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));                             
    put(block, get(block) & ~1);
}

static inline void set_prev_free(void *block, char *p){
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));                             
    // set 'p' to be previous free block of 'bp' in free list
    put((char*)block, p - heap_listp);
}

static inline void set_next_free(void * block, char * p) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));                             
    put((char*)(block) + 4, p - heap_listp);
}

static inline void set_prev_aloc_flag(void *block){
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));                             
    // flag indicate free/allocate of previous block
    put(block, get(block) | 0x02);
}

static inline void set_prev_free_flag(void *block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));                             
    put(block, get(block) & ~0x02);
}

static inline void set_size(void * block, size_t size) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));                             
    put(block, PACK(size, (unsigned)get(block) & 0x03));
}

static inline int get_level(size_t size) {
    int r = 0, s = 16;
    while ((int)size > s-1 && r < SEGLEVEL) {
        s = s << 1; // double the size
        r++;
    }
    return r - 1;
}

// get the head of free list
static inline char **get_head(int level) {
    return (char **)(free_table + (level * DSIZE));
}
// get the end of free list
static inline char **get_end(int level) {
    return (char **)(free_table + (level * DSIZE) + WSIZE);    
}

static inline void* prev_free(void *block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));                             
    int off = get(block);
    if (off < 0) return NULL;
    return heap_listp + off;
}

static inline void* next_free(void *block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));                             
    int off = get((char*)(block) + 4);
    if (off < 0)  return NULL;
    return heap_listp + off;
} 

// Mark the given block as free(1)/alloced(0) by marking the header and footer.
static inline void block_mark(uint32_t* block, int free) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    unsigned int next = block_size(block) + 1;
    block[0] = free ? block[0] & (int) 0xBFFFFFFF : block[0] | 0x40000000;
    block[next] = block[0];
}

// Return a pointer to the memory malloc should return
static inline uint32_t* block_mem(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));
    REQUIRES(aligned(block + 1));

    return block + 1;
}


/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);

static void checkfreetable();
static void blockdetails(void *bp);
static int checkblock(void *bp);


/*
 *  Malloc Implementation
 *  ---------------------
 *  The following functions deal with the user-facing malloc implementation.
 */

/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
    if ((heap_listp = mem_sbrk(WSIZE + SEGLEVEL*DSIZE)) == (void *)-1) 
        return -1;
    
    free_table = heap_listp;
    memset(free_table, 0, SEGLEVEL*DSIZE); // initialize the free table with 0s
    
    // store entry of Segregated Free Lists at prologue of heap 
    int offset = SEGLEVEL*DSIZE;
    
    //PUT(heap_listp, 0);                           /* Alignment padding */
    put(heap_listp + offset, PACK(4, 1));     /* Prologue header */
    put(heap_listp + offset + 4, PACK(0, 1)); /* Epilogue header */
    
    set_prev_aloc_flag(heap_listp + offset); // header
    set_prev_aloc_flag(heap_listp + offset + 4); // Segregated Free List
    
    heap_listp += (offset + 4);
    
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * malloc
 */
void *malloc (size_t size) {
#ifdef DEBUG    
    mm_checkheap(1);  // Let's make sure the heap is ok!
#endif
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;
    
    if (heap_listp == 0){
        mm_init();
    }
    
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;
    
    asize = ALIGN(size + 4); /* header = 4 byte */
    
    /* Adjust block size to include overhead and alignment reqs. */
    if (asize < 16)
        asize = 16;
    
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
#ifdef DEBUG    
        printf("malloc: before alloc.\n");
        mm_checkheap(1);
#endif    
        place(bp, asize);
#ifdef DEBUG
        printf("malloc: after alloc.\n");        
        mm_checkheap(1);
        printf("\n\n");
#endif 
        return bp;
    }
    
    /* No fit found.  more memory and place the block */
    int available = 0; // available size in heap
    
    if (heap_endp && !block_alloc(block_header(heap_endp))) {
        available = block_size(block_header(heap_endp)); // get left space if available...
    }
    
    if (asize-available > CHUNKSIZE) {
        extendsize = asize-available; // use available size to reduce external fragmentation 
    } else {
        extendsize = CHUNKSIZE;
    }
    
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * free
 */
void free (void *ptr) {
    if (ptr == NULL) {
        return;
    }

    if (heap_listp == 0){
        mm_init();
    }
    
    set_free(block_header(ptr));
    put(block_footer(ptr), get(block_header(ptr))); // make footer consist with header
    coalesce(ptr);
}

static void insert_node(int level, void *bp) {
    char **group_head = (char **)(free_table + (level * DSIZE));
    char **group_end = (char **)(free_table + (level * DSIZE) + WSIZE);
    
    if (*group_head == NULL) {
        // empty list
        *group_head = bp;
        *group_end = bp;
        set_prev_free(bp, NULL);
        set_next_free(bp, NULL);
    } else {
        if ((char *)bp < (*group_head)) {
            // insert at head
            set_prev_free(*group_head, bp);
            set_next_free(bp, *group_head);
            set_prev_free(bp, NULL);
            *group_head = bp;
        } else if ((*group_end) < (char *)bp) {
            // insert to tail
            set_next_free(*group_end, bp);
            set_prev_free(bp, *group_end);
            set_next_free(bp, NULL);
            *group_end = bp;
        } else {
            // find some place in the list
            char *c = *group_head;
            while (c < (char *)bp) {
                c = next_free(c);
            }
            set_next_free(prev_free(c), bp);
            set_prev_free(bp, prev_free(c));
            set_prev_free(c, bp);
            set_next_free(bp, c);
        }
    }
}

static void delete_node(int level, void *bp) {
    char **group_head = get_head(level);
    char **group_end = get_end(level);
    
    if (bp == *group_head) {
        *group_head = next_free(bp);
        if (*group_head) {
            set_prev_free(*group_head, NULL);
        } else {
            *group_end = NULL;
        }
    } else if (bp == *group_end) {
        *group_end = prev_free(bp);
        if (*group_end) {
            set_next_free(*group_end, NULL);
        } else {
            *group_head = NULL;
        }
    } else {
        set_next_free(prev_free(bp), next_free(bp));
        set_prev_free(next_free(bp), prev_free(bp));
    }
}


static void *coalesce(void *bp)
{
    size_t prev_alloc = !!(get(block_header(bp))& 0x02); // use free bit to store info about previous allocation
    size_t next_alloc = block_alloc(block_header(block_next(bp)));
    size_t size = block_size(block_header(bp));
    
    if (prev_alloc && next_alloc) {            /* Case 1 0 1 */
        //return bp;
    }
    
    else if (prev_alloc && !next_alloc) {      /* Case 1 0 0 */
        if (heap_endp == block_next(bp)) { 
            // free block right before the last one
            heap_endp = bp;
        }
        // free block in the middle
        delete_node(get_level(block_size(block_header(block_next(bp)))), block_next(bp));
        
        size += block_size(block_header(block_next(bp)));
        
        put(block_header(bp), SUPER_PACK(size, 0x02, 0));
        put(block_footer(bp), SUPER_PACK(size, 0x02, 0));
    }
    
    else if (!prev_alloc && next_alloc) {      /* Case 0 0 1 */
        int c = (bp == heap_endp); // free end of heap
        
        delete_node(get_level(block_size(block_header(block_prev(bp)))), block_prev(bp));
        
        size += block_size(block_header(block_prev(bp)));
        set_size(block_footer(bp), size); // new size
        set_size(block_header(block_prev(bp)), size);
        
        bp = block_prev(bp);
        
        if( c ) { 
            heap_endp = bp;
        }
    }
    
    else {                                     /* Case 0 0 0 */
        int c = (block_next(bp) == heap_endp); // free one block before end of heap
        
        delete_node(get_level(block_size(block_header(block_prev(bp)))), block_prev(bp));
        delete_node(get_level(block_size(block_header(block_next(bp)))), block_next(bp));
        
        size += block_size(block_header(block_prev(bp))) + block_size(block_footer(block_next(bp)));
        
        set_size(block_header(block_prev(bp)), size);
        set_size(block_footer(block_next(bp)), size);
        
        bp = block_prev(bp);
        
        if ( c ) {
            heap_endp = bp;
        }
    }
    set_prev_free_flag(block_header(block_next(bp)));
    insert_node(get_level(block_size(block_header(bp))), bp); // update free list
    return bp;
}

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) {
    size_t oldsize;
    void *newptr;
    
    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        free(oldptr);
        return 0;
    }
    
    /* If oldptr is NULL, then this is just malloc. */
    if(oldptr == NULL) {
        return malloc(size);
    }
    
    newptr = malloc(size);
    
    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
        return 0;
    }
    
    /* Copy the old data. */
    oldsize = block_size(block_header(oldptr));
    if(size < oldsize) 
        oldsize = size;
    memcpy(newptr, oldptr, oldsize);
    
    /* Free the old block. */
    free(oldptr);
    
    return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 */
void *calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}

static void checkfreetable(int verbose) {
     // unfinished!
    
    /*
     * All next/previous pointers are consistent 
     * All free list pointers points between mem heap lo() and mem heap hi().
     * Count free blocks by iterating through every block and traversing free list by pointers and see if they match.
     * All blocks in each list bucket fall within bucket size range (segregated list).
     */
    printf("Free table test...\n");
    if (verbose) {
        for (int i = 0; i < SEGLEVEL; i++) {
            char * bp = free_table + (i*DSIZE);
            if (!in_heap(bp)) {
                //free list pointers points between mem heap lo() and mem heap hi()                       
                printf("free list [%p] at level - %d is out of heap...\n", *(char **)bp, i);                             
            }
            printf("Level %d: head[%p], tail[%p]\n", i, *(char **)bp, *(char **)(bp + WSIZE));
        }
    }
}

static void blockdetails(void *block) 
{
    /* 
     * Check each block’s header and footer: 
     * size (minimum size, alignment), previous/next allo- cate/free bit consistency, 
     * header and footer matching each other.
     */
    size_t size, alloc;

    size = block_size(block_header(block));
    alloc = block_alloc(block_header(block));  

    if (size == 0) {
        printf("%p: empty, prev_alloc: [%d]\n", block, get(block_header(block)) & 0x02);
        return;
    }

    if (alloc){
        printf("%p: [size: %u; allocated/free: %c; prev_alloc: %d]\n", 
            block, (unsigned)size, (alloc ? 'a' : 'f'), get(block_header(block)) & 0x02);
    } 

}

static int checkblock(void *bp) 
{
    // unfinished!
    
    /*
     * Check epilogue and prologue blocks.
     * Check each block’s address alignment.
     * Check heap boundaries.
     * Check coalescing: no two consecutive free blocks in the heap.
     */
    if ((size_t)bp % 8) {
        // check alignment
        printf("%p is not well aligned!\n", bp);
        return 1;
    }
    
    if (!block_alloc(block_header(bp))) { 
        if (block_size(block_header(bp)) != block_size(block_footer(bp))) {
            printf("header & footer do not match size!\n");
            return 1;
        }
    }
    
    if (!in_heap(bp)) {
        // boundary error
        printf("boundary error!\n");
        return 1;
    }
    
    if ((unsigned)block_alloc(block_header(bp)) != get(prev_free(block_next(bp))) ) {
        printf("prev_free flag error!\n");
        return 1;
    }
    
    if (!block_alloc(block_header(bp)) && !block_alloc(block_header(block_next(bp)))) {
        printf("two consecutive free blocks in the heap!\n");
        return 1;
    }
    
    return 0;
}


// Returns 0 if no errors were found, otherwise returns the error
int mm_checkheap(int verbose) {
    // check heap   
    char *bp = heap_listp;
    
    if (verbose)
        printf("Heap (%p):\n", heap_listp);
        
    if (!block_alloc(block_header(heap_listp))) {
        // check prologue allocated;
        printf("Prologue Malicious\n");
        return 1;
    }
        
    if (verbose) {
        printf("Heap...\n");
        blockdetails(heap_listp);	
    }
        
    for (bp = block_next(heap_listp); block_size(block_header(bp)) > 0; bp = block_next(bp)) {
        if (verbose) {
            // printf("Block...");                         
            blockdetails(bp);	
        }
        // dive into the detial info about block
        checkblock(bp);
    }    
        
    if (!(block_alloc(block_header(bp)))) {
        printf("Epilogue Malicious\n");        
        return 1;
    }
    
    // check free list
    checkfreetable(verbose);
    
    return 0;
}

static void *extend_heap(size_t words)
{ // need improve!                                                     
    char *bp;
    size_t size;
    
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    /* Initialize free block header/footer and the epilogue header */
    int prev_alloc = !!(get(block_header(bp)) & 0x02) << 1;   // 8-byte alignment 
    
    put(block_header(bp), SUPER_PACK(size, prev_alloc, 0));         /* Free block header */
    put(block_footer(bp), SUPER_PACK(size, prev_alloc, 0));         /* Free block footer */
    
    set_prev_free(bp, NULL);
    set_next_free(bp, NULL);
    
    put(block_header(block_next(bp)), PACK(0, 1)); /* New epilogue header */
    
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

static void place(void *bp, size_t asize)
/* $end mmplace-proto */
{
    size_t csize = block_size(block_header(bp));
    
    if ((csize - asize) >= 16) { // min. requirement
        int c = (bp == heap_endp);
    	
        delete_node(get_level(block_size(block_header(bp))), bp);
    	
        set_size(block_header(bp), asize);
        set_aloc(block_header(bp));
        bp = block_next(bp);
        
        put(block_header(bp), SUPER_PACK(csize-asize, 0x02, 0));
        put(block_footer(bp), SUPER_PACK(csize-asize, 0x02, 0));
        
        insert_node(get_level(block_size(block_header(bp))), bp);
        
        if (c) {
            heap_endp = bp;
        }
    }
    else {
        delete_node(get_level(block_size(block_header(bp))), bp);
        set_aloc(block_header(bp));
        set_prev_aloc_flag(block_header(block_next(bp)));
    }
}

static void *find_fit(size_t asize)
{
    // first fit
    void *bp;
    char *group_head;
    
    int level = get_level(asize);

    while (level < SEGLEVEL) { // serach in the size-class from small to large
        group_head = *(get_head(level));
        for (bp = group_head; bp && block_size(block_header(bp)) > 0; bp = next_free(bp)) {
            if (!block_alloc(block_header(bp)) && asize <= block_size(block_header(bp))) {
                return bp;
            }
        }
        level++;
    }
    
    return NULL; /* No fit */
}
