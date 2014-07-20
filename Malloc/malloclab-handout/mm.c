/*
 * mm.c
 * Yang Wu
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
#define CHUNKSIZE  (1<<8)  /* Extend heap by this amount (bytes) */
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
 * macro to inline
 */
static inline unsigned GET(void *p) {
    /*
     * #define GET(p)       (*(unsigned int *)(p))
     * ------------------------------------
     * read a word at address p 
     */
    return (*(unsigned *)(p));
}

static inline void PUT(void *p, unsigned val) {
    // #define PUT(p, val)  (*(unsigned int *)(p) = (val))
    *(unsigned *)(p) = val;
}

static inline unsigned GET_SIZE(void *p) {
    // #define GET_SIZE(p)  (GET(p) & ~0x3)
    return (GET(p) & ~0x3);
}               
static inline int GET_ALLOC(void *p) {
    // #define GET_ALLOC(p) (GET(p) & 0x1)
    return (GET(p) & 0x1);
}

/* Given block ptr bp, compute address of its header and footer */
static inline char* HDRP(void *p) {
    // #define HDRP(bp)       ((char *)(bp) - WSIZE)
    return ((char *)(p) - 4);
} 

// ALARM: this only works for free block
static inline char* FTRP(void *p) {
    // #define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
    return ((char *)(p) + GET_SIZE(HDRP(p)) - WSIZE);
}

static inline char* NEXT_BLKP(void *p) {
    // #define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
    return ((char *)(p) + GET_SIZE(HDRP(p)));
}

// only works for free block
static inline char* PREV_BLKP(void *p) {
    // #define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
    return ((char *)(p) - GET_SIZE(((char *)(p) - WSIZE)));
}

static inline void SET_ALOC(void *bp) {
    // flag indicate free/allocate of this block
    PUT(bp, (GET(bp) | 1));
}

static inline void SET_FREE(void *bp) {
    // flag indicate free/allocate of previous block
    PUT(bp, GET(bp) & ~1);
}

static inline void SET_PREV_FREE(void *bp, char *p){
    int off = p ? p - heap_listp : -1;
    PUT(bp, off);
}

static inline void SET_PREV_ALOC_FLAG(void *bp){
    PUT(bp, GET(bp) | 0x02);
}

static inline void SET_PREV_FREE_FLAG(void *bp) {
    PUT(bp, GET(bp) & ~0x02);
}

static inline void SET_NEXT_FREE(void * bp, char * p) {
    int off = p ? p - heap_listp : -1;
    PUT((char*)FTRP(bp) - 4, off);
}

static inline void SET_SIZE(void * bp, size_t size) {
    unsigned flag = GET(bp) & 0x03;
    PUT(bp, size|flag);
}

static inline int GET_LEVEL(size_t size) {
    int r = 0, s = 16;
    
    while ((int)size > s - 1 && r < SEGLEVEL) {
        s <<= 1;
        r++;
    }
    
    return r - 1;
}

// get the head of free list
static inline char **GET_HEAD(int level) {
    char *bp = free_table + (level * DSIZE);
    return (char **)(bp);
}
// get the end of free list
static inline char **GET_END(int level) {
    char *bp = free_table + (level * DSIZE) + WSIZE;
    return (char **)(bp);    
}

static inline void* PREV_FREE(void * bp) {
    int off = GET(bp);
    if (off < 0) return NULL;
    return heap_listp + off;
}

static inline void* NEXT_FREE(void *bp) {
    int off = GET((char*)FTRP(bp) - 4);
    if (off < 0) 
        return NULL;
  
    return heap_listp + off;
} 

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);

static void checkfreetable();
static void printblock(void *bp);
static int checkblock(void *bp);

/*
 *  Block Functions
 *  ---------------
 *  TODO: Add your comment describing block functions here.
 *  The functions below act similar to the macros in the book, but calculate
 *  size in multiples of 4 bytes.
 */


// Return the size of the given block in multiples of the word size
static inline unsigned int block_size(const uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return (block[0] & 0x3FFFFFFF);
}

// Return true if the block is free, false otherwise
static inline int block_free(const uint32_t* block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return !(block[0] & 0x40000000);
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

// Return the header to the previous block
static inline uint32_t* block_prev(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return block - block_size(block - 1) - 2;
}

// Return the header to the next block
static inline uint32_t* block_next(uint32_t* const block) {
    REQUIRES(block != NULL);
    REQUIRES(in_heap(block));

    return block + block_size(block) + 2;
}


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
    PUT(heap_listp + offset, PACK(4, 1));     /* Prologue header */
    PUT(heap_listp + offset + 4, PACK(0, 1)); /* Epilogue header */
    
    SET_PREV_ALOC_FLAG(heap_listp + offset); // header
    SET_PREV_ALOC_FLAG(heap_listp + offset + 4); // Segregated Free List
    
    heap_listp += (offset + 4);
    
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/*
 * malloc
 */
void *malloc (size_t size) {
    mm_checkheap(1);  // Let's make sure the heap is ok!
    
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
    
    /* No fit found. Get more memory and place the block */
    int available = 0; // available size in heap
    
    if (heap_endp && !GET_ALLOC(HDRP(heap_endp))) {
        available = GET_SIZE(HDRP(heap_endp)); // get left space if available...
    }
    
    extendsize = MAX(asize - available, CHUNKSIZE); // use available size to reduce external fragmentation
    
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
    
    SET_FREE(HDRP(ptr));
    PUT(FTRP(ptr), GET(HDRP(ptr))); // make footer consist with header
    coalesce(ptr);
}

static void INSERT_NODE(int level, void *bp) {
    char **group_head = (char **)(free_table + (level * DSIZE));
    char **group_end = (char **)(free_table + (level * DSIZE) + WSIZE);
    
    if (!(*group_head)) {
        // empty list
        *group_head = bp;
        *group_end = bp;
        SET_PREV_FREE(bp, NULL);
        SET_NEXT_FREE(bp, NULL);
    } else {
        if ((char *)bp < (*group_head)) {
            // insert at head
            SET_PREV_FREE(*group_head, bp);
            SET_NEXT_FREE(bp, *group_head);
            SET_PREV_FREE(bp, NULL);
            *group_head = bp;
        } else if ((*group_end) < (char *)bp) {
            // insert to tail
            SET_NEXT_FREE(*group_end, bp);
            SET_PREV_FREE(bp, *group_end);
            SET_NEXT_FREE(bp, NULL);
            *group_end = bp;
        } else {
            // find some place in the list
            char *c = *group_head;
            while (c < (char *)bp) {
                c = NEXT_FREE(c);
            }
            SET_NEXT_FREE(PREV_FREE(c), bp);
            SET_PREV_FREE(bp, PREV_FREE(c));
            SET_PREV_FREE(c, bp);
            SET_NEXT_FREE(bp, c);
        }
    }
}

static void DELETE_NODE(int level, void *bp) {
    char **group_head = GET_HEAD(level);
    char **group_end = GET_END(level);
    
    if (bp == *group_head) {
        *group_head = NEXT_FREE(bp);
        if (*group_head) {
            SET_PREV_FREE(*group_head, NULL);
        } else {
            *group_end = NULL;
        }
    } else if (bp == *group_end) {
        *group_end = PREV_FREE(bp);
        if (*group_end) {
            SET_NEXT_FREE(*group_end, NULL);
        } else {
            *group_head = NULL;
        }
    } else {
        SET_NEXT_FREE(PREV_FREE(bp), NEXT_FREE(bp));
        SET_PREV_FREE(NEXT_FREE(bp), PREV_FREE(bp));
    }
}


static void *coalesce(void *bp)
{
    size_t prev_alloc = !!(GET(HDRP(bp))& 0x02); // use free bit to store info about previous allocation
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    if (prev_alloc && next_alloc) {            /* Case 1 0 1 */
        //return bp;
    }
    
    else if (prev_alloc && !next_alloc) {      /* Case 1 0 0 */
        if (heap_endp == NEXT_BLKP(bp)) { 
            // free block right before the last one
            heap_endp = bp;
        }
        // free block in the middle
        DELETE_NODE(GET_LEVEL(GET_SIZE(HDRP(NEXT_BLKP(bp)))), NEXT_BLKP(bp));
        
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        
        PUT(HDRP(bp), SUPER_PACK(size, 0x02, 0));
        PUT(FTRP(bp), SUPER_PACK(size, 0x02, 0));
    }
    
    else if (!prev_alloc && next_alloc) {      /* Case 0 0 1 */
        int c = (bp == heap_endp); // free end of heap
        
        DELETE_NODE(GET_LEVEL(GET_SIZE(HDRP(PREV_BLKP(bp)))), PREV_BLKP(bp));
        
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        SET_SIZE(FTRP(bp), size); // new size
        SET_SIZE(HDRP(PREV_BLKP(bp)), size);
        
        bp = PREV_BLKP(bp);
        
        if( c ) { 
            heap_endp = bp;
        }
    }
    
    else {                                     /* Case 0 0 0 */
        int c = (NEXT_BLKP(bp) == heap_endp); // free one block before end of heap
        
        DELETE_NODE(GET_LEVEL(GET_SIZE(HDRP(PREV_BLKP(bp)))), PREV_BLKP(bp));
        DELETE_NODE(GET_LEVEL(GET_SIZE(HDRP(NEXT_BLKP(bp)))), NEXT_BLKP(bp));
        
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        
        SET_SIZE(HDRP(PREV_BLKP(bp)), size);
        SET_SIZE(FTRP(NEXT_BLKP(bp)), size);
        
        bp = PREV_BLKP(bp);
        
        if ( c ) {
            heap_endp = bp;
        }
    }
    SET_PREV_FREE_FLAG(HDRP(NEXT_BLKP(bp)));
    INSERT_NODE(GET_LEVEL(GET_SIZE(HDRP(bp))), bp); // update free list
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
    oldsize = GET_SIZE(HDRP(oldptr));
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

static void checkfreetable() {
    printf("Free table:\n");
    for (int i = 0; i < SEGLEVEL; i++) {
        char * bp = free_table + (i*DSIZE);
        printf("Level %d: head[%p], tail[%p]\n", i, *(char **)bp, *(char **)(bp + WSIZE));
    }
}

static void printblock(void *bp) 
{
    size_t hsize, halloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  

    if (hsize == 0) {
        printf("%p: EOL, prev_alloc: [%d]\n", bp, GET(HDRP(bp)) & 0x02);
        return;
    }

    if (halloc){
        printf("%p: header: [%u:%c], prev_alloc: [%d]\n", 
            bp, (unsigned)hsize, (halloc ? 'a' : 'f'), GET(HDRP(bp)) & 0x02);
    } else {
        printf("%p: header: [%u:%c], footer: [%u, %c], prev[%p], next[%p], prev_alloc: [%d]\n", 
            bp, (unsigned)hsize, (halloc ? 'a' : 'f'), GET_SIZE(FTRP(bp)), (GET_ALLOC(FTRP(bp)) ? 'a' : 'f'), 
            (void *)PREV_FREE(bp), (void *)NEXT_FREE(bp), GET(HDRP(bp)) & 0x02);
    }

}

static int checkblock(void *bp) 
{
    if ((size_t)bp % 8) {
        printf("Error: %p is not doubleword aligned\n", bp);
        return -1;
    }
    if (!GET_ALLOC(HDRP(bp))) { // free block
        if (GET_SIZE(HDRP(bp)) != GET_SIZE(FTRP(bp))) {
            printf("Error: header does match footer.\n");
            return -1;
        }
    }
    return 0;
}


// Returns 0 if no errors were found, otherwise returns the error
int mm_checkheap(int verbose) {
    char *bp = heap_listp;
    checkfreetable();
    
    if (verbose)
        printf("Heap (%p):\n", heap_listp);
        
    if ((GET_SIZE(HDRP(heap_listp)) != 4) || !GET_ALLOC(HDRP(heap_listp))) {
    	printf("Bad prologue header\n");
    	return 1;
    }
        
    if (verbose) {
        printblock(heap_listp);	
    }
        
    for (bp = NEXT_BLKP(heap_listp); GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose) {
            printblock(bp);	
        } 
        checkblock(bp);
    }    
    
    if (verbose)
        printblock(bp);
        
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) {
        printf("Bad epilogue header\n");        
        return 1;
    }
    
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
    int prev_alloc = !!(GET(HDRP(bp)) & 0x02);
    
    PUT(HDRP(bp), SUPER_PACK(size, prev_alloc << 1, 0));         /* Free block header */
    PUT(FTRP(bp), SUPER_PACK(size, prev_alloc << 1, 0));         /* Free block footer */
    
    SET_PREV_FREE(bp, NULL);
    SET_NEXT_FREE(bp, NULL);
    
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
    
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

static void place(void *bp, size_t asize)
/* $end mmplace-proto */
{
    size_t csize = GET_SIZE(HDRP(bp));
    
    if ((csize - asize) >= 16) { // min. requirement
        int c = (bp == heap_endp);
    	
        DELETE_NODE(GET_LEVEL(GET_SIZE(HDRP(bp))), bp);
    	
        SET_SIZE(HDRP(bp), asize);
        SET_ALOC(HDRP(bp));
        bp = NEXT_BLKP(bp);
        
        PUT(HDRP(bp), SUPER_PACK(csize-asize, 0x02, 0));
        PUT(FTRP(bp), SUPER_PACK(csize-asize, 0x02, 0));
        
        INSERT_NODE(GET_LEVEL(GET_SIZE(HDRP(bp))), bp);
        
        if (c) {
            heap_endp = bp;
        }
    }
    else {
        DELETE_NODE(GET_LEVEL(GET_SIZE(HDRP(bp))), bp);
        SET_ALOC(HDRP(bp));
        SET_PREV_ALOC_FLAG(HDRP(NEXT_BLKP(bp)));
    }
}

static void *find_fit(size_t asize)
{
    // first fit
    void *bp;
    char *group_head;
    
    int level = GET_LEVEL(asize);

    while (level < SEGLEVEL) { // serach in the size-class from small to large
        group_head = *(GET_HEAD(level));
        for (bp = group_head; bp && GET_SIZE(HDRP(bp)) > 0; bp = NEXT_FREE(bp)) {
            if (asize <= GET_SIZE(HDRP(bp))) {
                return bp;
            }
        }
        level++;
    }
    
    return NULL; /* No fit */
}
