/* 
 * Simple, 32-bit and 64-bit clean allocator based on an implicit free list,
 * first fit placement, and boundary tag coalescing, as described in the
 * CS:APP2e text.  Blocks are aligned to double-word boundaries.  This
 * yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned
 * blocks on a 64-bit processor.  However, 16-byte alignment is stricter
 * than necessary; the assignment only requires 8-byte alignment.  The
 * minimum block size is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"/* Team name */",
	/* First member's full name */
	"Xin Huang",
	/* First member's email address */
	"xyh1@rice.edu",
	/* Second member's full name (leave blank if none) */
	"Leo Meister",
	/* Second member's email address (leave blank if none) */
	"lpm2@rice.edu"
};

struct node {
	struct node *next;
	struct node *previous;
};

/* Basic constants and macros: */
#define ASIZE	   8		  /* Number of bytes to align to */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define QSIZE	   (4 * WSIZE)	  /* Quadword size (bytes) */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(ASIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)



/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Global variables: */
static char *heap_listp; /* Pointer to first block */
static struct node *list_start;

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

static void splice(struct node *nodep);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 



/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
int
mm_init(void) 
{

	/* Create the initial empty heap. */
	
	struct node *head;
	printf("INIT\n");	
	if ((heap_listp = mem_sbrk(5 * WSIZE)) == (void *)-1)
		return (-1);
	//PUT(heap_listp, 0);                            /* Alignment padding */
	PUT(heap_listp, PACK(DSIZE, 1)); /* Prologue header */ 
	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
	printf("Set prologue\n");
	head = (struct node *)heap_listp + 2 * WSIZE;
	printf("Initialized head to be two words after the prologue start\n");
	/* Insert the next and previous pointers, the head of the list */
	/* Can use heap_listp + 2*WSIZE to access head of list */
	/*PUT(heap_listp + (2 * WSIZE), head.next);
	PUT(heap_listp + (3 * WSIZE), head.previous);*/
	head->previous = head;
	head->next = head;	
	list_start = head;
	
	PUT(heap_listp + (4 * WSIZE), PACK(0, 1));     /* Epilogue header */
	printf("Set header epilogue\n");
	heap_listp += (WSIZE);
	printf("Entering extend heap\n");
	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
		printf("Failed INIT\n");
		return (-1);
	}
	if (1) {
		printf("Completed init!\n");
		if (list_start == NULL)
			printf("List start is NULL!\n");	
	}
	checkheap(1);

	return (0);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *
mm_malloc(size_t size) 
{
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;
	printf("Start malloc\n");
	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);

	/* Adjust block size to include overhead and alignment reqs. */
	/* Increased size to 4 words of overhead from 2 */
	/* Smallest useable block size is now 2 words instead of 1 */
	if (size <= ASIZE)
		asize = ASIZE + QSIZE;
	else
		asize = ASIZE * ((size + QSIZE + (ASIZE - 1)) / ASIZE);

	/* Search the free list for a fit. */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return (bp);
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE, list_start)) == NULL)  
		return (NULL);
	place(bp, asize);
	checkheap(1);
	return (bp);
} 

/* 
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.
 */
void
mm_free(void *bp)
{
	size_t size;
	struct node *new_node;
	
	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	new_node = (struct node *)coalesce(bp);
	
	/* Add to beginning of free list after coalescing */
	new_node->next = list_start;
	new_node->previous = NULL;
	list_start->previous = new_node;
	list_start = new_node;
	checkheap(1);
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.  If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" may optionally be returned.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */
void *
mm_realloc(void *ptr, size_t size)
{
	size_t oldsize;
	void *newptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0) {
		mm_free(ptr);
		return (NULL);
	}

	/* If oldptr is NULL, then this is just malloc. */
	if (ptr == NULL)
		return (mm_malloc(size));

	newptr = mm_malloc(size);

	/* If realloc() fails the original block is left untouched  */
	if (newptr == NULL)
		return (NULL);

	/* Copy the old data. */
	oldsize = GET_SIZE(HDRP(ptr));
	if (size < oldsize)
		oldsize = size;
	memcpy(newptr, ptr, oldsize);

	/* Free the old block. */
	mm_free(ptr);
	checkheap(1);
	return (newptr);
}

/*
 * The following routines are internal helper routines.
 */

/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 */
static void *
coalesce(void *bp) 
{
	printf("Start coalesce\n");
	if (bp == NULL)
		printf("Pointer is NULL\n");
	size_t size = GET_SIZE(HDRP(bp));
	printf("Got size\n");
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	printf("Stored whether previous block was allocated\n");
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	printf("Stored whether the next block was allocated\n");
	printf("Finished coalesce initializations\n");
	if (prev_alloc && next_alloc) {                 /* Case 1 */
		printf("Case 1\n");
		return (bp);
	} else if (prev_alloc && !next_alloc) {         /* Case 2 */
		printf("Case 2\n");
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		splice((struct node *)NEXT_BLKP(bp));
	} else if (!prev_alloc && next_alloc) {         /* Case 3 */
		printf("Case 3\n");
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));

		/* Seems to work for now, but rather hackish */
		/* the issue arises because bp is not actually in the list yet (I think) */
		struct node *temp = (struct node *)bp;
		if (temp->next != NULL)
			splice(bp);
		bp = PREV_BLKP((void *)bp);
	} else {                                        /* Case 4 */
		printf("Case 4\n");
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
		    GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		splice((struct node *)bp);
		splice((struct node *)NEXT_BLKP(bp));
		bp = PREV_BLKP(bp);
	}
	checkheap(1);
	return (bp);
}

/* 
 * Requires:
 *   words: the number of words to increase the heap by
 *   next: next pointer at the end of the linked list, to be set to the 
 	   header of the new block
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
static void *
extend_heap(size_t words) 
{
	struct node *new_node;
	size_t size;
	void *bp;

	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *)-1)  
		return (NULL);
	
	/* Initialize the new node pointers, next precedes previous */
	/* The previous point points to the header of the previous block*/	
	new_node = (struct node *)bp;
	new_node->next = list_start;
	new_node->previous = list_start->previous;
	list_start->previous = new_node;
	/*PUT(bp, NULL);
	PUT(bp + WSIZE, HDRP(next));*/

	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
	printf("Entering coalesce from extend_heap\n");
	/* Coalesce if the previous block was free. */
	checkheap(1);
	return (coalesce(bp));
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 */
static void *
find_fit(size_t asize)
{
	//void *bp;
	struct node *cur = list_start;
	
	
	/* Iterate through the list, find first fit */
	do {
		if (asize <= GET_SIZE(HDRP(cur)))
			return cur;
		cur = cur->next;
	} while (cur != list_start);
	
	/* Search for the first fit. 
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp)))
			return (bp);
	} */
	/* No fit was found. */
	return (NULL);
}

/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size. 
 */
static void
place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));
	struct node *nodep = (struct node *) bp;
	struct node *new_nodep;

	/* increased size to account for next and previous pointer overhead */
	if ((csize - asize) >= (ASIZE + QSIZE)) { 
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		
		bp = NEXT_BLKP(bp);
		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));
		
		/* Set new node for the leftover free block */
		new_nodep = (struct node *)bp;
		
		new_nodep->previous = nodep->previous;
		new_nodep->next = nodep->next;
				
		/* Remove node from allocated block */
		splice(nodep);
		
	} else {
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
		
		/* Remove node from allocated block */
		splice(nodep);
	}
	checkheap(1);
}

static void
splice(struct node *nodep)
{
	printf("Start splice\n");
	if (nodep == NULL)
		printf("Node pointer is NULL!\n");
	if (nodep->previous == NULL)
		printf("Node pointer's previous is NULL!\n");
	if (nodep->next == NULL)
		printf("Node pointer's next is NULL!\n");

	nodep->previous->next = nodep->next;
	nodep->next->previous = nodep->previous;
	nodep->next = NULL;
	nodep->previous = NULL;
	printf("End splice\n");

}

/* 
 * The remaining routines are heap consistency checker routines. 
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static void
checkblock(void *bp) 
{

	if ((uintptr_t)bp % ASIZE)
		printf("Error: %p is not word aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency. 
 */
void
checkheap(bool verbose) 
{
	void *bp;

	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(heap_listp)) != DSIZE ||
	    !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
			printblock(bp);
		checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
		printf("Bad epilogue header\n");
}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void
printblock(void *bp) 
{
	size_t hsize, fsize;
	bool halloc, falloc;

	checkheap(false);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));  
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));  

	if (hsize == 0) {
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
	    hsize, (halloc ? 'a' : 'f'), 
	    fsize, (falloc ? 'a' : 'f'));
}

/*
 * The last lines of this file configure the behavior of the "Tab" key in
 * emacs.  Emacs has a rudimentary understanding of C syntax and style.  In
 * insert as many tabs and/or spaces as are needed for proper indentation.
 */

/* Local Variables: */
/* mode: c */
/* c-default-style: "bsd" */
/* c-basic-offset: 8 */
/* c-continued-statement-offset: 4 */
/* indent-tabs-mode: t */
/* End: */
