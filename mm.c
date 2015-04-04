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
#include <assert.h>
#include <stdlib.h>

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
	struct node *prev;
};

/* Basic constants and macros: */
#define ASIZE	   8		  /* Number of bytes to align to */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define TSIZE	   (3 * WSIZE)	  /* Tripleword size (bytes) */
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

/* The number of segregated list */
#define BIN_NUM  (12) // xin
/* The smallest seglist range: 1 - 64 bytes*/
#define BOUND   (128) // xin

/* Global variables: */
static char *heap_listp; /* Pointer to first block */
static struct node *list_start;

static void **seg_list; // xin

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp);

/* Function prototypes that we created */
static void add_node(void *bp);
static void remove_node(void *bp);

/* Xin added 3 similar to 2 functions above*/
static void insert_block(void *bp, int size);
static void delete_block(void *bp);
static void find_block_from_list(struct node *bp, int asize);
static int get_list_index(int size);


/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
int
mm_init(void) // xin thinks this is fine now
{
	printf("ENTER INIT\n");

	/* Create the initial empty heap. */
	if ((heap_listp = mem_sbrk(3 * WSIZE)) == (void *)-1)
		return (-1);
	//PUT(heap_listp, 0);                            /* Alignment padding */ // This probably should be padded later on when we bin?

	PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */ // Xin changed here
	PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */

	heap_listp += (WSIZE); // might need change

	printf("INIT CHECKHEAP\n");
	checkheap(1);

	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
		return (-1);

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
mm_malloc(size_t size) // xin also thinks this is fine now
{
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;

	printf("ENTER MALLOC\n");

	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= ASIZE)
		asize = ASIZE + TSIZE; // basically 4 words
	else
		if (size % WSIZE == 0) // xin added this
			asize = DSIZE + size;
		else
			// asize = ASIZE * ((size + TSIZE + (ASIZE - 1)) / ASIZE);
			asize = DSIZE + (((size / WSIZE) + 1) * WSIZE); // xin changed this

	/* Search the free list for a fit. */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return (bp);
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = MAX(asize, CHUNKSIZE);

	if (extendsize % WSIZE != 0)	// xin added this
		extendsize = ((extendsize / WSIZE) + 1) * WSIZE;

	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
		return (NULL);

	place(bp, asize);

	printf("MALLOC CHECKHEAP\n");
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
mm_free(void *bp) // xin thinks this is perfect now
{
	size_t size;
	printf("ENTER FREE\n");

	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));

	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));

	insert_block(bp, size);

	coalesce(bp);

	printf("FREE CHECKHEAP\n");
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
mm_realloc(void *ptr, size_t size)  // xin has a lot of code to write for this, he thinks
{
	size_t oldsize;
	void *newptr;

	printf("ENTER REALLOC\n");

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

	printf("REALLOC CHECKHEAP\n");
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
coalesce(void *bp) // xin has an idea here but not really
{
	size_t size = GET_SIZE(HDRP(bp));
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	printf("ENTER COALESCE\n");

	if (prev_alloc && next_alloc) {                 /* Case 1 */
		printf("Case 1\n");
		return (bp);
	} else if (prev_alloc && !next_alloc) {         /* Case 2 */
		printf("Case 2\n");
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		remove_node(NEXT_BLKP(bp));
	} else if (!prev_alloc && next_alloc) {         /* Case 3 */
		printf("Case 3\n");
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		remove_node(bp);
		bp = PREV_BLKP(bp);
	} else {                                        /* Case 4 */
		printf("Case 4\n");
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
		    GET_SIZE(FTRP(NEXT_BLKP(bp)));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		remove_node(bp);
		remove_node(NEXT_BLKP(bp));
		bp = PREV_BLKP(bp);
	}
	add_node(bp);
	printf("COALESCE CHECKHEAP\n");
	checkheap(1);
	return (bp);
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
static void *
extend_heap(size_t words) // xin thinks this is good now
{
	size_t size;
	void *bp;

	printf("ENTER EXTEND HEAP\n");

	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

	if ((bp = mem_sbrk(size)) == (void *)-1)
		return (NULL);

	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	// add_node(bp); // xin changed
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

	insert_block(bp, GET_SIZE(HDRP(bp))); // xin added

	printf("EXTEND_HEAP CHECKHEAP\n");
	checkheap(1);
	/* Coalesce if the previous block was free. */
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
find_fit(size_t asize) // xin changed all of this
{
// 	//void *bp;
// 	struct node *cur = list_start;
// 	printf("ENTER FIND FIT\n");
// 	if(list_start == NULL) {
// 		printf("List is empty, can't find fit\n");
// 		return NULL;
// 	}

// 	do {
// 		printf("LOOP\n");

// /*		if (cur == NULL)
// 			printf("Cur is NULL\n");
// 		if (cur->next == NULL)
// 			printf("Cur's next is NULL\n"); */

// 		if (HDRP(cur) == NULL)
// 			printf("Header is NULL\n");

// 		printf("Could be here\n");
// 		/* [TODO] Fix the bug on the line below*/
// 		/* It has something to do with GET_SIZE */
// 		if (asize <= GET_SIZE(HDRP(cur)))
// 			printf("GET_SIZE if\n");
// 		printf("Here?\n");
// 		if (!GET_ALLOC(HDRP(cur)))
// 			printf("GET_ALLOC is the issue\n");

// 		if (!GET_ALLOC(HDRP(cur)) && asize <= GET_SIZE(HDRP(cur)))
// 			return (cur);
// 		cur = cur->next;
// 		printf("END LOOP\n");
// 	} while (cur != list_start);


// 	/* Search for the first fit. */
// 	/*for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
// 		if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp)))
// 			return (bp);
// 	}*/
// 	/* No fit was found. */
// 	printf("FIND_FIT CHECKHEAP\n");
// 	checkheap(1);
// 	return (NULL);


	int i;
	int list_idx = get_list_index(asize);

	struct node *bp;
	/* Search for the first fit from the lists with index lst_idx or bigger */
	for (i = list_idx; i < BIN_NUM; i ++) {

		bp = seg_list[i];

		if ((bp = find_block_from_list(bp, asize)) != NULL)
			return bp;
	}

	// return (NULL); // couldn't find a valid block
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

	printf("ENTER PLACE\n");

	if ((csize - asize) >= (ASIZE + TSIZE)) { // xin changed this
		delete_block(bp);

		PUT(HDRP(bp), PACK(csize - asize, 0));
		PUT(FTRP(bp), PACK(csize - asize, 0));

		insert_block(bp, (int)(csize - asize));

		bp = NEXT_BLKP(bp);

		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		// PUT(HDRP(bp), PACK(asize, 1));
		// PUT(FTRP(bp), PACK(asize, 1));
		// bp = NEXT_BLKP(bp);
		// PUT(HDRP(bp), PACK(csize - asize, 0));
		// PUT(FTRP(bp), PACK(csize - asize, 0));
		// add_node(bp);
	}

	else {
		delete_block(bp);

		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
		// PUT(HDRP(bp), PACK(csize, 1));
		// PUT(FTRP(bp), PACK(csize, 1));
		// remove_node(bp);
	}

	printf("PLACE CHECKHEAP\n");
	checkheap(1);

	// return (bp);
}


static void
add_node(void *bp)
{
	struct node *nodep = (struct node *)bp;

	printf("ENTER ADD\n");
	if (nodep == NULL)
		printf("Node pointer is NULL!\n");
	if (list_start == NULL || (list_start->next == NULL && list_start->previous == NULL)) {
		list_start = nodep;
		nodep->next = nodep;
		nodep->previous = nodep;
	} else {
		printf("Adding to list\n");
		nodep->next = list_start;
		nodep->previous = list_start->previous;
		printf("Iso 1\n");
		if(list_start->previous == NULL)
			printf("List start previous is null\n");
		if(list_start->next == NULL)
			printf("List start next is null\n");
		list_start->previous->next = nodep;
		printf("Iso 2\n");
		list_start->previous = nodep;
		printf("Iso 3\n");
		list_start = nodep;
	}

	printf("ADD CHECKHEAP\n");
	checkheap(1);

	return;
}


static void
remove_node(void *bp)
{
	assert(bp != NULL); // xin added this
	struct node *nodep = (struct node *)bp;

	printf("ENTER REMOVE\n");

	if (nodep == NULL)
		printf("Node pointer is NULL!\n");
	if (nodep->next == NULL)
		printf("Node pointer's next is NULL!\n");
	if (nodep->previous == NULL)
		printf("Node pointer's previous is NULL!\n");

	nodep->previous->next = nodep->next;
	nodep->next->previous = nodep->previous;
	nodep->next = NULL;
	nodep->previous = NULL;

	printf("REMOVE CHECKHEAP\n");
	checkheap(1);

	return;
}

// Start of Xin functions


/*
 * Requires:
 *	Valid bp
 *  Valid size
 *
 * Effects:
 * 	Find block size in bins where block size is >= to asize
 */
static void
find_block_from_list(struct node *bp, int asize)
{

	assert(asize > 0);
	assert(bp != NULL); // xin thinks this could causes problems

	size_t block_size;

	while (bp != NULL) {
		block_size = GET_SIZE(HDRP(bp));
		if ((int) block_size >= asize)
			return bp;
		bp = bp->next;
	}
}

/*
 * Requires:
 *	valid size
 * Effects:
 *	Return seglist index of block size
 */
static int
get_list_index(int size)
{

	assert(size >= 0);

	int count = size;
	int list;

	for (list = 0; list < BIN_NUM; list++) {
		if ((count <= BOUND) || (list == BIN_NUM - 1)) {
			return list;
		}

		count = count >> 1; /* divide count by 2 */
	}

	return BIN_NUM - 1;
}


/*
 * Requires:
 *	valid bp
 * Effects:
 * 	Insert block bp to a specific seglist
 * 	Insertion order will base on block size
 */
static void
insert_block(void *bp, int size)
{

	assert(bp != NULL);
	assert(size == (int)GET_SIZE(HDRP(bp)));

	int list_idx;
	struct node *new_block, *start_block = NULL;

	list_idx = get_list_index(size);

	/* LIFO insert block to seglist  */
	start_block = seg_list[list_idx];

	new_block = bp;
	/* seglist been insert into is empty */
	if (start_block == NULL) {
		new_block->prev = NULL;
		new_block->next = NULL;
		seg_list[list_idx] = new_block;
	}
	/* seglist been insert into is not empty */
	else {
		new_block->prev = NULL;
		new_block->next = start_block;
		start_block->prev = new_block;
		seg_list[list_idx] = new_block;
	}

}

/*
 * Requires:
 *	Valid BP
 * Effects:
 * 	Remove block bp from the specific seglist
 */
static void
delete_block(void *bp)
{

	assert(bp != NULL);

	struct node *current;
	struct node *smaller;
	struct node *bigger;

	int list_idx;
	size_t block_size;

	/* Get size of the block */
	block_size = GET_SIZE(HDRP(bp));

	/* Get bin index */
	list_idx = get_list_index(block_size);

	current = (struct node *)bp;
	bigger = current->prev;
	smaller = current->next;

	/* No block preceding Delete Block */
	if (bigger == NULL) {
		/* No block after Delete Block */
		if (smaller == NULL) {
			seg_list[list_idx] = NULL; // no left/right
		}
		/* Block after Delete Block */
		else {
			smaller->prev = NULL;
			seg_list[list_idx] = smaller;
		}

	/* Block preceding Delete Block */
	} else {
		/* No block after Delete Block */
		if (smaller == NULL) {
			bigger->next = NULL;
		}
		/* Block after Delete Block */
		else {
			bigger->next = smaller;
			smaller->prev = bigger;
		}
	}

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

	if (GET_SIZE(HDRP(heap_listp)) != DSIZE)
		printf("Bad prologue header: size\n");
	if (!GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header: alloc\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
		//	printblock(bp);
		checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0)
		printf("Bad epilogue header: size\n");
	if (!GET_ALLOC(HDRP(bp)))
		printf("Bad epilogue header: alloc\n");

	printf("End of checkheap\n");
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
 * particular, depressing the "Tab" key once at the start of a new line will
 * insert as many tabs and/or spaces as are needed for proper indentation.
 */

/* Local Variables: */
/* mode: c */
/* c-default-style: "bsd" */
/* c-basic-offset: 8 */
/* c-continued-statement-offset: 4 */
/* indent-tabs-mode: t */
/* End: */
