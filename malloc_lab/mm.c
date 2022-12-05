/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void *first_fit(size_t asize);
static void *next_fit(size_t asize);
static void place(void *bp, size_t asize);

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8 // 정렬 기준 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7) // size 할당이 들어오면 8의 배수로 반올림  


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4 // 1개의 word 사이즈
#define DSIZE 8 // double word 사이즈
// 초기 가용 블록과 힙 확장을 위한 기본 크기
#define CHUNKSIZE (1<<12) // 001을 왼쪽으로 12칸 쉬프트 => 4096 = 4kb

// 주어진 두 값중 더 큰 값을 정하는 MAX 함수
#define MAX(x, y) ((x) > (y) ? (x) : (y)) // 삼항연산자 if x > y = x else = y

// 크기와 할당 비트를 OR 연산해서 헤더와 푸터에 저장할 수 있는 값
#define PACK(size, alloc) ((size) | (alloc)) // alloc : 가용 여부(ex. 000) / size : block size를 의미 => 합치면 온전한 주소가 나옴

// 인자 p가 참조하는 워드를 읽어서 리턴
#define GET(p) (*(unsigned int*)(p)) // 4byte 블록의 주소에서 값을 참조
// 인자 p가 가리키는 워드에 val을 저장
#define PUT(p, val) (*(unsigned int*)(p) = (val)) // 4byte 블록 주소의 값에 val 대입

// 각각 주소 p에 있는 헤더 또는 푸터의 size와 할당 비트를 리턴
#define GET_SIZE(p) (GET(p) & ~0x7) // ~0x7 = 11111000, & 연산하면 000 앞에 수만 가져올 수 있음, 헤더에서 블록 size만 가져오겠다
#define GET_ALLOC(p) (GET(p) & 0x1) // 0x1 = 00000001, & 연산하면 할당 여부만 확인 가능

// 각각 블록 헤더와 푸터를 가리키는 포인터를 리턴
#define HDRP(bp) ((char*)(bp) - WSIZE) // 현재 bp에서 - 4를 하면 헤더의 주소를 가리킴
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // bp에서 블록의 사이즈만큼 + 해준 뒤 - 8을 하면 푸터의 주소를 가리킴

// 다음과 이전 블록의 포인터를 각각 리턴
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE))) // 현재 bp에서 블록 사이즈만큼 더해준 뒤 - 4를 하면 다음 블록의 bp를 가리킴
// 현재 블록의 이전 블록 위치로 이동하는 함수
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE))) // 현재 bp에서 블록 사이즈만큼 빼준 뒤 - 8을 하면 이전 블록의 bp를 가리킴

// 초기에 세팅할 힙
static char *heap_listp; // 가용리스트의 시작 포인터
static char *last_bp; // 이전 검색 포인터


/* 
    힙 연장 함수
    힙이 초기화 될 때, mm_malloc이 적당한 맞춤 fit을 찾지 못했을 때 선언
*/
static void *extend_heap(size_t words){
    char *bp;
    size_t size; // 이 함수에서 넣을 size를 하나 만들어줌

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; // 받은 값이 홀수면 8의 배수를 맞춰주기 위해 +1
    if ((long)(bp = mem_sbrk(size)) == -1){ // 가용리스트 내에 저장할 수 있는지 검사
        return NULL; // 가용리스트를 초과한다면 NULL 반환
    }

    /* Initialize free block header/footer and the epilogue header */
    // 가용 블록의 헤더와 푸터 그리고 에필로그 헤더 초기화
    PUT(HDRP(bp), PACK(size, 0));               /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));               /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));       /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp); // 이전의 블록이 가용 블록이라면 연결
}

/*
    메모리를 검사해서 크기가 충분한 공간에 메모리 할당
*/
static void *find_fit(size_t asize){
    // return first_fit(asize);
    return next_fit(asize);
}


/*
    메모리의 처음부터 끝까지 검사하여 크기에 알맞는 공간에 메모리 할당
*/
static void *first_fit(size_t asize){
    void  *bp;

    // heap_listp부터 헤더의 사이즈가 0이 될 때(에필로그 헤더의 크기 = 0)까지 다음 블록으로 넘겨가며 탐색
    for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){ //찾은 블록이 가용 블록이면서 사이즈가 asize보다 클 경우
            // bp 반환
            return bp;
        }
    }
    
    return NULL; // 할당 불가
}

/*
    메모리의 마지막 포인터부터 검사하여 크기에 알맞는 공간에 메모리 할당
*/
static void *next_fit(size_t asize){
    void *bp;

    for(bp = last_bp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){ // 마지막 검색 포인터부터 블록의 사이즈가 0이 나올 때 까지 다음 블록으로 이동
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){ // 가용상태이고 해당 블록에 할당이 가능하다면
            last_bp = bp; // 포인터 갱신
            return bp; // 포인터 반환
        }
    }
    // 위의 검색에서 나오지 않았다면
    for(bp = heap_listp; bp < last_bp; bp = NEXT_BLKP(bp)){ // 가용 리스트 시작점 부터 마지막 검색 포인터 까지 다음 블록으로 이동
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){ // 가용상태이고 해당 블록에 할당이 가능하다면
            last_bp = bp; // 포인터 갱신
            return bp; // 포인터 반환
        }
    }

    return NULL; // 할당 불가
}

/*
    가용 블록 분할
*/
static void place(void *bp, size_t asize){ // 인자값 = 들어갈 위치와 크기
    
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록 사이즈

    if((csize - asize) >= (2*DSIZE)){ // 현재 블록 사이즈 안에 요청받은 asize를 넣어도 2*DSIZE 이상 남는 경우

        PUT(HDRP(bp), PACK(asize, 1)); // 헤더 위치에 asize만큼 넣고 할당 상태로 변경
        PUT(FTRP(bp), PACK(asize, 1)); // 푸터 위치에 asize만큼 넣고 할당 상태로 변경

        // 다음 블록 이동을 위해 bp 갱신
        bp = NEXT_BLKP(bp);

        PUT(HDRP(bp), PACK(csize - asize, 0)); // 나머지 블록은 가용 상태로 변경
        PUT(FTRP(bp), PACK(csize - asize, 0)); // 나머지 블록은 가용 상태로 변경

    }else{ // 남은 공간의 크기가 16byte보다 작으면 => 어차피 8배수 정렬이 안되므로 전부 할당

        PUT(HDRP(bp), PACK(csize, 1)); // 헤더에 asize를 넣고 할당 상태로 변경
        PUT(FTRP(bp), PACK(csize, 1)); // 푸터에 asize를 넣고 할당 상태로 변경

    }
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) - 1){ // 4 word를 할당 가능한지 검사
        return -1; // 불가능하면 -1 반환
    }

    PUT(heap_listp, 0);                             /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        /* Epilogue header */

    heap_listp += (2*WSIZE); // 가용리스트의 위치 설정
    last_bp = heap_listp;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    // CHUNKSIZE 사이즈 만큼 힙을 확장해 초기 가용 블록 생성 1kb
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL){ 
        return -1; // 실패하면 -1 반환
    }

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) /* 블록을 할당하는 함수 */
{
    // 기존 malloc 코드
    // int newsize = ALIGN(size + SIZE_T_SIZE);
    // void *p = mem_sbrk(newsize);
    // if (p == (void *)-1)
	// return NULL;
    // else {
    //     *(size_t *)p = size;
    //     return (void *)((char *)p + SIZE_T_SIZE);
    // }

    size_t asize; // 블록 사이즈 조정
    size_t extendsize; // heap에 맞는 fit이 없으면 확장하기 위한 사이즈
    char *bp;

    if(size == 0){ /* 인자로 받은 size가 0이면 할당 필요 없음 */
        return NULL;
    }

    /* overhead, alignment 요청 포함해서 블록 사이즈 조정 */
    if(size <= DSIZE){ // 받은 size가 DSIZE보다 작다면
        asize = 2*DSIZE; // 8의 배수로 정렬해야하기 때문에 블록 최소 크기는 16byte
    }else{ // DSIZE보다 클 때
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE); // 블록이 가질 수 있는 크기 중 최적화된 크기로 재조정
    }

    /* fit에 맞는 free 리스트를 찾는다 */
    if((bp = find_fit(asize)) != NULL){
        place(bp, asize); // 분할하여 할당
        return bp; // place를 마친 블록의 위치를 리턴
    }

    /* fit에 맞는게 없다면 메모리를 더 가져와 block을 위치시킨다 */
    extendsize = MAX(asize, CHUNKSIZE); // asize와 CHUNKSIZE중 큰 값

    if((bp = extend_heap(extendsize/WSIZE)) == NULL){ // 힙 확장해서 추가적인 가용블록 생성
        return NULL;
    }

    place(bp, asize); // 분할하여 할당
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 * 블록의 할당을 해제함
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); // 해당 블록의 size를 알아내 헤더와 푸터의 정보 수정

    // 헤더와 푸터를 size, 0으로 변경
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // 앞, 뒤 가용 상태 확인 후 연결
    coalesce(bp);
}

// 해당 가용 블록을 앞 뒤 가용 블륵과 연결하고 연결된 가용 블록의 주소를 리턴
static void *coalesce(void *bp){
    // 직전 블록의 푸터, 직후 블록의 헤더를 보고 가용 블록인지 확인
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    // 지금 블록의 헤더 사이즈
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc){                // case 1 이전과 다음 블록 모두 할당 상태인 경우
        last_bp = bp;
        return bp; // 현재 블록만 반환
    }

    else if(prev_alloc && !next_alloc){          // case 2 이전 블록은 할당, 다음 블록은 가용 상태인 경우
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 현재 블록의 사이즈 + 다음 블록의 사이즈
        PUT(HDRP(bp), PACK(size, 0)); // 헤더 갱신
        PUT(FTRP(bp), PACK(size, 0)); // 푸터 갱신
    }

    else if(!prev_alloc && next_alloc){          // case 3 이전 블록은 가용, 다음 블록은 할당 상태인 경우
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); // 현재 블록의 사이즈 + 이전 블록의 사이즈
        PUT(FTRP(bp), PACK(size, 0)); // 푸터 갱신
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 헤더 갱신
        bp = PREV_BLKP(bp); // 이전 블록의 포인터로 변경
    }

    else {                                       // case 4 이전과 다음 블록 모두 가용 상태인 경우
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 현재 블록의 사이즈 + 이전 블록, 다음 블록의 사이즈
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 헤더 갱신
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록의 푸터 갱신
        bp = PREV_BLKP(bp); // 이전 블록의 포인터로 변경
    }

    last_bp = bp;

    return bp; // 블록 포인터 반환
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t old_size = GET_SIZE(HDRP(ptr)); // 현재 할당되어 있는 공간
    size_t new_size = size + (2 * WSIZE); // 헤더와 푸터 공간 +

    if(new_size <= old_size){
        return ptr;
    }else{
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr))); // 다음 블록의 가용상태 확인
        size_t current_size = old_size + GET_SIZE(HDRP(NEXT_BLKP(ptr))); // 다음 블록의 사이즈와 현재 블록의 사이즈 더함

        if(!next_alloc && current_size >= new_size){ // 다음블록이 가용상태이고, 새로 할당하는 사이즈가 들어갈 공간이 충분하다면
            PUT(HDRP(ptr), PACK(current_size, 1)); // 헤더 갱신
            PUT(FTRP(ptr), PACK(current_size, 1)); // 푸터 갱신

            return ptr;
        }else{ // 다음 블록이 할당상태이거나, 새로 할당하는 사이즈가 들어갈 공간이 부족하다면
            void *new_bp = mm_malloc(new_size); // 새로운 할당에 대한 블록 포인터
            memcpy(new_bp, ptr, new_size); // 새로운 할당 블록에 ptr부터 new_size까지의 크기의 블록 할당

            mm_free(ptr); // 기존의 블록 할당 해제
            return new_bp; // 새로운 블록 포인터 반환
        }
    }
}