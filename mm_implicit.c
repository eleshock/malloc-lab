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
    "SWJUNGLE_4th_A",
    /* First member's full name */
    "Seung-won Lee",
    /* First member's email address */
    "energydonation1@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


#define WSIZE 4 // word and header footer 사이즈를 byte로. 
#define DSIZE 8 // double word size를 byte로
#define CHUNKSIZE (1<<12) // heap 확장을 위한 기본 크기(최소크기)를 4KB로 지정

#define MAX(x,y) ((x)>(y)? (x) : (y)) // x, y 비교하여 큰 값 취하기

// size를 pack하고 개별 word 안의 bit를 할당 (size와 alloc을 비트연산), header와 footer가 해당 데이터를 갖고 있음
#define PACK(size,alloc) ((size)| (alloc)) // | 연산을 통해 block size와 alloc 여부를 모두 포함한 데이터 획득

/* address p에 있는 words를 read(GET) or write(PUT) */
#define GET(p) (*(unsigned int*)(p)) // 포인터를 써서 p를 참조한다. 주소와 값(값에는 다른 블록의 주소를 담는다.)을 알 수 있음. 다른 블록을 가리키거나 이동할 때 쓸 수 있음
#define PUT(p,val) (*(unsigned int*)(p)=(int)(val)) // 블록의 주소를 담음. 위치를 담아야지 나중에 헤더나 푸터를 읽어서 이동 혹은 연결할 수 있음

/* address p위치로부터 size를 읽고 field를 할당 */
#define GET_SIZE(p) (GET(p) & ~0x7) // '~'은 not연산으로 11111000이 됨. 비트 연산하면 끝 3자리(alloc 여부)를 제외하고 size만 확인
#define GET_ALLOC(p) (GET(p) & 0x1) // 00000001과의 & 연산을 통해 헤더에서 alloc 여부만 확인

/* given block ptr bp, header와 footer의 주소 */
#define HDRP(bp) ((char*)(bp) - WSIZE) // Header의 주소를 가리키는 포인터
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // Footer의 주소를 가리키는 포인터

/* given block ptr bp, 이전 블록과 다음 블록의 주소를 계산*/
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE))) // 다음 블록의 bp 위치로 이동
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE))) // 이전 블록의 bp위치로 이동
static char *heap_listp;  // 최초 가용 블록으로 힙 생성 시 시작 지점의 포인터

static void *extend_heap(size_t words);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* create 초기 빈 heap*/
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void*)-1){ // 최초 가용 블록으로 힙 생성(+ 생성 불가능시 -1 리턴)
        return -1;
    }
    PUT(heap_listp,0); // 더블워드 경계 정렬을 위한 미사용 패딩 초기화
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1)); // prologue header 초기화
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1)); // prologue footer 초기화
    PUT(heap_listp + (3*WSIZE), PACK(0,1)); // epilogue block header 초기화
    heap_listp+= (2*WSIZE); // prologue header와 footer 사이로 포인터 이동. header 뒤에 위치하여 향후 다른 블록의 bp로 접근

    if (extend_heap(CHUNKSIZE/WSIZE)==NULL) // 초기화 시 chuncksize만큼 힙을 늘려줌
        return -1;
    return 0;
}

/*
 * coalesce - 블록 연결하는 함수 만들기
 */

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 직전 블록의 가용 여부 확인
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 직후 블록의 가용 여부 확인
    size_t size =  GET_SIZE(HDRP(bp)); // 현재 블록의 사이즈 확인

    if (prev_alloc && next_alloc){ // case 1 - 직전과 직후 블록이 모두 할당 되어있는 경우, 연결가능한 가용블록이 없으므로 bp를 그대로 리턴
        return bp;
    }
    else if (prev_alloc && !next_alloc){ // case2 - 직후 블록이 가용 상태이므로 현재 블록과 연결
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 직후 블록의 헤더로 접근하여 그 블록의 크기 확인 후 현재 블록의 사이즈에 추가
        PUT(HDRP(bp),PACK(size,0)); // 헤더를 먼저 갱신(Footer를 갱신하기 전에 Header에 추가된 size 정보가 갱신되어 있어야 함)
        PUT(FTRP(bp), PACK(size,0)); // 푸터 갱신
    }
    else if(!prev_alloc && next_alloc){ // case 3 - 직전 블록이 가용 상태이므로 현재 블록과 연결
        size+= GET_SIZE(HDRP(PREV_BLKP(bp))); // 직전 블록의 헤더로 접근하여 그 블록의 크기 확인 후 현재 블록의 사이즈에 추가
        PUT(FTRP(bp), PACK(size,0));  // 푸터에 먼저 조정하려는 크기로 상태 변경
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0)); // 현재 헤더에서 그 앞블록의 헤더 위치로 접근하여 변경된 정보 갱신
        bp = PREV_BLKP(bp); // bp를 그 앞블록의 헤더로 이동(늘린 블록의 헤더이니까.)
    }
    else { // case 4- 이전 블록과 다음 블록 모두 가용상태. 이전,현재,다음 3개의 블록 모두 하나의 가용 블록으로 통합.
        size+= GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 이전 블록 헤더, 다음 블록 푸터 까지로 사이즈 늘리기
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0)); // 헤더부터 앞으로 가서 사이즈 넣고
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0)); // 푸터를 뒤로 가서 사이즈 넣는다.
        bp = PREV_BLKP(bp); // 헤더는 그 전 블록으로 이동.
    }
    return bp; // 4개 케이스중에 적용된거로 bp 리턴
}

/*
 * extend_heap - 새 가용 블록으로 힙 확장하기
 */

static void *extend_heap(size_t words) // 새 가용 블록으로 힙 확장
{
    char *bp;
    size_t size;
    /* alignment 유지를 위해 짝수 개수의 words를 Allocate */
    size = (words%2) ? (words+1) * WSIZE : words * WSIZE; // 삼항 연산자로 words의 수를 짝수로 맞춰주고, 다시 WSIZE를 곱해서 나누기 전으로 복구해줌
    if ((long)(bp = mem_sbrk(size)) == -1){ // sbrk로 size로 늘려서 long 형으로 반환한다.(한번 쫙 미리 늘려놓는 것) mem_sbrk가 반환되면 bp는 현재 만들어진 블록의 끝에 가있음.
        return NULL;
    } // 사이즈를 늘릴 때마다 old brk는 과거의 mem_brk위치로 감.

    /* free block 헤더와 푸터를 init하고 epilogue 헤더를 init*/
    PUT(HDRP(bp), PACK(size,0)); // free block header 초기화
    PUT(FTRP(bp),PACK(size,0)); // free block footer 초기화
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); // epilogue header 위치 새로 갱신

    /* 만약 인접블록이 가용블록이면 연결 */
    return coalesce(bp); // 처음에는 coalesce를 할게 없지만 함수 재사용을 위해 리턴값으로 선언
}


/*
 * find_fit - 가용 리스트에 적절한 블록을 찾는 함수
 */

static void *find_fit(size_t asize) // first fit 검색을 수행
{
    void *bp;
    for (bp= heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){ // heap_listp에서 시작하여 size가 0인 epilogue block을 만날 때까지 계속 다음 블록의 size를 확인
        if (!GET_ALLOC(HDRP(bp)) && (asize<=GET_SIZE(HDRP(bp)))){ // 현재 size를 확인 중인 블록이 가용 상태이고 asize보다 작으면
            return bp; // 해당 블록의 bp를 리턴
        }
    }
    return NULL;  // 맞는 블록을 찾지 못하면 NULL 리턴
}

/*
 * place - 위치와 할당할 크기를 인자로 받음
 */

static void place(void *bp, size_t asize) // 들어갈 위치를 포인터로 받는다.(find fit에서 찾는 bp) 크기는 asize로 받음.
    // 요청한 블록을 가용 블록의 시작 부분에 배치, 나머지 부분의 크기가 최소 블록크기와 같거나 큰 경우에만 분할하는 함수.
{
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 할당처리 해주려는 가용 블록의 사이즈 확인
    if ( (csize-asize) >= (2*DSIZE)){ // 현재 블록 사이즈 내에서 asize를 넣어도 2*DSIZE(4칸)이상 남으면
        PUT(HDRP(bp), PACK(asize,1)); // header에 asize만큼만 할당했다고 갱신(남은 csize-asize만큼의 블록은 가용블록으로 남아있음)
        PUT(FTRP(bp), PACK(asize,1)); // footer도 갱신
        bp = NEXT_BLKP(bp); // 자르고 남은 가용블록의 bp 위치로 이동
        PUT(HDRP(bp), PACK(csize-asize,0)); // 나머지 블록은(csize-asize) 다 가용하다(0)하다라는 것을 header에 갱신
        PUT(FTRP(bp), PACK(csize-asize,0)); // footer에도 갱신
    }
    else{ // 잘랐을 때 4칸 이상이 안남으면 그냥 csize만큼 할당처리
        PUT(HDRP(bp), PACK(csize,1));
        PUT(FTRP(bp), PACK(csize,1));
    }
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize; // 블록 사이즈 조정
    size_t extendsize; // heap에 맞는 fit이 없으면 확장하기 위함
    char *bp;

    /* 거짓된 요청 무시*/
    if (size == 0) return NULL; // 인자로 받은 size가 0이니까 할당할 필요 없음.

    /* overhead, alignment 요청 포함해서 블록 사이즈 조정*/
    if (size <= DSIZE){
        asize = 2*DSIZE; // header와 footer를 포함해서 최소 4칸이 할당될 수 있도록 최소 size 조정
    }
    else {
        asize = DSIZE* ( (size + (DSIZE)+ (DSIZE-1)) / DSIZE ); // size보다 클 때, 블록이 가질 수 있는 크기 중에 최적화된 크기로 재조정(경계조건 고려)
    }
    /* fit에 맞는 free 리스트를 찾는다.*/
    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp; // place를 마친 블록의 위치를 리턴.
    }
    /* fit 맞는게 없을 경우 힙을 확장해서 다시 place를 수행.*/
    extendsize = MAX(asize,CHUNKSIZE); // 힙 확장 시 최소 사이즈를 CHUNKSIZE로 해줌
    if ( (bp = extend_heap(extendsize/WSIZE)) == NULL){ 
        return NULL;
    }
    place(bp, asize); // 확장된 상태에서 asize를 넣어라.
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size){
    if(size <= 0){ 
        mm_free(bp);
        return 0;
    }
    if(bp == NULL){
        return mm_malloc(size); 
    }
    void *newp = mm_malloc(size); 
    if(newp == NULL){
        return 0;
    }
    size_t oldsize = GET_SIZE(HDRP(bp));
    if(size < oldsize){
    	oldsize = size; 
	}
    memcpy(newp, bp, oldsize); 
    mm_free(bp);
    return newp;
}













