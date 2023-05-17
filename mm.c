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
    "team_junik",
    /* First member's full name */
    "Park Junik",
    /* First member's email address */
    "cod2048@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)



// 기본 상수, 매크로
#define WSIZE 4 // 워드, 헤더/푸터 크기 선언(메모리 블록의 크기와 관련된 정보 저장)
#define DSIZE 8 // 더블 워드, 주소 정보 저장
#define CHUNKSIZE (1<<12) // 2의 12제곱(4096bytes), 힙을 확장할 때 사용되는 양

#define MAX(x, y) ((x) > (y)? (x):(y)) // x,y 중 큰 값을 반환하는 매크로 수

// 워드
#define PACK(size, alloc) ((size) | (alloc)) // 워드(헤더, 푸터)에 할당정보(0,1)와 크기(메모리 블록의 크기) 저장(패킹)

// 주소 p에 워드 읽고 쓰기
#define GET(p)  (*(unsigned int *)(p)) // p 주소에 위치한 워드값 반환
#define PUT(p, val) (*(unsigned int*)(p) = (val)) // p 주소에 워드값 val 작성

// 주소 p의 크기와 할당상태 읽어오기
#define GET_SIZE(p) (GET(p) & ~0x7) // 크기 읽어오기, get매크로로 가져온 워드값에 ~0x7을 이용해 마지막 3비트를 0으로 설정한 후 크기 필드만 남기고 다른 비트를 0으로 만듦
#define GET_ALLOC(p) (GET(p) & 0x1) // 할당상태 읽어오기, get매크로로 가져온 워드값에 ~0x1을 이용해 마지막 비트를 0으로 설정한 후 다른 비트들은 0으로 만듦

// 블록 포인터로 해당 블록의 헤더와 푸터 주소를 계산하는 매크로 함수
#define HDRP(bp)    ((char *)(bp) - WSIZE) // 블록 포인터값에서 워드 크기만큼을 뺀 주소를 반환(헤더 주소 반환)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //푸터 주소 반환

// 블록 포인터로 이전/다음 블록 주소 계산하는 매크로 함수
#define NEXT_BLKP(bp)   ((char *)(bp)) + GET_SIZE(((char *)(bp) - WSIZE)) // 블록 포인터로 현재 헤더 주소에서 헤더의 크기를 더한 주소를 반환(다음 블록 주소 반환)
#define PREV_BLKP(bp)   ((char *)(bp)) - GET_SIZE(((char *)(bp) - DSIZE)) // 블록포인터로 이전 블록의 헤더 크기를 뺀 주소를 반환(이전 블록의 주소 반환)


static void *heap_listp; // 할당기 선언(프롤로그 블록)
static char *last_bp; // next fit에서 필요한 변수

// 함수 선언
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
// static void *find_fit(size_t asize);
static void *next_fit(size_t asize);
static void place(void *bp, size_t asize);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void) // 힙 자체를 초기화하는 함수
{
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) // heap_listp변수에 mem_sbrk함수(힙의 break 값을 반환하는 함수)에 값을 넣었는데 그게 -1이면
        return -1; // -1 반환
    PUT(heap_listp, 0); // 힙의 맨 앞 주소 즉, 패딩에 0저장(힙의 경계선을 표시하기 위하고 8배수 혹은 16배수로 맞추기 위함(근데 왜 패딩이 하나지?))
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // 패딩 다음주소에, 8바이트 1(할당여부를 나타내는 숫자)저장(프롤로그의 헤더를 나타냄)
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); // 헤더 다음주소에, 8바이트 1(할당여부를 나타내는 숫자)저장(프롤로그의 푸터를 나타냄)
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); // 푸터 다음주소 즉, 에필로그에 0, 1(할당여부를 나타내는 숫자) 저장
    heap_listp += (2*WSIZE); // heap의 맨 앞 주소를 프롤로그와 에필로그 사이로 바꿈(최적화를 위함)

    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    last_bp = (char *)heap_listp;
    return 0;
}

// 힙 확장 함수
static void *extend_heap(size_t words)
{
    char *bp; // 새로 할당된 블록의 주소를 가리키는 포인터 변수
    size_t size; // 확장할 힙 공간의 크기를 저장하는 변수

    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; // 요청된 워드 수를 바이트 크기로 변환해 size함수에 저장(홀수면 1더해서 짝수로 맞춤)
    if ((long)(bp = mem_sbrk(size)) == -1) // bp가 -1이면
        return NULL;    // NULL 반환

    // 새로 할당된 블록의 헤더와 푸터에 크기 정보와 할당상태 정보 저장
    PUT(HDRP(bp), PACK(size, 0)); // size를 크기로 가지고 할당 상태는 0으로 설정
    PUT(FTRP(bp), PACK(size, 0)); // size를 크기로 가지고 할당 상태는 0으로 설정

    // 힙의 끝에 블록 헤더를 추가하여 빈 블록 생성
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); // 새로 할당된 블록 다음에 위치한 빈 블록의 헤더의 크기에 0과 할당상태 1을 저장

    // 블록을 병합하고 재배치해 블록을 연속시킴
    return coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) // 동적할당 함수 구현하기
{
    size_t asize; // 정렬조건에 만족하는 값을 저장할 변수
    size_t extendsize; // 공간이 없는 경우, 확장할 공간의 크기를 저장할 변수
    char *bp; // 어떤 블록을 가르킬지 저장하는 포인터 변수

    if (size == 0) // size 0인경우,
        return NULL; // 메모리 할당이 필요 없으므로, NULL반환

    if (size <= DSIZE) // size가 DSIZE이하인 경우
        asize = 2*DSIZE; // 최소 블록 크기인 2*DSZIE로 설정
    else // size가 DSIZE를 초과하면
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); // 블록 크기를 계산해(공식임) 블록 크기를 설정

    if ((bp = next_fit(asize)) != NULL) { // 할당 가능한 메모리 블록 찾기(요청된 크기에 맞는 블록)가 성공하면,
        place(bp, asize);   // 블록을 할당하고
        last_bp = bp; // next fit
        return bp;  // 해당 블록의 포인터를 반환
    }

    extendsize = MAX(asize,CHUNKSIZE);  // asize랑 CHUNKSIZE 중에 큰 값을 저장하고 
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) // 확장할 수 있는 장소가 없을 경우
        return NULL; // 널 리턴
    place(bp, asize); // 확장한 블록을 할당하고,
    last_bp = bp; // next fit
    return bp; // 해당 블록의 포인터를 반환
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 크기를 헤더에서 읽어옴

    // 현재 블록의 헤더와 푸터의 할당상태를 0으로 설정하여 해제
    PUT(HDRP(bp), PACK(size, 0)); // 현재 블록의 헤더의 크기와 할당상태를 설정
    PUT(FTRP(bp), PACK(size, 0)); // 푸터도 크기와 할당상태를 설정

    // 인접한 빈 블록들을 병합하여 하나의 큰 블록으로 재배치
    coalesce(bp);
}

// 빈 블록을 병합하는 함수
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록의 할당상태만 불러옴
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록의 할당상태만 불러옴
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 크기를 헤더에서 읽어옴

    // 이전 블록과 다음 블록의 할당 상태를 확인하여 병합 가능한 경우 처리
    if (prev_alloc && next_alloc) { // 이전, 다음 블록이 모두 할당 돼 있으면,
        last_bp = bp;
        return bp;  // 병합할 수 없음, 그냥 기존 bp 반환
    }

    // 다음 블록이 빈 블록인 경우, 현재 블록과 다음 블록을 병합
    else if (prev_alloc && !next_alloc) { // 다음 블록만 비어 있으면,
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 크기를 가져와 현재 블록의 크기에 더함
        PUT(HDRP(bp), PACK(size, 0)); // 현재 블록의 헤더에 새로운 크기(다음 블록의 크기를 합친 크기)와 할당상태 0으로 변경
        PUT(FTRP(bp), PACK(size, 0)); // 푸터에도 동일하게 변경
    }

    // 이전 블록이 빈 블록인 경우, 현재 블록과 이전 블록을 병합
    else if (!prev_alloc && next_alloc) { // 이전 블록만 비어 있으면
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); // 이번 블록의 크기를 가져와 현재 블록의 크기에 더함
        PUT(FTRP(bp), PACK(size, 0)); // 현재 블록의 푸터에 새로운 크기와 할당상태를 설정
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 헤더에도 동일하게 설정
        bp = PREV_BLKP(bp); // bp를 이전 블록의 주소로 업데이트
    }

    // 이전 블록과 다음 블록이 모두 빈 블록인 경우, 세 개의 블록을 모두 병합
    else { // 둘 다 비어 있을 경우
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 이전, 다음 블록의 크기를 얻어와서 사이즈에 더함
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 헤더에 새로운 크기와 할당상태 설정
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록의 푸터에 새로운 크기와 할당상태 설정
        bp = PREV_BLKP(bp); // bp를 이전 블록의 주소로 업데이트
    }
    last_bp = bp;
    return bp;
}

// static void *find_fit(size_t asize) //first fit
// {
//     void *bp; // 공간을 찾을 포인터 변수 선언

//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) { // heap_listp부터 모든 블록을 순회, 블록 크기가 0인 블록은 힙의 끝을 나타냄
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) { // 블록이 할당되지 않았고, 요청된 크기보다 크거나 같은 크기의 블록이라면
//             return bp; // 해당 블록의 포인터를 반환
//         }
//     }
//     return NULL; // 할당 가능한 블록이 없을 경우 NULL 반환
// }

static void *next_fit(size_t asize) //next fit
{
    char *bp = last_bp; // 이전에 할당된 블록의 다음 블록부터 탐색 시작

    // 힙의 끝까지 루프를 돌며 탐색
    for (bp = NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) != 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize) {
            last_bp = bp; // 다음 탐색을 위해 last_bp 갱신
            return bp;
        }
    }

    // 탐색 실패 시 힙의 처음부터 last_bp까지 다시 탐색
    bp = heap_listp;
    while (bp < last_bp) {
        bp = NEXT_BLKP(bp);
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize) {
            last_bp = bp; // 다음 탐색을 위해 last_bp 갱신
            return bp;
        }
    }

    return NULL; // 적합한 블록을 찾지 못한 경우 NULL 반환
}


static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기 저장

    if ((csize - asize) >= (2*DSIZE)) { // 현재 블록의 크기에서 요청된 블록의 크기를 뺀 값이 최소 블록 크기보다 크거나 같다면
        PUT(HDRP(bp), PACK(asize, 1)); // 현재 블록의 요청된 블록사이즈만큼 저장(딱 맞게)
        PUT(FTRP(bp), PACK(asize, 1)); // 마찬가지
        bp = NEXT_BLKP(bp); // bp를 다음 bp로 바꿈
        PUT(HDRP(bp), PACK(csize-asize, 0)); // 다음 블록을 비워둠(남은 거 비워두기)
        PUT(FTRP(bp), PACK(csize-asize, 0)); // 다음 블록을 비워둠(마찬가지))
    }
    else { //가용 블록(현재 블록)의 크기가 부족하다면
        PUT(HDRP(bp), PACK(csize, 1)); // 그냥 다 써라
        PUT(FTRP(bp), PACK(csize, 1)); // 너 다 해라
    }
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
// void *mm_realloc(void *ptr, size_t size) // 지금 할당된 공간을 아예 이사시키는 함수
// {
//     void *oldptr = ptr; // 이전 공간을 나타내는 변수
//     void *newptr; // 이사갈 공간 변수
//     size_t copySize; // 이삿짐이 얼마나 많은지를 저장
    
//     newptr = mm_malloc(size); // 새로운 메모리 블록 할당
//     if (newptr == NULL) // 새로운 메모리 블록 할당에 실패한 경우
//       return NULL; // 함수 종료
//     copySize = GET_SIZE(HDRP(ptr)); // 이전 메모리 블록의 크기 가져오기
//     if (size < copySize) // 요청 된 크기가 복사할 크기보다 작은 경우
//       copySize = size; // 복사사이즈를 사이즈로 조정
//     memcpy(newptr, oldptr, copySize); // 이전 메모리 블록의 데이터를 새로운 메모리 블록으로 복사
//     mm_free(oldptr); // 이전 메모리 블록을 해제
//     return newptr; // 새로운 메모리 블록의 포인터 반환
// }

void *mm_realloc(void *bp, size_t size) {
    size_t old_size = GET_SIZE(HDRP(bp));
    size_t new_size = size + (2 * WSIZE);   // 2*WISE는 헤더와 풋터

    // new_size가 old_size보다 작거나 같으면 기존 bp 그대로 사용
    if (new_size <= old_size) {
        return bp;
    }
    // new_size가 old_size보다 크면 사이즈 변경
    else {
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
        size_t current_size = old_size + GET_SIZE(HDRP(NEXT_BLKP(bp)));

        // next block이 가용상태이고 old, next block의 사이즈 합이 new_size보다 크면 그냥 그거 바로 합쳐서 쓰기
        if (!next_alloc && current_size >= new_size) {
            PUT(HDRP(bp), PACK(current_size, 1));
            PUT(FTRP(bp), PACK(current_size, 1));
            return bp;
        }
        // 아니면 새로 block 만들어서 거기로 옮기기
        else {
            void *new_bp = mm_malloc(new_size);
            place(new_bp, new_size);
            memcpy(new_bp, bp, new_size);  // 메모리의 특정한 부분으로부터 얼마까지의 부분을 다른 메모리 영역으로 복사해주는 함수(old_bp로부터 new_size만큼의 문자를 new_bp로 복사해라!)
            mm_free(bp);
            return new_bp;
        }
    }
}














