/*
 * mm-implicit.c - an empty malloc package
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 *
 * @id : 201302397 
 * @name : 문준영
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc //mm_malloc을 malloc으로세팅
#define free mm_free // 위와동일
#define realloc mm_realloc //위와동일
#define calloc mm_calloc //위와동일
#endif /* def DRIVER */


/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8 //블록을 8의배수로할당하기위해 사용
#define WSIZE 4 //word 크기로지정
#define DSIZE 8 //dword 크기
#define CHUNKSIZE (1<<12) // 초기heap사이즈설정 4096
#define OVERHEAD 8 //header+footer 사이즈
#define MAX(x,y)((x)>(y)?(x):(y)) //x y와비교후 큰값을반혼
#define PACK(size,alloc) ((size)|(alloc)) //header와footer에 메모리가할당된지 기록해주는매크로


/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p)(((size_t)(p) + (ALIGNMENT-1)) & ~0x7)// p값을 인근8의배수로변환

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))// 들어오는값을형변환후 8을나타탬
#define SIZE_PTR(p) ((size_t*)(((char*)(p))-SIZE_T_SIZE)) //블록의사이즈를나타내는 포인터
 
#define PUT(p,val) (*(unsigned int *)(p)=(val)) //포인터p가가리키는곳에 val 저장
#define GET(p) (*(unsigned int *)(p))// 포인터p가가리키는곳의값가져옴

#define GET_SIZE(p)(GET(p)&~0x7) //포인터 p가 가리키는곳ㅇ서 한워드를읽고
//하위3비트를버림 header에서 blocksize읽음
#define GET_ALLOC(p)(GET(p)&0x1)// 포인터p가 가리키는곳에서의 한 word를
//읽고 최하위1bit가져옴 할당된블록이면 1 아니면 0을 알수있음

#define HDRP(bp)((char *)(bp)-WSIZE)//주어진포인터 bp의 header주소계산
#define FTRP(bp)((char *)(bp) + GET_SIZE(HDRP(bp))-DSIZE) //주어진포인터 bp의 footer 주소계산
#define NEXT_BLKP(bp)((char*)(bp) + GET_SIZE((char*)(bp)-WSIZE)) //주어진포인터 bp의 다음블록주소를읽음
#define PREV_BLKP(bp)((char*)(bp) - GET_SIZE((char*)(bp)-DSIZE))	
// 위와달리 이전블록의주소를읽음

static void *find_fit(size_t asize); //free 블록을 찾는 함수
static void *extend_heap(size_t words); //heap사이즈를 늘려주기위한함수
static void place(void *bp,size_t asize); //find fit을통해 찾은free block을메모리할당을 위한함수
static void *coalesce(void *bp); //4가지경우로 나눠서 인근free블록을합쳐줌
static char *heap_listp=0; // 처음init을 하기위해 사용된포인터
static char *cur=0; //nextfit 을위한변수
/*
 * Initialize: return -1 on error, 0 on success.
 */
int mm_init(void) {
	if((cur = mem_sbrk(4*WSIZE))== NULL) //초기 empty heap생성여기서
		return -1;  // empty heap 늘림 

	PUT(cur,0);//healp_listp가 가리키는곳에 0을 넣음
	PUT(cur+WSIZE,PACK(OVERHEAD,1)); //heap_listp+4 위치에9들어감1은 block의 할당유무를 알려주는 word
	PUT(cur+DSIZE, PACK(OVERHEAD,1));//heap_list+8 위치에 위와 동일
	PUT(cur+WSIZE+DSIZE,PACK(0,1)); //heap_list+12 위치에 1 위와동일
	cur+=DSIZE; //heap_listp+8위치로 heap_listp 가이동
	//cur=heap_listp;

	if(extend_heap(CHUNKSIZE/WSIZE)==NULL) //요청받은 크기의 빈블록을만들어줌(4096 이들어감)
		return -1;
	return 0;
}
static void *coalesce(void *bp){ //free 공간을 합쳐주는 역할을 하는 함수
	size_t prev_alloc= GET_ALLOC(FTRP(PREV_BLKP(bp))); //bp의 전블럭의 footer의 할당된블록 1or 0을 가져옴
	size_t next_alloc= GET_ALLOC(HDRP(NEXT_BLKP(bp))); //bp의 다음블럭의 header의 할당된블록 1 or0 을가져옴
	size_t size =GET_SIZE(HDRP(bp)); //bp의 헤더의 사이즈를 저장

	if(prev_alloc && next_alloc){ // 둘다 할당되어있을떄 세팅안하고 바로 리턴
		return bp;
	} //case 1

	else if(prev_alloc && !next_alloc){ //이전 블록은 할당되었으나 다음블럭이 할당안되있는상태면
		size +=GET_SIZE(HDRP(NEXT_BLKP(bp)));//bp의 다음블록의 헤더의 사이즈를 읽어서 현재 bp의헤더 사이즈와 더함 사이즈갱신
		PUT(HDRP(bp),PACK(size,0)); //bp의 헤더에 갱신한 사이즈와 할당안된블록 0을넣음
		PUT(FTRP(bp),PACK(size,0)); //bp의 풋터에 갱신한사이즈와 할당안된 블록0을넣음
		//이말은 즉 bp기준으로 이전블록은 할당되었으나 다음블럭이 할당이안되있으면 합쳐주고 현재bp의 헤더와 풋터의 size와 할당안됨 0을넣으줌으로 셋팅완료
		 
	} //case 2
	
	else if(!prev_alloc && next_alloc){ //이전블록이 할당(0) x 다음블록이 할당되있으면(1) bp와 이전블록을 합쳐야됨
	size+=GET_SIZE(HDRP(PREV_BLKP(bp))); //이전블록의 헤더의 사이즈 읽어서 사이즈를 갱신
	PUT(FTRP(bp),PACK(size,0));//bp의 풋터에 갱신한사이즈넣음
	PUT(HDRP(PREV_BLKP(bp)),PACK(size,0)); //bp의 이전블록의 헤더에 갱신한 사이즈를 넣음
	bp=PREV_BLKP(bp); //bp는 bp의 이전블록으로 이동
	}
	else{ //이전free 블록과 다음 free블록을 함침
		size+=GET_SIZE(HDRP(PREV_BLKP(bp)))+  //이전블록의헤더사이즈와
			GET_SIZE(FTRP(NEXT_BLKP(bp))); //다음블록의 풋터사이즈를 더해서 사이즈갱신
		PUT(HDRP(PREV_BLKP(bp)),PACK(size,0)); //이전블록의헤더에 사이즈넣음
		PUT(FTRP(NEXT_BLKP(bp)),PACK(size,0)); //다음브록풋터에 사이즈넣음
		bp=PREV_BLKP(bp); //현재bp는전블록으로이동
	}
	return bp;
 }
void *malloc (size_t size) {
	size_t asize;
	size_t extendsize;
	char *bp;

	if(size==0) //사이즈가 0일경우종료
		return NULL;

	if(size <=DSIZE) //사이즈가 8보다작으면 2배늘림
		asize=2*DSIZE;
	else //들어오는사이즈를 8의배수로 맞춰줌
		asize=DSIZE * ((size+(DSIZE)+(DSIZE-1)) /DSIZE);

	if((bp=find_fit(asize))!=NULL){ //free블록을찾아서 bp에넣고
		place(bp,asize); //bp의주소를 통해 블록을할당
		return bp;
	}
	/*NO fit found . get more memory and place the block */
	extendsize=MAX(asize,CHUNKSIZE);// asize가 더크면
	if((bp=extend_heap(extendsize/WSIZE))==NULL) // extend_heap을통해늘려줌
		return NULL;
	place(bp,asize); //메모리를할당
	return bp;	
} //책에있음fint_fit() 을 구현 place() 를 추가구현 cleasce 병합 추가구현
// fint_fit fist fit,next fit , bestfit.. 을 사용
/*
 * free
 */
void free (void *bp) {
   if(bp==0) return; //잘못된 free 요청인 경우 함수를 종료한다. 이전프로시저로return
	
   
   size_t size=GET_SIZE(HDRP(bp));

	

   PUT(HDRP(bp),PACK(size,0)); //bp의 header에 block size와 alloc =0저장
   PUT(FTRP(bp),PACK(size,0)); //bp의 footer에 block size와 alloc=0 저장
  cur=coalesce(bp); //주위에 빈 블로기 있을시 병합한다.

	
} //책에있음

/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *oldptr, size_t size) { //naive와동일
  size_t oldsize;
  void *newptr;

  if(size==0){
	  free(oldptr);
	  return 0;
  }
  if(oldptr ==NULL)
	  return malloc(size);
	
	newptr =malloc(size);
	
	if(!newptr)
		return 0;

	oldsize= *SIZE_PTR(oldptr);
	
	if(size<oldsize) oldsize=size;
	memcpy(newptr,oldptr,oldsize);

	free(oldptr);

	return newptr;

} //naive에있는거그대로씀

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) { //navie와 동일
    size_t bytes= nmemb *size;
	void *newptr;

	newptr=malloc(bytes);

	memset(newptr,0,bytes);
	
	return newptr;
} //naive에있는거그대로씀


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p < mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap
 */
void mm_checkheap(int verbose) {
}


static void *find_fit(size_t asize){//free블록을찾음
	char *bp; //nextfit
 

	for(bp=cur;GET_SIZE(HDRP(bp))>0;bp=NEXT_BLKP(bp)){ //bp= cur로두어 bp의헤더사이즈보다 커야 다음블록으로이동
		if(!GET_ALLOC(HDRP(bp)) && (asize<=GET_SIZE(HDRP(bp))))
			return bp; //bp의헤더가 할당 안되있꼬 bp의사이즈가 들어오는 사이즈보다 작거나같으면 freeblock을 찾음
	
	}

		return NULL;
	}
static void *extend_heap(size_t words){
	void *bp; //void 형 block pointer선언
	size_t size; // unsigind int 64비트 타입 size 선언

	size= (words%2)?(words+1)*WSIZE:words*WSIZE; //들어오는 words를 size로변환시켜줌 	
		
//1024가들어오면 4096이됨

	if((long)(bp=mem_sbrk(size))==-1) //위에서 정한size로 mem_sbrk를통해힙 영역이 늘어남 bp는 기존heap의마지막을가리킴
		return NULL;
	PUT(HDRP(bp),PACK(size,0)); //bp의 헤더에 size와 워드에 0저장
	PUT(FTRP(bp),PACK(size,0)); //bp의 footer에 size와 워드에 0저장
	PUT(HDRP(NEXT_BLKP(bp)),PACK(0,1));//bp의다음block주소의헤더에 1,1저장
	

	cur=coalesce(bp); //병합을해준다.
	return cur;
}
static void place(void *bp,size_t asize){
	size_t csize=GET_SIZE(HDRP(bp)); //현재 bp의헤더사이즈를 csize저장
		
	
	if((csize-asize)>=(OVERHEAD+DSIZE)){ //csize와 asize를 뺀값이 최소16바이트보다커야함
		PUT(HDRP(bp),PACK(asize,1));	//할당할사이즈를 헤더에 집어넣고 할당
		PUT(FTRP(bp),PACK(asize,1)); //풋터에집어넣고 할당
		bp=NEXT_BLKP(bp); //다음으로이동해서
		PUT(HDRP(bp),PACK(csize-asize,0)); //남는사이즈를 헤더에
		PUT(FTRP(bp),PACK(csize-asize,0)); //남는사이즈를 풋터에넣음
		cur=bp; //현재의주소를 cur에저장
	}
	else{ //위조건 만족 x
		PUT(HDRP(bp),PACK(csize,1)); //현재 헤더에 현재사이즈만큼할당
		PUT(FTRP(bp),PACK(csize,1)); //현재 풋터에 현재사이즈를 할당
		cur=bp;//현재주소를 cur에저장
	}
}
