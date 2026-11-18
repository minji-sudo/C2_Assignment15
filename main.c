#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define NUM_SIZES    6 
#define RANGE_FACTOR 2      
#define SEED         2024

enum { OP_INSERT = 0, OP_DELETE = 1 };


static long long g_cmp = 0;    
static long long g_move = 0;    
static int g_depth = 0;         
static int g_maxDepth = 0;      
static long g_nodes = 0;         

typedef struct Node {
    int key;
    int count;                
    int height;
    struct Node *left, *right;
} Node;


#define FRAME_OVERHEAD  (2 * sizeof(void *))
#define FRAME_QUICK     (sizeof(int *) + 2 * sizeof(int) /* lo, hi */ + sizeof(int) /* p */ + FRAME_OVERHEAD)
#define FRAME_PARTITION (sizeof(int *) + 2 * sizeof(int) /* lo, hi */ + 4 * sizeof(int) /* pivot,i,j,mid */ + FRAME_OVERHEAD)
#define FRAME_AVL_INS   (sizeof(Node *) + sizeof(int) /* key */ + sizeof(int) /* c */ + FRAME_OVERHEAD)
#define FRAME_AVL_DEL   (sizeof(Node *) + sizeof(int) + sizeof(int *) /* ok */ + sizeof(int) /* c */ + 2 * sizeof(Node *) /* tmp, succ */ + FRAME_OVERHEAD)
#define FRAME_REBAL     (sizeof(Node *) + sizeof(int) /* bf */ + FRAME_OVERHEAD)
#define FRAME_ROT       (sizeof(Node *) + 2 * sizeof(Node *) /* x, t */ + FRAME_OVERHEAD)


static double now_ms(void)
{
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec * 1000.0 + ts.tv_nsec / 1e6;
}


static int rnd(int range)
{
    return (int)(((long long)rand() * 32768 + rand()) % range);
}


static int cmp3(int a, int b)
{
    g_cmp++;
    return (a > b) - (a < b);
}


static void swap_int(int *a, int *b)
{
    int t = *a;
    *a = *b;
    *b = t;
    g_move += 3;
}


static int partition(int *a, int lo, int hi)
{
    /* a[lo], a[mid], a[hi] 의 중앙값을 a[hi]로 */
    int mid = (lo + hi) / 2;
    g_cmp++; if (a[lo] > a[mid]) swap_int(&a[lo], &a[mid]);
    g_cmp++; if (a[lo] > a[hi])  swap_int(&a[lo], &a[hi]);
    g_cmp++; if (a[mid] > a[hi]) swap_int(&a[mid], &a[hi]);
    swap_int(&a[mid], &a[hi]);

    int pivot = a[hi];
    int i = lo - 1;
    for (int j = lo; j < hi; j++) {
        g_cmp++;
        if (a[j] <= pivot) {
            i++;
            swap_int(&a[i], &a[j]);
        }
    }
    swap_int(&a[i + 1], &a[hi]);
    return i + 1;
}

static void quick_sort_rec(int *a, int lo, int hi)
{
    g_depth++;
    if (g_depth > g_maxDepth) g_maxDepth = g_depth;

    if (hi - lo == 1) {
        g_cmp++;
        if (a[lo] > a[hi]) swap_int(&a[lo], &a[hi]);
    } else if (lo < hi) {
        int p = partition(a, lo, hi);
        quick_sort_rec(a, lo, p - 1);
        quick_sort_rec(a, p + 1, hi);
    }
    g_depth--;
}


static void arr_insert(int *a, int *cnt, int x)
{
    int i = 0;
    while (i < *cnt && cmp3(a[i], x) <= 0)
        i++;
    for (int k = *cnt; k > i; k--) {     /* 뒤로 이동 */
        a[k] = a[k - 1];
        g_move++;
    }
    a[i] = x;
    g_move++;
    (*cnt)++;
}


static int arr_delete(int *a, int *cnt, int x)
{
    int i = 0, c = -1;
    while (i < *cnt) {
        c = cmp3(a[i], x);
        if (c >= 0) break;             
        i++;
    }
    if (i >= *cnt || c != 0)
        return 0;
    for (int k = i; k < *cnt - 1; k++) { /
        a[k] = a[k + 1];
        g_move++;
    }
    (*cnt)--;
    return 1;
}


static int height(const Node *n) { return n ? n->height : 0; }

static void update_height(Node *n)
{
    int l = height(n->left), r = height(n->right);
    n->height = 1 + (l > r ? l : r);
}

static Node *rot_right(Node *y)
{
    Node *x = y->left;
    Node *t = x->right;
    x->right = y;
    y->left = t;
    update_height(y);
    update_height(x);
    return x;
}

static Node *rot_left(Node *x)
{
    Node *y = x->right;
    Node *t = y->left;
    y->left = x;
    x->right = t;
    update_height(x);
    update_height(y);
    return y;
}

static Node *rebalance(Node *n)
{
    update_height(n);
    int bf = height(n->left) - height(n->right);   

    if (bf > 1) {
        if (height(n->left->left) < height(n->left->right))
            n->left = rot_left(n->left);       
        return rot_right(n);                 
    }
    if (bf < -1) {
        if (height(n->right->right) < height(n->right->left))
            n->right = rot_right(n->right);      
        return rot_left(n);                     
    }
    return n;
}

static Node *new_node(int key)
{
    Node *n = (Node *)malloc(sizeof(Node));
    if (n == NULL) {
        fprintf(stderr, "메모리 할당 실패\n");
        exit(1);
    }
    n->key = key;
    n->count = 1;
    g_move += 2;                                   
    n->height = 1;
    n->left = n->right = NULL;

    g_nodes++;
    if (g_nodes > g_peakNodes) g_peakNodes = g_nodes;
    return n;
}

static Node *avl_insert(Node *n, int key)
{
    g_depth++;
    if (g_depth > g_maxDepth) g_maxDepth = g_depth;

    if (n == NULL) {
        g_depth--;
        return new_node(key);
    }

    int c = cmp3(key, n->key);
    if (c < 0)
        n->left = avl_insert(n->left, key);
    else if (c > 0)
        n->right = avl_insert(n->right, key);
    else {                                        
        n->count++;
        g_move++;
        g_depth--;
        return n;
    }

    n = rebalance(n);
    g_depth--;
    return n;
}


static Node *remove_min(Node *n)
{
    g_depth++;
    if (g_depth > g_maxDepth) g_maxDepth = g_depth;

    if (n->left == NULL) {
        Node *r = n->right;
        free(n);
        g_nodes--;
        g_depth--;
        return r;
    }
    n->left = remove_min(n->left);
    n = rebalance(n);
    g_depth--;
    return n;
}

static Node *avl_delete(Node *n, int key, int *ok)
{
    g_depth++;
    if (g_depth > g_maxDepth) g_maxDepth = g_depth;

    if (n == NULL) {                            
        g_depth--;
        return NULL;
    }

    int c = cmp3(key, n->key);
    if (c < 0) {
        n->left = avl_delete(n->left, key, ok);
    } else if (c > 0) {
        n->right = avl_delete(n->right, key, ok);
    } else {
        *ok = 1;
        if (n->count > 1) {                        
            n->count--;
            g_move++;
            g_depth--;
            return n;
        }
        if (n->left == NULL || n->right == NULL) {  /* 자식 0~1개 */
            Node *tmp = n->left ? n->left : n->right;
            free(n);
            g_nodes--;
            g_depth--;
            return tmp;
        }
       
        Node *succ = n->right;
        while (succ->left)
            succ = succ->left;
        n->key = succ->key;
        n->count = succ->count;
        g_move += 2;
        n->right = remove_min(n->right);
    }

    n = rebalance(n);
    g_depth--;
    return n;
}

static void free_tree(Node *n)
{
    if (n == NULL) return;
    free_tree(n->left);
    free_tree(n->right);
    free(n);
}


static void avl_to_array(const Node *n, int *out, int *idx)
{
    if (n == NULL) return;
    avl_to_array(n->left, out, idx);              
    for (int i = 0; i < n->count; i++)
        out[(*idx)++] = n->key;
    avl_to_array(n->right, out, idx);
}


static int avl_check(const Node *n)
{
    if (n == NULL) return 0;
    int l = avl_check(n->left), r = avl_check(n->right);
    if (l < 0 || r < 0) return -1;
    if (l - r > 1 || r - l > 1) return -1;
    int h = 1 + (l > r ? l : r);
    return (h == n->height) ? h : -1;
}

static int is_sorted(const int *a, int n)
{
    for (int i = 1; i < n; i++)
        if (a[i - 1] > a[i]) return 0;
    return 1;
}


static int verify_sort_stage(const int *origin, int n, int *work, int *buf)
{
    memcpy(work, origin, sizeof(int) * n);
    quick_sort_rec(work, 0, n - 1);

    Node *root = NULL;
    for (int i = 0; i < n; i++)
        root = avl_insert(root, origin[i]);
    int idx = 0;
    avl_to_array(root, buf, &idx);

    int ok = is_sorted(work, n) && idx == n && memcmp(work, buf, sizeof(int) * n) == 0 && avl_check(root) >= 0;
    free_tree(root);
    return ok;
}


typedef struct {
    double time;
    long long cmp, move;
    size_t mem;
    int finalCount;
    int delOk;
#ifdef SHOW_BREAKDOWN
    double timeSort;
    long long cmpSort, moveSort;
#endif
} Result;

static void run_quick(const int *origin, int n, int cap, int *work,
                      const int *opType, const int *opVal, int ops, Result *res)
{
    int cnt = n, delOk = 0;

    memcpy(work, origin, sizeof(int) * n);         
    g_cmp = g_move = 0;
    g_depth = g_maxDepth = 0;

    double t0 = now_ms();
    quick_sort_rec(work, 0, n - 1);
#ifdef SHOW_BREAKDOWN
    double tMid = now_ms();
    res->cmpSort = g_cmp;
    res->moveSort = g_move;
#endif
    for (int i = 0; i < ops; i++) {
        if (opType[i] == OP_INSERT) arr_insert(work, &cnt, opVal[i]);
        else                        delOk += arr_delete(work, &cnt, opVal[i]);
    }
    double t1 = now_ms();

    res->time = t1 - t0;
#ifdef SHOW_BREAKDOWN
    res->timeSort = tMid - t0;
#endif
    res->cmp = g_cmp;
    res->move = g_move;
    /* 배열 전체 할당 공간(n + 최대 삽입 횟수) + 퀵 정렬 재귀 스택 */
    res->mem = (size_t)cap * sizeof(int) + (size_t)g_maxDepth * FRAME_QUICK + FRAME_PARTITION;
    res->finalCount = cnt;
    res->delOk = delOk;
}

static Node *run_avl(const int *origin, int n,
                     const int *opType, const int *opVal, int ops, Result *res)
{
    Node *root = NULL;
    int delOk = 0;

    g_cmp = g_move = 0;
    g_depth = g_maxDepth = 0;
    g_nodes = g_peakNodes = 0;

    double t0 = now_ms();
    for (int i = 0; i < n; i++)
        root = avl_insert(root, origin[i]);
#ifdef SHOW_BREAKDOWN
    double tMid = now_ms();
    res->cmpSort = g_cmp;
    res->moveSort = g_move;
#endif
    for (int i = 0; i < ops; i++) {
        if (opType[i] == OP_INSERT) {
            root = avl_insert(root, opVal[i]);
        } else {
            int ok = 0;
            root = avl_delete(root, opVal[i], &ok);
            delOk += ok;
        }
    }
    double t1 = now_ms();

    size_t frame = FRAME_AVL_INS > FRAME_AVL_DEL ? FRAME_AVL_INS : FRAME_AVL_DEL;
    res->time = t1 - t0;
#ifdef SHOW_BREAKDOWN
    res->timeSort = tMid - t0;
#endif
    res->cmp = g_cmp;
    res->move = g_move;
    /* 최대 노드 수 * 노드 크기 + 재귀 스택 + 리프 호출(rebalance -> rotate) */
    res->mem = (size_t)g_peakNodes * sizeof(Node) + (size_t)g_maxDepth * frame + FRAME_REBAL + FRAME_ROT;
    res->finalCount = 0;                            /* 중위 순회 */
    res->delOk = delOk;
    return root;
}

int main(void)
{
    const int sizes[NUM_SIZES] = {1000, 2000, 4000, 8000, 16000, 20000};
    int allOk = 1;

    srand(SEED);

    for (int s = 0; s < NUM_SIZES; s++) {
        int n = sizes[s];
        int ops = n / 5;                          
        int cap = n + ops;                        
        int range = RANGE_FACTOR * n;

        int *origin = (int *)malloc(sizeof(int) * n);
        int *work   = (int *)malloc(sizeof(int) * cap);
        int *buf    = (int *)malloc(sizeof(int) * cap);
        int *opType = (int *)malloc(sizeof(int) * ops);
        int *opVal  = (int *)malloc(sizeof(int) * ops);
        if (!origin || !work || !buf || !opType || !opVal) {
            fprintf(stderr, "메모리 할당 실패\n");
            return 1;
        }

      
        for (int i = 0; i < n; i++)
            origin[i] = rnd(range);
        int insertCnt = 0;
        for (int i = 0; i < ops; i++) {
            opType[i] = (rnd(100000) % 2 == 0) ? OP_INSERT : OP_DELETE;  
            opVal[i] = rnd(range);                                    
            if (opType[i] == OP_INSERT) insertCnt++;
        }

       
        if (!verify_sort_stage(origin, n, work, buf)) {
            allOk = 0;
            printf("[오류] 정렬 결과 불일치 (n=%d)\n", n);
        }

        
        Result rq = {0}, ra = {0};
        double totalQ = 0.0, totalA = 0.0;
#ifdef SHOW_BREAKDOWN
        double sortQ = 0.0, sortA = 0.0;
#endif

        for (int r = 0; r < REPEAT; r++) {
            Result tq, ta;

            run_quick(origin, n, cap, work, opType, opVal, ops, &tq);
            Node *root = run_avl(origin, n, opType, opVal, ops, &ta);

            totalQ += tq.time;
            totalA += ta.time;
#ifdef SHOW_BREAKDOWN
            sortQ += tq.timeSort;
            sortA += ta.timeSort;
#endif

         
            int idx = 0;
            avl_to_array(root, buf, &idx);
            ta.finalCount = idx;
            if (!is_sorted(work, tq.finalCount) || avl_check(root) < 0 ||
                tq.finalCount != ta.finalCount ||
                memcmp(work, buf, sizeof(int) * idx) != 0 ||
                tq.delOk != ta.delOk) {
                allOk = 0;
                printf("[오류] 연산 후 데이터 구성이 다름 (n=%d)\n", n);
            }
            free_tree(root);

            if (r == 0) { rq = tq; ra = ta; }      
            else if (tq.cmp != rq.cmp || tq.move != rq.move || ta.cmp != ra.cmp || ta.move != ra.move) {
                allOk = 0;
                printf("[오류] 반복 실행 간 카운터 값이 달라짐 (n=%d)\n", n);
            }
        }

        
        char q1[32], q2[32], a1[32], a2[32];
        printf("Data Size : %d\n", n);
        printf("Operations: %d\n\n", ops);
        printf("                  Quick Sort      AVL Tree\n");
        printf("------------------------------------------------\n");
        snprintf(q1, sizeof q1, "%.4f ms", totalQ / REPEAT);
        snprintf(a1, sizeof a1, "%.4f ms", totalA / REPEAT);
        printf("%-18s%-16s%s\n", "Total Time", q1, a1);
        printf("%-18s%-16lld%lld\n", "Comparisons", rq.cmp, ra.cmp);
        printf("%-18s%-16lld%lld\n", "Data Movements", rq.move, ra.move);
        snprintf(q2, sizeof q2, "%zu Bytes", rq.mem);
        snprintf(a2, sizeof a2, "%zu Bytes", ra.mem);
        printf("%-18s%-16s%s\n", "Memory Usage", q2, a2);
        printf("\n");
        printf("%-18s%-16d%d\n", "Final Data Count", rq.finalCount, ra.finalCount);
        printf("(참고) 삽입 %d회, 삭제 성공 %d회 / 삭제 시도 %d회\n\n",
               insertCnt, rq.delOk, ops - insertCnt);

#ifdef SHOW_BREAKDOWN
        printf("[분해] Quick: 정렬 cmp=%lld move=%lld time=%.4fms | 삽입삭제 cmp=%lld move=%lld time=%.4fms\n",
               rq.cmpSort, rq.moveSort, sortQ / REPEAT,
               rq.cmp - rq.cmpSort, rq.move - rq.moveSort, (totalQ - sortQ) / REPEAT);
        printf("[분해] AVL  : 구축 cmp=%lld move=%lld time=%.4fms | 삽입삭제 cmp=%lld move=%lld time=%.4fms\n\n",
               ra.cmpSort, ra.moveSort, sortA / REPEAT,
               ra.cmp - ra.cmpSort, ra.move - ra.moveSort, (totalA - sortA) / REPEAT);
#endif

        free(origin); free(work); free(buf); free(opType); free(opVal);
    }

    if (allOk)
        printf("모든 검증 통과: 정렬 결과, AVL 균형, 연산 후 데이터 구성이 두 방법에서 동일합니다.\n");
    return 0;
}
