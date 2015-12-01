#ifdef CODEJUDGE
#define NDEBUG
#endif

#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>
#include <limits.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <stdio.h>

#ifdef CODEJUDGE
#include <time.h>
#else
#include <sys/time.h>
#endif

#define MAX_LINE 42
#define SORT_CUTOFF 16
#define VERTEX_FACTOR 5

/*
 * STRUCTS
 */

typedef struct Edge {
  uint32_t from;
  uint32_t to;
  uint32_t flow;
  uint32_t capacity : 31;
  bool forwards : 1;
} Edge;

typedef struct Vertex {
  Edge * parent_edge;
  Edge * edge_list;
  size_t capacity;
  size_t size;
} Vertex;

typedef struct {
  Vertex * vertices;
  size_t const size;
} Graph;

typedef struct {
  uint32_t * const data;
  size_t head;
  size_t tail;
  size_t const capacity;
} Queue;

typedef struct {
  int32_t x, y;
  uint32_t n, a1, a2, a3, a4;
} Platform;

/*
 * PROTOTYPES
 */

typedef bool (*LESS)(Platform, Platform);

Graph graph_alloc(Vertex * const vertices, size_t const V);
void graph_free(Graph * const G);
void insert_edge(Graph * const G, uint32_t const from, uint32_t const to, uint32_t const capacity, bool const forwards);

Queue queue_alloc(uint32_t * const data, size_t const capacity);
void enqueue(Queue * const Q, uint32_t const x);
uint32_t dequeue(Queue * const Q);
bool queue_is_empty(Queue const * const Q);
void queue_clear(Queue * const Q);

uint32_t min(uint32_t const a, uint32_t const b);
uint32_t max(uint32_t const a, uint32_t const b);

void insert_flow_edge(Graph * const  G, uint32_t const from, uint32_t const, uint32_t const capacity);
uint32_t edmonds_karp(Graph * const G, uint32_t const source, uint32_t const sink, uint32_t * const queue_data, uint8_t * const marked, uint32_t * const caps);

bool lessxy(Platform const a, Platform const b);
bool lessy(Platform const a, Platform const b);
void swap_platform(Platform * const a, Platform * const b);
void quicksort(Platform * const xs, int const lo, int const hi, LESS less);
int partition(Platform * const xs, int const lo, int const hi, LESS less);
void insertion_sort(Platform * const xs, size_t const len, LESS less);
void sort(Platform * const ps, size_t const P, LESS less);

uint32_t next_prime(uint32_t const a);
bool update_slope_count(uint32_t * const slopes, uint8_t * const counts, uint32_t const slopes_len, uint32_t const key);

double ccw(Platform * p1, Platform * p2, Platform * p3);
void convex_hull(Platform * points, size_t npoints, Platform ** const out_hull, size_t * out_hullsize);

/*
 * GRAPH
 */

Graph graph_alloc(Vertex * const vertices, size_t const V) {
  for (size_t i = 0; i < V; i++) {
    Edge * const edge_list = malloc(64 * sizeof *edge_list);
    vertices[i] = (Vertex) {.edge_list = edge_list, .size = 0, .capacity = 64, .parent_edge = NULL};
  }

  return (Graph) {.vertices = vertices, .size = V};
}

void graph_free(Graph * const G) {
  assert(G != NULL);
  for (size_t i = 0; i < G->size; i++)
    free(G->vertices[i].edge_list);
}

void insert_edge(Graph * const G, uint32_t const from, uint32_t const to, uint32_t capacity, bool forwards) {
  assert(G != NULL);
  Vertex * v = &G->vertices[from];

  v->edge_list[v->size++] = (Edge) {.from = from, .to = to, .flow = 0, .capacity = capacity, .forwards = forwards};

  if (v->size == v->capacity) {
    v->capacity *= 2;
    v->edge_list = realloc(v->edge_list, v->capacity * sizeof *v->edge_list);
  }
}

/*
 * QUEUE
 */

Queue queue_alloc(uint32_t * const data, size_t const capacity) {
  return (Queue) {.capacity = capacity, .data = data, .head = 0, .tail = 0};
}

void enqueue(Queue * const Q, uint32_t const x) {
  assert(Q != NULL);
  assert(Q->head != (Q->tail+1) % Q->capacity);

  Q->data[Q->tail] = x;
  Q->tail = (Q->tail + 1) % Q->capacity;
}

uint32_t dequeue(Queue * const Q) {
  assert(Q != NULL);
  assert(!queue_is_empty(Q));

  uint32_t const x = Q->data[Q->head];
  Q->head = (Q->head+1) % Q->capacity;

  return x;
}

bool queue_is_empty(Queue const * const Q) {
  assert(Q != NULL);
  return Q->head == Q->tail;
}

void queue_clear(Queue * const Q) {
  Q->head = 0;
  Q->tail = 0;
}

/*
 * FLOW
 */

uint32_t min(uint32_t const a, uint32_t const b) {
  if (a < b) return a; else return b;
}

uint32_t max(uint32_t const a, uint32_t const b) {
  if (a > b) return a; else return b;
}

uint32_t edmonds_karp(Graph * const G, uint32_t const source, uint32_t const sink, uint32_t * const queue_data, uint8_t * const marked, uint32_t * const caps) {
  assert(G != NULL);

  Edge * head;
  Queue q = queue_alloc(queue_data, G->size);

  do {
    queue_clear(&q);
    enqueue(&q, source);
    caps[source] = UINT_MAX;
    marked[source] = 1;
    G->vertices[sink].parent_edge = NULL;

    while (!queue_is_empty(&q)) {
      uint32_t v = dequeue(&q);

      for (size_t i = 0; i < G->vertices[v].size; i++) {
        uint32_t u;
        uint32_t residual;
        Edge * cur = &G->vertices[v].edge_list[i];

        if (cur->forwards) {
          u = cur->to;
          residual = cur->capacity - cur->flow;
        } else {
          u = cur->from;
          residual = cur->flow;
        }

        if (residual > 0 && !marked[u]) {
          marked[u] = 1;
          G->vertices[u].parent_edge = cur;
          caps[u] = min(caps[v], residual);

          if (u == sink)
            goto done;

          enqueue(&q, u);
        }
      }
    }

  done:
    head = G->vertices[sink].parent_edge;

    while (head != NULL) {
      size_t idx;

      if (head->forwards) {
        head->flow += caps[sink];
        idx = head->from;
      } else {
        head->flow -= caps[sink];
        idx = head->to;
      }

      head = G->vertices[idx].parent_edge;
    }

    memset(marked, 0, G->size * sizeof *marked);

  } while (G->vertices[sink].parent_edge != NULL);

  int32_t sum = 0;
  for (size_t i = 0; i < G->vertices[source].size; i++) {
    Edge cur = G->vertices[source].edge_list[i];
    sum += cur.forwards ? cur.flow : -cur.flow;
  }

  return (uint32_t) sum;
}

void insert_flow_edge(Graph * const  G, uint32_t const from, uint32_t const to, uint32_t const capacity) {
  assert(G != NULL);
  assert(from != to);

  if (capacity == 0) return;

  insert_edge(G, from, to, capacity, true);
  insert_edge(G, to, from, capacity, false);
}

/*
 * SORTING
 */

void swap_platform(Platform * a, Platform * b) {
  Platform const t = *a;
  *a = *b;
  *b = t;
}

bool lessxy(Platform const a, Platform const b) {
  return a.x < b.x || (a.x == b.x && a.y < b.y);
}

bool lessy(Platform const a, Platform const b) {
  return a.y < b.y;
}

int partition(Platform * const xs, int const lo, int const hi, LESS less) {
  int const idx = rand() % (hi-lo+1) + lo;
  swap_platform(xs+idx, xs+lo);

  int i = lo;
  int j = hi + 1;
  Platform const x = xs[lo];

  while (true) {
    while (less(xs[++i], x))
      if (i == hi) break;

    while (less(x, xs[--j]))
      if (j == lo) break;

    if (i >= j) break;

    swap_platform(xs+i, xs+j);
  }

  swap_platform(xs+lo, xs+j);

  return j;
}

void quicksort(Platform * const xs, int const lo, int const hi, LESS less) {
  if (hi - lo > SORT_CUTOFF) {
    int const p = partition(xs, lo, hi, less);
    quicksort(xs, lo, p-1, less);
    quicksort(xs, p+1, hi, less);
  }
}

void insertion_sort(Platform * const xs, size_t const len, LESS less) {
  for (size_t i = 1; i < len; i++) {
    Platform x = xs[i];
    size_t j = i;

    while(j > 0 && less(x, xs[j-1])) {
      xs[j] = xs[j-1];
      j--;
    }

    xs[j] = x;
  }
}

void sort(Platform * const ps, size_t const P, LESS less) {
  quicksort(ps, 0, (int) P-1, less);
  insertion_sort(ps, P, less);
}

/*
 * HASHING
 */

bool update_slope_count(uint32_t * const slopes, uint8_t * const counts, uint32_t const slopes_len, uint32_t const key) {
  assert(slopes != NULL);

  for (uint32_t idx = key % slopes_len;; idx++, idx %= slopes_len) {
    if (counts[idx] == 0) {
      counts[idx] = 1;
      slopes[idx] = key;
      return false;
    }

    if (slopes[idx] == key) {
      if (counts[idx] >= 2) {
        return true;
      } else {
        counts[idx]++;
        return false;
      }
    }
  }

  return false;
}

uint32_t next_prime(uint32_t const a) {
  for (uint32_t x = a;; x++) {
    if (x % 2 == 0) continue;
    bool is_prime = true;
    double const limit = sqrt(x);
    for (uint32_t i = 3; i <= limit; i += 2) {
      if (x % i == 0) {
        is_prime = false;
        break;
      }
    }
    if (is_prime) return x;
  }
}

/*
 * CONVEX HULL
 */

double ccw(Platform * p1, Platform * p2, Platform * p3) {
  return (p2->x - p1->x)*(p3->y - p1->y) - (p2->y - p1->y)*(p3->x - p1->x);
}

void convex_hull(Platform * points, size_t npoints, Platform ** const out_hull, size_t * out_hullsize) {
  Platform * hull;
  size_t t, k = 0;
  int64_t i;

  hull = *out_hull;

  for (i = 0; i < (int64_t) npoints; ++i) {
    while (k >= 2 && ccw(&hull[k-2], &hull[k-1], &points[i]) <= 0) --k;
    hull[k++] = points[i];
  }

  for (i = (int64_t) npoints-2, t = k+1; i >= 0; i--) {
    while (k >= t && ccw(&hull[k-2], &hull[k-1], &points[i]) <= 0) --k;
    hull[k++] = points[i];
  }

  *out_hull = hull;
  *out_hullsize = k;
}


/*
 * MAIN
 */

int main() {
#ifndef CODEJUDGE
  struct timeval t1, t2, t3, t4, t5, t6, t7;
  gettimeofday(&t1, NULL);
#endif

  srand((unsigned int) time(NULL));

  uint32_t P;
  char line[MAX_LINE];

  fgets(line, MAX_LINE, stdin);
  sscanf(line, "%d", &P);

  uint32_t const n_slopes = next_prime(VERTEX_FACTOR*P);

  Platform * const ps = malloc(P * sizeof *ps);
  Vertex * const vertices = malloc(VERTEX_FACTOR*P * sizeof *vertices);
  uint32_t * const slopes = malloc(n_slopes * sizeof *slopes);
  uint8_t * const counts = calloc(n_slopes, sizeof *counts);
  uint32_t * const caps = malloc(VERTEX_FACTOR*P * sizeof *caps);
  Platform * hull = malloc((P+1) * sizeof *hull);

  Graph G = graph_alloc(vertices, VERTEX_FACTOR*P);

  for (uint32_t i = 0; i < P; i++) {
    fgets(line, MAX_LINE, stdin);
    sscanf(line, "%d %d %u %u %u %u", &ps[i].x, &ps[i].y, &ps[i].a1, &ps[i].a2, &ps[i].a3, &ps[i].a4);
    ps[i].n = i;
  }

#ifndef CODEJUDGE
  gettimeofday(&t2, NULL);
#endif

  /* Vertex schema:
   * i: ingoing (original vertex)
   * i+1*P: A1
   * i+2*P: A2
   * i+3*P: A3
   * i+4*P: A4
   */

  for (uint32_t i = 0; i < P; i++) {
    Platform const p = ps[i];

    // Vertex -> edge capacities
    insert_flow_edge(&G, p.n, p.n+1*P, p.a1);
    insert_flow_edge(&G, p.n, p.n+2*P, p.a2);
    insert_flow_edge(&G, p.n, p.n+3*P, p.a3);
    insert_flow_edge(&G, p.n, p.n+4*P, p.a4);

    // A4 (EOF)
    insert_flow_edge(&G, p.n+4*P, P-1, p.a4);
  }

#ifndef CODEJUDGE
  gettimeofday(&t3, NULL);
#endif

  // A1 (NEWS)
  sort(ps, P, lessy);

  for (size_t i = 0; i < P; i++) {
    Platform const p = ps[i];
    for (size_t j = i+1; j < P && ps[j].y == p.y; j++) {
      insert_flow_edge(&G, p.n+P, ps[j].n, p.a1);
      insert_flow_edge(&G, ps[j].n+P, p.n, ps[j].a1);
    }
  }

  sort(ps, P, lessxy);

  for (size_t i = 0; i < P; i++) {
    Platform const p = ps[i];
    for (size_t j = i+1; j < P && ps[j].x == p.x; j++) {
      insert_flow_edge(&G, p.n+P, ps[j].n, p.a1);
      insert_flow_edge(&G, ps[j].n+P, p.n, ps[j].a1);
    }
  }


#ifndef CODEJUDGE
  gettimeofday(&t4, NULL);
#endif

  // A2 (Human Cannon)

  size_t hull_size;
  convex_hull(ps, P, &hull, &hull_size);

  for (size_t i = 0; i < P; i++) {
    Platform const p = ps[i];
    uint32_t furthest = UINT_MAX;
    int64_t furthest_dist = 0;

    for (size_t j = 0; j < (size_t) hull_size; j++) {
      Platform const q = hull[j];
      if (p.n == q.n) continue;

      int64_t const dx = p.x - q.x, dy = p.y - q.y;
      int64_t const dist = dx*dx + dy*dy;

      if (dist > furthest_dist || (dist == furthest_dist && q.n < furthest)) {
        furthest = q.n;
        furthest_dist = dist;
      }
    }

    insert_flow_edge(&G, p.n+2*P, furthest, p.a2);
  }

#ifndef CODEJUDGE
  gettimeofday(&t5, NULL);
#endif

  // A3 (Platform Trampoline)
  for (uint32_t i = 0; i < P; i++) {
    Platform const p = ps[i];
    if (p.a3 == 0) continue;

    for (uint32_t j = i+1; j < P; j++) {
      Platform const q = ps[j];

      int64_t const dx = p.x - q.x, dy = p.y - q.y;

      float const fslope = (float) dy / dx;
      uint32_t slope;
      memcpy(&slope, &fslope, sizeof slope);
      if (update_slope_count(slopes, counts, n_slopes, slope)) {
        insert_flow_edge(&G, p.n+3*P, q.n, p.a3);
        insert_flow_edge(&G, q.n+3*P, p.n, q.a3);
      }

    }

    memset(counts, 0, n_slopes * sizeof *counts);
  }

#ifndef CODEJUDGE
  gettimeofday(&t6, NULL);
#endif

  uint32_t const flow = edmonds_karp(&G, 0, P-1, slopes, counts, caps);
  printf("%u\n", flow);

  free(ps);
  free(slopes);
  free(counts);
  free(caps);
  free(hull);

#ifndef CODEJUDGE
  gettimeofday(&t7, NULL);

  graph_free(&G);
  free(vertices);

  double const input_time = (t2.tv_sec - t1.tv_sec) * 1000.0 + (t2.tv_usec - t1.tv_usec) / 1000.0;

  double const a4_time = (t3.tv_sec - t2.tv_sec) * 1000.0 + (t3.tv_usec - t2.tv_usec) / 1000.0;

  double const a1_time = (t4.tv_sec - t3.tv_sec) * 1000.0 + (t4.tv_usec - t3.tv_usec) / 1000.0;

  double const a2_time = (t5.tv_sec - t4.tv_sec) * 1000.0 + (t5.tv_usec - t4.tv_usec) / 1000.0;

  double const a3_time = (t6.tv_sec - t5.tv_sec) * 1000.0 + (t6.tv_usec - t5.tv_usec) / 1000.0;

  double const flow_time = (t7.tv_sec - t6.tv_sec) * 1000.0 + (t7.tv_usec - t6.tv_usec) / 1000.0;

  double const total_time = (t7.tv_sec - t1.tv_sec) * 1000.0 + (t7.tv_usec - t1.tv_usec) / 1000.0;

  printf("IN: %3.2f, A4: %4.2f\tA1: %4.2f\tA2: %3.2f\tA3: %5.2f\tFLOW: %5.2f\tTOTAL: %5.2f\n", input_time, a4_time, a1_time, a2_time, a3_time, flow_time, total_time);
#endif

  return 0;
}
