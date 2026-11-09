/* Spike (2026-11-09): size-stratified dictionary enumeration of minimum fan-in-2 *formula*
 * (tree) size for every Boolean function on n <= 4 variables, under
 *   (1) the PC-NNF polarity rule with Pareto keying on (tt, vars+, vars-),
 *   (2) the PC-NNF rule keyed on tt only (first entry wins)  -- tests pitfall (a),
 *   (3) unrestricted NNF (no rule).
 * Leaves are literals (shared) plus the constants T, F at level 0.  Plan 2.1 size of a tree
 * with k gates and literal sets P, N is 3k + |P| + |N|.
 * Companion to enum_tree_minima.py (same algorithm, n=3 cross-check).  Build and run:
 *   gcc -O2 -o /tmp/enum scripts/spikes/enum_tree_minima.c && /tmp/enum 4
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int n, NPOS, NTT, NP;               /* variables, 2^n positions, 2^(2^n) tables, 2^n masks */
static uint32_t FULL;

typedef struct { uint32_t tt; uint8_t P, N; } Entry;

typedef struct {
    Entry *e; int cnt, cap;
    int *lvl_start; int nlvl;               /* lvl_start[k] .. lvl_start[k+1]-1 are level k */
    uint8_t *covered;                       /* [tt*NP*NP + P*NP + N] */
    uint8_t *best;                          /* min k per tt, 255 = unreached */
    int reached;
    int pc_rule, pareto;
} Dict;

static inline int popc(uint32_t x) { return __builtin_popcount(x); }

static void push(Dict *d, uint32_t tt, int P, int N) {
    if (d->cnt == d->cap) { d->cap = d->cap ? 2 * d->cap : 1024; d->e = realloc(d->e, d->cap * sizeof(Entry)); }
    d->e[d->cnt++] = (Entry){tt, (uint8_t)P, (uint8_t)N};
}

static void add(Dict *d, uint32_t tt, int P, int N, int k) {
    size_t base = (size_t)tt * NP * NP;
    if (d->pareto) {
        for (int P2 = 0; P2 < NP; P2++) if ((P2 & P) == P)
            for (int N2 = 0; N2 < NP; N2++) if ((N2 & N) == N) d->covered[base + P2 * NP + N2] = 1;
    } else {
        memset(d->covered + base, 1, (size_t)NP * NP);
    }
    if (d->best[tt] == 255) { d->best[tt] = (uint8_t)k; d->reached++; }
    push(d, tt, P, N);
}

static int cmp_key(const void *a, const void *b) {
    uint32_t x = *(const uint32_t *)a, y = *(const uint32_t *)b;
    int px = popc(x & (NP * NP - 1)), py = popc(y & (NP * NP - 1));
    if (px != py) return px - py;
    return (x > y) - (x < y);
}

static Dict *enumerate(int pc_rule, int pareto, int max_level, int verbose) {
    Dict *d = calloc(1, sizeof(Dict));
    d->pc_rule = pc_rule; d->pareto = pareto;
    d->covered = calloc((size_t)NTT * NP * NP, 1);
    d->best = malloc(NTT); memset(d->best, 255, NTT);
    d->lvl_start = calloc(max_level + 3, sizeof(int));
    uint8_t *mark = calloc((size_t)NTT * NP * NP, 1);
    uint32_t *cands = malloc(sizeof(uint32_t) * (size_t)NTT * 4); size_t ncand;
    int shift = 2 * n;

    d->lvl_start[0] = 0;
    for (int v = 0; v < n; v++) {
        uint32_t pos = 0;
        for (int i = 0; i < NPOS; i++) if ((i >> v) & 1) pos |= 1u << i;
        add(d, pos, 1 << v, 0, 0);
        add(d, pos ^ FULL, 0, 1 << v, 0);
    }
    add(d, 0, 0, 0, 0); add(d, FULL, 0, 0, 0);
    d->nlvl = 1; d->lvl_start[1] = d->cnt;

    for (int s = 1; s <= max_level && d->reached < NTT; s++) {
        ncand = 0;
        for (int a = 0; a <= s - 1 - a; a++) {
            int b = s - 1 - a;
            int a0 = d->lvl_start[a], a1 = d->lvl_start[a + 1];
            int b0 = d->lvl_start[b], b1 = d->lvl_start[b + 1];
            for (int i = a0; i < a1; i++) {
                Entry x = d->e[i];
                int jstart = (a == b) ? i : b0;
                for (int j = jstart; j < b1; j++) {
                    Entry y = d->e[j];
                    int P = x.P | y.P, N = x.N | y.N;
                    uint32_t k2 = ((uint32_t)P << n) | N;
                    uint32_t key = ((x.tt | y.tt) << shift) | k2;
                    if (!d->covered[key] && !mark[key]) { mark[key] = 1; cands[ncand++] = key; }
                    if (!pc_rule || !((x.P & y.N) | (y.P & x.N))) {
                        key = ((x.tt & y.tt) << shift) | k2;
                        if (!d->covered[key] && !mark[key]) { mark[key] = 1; cands[ncand++] = key; }
                    }
                }
            }
        }
        qsort(cands, ncand, sizeof(uint32_t), cmp_key);
        int added = 0;
        for (size_t c = 0; c < ncand; c++) {
            uint32_t key = cands[c];
            mark[key] = 0;
            if (d->covered[key]) continue;
            add(d, key >> shift, (key >> n) & (NP - 1), key & (NP - 1), s);
            added++;
        }
        d->nlvl = s + 1; d->lvl_start[s + 1] = d->cnt;
        if (verbose) printf("  level %2d: +%7d entries (%zu cands), %6d/%d functions reached\n", s, added, ncand, d->reached, NTT);
        fflush(stdout);
    }
    free(mark); free(cands);
    return d;
}

/* ---- fixed-graph clique formulas on n vertices, graphs up to isomorphism ---- */
static int perms[24][4], nperm;
static void gen_perms(void) {
    int p[4] = {0, 1, 2, 3}; nperm = 0;
    /* Heap's algorithm would do; brute force over all n^n maps and keep bijections */
    int total = 1; for (int i = 0; i < n; i++) total *= n;
    for (int code = 0; code < total; code++) {
        int c = code, used = 0, ok = 1;
        for (int i = 0; i < n; i++) { p[i] = c % n; c /= n; if (used >> p[i] & 1) ok = 0; used |= 1 << p[i]; }
        if (ok) { memcpy(perms[nperm++], p, sizeof(p)); }
    }
}
static int pair_index(int u, int v) { if (u > v) { int t = u; u = v; v = t; } int idx = 0; for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) { if (a == u && b == v) return idx; idx++; } return -1; }

static void clique_report(Dict *pc, Dict *nnf) {
    int npairs = n * (n - 1) / 2, ngraph = 1 << npairs;
    char *seen = calloc(ngraph, 1);
    gen_perms();
    printf("\n== fixed-graph clique formulas phi_(G,k), n=%d vertices: k_pc (k_nnf) gates, tree minima ==\n", n);
    for (int m = 0; m < ngraph; m++) {
        if (seen[m]) continue;
        /* mark the isomorphism class */
        for (int pi = 0; pi < nperm; pi++) {
            int img = 0, idx = 0;
            for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++, idx++)
                if ((m >> idx) & 1) img |= 1 << pair_index(perms[pi][a], perms[pi][b]);
            seen[img] = 1;
        }
        printf("  edges {");
        int idx = 0, first = 1;
        for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++, idx++)
            if ((m >> idx) & 1) { printf("%s%d%d", first ? "" : ",", a, b); first = 0; }
        printf("}:");
        for (int k = 0; k <= n; k++) {
            uint32_t tt = 0;
            for (int s = 0; s < NPOS; s++) {
                int ok = popc(s) >= k;
                for (int a = 0; a < n && ok; a++) for (int b = a + 1; b < n && ok; b++)
                    if (((s >> a) & 1) && ((s >> b) & 1) && !((m >> pair_index(a, b)) & 1)) ok = 0;
                if (ok) tt |= 1u << s;
            }
            if (tt == 0) printf("  k=%d:F", k);
            else if (tt == FULL) printf("  k=%d:T", k);
            else printf("  k=%d:%d(%d)", k, pc->best[tt], nnf->best[tt]);
        }
        printf("\n");
    }
    free(seen);
}

int main(int argc, char **argv) {
    n = argc > 1 ? atoi(argv[1]) : 4;
    if (n < 2 || n > 4) { fprintf(stderr, "n must be 2..4\n"); return 1; }
    NPOS = 1 << n; NTT = 1 << NPOS; NP = 1 << n; FULL = (NPOS == 32) ? 0xffffffffu : ((1u << NPOS) - 1);
    clock_t t0;

    printf("== PC-NNF tree minima, n=%d, Pareto keying on (tt, vars+, vars-) ==\n", n);
    t0 = clock();
    Dict *pc = enumerate(1, 1, 40, 1);
    printf("  time %.1fs; entries per level:", (double)(clock() - t0) / CLOCKS_PER_SEC);
    for (int k = 0; k < pc->nlvl; k++) printf(" %d", pc->lvl_start[k + 1] - pc->lvl_start[k]);
    printf("\n  total entries %d, functions reached %d\n", pc->cnt, pc->reached);
    int *front = calloc(NTT, sizeof(int)); int multi = 0, maxf = 0;
    for (int i = 0; i < pc->cnt; i++) front[pc->e[i].tt]++;
    for (int t = 0; t < NTT; t++) { if (front[t] > 1) multi++; if (front[t] > maxf) maxf = front[t]; }
    printf("  functions with Pareto frontier > 1 entry: %d; max frontier size %d\n", multi, maxf);
    /* essential polarities from the truth table: x in P_ess iff f increases somewhere in x */
    int mismatch = 0;
    for (int i = 0; i < pc->cnt; i++) {
        uint32_t tt = pc->e[i].tt; int Pe = 0, Ne = 0;
        for (int v = 0; v < n; v++)
            for (int s = 0; s < NPOS; s++) if (!((s >> v) & 1)) {
                int lo = (tt >> s) & 1, hi = (tt >> (s | (1 << v))) & 1;
                if (lo < hi) Pe |= 1 << v;
                if (lo > hi) Ne |= 1 << v;
            }
        if (Pe != pc->e[i].P || Ne != pc->e[i].N) mismatch++;
    }
    printf("  minimal trees whose (vars+, vars-) differ from the essential polarities of f: %d\n", mismatch);

    printf("\n== PC-NNF tree minima, n=%d, keyed on tt only ==\n", n);
    t0 = clock();
    Dict *pc1 = enumerate(1, 0, 40, 0);
    printf("  time %.1fs; functions reached %d\n", (double)(clock() - t0) / CLOCKS_PER_SEC, pc1->reached);
    int worse = 0, better = 0;
    for (int t = 0; t < NTT; t++) {
        if (pc1->best[t] > pc->best[t]) { if (worse < 6) printf("  tt %#x: pareto %d, tt-only %d\n", t, pc->best[t], pc1->best[t]); worse++; }
        else if (pc1->best[t] < pc->best[t]) better++;
    }
    printf("  functions with a worse minimum when keyed on tt only: %d (better: %d, must be 0)\n", worse, better);

    printf("\n== NNF tree minima (no polarity rule), n=%d ==\n", n);
    t0 = clock();
    Dict *nnf = enumerate(0, 0, 40, 0);
    printf("  time %.1fs; functions reached %d; entries per level:", (double)(clock() - t0) / CLOCKS_PER_SEC, nnf->reached);
    for (int k = 0; k < nnf->nlvl; k++) printf(" %d", nnf->lvl_start[k + 1] - nnf->lvl_start[k]);
    printf("\n");

    printf("\n== k_pc vs k_nnf over all functions (fan-in-2 gates, tree) ==\n");
    int maxk_pc = 0, maxk_nnf = 0, gaphist[16] = {0}; int maxgap = 0;
    static int joint[40][40];
    for (int t = 0; t < NTT; t++) {
        int kp = pc->best[t], kn = nnf->best[t];
        if (kp > maxk_pc) maxk_pc = kp;
        if (kn > maxk_nnf) maxk_nnf = kn;
        int g = kp - kn; if (g < 0) g = 0; if (g > 15) g = 15; gaphist[g]++; if (kp - kn > maxgap) maxgap = kp - kn;
        joint[kn][kp]++;
    }
    printf("  max k_nnf = %d, max k_pc = %d\n  gap histogram (k_pc - k_nnf -> count):", maxk_nnf, maxk_pc);
    for (int g = 0; g < 16; g++) if (gaphist[g]) printf(" %d:%d", g, gaphist[g]);
    printf("\n  joint table rows k_nnf, cols k_pc (count):\n");
    for (int kn = 0; kn <= maxk_nnf; kn++) {
        printf("   k_nnf=%2d:", kn);
        for (int kp = 0; kp <= maxk_pc; kp++) if (joint[kn][kp]) printf(" k_pc=%d:%d", kp, joint[kn][kp]);
        printf("\n");
    }
    printf("  functions with the maximum gap %d (up to 8): ", maxgap);
    int shown = 0;
    for (int t = 0; t < NTT && shown < 8; t++) if (pc->best[t] - nnf->best[t] == maxgap) { printf("%#x(%d->%d) ", t, nnf->best[t], pc->best[t]); shown++; }
    printf("\n");

    clique_report(pc, nnf);
    return 0;
}
