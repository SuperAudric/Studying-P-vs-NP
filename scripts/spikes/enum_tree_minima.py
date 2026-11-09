"""Spike: size-stratified dictionary enumeration of minimum PC-NNF *formula* (tree) size
for every Boolean function on n <= 4 variables, and the same for unrestricted NNF formulas.

Purpose (evaluation of the dictionary design, 2026-11-09):
  1. measure how many (truth table, vars+, vars-) Pareto entries the dictionary holds per level;
  2. test whether keying on (tt, vars+, vars-) ever changes a minimum compared with keying on tt
     alone (pitfall (a) in docs/plan.md 6.2 discussion);
  3. report the distribution of k_pc(f) / k_nnf(f) (fan-in-2 gate counts) over all functions;
  4. read off tree minima for the fixed-graph clique formulas phi_{G,k} on <= 4 vertices;
  5. count NP equivalence classes (input permutation + input polarity, no output negation)
     by Burnside, for n = 3, 4, 5, to size the symmetry-reduced table.

Size measure: k = number of fan-in-2 gates in a tree whose literal leaves are shared, so the
plan 2.1 size is 3k + |vars+| + |vars-| (k nodes + 2k references + one leaf per literal).
Constants are not needed for non-constant functions (T in AND / F in OR are droppable, the
other two collapse the node) and are omitted.

Run: python3 -I scripts/spikes/enum_tree_minima.py [n]   (default 4; n=4 needs numpy)
"""
import sys, itertools, math, time
from collections import defaultdict

try:
    import numpy as np
except ImportError:  # pragma: no cover
    np = None


def literal_tables(n):
    N = 1 << n
    full = (1 << N) - 1  # all 2^n positions set
    tabs = []
    for v in range(n):
        pos = sum(1 << i for i in range(N) if (i >> v) & 1)
        tabs.append((pos, 1 << v, 0))           # x_v : P={v}
        tabs.append((pos ^ full, 0, 1 << v))    # not x_v : N={v}
    return tabs


def enumerate_levels(n, pc_rule=True, pareto=True, max_level=40, verbose=True):
    """Returns (levels, best) where levels[k] = list of (tt, P, N) added with k gates and
    best[tt] = minimal k.  pc_rule: enforce polarity consistency at AND.
    pareto: key on (tt,P,N) with Pareto dominance; else keep one entry per tt (first found)."""
    N = 1 << n
    full = N - 1
    nP = 1 << n
    # covered[(tt<<2n) | (P<<n) | N] = already dominated by an existing entry
    n_tts = 1 << N  # number of truth tables on n variables
    covered = np.zeros(n_tts * nP * nP, dtype=bool) if np is not None else bytearray(n_tts * nP * nP)
    best = {}
    levels = [[]]
    # supersets of a mask within n bits, precomputed
    sups = [[m for m in range(nP) if m & p == p] for p in range(nP)]

    def add(tt, P, N_, k):
        if pareto:
            for P2 in sups[P]:
                base = (tt << (2 * n)) | (P2 << n)
                for N2 in sups[N_]:
                    covered[base | N2] = True
        else:
            base = tt << (2 * n)
            for P2 in range(nP):
                for N2 in range(nP):
                    covered[base | (P2 << n) | N2] = True
        if tt not in best:
            best[tt] = k
        levels[k].append((tt, P, N_))

    for (tt, P, N_) in literal_tables(n):
        add(tt, P, N_, 0)
    add(0, 0, 0, 0)                 # bottom: unreachable in PC-NNF without the constant leaf
    add((1 << N) - 1, 0, 0, 0)      # top

    all_tts = 1 << N
    for s in range(1, max_level + 1):
        levels.append([])
        cands = {}
        for a in range(0, s):
            b = s - 1 - a
            if a > b:
                break
            La, Lb = levels[a], levels[b]
            if not La or not Lb:
                continue
            if np is not None and len(La) * len(Lb) > 2000:
                A = np.array(La, dtype=np.int64)
                B = np.array(Lb, dtype=np.int64)
                ttA, PA, NA = A[:, 0][:, None], A[:, 1][:, None], A[:, 2][:, None]
                ttB, PB, NB = B[:, 0][None, :], B[:, 1][None, :], B[:, 2][None, :]
                P = (PA | PB).ravel()
                Nn = (NA | NB).ravel()
                ttor = (ttA | ttB).ravel()
                ttand = (ttA & ttB).ravel()
                keys_or = (ttor << (2 * n)) | (P << n) | Nn
                keys_and = (ttand << (2 * n)) | (P << n) | Nn
                if pc_rule:
                    ok = ((PA & NB) | (PB & NA)).ravel() == 0
                    keys_and = keys_and[ok]
                keys = np.unique(np.concatenate([keys_or, keys_and]))
                keys = keys[~covered[keys]]
                for key in keys.tolist():
                    cands[key] = True
            else:
                for (t1, P1, N1) in La:
                    for (t2, P2, N2) in Lb:
                        P, Nn = P1 | P2, N1 | N2
                        for tt in ((t1 | t2),) + (((t1 & t2),) if (not pc_rule or not ((P1 & N2) | (P2 & N1))) else ()):
                            key = (tt << (2 * n)) | (P << n) | Nn
                            if not covered[key]:
                                cands[key] = True
        # insert in order of increasing |P|+|N| so same-level dominated entries are skipped
        mask = nP - 1
        order = sorted(cands, key=lambda key: bin((key >> n) & mask).count('1') + bin(key & mask).count('1'))
        added = 0
        for key in order:
            if covered[key]:
                continue
            tt, P, N_ = key >> (2 * n), (key >> n) & mask, key & mask
            add(tt, P, N_, s)
            added += 1
        if verbose:
            print(f"  level {s:2d}: +{added:6d} entries, {len(best):6d}/{all_tts} functions reached", flush=True)
        # NB: an empty level does not imply later levels are empty (a 7-gate minimum can have two
        # 3-gate operands while nothing needs exactly 6), so stop only when every function is reached.
        if len(best) == all_tts:
            break
    return levels, best


def burnside_np_classes(n):
    """Number of NP classes (permute inputs, complement inputs) of n-variable functions."""
    N = 1 << n
    total = 0
    for perm in itertools.permutations(range(n)):
        for mask in range(N):
            # action on truth-table positions: i -> perm(i) ^ mask
            seen = [False] * N
            cycles = 0
            for i in range(N):
                if seen[i]:
                    continue
                cycles += 1
                j = i
                while not seen[j]:
                    seen[j] = True
                    j2 = 0
                    for v in range(n):
                        if (j >> v) & 1:
                            j2 |= 1 << perm[v]
                    j = j2 ^ mask
            total += 1 << cycles
    return total // (math.factorial(n) * N)


def clique_tts(n):
    """Truth tables of phi_{G,k} for every graph on n vertices (up to isomorphism) and k."""
    pairs = list(itertools.combinations(range(n), 2))
    seen_graphs = {}
    for m in range(1 << len(pairs)):
        edges = frozenset(pairs[i] for i in range(len(pairs)) if (m >> i) & 1)
        canon = min(frozenset(tuple(sorted((p[u], p[v]))) for u, v in edges)
                    for p in itertools.permutations(range(n)))
        if canon in seen_graphs:
            continue
        seen_graphs[canon] = True
        out = []
        for k in range(0, n + 1):
            tt = 0
            for s in range(1 << n):
                S = [u for u in range(n) if (s >> u) & 1]
                if len(S) >= k and all((u, v) in edges for u, v in itertools.combinations(S, 2)):
                    tt |= 1 << s
            out.append((k, tt))
        yield sorted(canon), out


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    if n >= 4 and np is None:
        print("numpy not available; n=4 would be too slow in pure Python", file=sys.stderr)
    print(f"NP classes by Burnside: n=3 {burnside_np_classes(3)}, n=4 {burnside_np_classes(4)}", flush=True)
    if n >= 5 or '--np5' in sys.argv:
        t0 = time.time()
        print(f"  n=5 {burnside_np_classes(5)}  ({time.time()-t0:.1f}s)", flush=True)

    t0 = time.time()
    print(f"\n== PC-NNF tree minima, n={n}, Pareto keying on (tt, vars+, vars-) ==")
    lv_pc, best_pc = enumerate_levels(n, pc_rule=True, pareto=True)
    print(f"  time {time.time()-t0:.1f}s; entries per level: {[len(l) for l in lv_pc]}")
    print(f"  total dictionary entries: {sum(len(l) for l in lv_pc)}; functions: {len(best_pc)}")
    per_tt = defaultdict(int)
    for l in lv_pc:
        for (tt, P, N_) in l:
            per_tt[tt] += 1
    multi = sum(1 for v in per_tt.values() if v > 1)
    print(f"  functions whose Pareto frontier has >1 entry: {multi}; max frontier size {max(per_tt.values())}")

    t0 = time.time()
    print(f"\n== PC-NNF tree minima, n={n}, keyed on tt only (first entry wins) ==")
    lv_pc1, best_pc1 = enumerate_levels(n, pc_rule=True, pareto=False, verbose=False)
    print(f"  time {time.time()-t0:.1f}s")
    diff = [(tt, best_pc[tt], best_pc1.get(tt)) for tt in best_pc if best_pc1.get(tt) != best_pc[tt]]
    worse = [d for d in diff if d[2] is None or d[2] > d[1]]
    print(f"  functions with a different (worse or missing) minimum when keyed on tt only: {len(worse)}")
    if worse:
        ex = worse[:5]
        print(f"  examples (tt, pareto min k, tt-only min k): {ex}")

    t0 = time.time()
    print(f"\n== NNF tree minima (no polarity rule), n={n} ==")
    lv_nnf, best_nnf = enumerate_levels(n, pc_rule=False, pareto=False, verbose=False)
    print(f"  time {time.time()-t0:.1f}s; entries per level: {[len(l) for l in lv_nnf]}")

    print(f"\n== k_pc / k_nnf over all {len(best_nnf)} functions (fan-in-2 gate counts, tree) ==")
    hist = defaultdict(int)
    worst = []
    for tt, knn in best_nnf.items():
        kpc = best_pc.get(tt)
        if kpc is None:
            hist['unreached'] += 1
            continue
        hist[(knn, kpc)] += 1
        worst.append((kpc - knn, kpc / knn if knn else float('inf'), tt, knn, kpc))
    maxk_nnf = max(best_nnf.values())
    maxk_pc = max(best_pc.values())
    print(f"  max k_nnf = {maxk_nnf}, max k_pc = {maxk_pc}")
    by_diff = defaultdict(int)
    for d in worst:
        by_diff[d[0]] += 1
    print(f"  distribution of k_pc - k_nnf: {dict(sorted(by_diff.items()))}")
    worst.sort(reverse=True)
    print("  largest additive gaps (gap, ratio, tt hex, k_nnf, k_pc):")
    for w in worst[:8]:
        print(f"    {w[0]:2d}  {w[1]:.2f}  {w[2]:#0{(1<<n)//4+2}x}  {w[3]}  {w[4]}")
    # ratio table restricted to k_nnf >= 1
    r = defaultdict(int)
    for d in worst:
        if d[3] > 0:
            r[round(d[1], 2)] += 1
    print(f"  ratio histogram (k_nnf>=1): {dict(sorted(r.items()))}")

    if n <= 4:
        print(f"\n== fixed-graph clique formulas phi_(G,k), n={n} vertices (tree minima, gates) ==")
        print("  edges | k: k_pc (k_nnf) ...")
        for edges, out in clique_tts(n):
            row = []
            for k, tt in out:
                kp = best_pc.get(tt)
                kn = best_nnf.get(tt)
                if tt == 0:
                    row.append(f"k={k}: F")
                elif tt == (1 << (1 << n)) - 1:
                    row.append(f"k={k}: T")
                else:
                    row.append(f"k={k}: {kp} ({kn})")
            print(f"  {edges}: " + ", ".join(row))


if __name__ == "__main__":
    main()
