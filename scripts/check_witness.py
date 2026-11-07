"""Throwaway checks for the claims added to docs/plan.md in November 2026, on tiny cases
(<= 4 variables / <= 4 vertices). Companion to check_tiny.py, which is left unchanged.
Node format is the same: ('lit', var, pos) | ('T',) | ('F',) | ('and', [ids]) | ('or', [ids]).

Checks:
  (W) witness extraction: one bottom-up pass (sat bits) plus one top-down walk yields a
      consistent literal set whose every extension is a model (Lemma W in plan.md, 2.2).
  (K) fixed-graph clique formula, fixed k: the PC-NNF
      OR over k-cliques K of ( AND_{u in K} s_u  AND  Conflicts | s_K := 1 )
      is valid and equivalent to "S is a clique of G with |S| >= k", for every graph on
      <= 4 vertices and every k (plan.md, 4.1).
  (C) clique-graph identity: for a CNF psi with m clauses and G its clique graph on literal
      occurrences, "S is a clique of G with |S| >= m" is exactly "S picks one occurrence per
      clause and contains no complementary pair"; and the literal sets of such S are
      exactly the witnessed models of psi (plan.md, 4.1 and 4.2).
"""
import itertools, random
random.seed(11)


def pols(nodes, i, memo):
    if i in memo: return memo[i]
    n = nodes[i]
    if n[0] == 'lit': r = ({n[1]}, set()) if n[2] else (set(), {n[1]})
    elif n[0] in ('T', 'F'): r = (set(), set())
    else:
        p, m = set(), set()
        for c in n[1]:
            cp, cm = pols(nodes, c, memo); p |= cp; m |= cm
        r = (p, m)
    memo[i] = r; return r


def valid(nodes):
    memo = {}
    for n in nodes:
        if n[0] == 'and':
            for a, b in itertools.permutations(n[1], 2):
                if pols(nodes, a, memo)[0] & pols(nodes, b, memo)[1]: return False
    return True


def ev(nodes, i, s, memo):
    if i in memo: return memo[i]
    n = nodes[i]
    if n[0] == 'lit': r = s[n[1]] if n[2] else 1 - s[n[1]]
    elif n[0] == 'T': r = 1
    elif n[0] == 'F': r = 0
    elif n[0] == 'and': r = int(all(ev(nodes, c, s, memo) for c in n[1]))
    else: r = int(any(ev(nodes, c, s, memo) for c in n[1]))
    memo[i] = r; return r


def table(nodes, root, assigns): return tuple(ev(nodes, root, s, {}) for s in assigns)


def bottom_up(nodes, root):
    """Returns (sat(root), memo of sat bits for every visited node)."""
    memo = {}
    def go(i):
        if i in memo: return memo[i]
        n = nodes[i]
        if n[0] in ('lit', 'T'): r = 1
        elif n[0] == 'F': r = 0
        elif n[0] == 'and': r = int(all(go(c) for c in n[1]))
        else: r = int(any(go(c) for c in n[1]))
        memo[i] = r; return r
    return go(root), memo


def witness(nodes, root):
    """Top-down walk over the pruned sub-DAG: at OR keep one child with sat=1, at AND keep all.
    Returns the set of literal leaves reached, as (var, pos) pairs, or None if sat(root)=0."""
    ok, sat = bottom_up(nodes, root)
    if not ok: return None
    lits, seen = set(), set()
    def walk(i):
        if i in seen: return
        seen.add(i)
        n = nodes[i]
        assert sat[i] == 1
        if n[0] == 'lit': lits.add((n[1], n[2]))
        elif n[0] == 'and':
            for c in n[1]: walk(c)
        elif n[0] == 'or':
            walk(next(c for c in n[1] if sat[c] == 1))
    walk(root)
    return lits


def rand_formula(N, size):
    nodes = [('T',), ('F',)] + [('lit', v, p) for v in range(N) for p in (1, 0)]
    while len(nodes) < size:
        k = random.randint(2, 3)
        kids = random.sample(range(len(nodes)), k)
        nodes.append((random.choice(['and', 'or']), kids))
    return nodes, len(nodes) - 1


def check_witness(trials=4000, N=4):
    assigns = list(itertools.product([0, 1], repeat=N))
    seen = 0
    for _ in range(trials):
        nodes, root = rand_formula(N, random.randint(11, 18))
        if not valid(nodes): continue
        seen += 1
        t = table(nodes, root, assigns)
        w = witness(nodes, root)
        if w is None:
            assert not any(t), ("witness None but satisfiable", nodes)
            continue
        assert any(t), ("witness returned for unsatisfiable formula", nodes)
        # consistent: no variable with both polarities
        assert not any((v, 1) in w and (v, 0) in w for v in range(N)), ("inconsistent witness", nodes, w)
        # every extension of the literal set is a model
        for s in assigns:
            if all(s[v] == p for v, p in w):
                assert t[assigns.index(s)] == 1, ("extension not a model", nodes, w, s)
    print(f"(W) witness extraction: {seen} random valid formulas, witness consistent and every extension a model")


def clique_formula_fixed_k(n, edges, k):
    """PC-NNF over s_0..s_{n-1}: OR over k-cliques K of (AND_{u in K} s_u AND Conflicts|s_K:=1)."""
    nodes = []
    def add(x): nodes.append(x); return len(nodes) - 1
    non_edges = [(u, v) for u, v in itertools.combinations(range(n), 2) if (u, v) not in edges]
    disj = []
    for K in itertools.combinations(range(n), k):
        if any((u, v) in non_edges for u, v in itertools.combinations(K, 2)): continue
        conj = [add(('lit', u, 1)) for u in K]
        for u, v in non_edges:            # Conflicts | s_K := 1
            if u in K and v in K: raise AssertionError
            elif u in K: conj.append(add(('lit', v, 0)))
            elif v in K: conj.append(add(('lit', u, 0)))
            else: conj.append(add(('or', [add(('lit', u, 0)), add(('lit', v, 0))])))
        disj.append(add(('and', conj)) if conj else add(('T',)))
    root = add(('or', disj)) if disj else add(('F',))
    return nodes, root


def check_fixed_k_clique(nmax=4):
    count = 0
    for n in range(1, nmax + 1):
        assigns = list(itertools.product([0, 1], repeat=n))
        pairs = list(itertools.combinations(range(n), 2))
        for mask in range(1 << len(pairs)):
            edges = {pairs[i] for i in range(len(pairs)) if mask >> i & 1}
            for k in range(0, n + 1):
                nodes, root = clique_formula_fixed_k(n, edges, k)
                assert valid(nodes), ("fixed-k clique PC-NNF invalid", n, edges, k)
                want = tuple(int(sum(s) >= k and all(not (s[u] and s[v]) for u, v in pairs if (u, v) not in edges))
                             for s in assigns)
                assert table(nodes, root, assigns) == want, ("fixed-k clique PC-NNF wrong", n, edges, k)
                count += 1
    print(f"(K) fixed-k clique PC-NNF: valid and equivalent on {count} (graph, k) pairs with <= {nmax} vertices")


def check_clique_graph_identity(trials=1500, N=4):
    assigns = list(itertools.product([0, 1], repeat=N))
    for _ in range(trials):
        m = random.randint(1, 4)
        clauses = []
        for _ in range(m):
            c = frozenset(random.sample([l for v in range(1, N + 1) for l in (v, -v)], random.randint(1, 3)))
            if any(-l in c for l in c): continue
            clauses.append(c)
        m = len(clauses)
        if m == 0: continue
        occ = [(ci, l) for ci, c in enumerate(clauses) for l in sorted(c)]
        adj = {(a, b) for a, b in itertools.combinations(range(len(occ)), 2)
               if occ[a][0] != occ[b][0] and occ[a][1] != -occ[b][1]}
        witnessed_models = set()
        for bits in itertools.product([0, 1], repeat=len(occ)):
            S = [i for i in range(len(occ)) if bits[i]]
            is_clique = all((a, b) in adj for a, b in itertools.combinations(S, 2))
            lhs = is_clique and len(S) >= m
            per_clause = [sum(1 for i in S if occ[i][0] == ci) for ci in range(m)]
            lits = {occ[i][1] for i in S}
            rhs = all(p == 1 for p in per_clause) and not any(-l in lits for l in lits)
            assert lhs == rhs, ("clique-graph identity", clauses, S)
            if lhs:
                for s in assigns:
                    if all((s[abs(l) - 1] == 1) == (l > 0) for l in lits): witnessed_models.add(s)
        models = {s for s in assigns if all(any((s[abs(l) - 1] == 1) == (l > 0) for l in c) for c in clauses)}
        assert witnessed_models == models, ("witnessed models != models", clauses)
    print(f"(C) clique-graph identity: holds on {trials} random CNFs with <= {N} variables")


check_witness(); check_fixed_k_clique(); check_clique_graph_identity()
