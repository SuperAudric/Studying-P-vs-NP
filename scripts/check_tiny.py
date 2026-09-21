"""Throwaway checks of PC-NNF claims on tiny cases (<=4 variables).
Node = ('lit', var, pos) | ('T',) | ('F',) | ('and', [ids]) | ('or', [ids]); a formula is (nodes, root).
"""
import itertools, random
random.seed(7)
N = 4
ASSIGN = list(itertools.product([0, 1], repeat=N))

def pols(nodes, i, memo):
    """(positive vars, negative vars) occurring in the unfolded tree below i."""
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
    for i, n in enumerate(nodes):
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

def table(nodes, root): return tuple(ev(nodes, root, s, {}) for s in ASSIGN)

def bottom_up(nodes, root):
    memo = {}
    def go(i):
        if i in memo: return memo[i]
        n = nodes[i]
        if n[0] == 'lit': r = 1
        elif n[0] == 'T': r = 1
        elif n[0] == 'F': r = 0
        elif n[0] == 'and': r = int(all(go(c) for c in n[1]))
        else: r = int(any(go(c) for c in n[1]))
        memo[i] = r; return r
    return go(root)

def subst(nodes, f):
    """f(var, pos) -> None (keep) or 'T'/'F'."""
    out = []
    for n in nodes:
        if n[0] == 'lit':
            r = f(n[1], n[2]); out.append(n if r is None else (r,))
        else: out.append(n)
    return out

def rand_formula(size):
    nodes = [('T',), ('F',)] + [('lit', v, p) for v in range(N) for p in (1, 0)]
    while len(nodes) < size:
        k = random.randint(2, 3)
        kids = random.sample(range(len(nodes)), k)
        nodes.append((random.choice(['and', 'or']), kids))
    return nodes, len(nodes) - 1

def check_random(trials=4000):
    seen = 0
    for _ in range(trials):
        nodes, root = rand_formula(random.randint(11, 18))
        if not valid(nodes): continue
        seen += 1
        t = table(nodes, root)
        # (a) bottom-up pass sound + complete
        assert bottom_up(nodes, root) == int(any(t)), ("pass", nodes)
        # (a') also after conditioning on every partial assignment of 2 vars
        for v1, v2 in itertools.combinations(range(N), 2):
            for b1, b2 in itertools.product([0, 1], repeat=2):
                cond = subst(nodes, lambda v, p: None if v not in (v1, v2) else
                             ('T' if ((b1 if v == v1 else b2) == p) else 'F'))
                assert valid(cond), "conditioning broke validity"
                tc = table(cond, root)
                assert bottom_up(cond, root) == int(any(tc)), ("pass|cond", nodes)
        # (b) forgetting x == substitute both literals of x by T
        for x in range(N):
            fx = subst(nodes, lambda v, p: 'T' if v == x else None)
            tf = table(fx, root)
            exists = tuple(int(t[ASSIGN.index(s)] or t[ASSIGN.index(s[:x] + (1 - s[x],) + s[x + 1:])])
                           for s in ASSIGN)
            assert tf == exists, ("forget", nodes, x)
        # (c) monotone collapse: if f monotone then F[negative literals := T] == f
        mono = all(t[ASSIGN.index(s)] <= t[ASSIGN.index(s2)]
                   for s in ASSIGN for s2 in ASSIGN if all(a <= b for a, b in zip(s, s2)))
        if mono:
            coll = subst(nodes, lambda v, p: None if p else 'T')
            assert table(coll, root) == t, ("collapse", nodes)
    print(f"random valid formulas checked: {seen}")

def check_shortcut_counterexample():
    # H = A ∧ B ; F = H ; G = (H ∧ ⊥) ∨ (¬A ∧ D) ; root = F ∧ G
    nodes = [('lit', 0, 1), ('lit', 1, 1), ('and', [0, 1]),           # 2 = H
             ('F',), ('and', [2, 3]), ('lit', 0, 0), ('lit', 3, 1),
             ('and', [5, 6]), ('or', [4, 7]),                          # 8 = G
             ('and', [2, 8])]                                          # 9 = F ∧ G
    assert not valid(nodes)                       # base rule rejects (A vs ¬A)
    assert bottom_up(nodes, 9) == 1 and not any(table(nodes, 9))   # pass would be wrong
    print("shortcut counterexample: base rule rejects; naive pass would be unsound (as claimed)")

# ---- Q1c compiler: clash-graph split + polarity-preserving decision, on random CNFs ----
def compile_cnf(clauses, nodes, cache):
    key = tuple(sorted(clauses))
    if key in cache: return cache[key]
    def add(n): nodes.append(n); return len(nodes) - 1
    if not clauses: r = add(('T',))
    elif any(len(c) == 0 for c in clauses): r = add(('F',))
    else:
        # clash-graph components
        cl = list(clauses); comp = list(range(len(cl)))
        def find(i):
            while comp[i] != i: comp[i] = comp[comp[i]]; i = comp[i]
            return i
        for i, j in itertools.combinations(range(len(cl)), 2):
            if any(-l in cl[j] for l in cl[i]): comp[find(i)] = find(j)
        groups = {}
        for i in range(len(cl)): groups.setdefault(find(i), []).append(cl[i])
        if len(groups) > 1:
            r = add(('and', [compile_cnf(frozenset(g), nodes, cache) for g in groups.values()]))
        else:
            lits = {l for c in cl for l in c}
            x = abs(next(iter(lits)))
            def cond(val):  # x := val
                out = []
                for c in cl:
                    if (x if val else -x) in c: continue
                    out.append(frozenset(l for l in c if abs(l) != x))
                return frozenset(out)
            r0, r1 = compile_cnf(cond(0), nodes, cache), compile_cnf(cond(1), nodes, cache)
            if x in lits and -x in lits:
                r = add(('or', [add(('and', [add(('lit', x - 1, 0)), r0])), add(('and', [add(('lit', x - 1, 1)), r1]))]))
            elif x in lits:
                r = add(('or', [r0, add(('and', [add(('lit', x - 1, 1)), r1]))]))
            else:
                r = add(('or', [add(('and', [add(('lit', x - 1, 0)), r0])), r1]))
    cache[key] = r; return r

def check_compiler(trials=3000):
    for _ in range(trials):
        m = random.randint(1, 7)
        clauses = frozenset(frozenset(random.sample([l for v in range(1, N + 1) for l in (v, -v)], random.randint(1, 3)))
                            for _ in range(m))
        clauses = frozenset(c for c in clauses if not any(-l in c for l in c))  # drop tautologies
        nodes, cache = [], {}
        root = compile_cnf(clauses, nodes, cache)
        assert valid(nodes), ("compiler validity", clauses)
        want = tuple(int(all(any((s[abs(l) - 1] == (1 if l > 0 else 0)) for l in c) for c in clauses)) for s in ASSIGN)
        assert table(nodes, root) == want, ("compiler equivalence", clauses)
    print("Q1c compiler: valid and equivalent on", trials, "random CNFs")

check_random(); check_shortcut_counterexample(); check_compiler()
