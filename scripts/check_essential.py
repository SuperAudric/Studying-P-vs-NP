"""Throwaway checks for the essential-polarity lemma (docs/exact-minima-strategy.md, 2026-11-09).
Node format as in check_tiny.py: ('lit', var, pos) | ('T',) | ('F',) | ('and', [ids]) | ('or', [ids]).
Formulas are DAGs with shared nodes (rand_formula samples children among all earlier nodes).

(P1) Per-variable closure. For valid F computing f and a variable x with f non-decreasing in x,
     F[not-x := T] computes f (and is valid, no larger). Dually, f non-increasing in x gives
     F[x := T] == f. This is the single-variable form of Theorem B' (plan 3.2).
(P2) Consequence. If a valid F has a leaf whose polarity is redundant for f (a not-x leaf with f
     non-decreasing in x, or an x leaf with f non-increasing in x), then replacing it by T and
     propagating constants gives a valid F' == f with strictly smaller plan-2.1 size (nodes +
     references) and no more gates. Hence every size-minimal valid PC-NNF, tree or DAG, has
     vars+ = {x : f not non-increasing in x} and vars- = {x : f not non-decreasing in x}.
"""
import itertools, random
random.seed(5)
N = 4
ASSIGN = list(itertools.product([0, 1], repeat=N))
IDX = {s: i for i, s in enumerate(ASSIGN)}


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


def valid(nodes, root):
    memo = {}
    for i in reach(nodes, root):
        n = nodes[i]
        if n[0] == 'and':
            for a, b in itertools.permutations(n[1], 2):
                if pols(nodes, a, memo)[0] & pols(nodes, b, memo)[1]: return False
    return True


def reach(nodes, root):
    seen, stack = set(), [root]
    while stack:
        i = stack.pop()
        if i in seen: continue
        seen.add(i)
        if nodes[i][0] in ('and', 'or'): stack.extend(nodes[i][1])
    return seen


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


def size21(nodes, root):
    """plan 2.1 size over the reachable sub-DAG: nodes + parent->child references."""
    R = reach(nodes, root)
    return len(R) + sum(len(nodes[i][1]) for i in R if nodes[i][0] in ('and', 'or'))


def gates(nodes, root):
    return sum(1 for i in reach(nodes, root) if nodes[i][0] in ('and', 'or'))


def flip(s, x): return s[:x] + (1 - s[x],) + s[x + 1:]


def nondecreasing(t, x): return all(t[IDX[s]] <= t[IDX[flip(s, x)]] for s in ASSIGN if s[x] == 0)
def nonincreasing(t, x): return all(t[IDX[s]] >= t[IDX[flip(s, x)]] for s in ASSIGN if s[x] == 0)


def subst(nodes, f):
    out = []
    for n in nodes:
        if n[0] == 'lit':
            r = f(n[1], n[2]); out.append(n if r is None else (r,))
        else: out.append(n)
    return out


def simplify(nodes, root):
    """Constant propagation on the DAG: T in and / F in or dropped; F in and -> F; T in or -> T;
    one-child gates collapse to the child. Returns (nodes, root) of a new DAG."""
    new, mapping = [], {}
    def go(i):
        if i in mapping: return mapping[i]
        n = nodes[i]
        if n[0] in ('lit', 'T', 'F'):
            new.append(n); r = len(new) - 1
        else:
            kids = [go(c) for c in n[1]]
            absorb, neutral = ('F', 'T') if n[0] == 'and' else ('T', 'F')
            if any(new[k][0] == absorb for k in kids):
                new.append((absorb,)); r = len(new) - 1
            else:
                kids = [k for k in kids if new[k][0] != neutral]
                kids = list(dict.fromkeys(kids))  # drop duplicate references
                if not kids: new.append((neutral,)); r = len(new) - 1
                elif len(kids) == 1: r = kids[0]
                else: new.append((n[0], kids)); r = len(new) - 1
        mapping[i] = r; return r
    r = go(root)
    return new, r


def rand_formula(size, share_bias=0.0):
    """share_bias: probability that a child is drawn from internal nodes only, to produce DAGs
    with many shared sub-circuits (the case where the DAG form of the lemma matters)."""
    nodes = [('T',), ('F',)] + [('lit', v, p) for v in range(N) for p in (1, 0)]
    while len(nodes) < size:
        k = random.randint(2, 3)
        internal = [i for i in range(len(nodes)) if nodes[i][0] in ('and', 'or')]
        kids = set()
        while len(kids) < k:
            if internal and random.random() < share_bias: kids.add(random.choice(internal))
            else: kids.add(random.randrange(len(nodes)))
        nodes.append((random.choice(['and', 'or']), sorted(kids)))
    return nodes, len(nodes) - 1


def check(trials=6000, share_bias=0.0):
    seen = p1 = p2 = shared = 0
    for _ in range(trials):
        nodes, root = rand_formula(random.randint(11, 20), share_bias)
        if not valid(nodes, root): continue
        seen += 1
        t = table(nodes, root)
        R = reach(nodes, root)
        # count DAGs with a genuinely shared internal node (more than one parent in R)
        parents = {}
        for i in R:
            if nodes[i][0] in ('and', 'or'):
                for c in nodes[i][1]:
                    if nodes[c][0] in ('and', 'or'): parents[c] = parents.get(c, 0) + 1
        if any(v > 1 for v in parents.values()): shared += 1
        memo = {}
        P, M = pols(nodes, root, memo)
        for x in range(N):
            for nd, pol_redundant in ((nondecreasing(t, x), 0), (nonincreasing(t, x), 1)):
                if not nd: continue
                # (P1): replace the redundant-polarity leaf by T
                g = subst(nodes, lambda v, p: 'T' if (v == x and p == pol_redundant) else None)
                assert valid(g, root), ("closure broke validity", nodes, x)
                assert table(g, root) == t, ("per-variable closure", nodes, x, pol_redundant)
                p1 += 1
                # (P2): if that leaf was actually used, the simplified DAG is strictly smaller
                used = (x in M) if pol_redundant == 0 else (x in P)
                if used:
                    s, r = simplify(g, root)
                    assert valid(s, r) and table(s, r) == t, ("simplified", nodes, x)
                    assert size21(s, r) < size21(nodes, root), ("size not reduced", nodes, x)
                    assert gates(s, r) <= gates(nodes, root), ("gates grew", nodes, x)
                    p2 += 1
    print(f"(P1) per-variable closure: {p1} (formula, variable) cases on {seen} random valid DAGs "
          f"({shared} with a shared internal node): F[redundant leaf := T] == f, valid")
    print(f"(P2) redundant-polarity leaf present in {p2} cases: simplified DAG valid, equivalent, strictly smaller")


check()
check(trials=12000, share_bias=0.6)
