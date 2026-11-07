# PC-NNF for per-instance clique: working plan

## 0. Status and conventions

Status: working document, 2026-11-07. An earlier assessment (September 2026) is kept at
docs/archive/plan-2026-09-assessment.md for history. This document is self-contained and
does not depend on it.

Tags. **[checked]**: verified on tiny cases by a script in `scripts/` (`check_tiny.py` for
Theorems A and B, conditioning, forgetting, the compiler and the shortcut counterexample;
`check_witness.py` for Lemma W, Theorem B′, the fixed-k construction of 3.5 and the identity
of 1.3). **[cited]**: rests on a published result, named at the tag. **[conjecture]**:
unproven. **[reported by an earlier review; script not in repository]**: a machine check
that was run but whose script is not here. A tag is never upgraded in this document;
untagged sentences are definitions, trivial consequences, or plans. Nothing here uses the
argument "it would solve a hard problem, so it must be false"; stakes are stated as stakes
only.

---

## 1. Goal and framing

### 1.1 The intended use

PC-NNF is negation normal form plus a polarity-consistency rule at ∧-nodes (Section 2). Its
defining property is that satisfiability, and a satisfying assignment, are computed by one
bottom-up pass and one top-down walk, in time linear in the circuit size (Theorem A, Lemma W).
The polarity rule is the current way of obtaining these properties, not the goal; section 5
is about relaxing or replacing the rule while keeping the properties of 5.1.

The use is per instance. Given one fixed graph G on n vertices and a target k, build a valid
PC-NNF for the **fixed-graph clique formula**

  φ_{G,k}(s) = "the selected vertex set S = {u : s_u = 1} is a clique of G with |S| ≥ k"

over vertex-selector variables s_u, and read a witness off the circuit. A previous constructor
did this and blew up exponentially. The question for the project is whether that blow-up is
forced by the language or caused by the constructor. It splits into two questions that this
document keeps separate throughout:

1. **Existence.** For a fixed G and k, how large is the smallest valid PC-NNF equivalent to
   φ_{G,k}? Write m(φ) for the minimum size. Open: no lower-bound technique is known for it
   (Section 4.1).
2. **Construction.** Can a polynomial-time, provably correct compiler (such as the clash-graph
   compiler of Section 3.6) reach that size, on the instances of interest? Only a
   correct-by-construction compiler gives an algorithmic consequence, because a circuit from an
   untrusted source cannot be verified equivalent to φ_{G,k} in polynomial time in general
   (equivalence is coNP-hard, Section 2.4); partial one-sided checks exist (Section 6.5).

Stakes, stated once. A compiler that is polynomial on *every* graph would decide CLIQUE in
polynomial time. A proof that m(φ_{G,k}) is super-polynomial for some graph family would be a
new kind of lower bound. Neither statement is used as an argument anywhere below.

### 1.2 What the relational results do and do not say

Theorems B, C, C′ and D (Section 3) show that the **relational**
clique formula φ_{n,k}(e, s, q, z), whose variables include the edge indicators e_uv of every
graph on n vertices, has no polynomial PC-NNF. The proof goes through monotone circuit
complexity: every valid PC-NNF for a monotone function collapses to a monotone circuit of the
same size (Theorem B), and ∃(s,q,z) φ_{n,k} is CLIQUE_{n,k}(e).

These results say nothing about any single graph. For a fixed G, φ_{G,k} is obtained from
φ_{n,k} by conditioning e := E(G) and forgetting the auxiliaries q, z; both operations are free
in PC-NNF (Section 2.3), so m(φ_{G,k}) ≤ m(φ_{n,k}) for every G, and the relational bound is a
bound on a maximum over all graphs plus the cost of uniformity. The two can differ
arbitrarily: a unate CNF ψ has m(ψ) = |ψ|, while the relational formula "x satisfies the CNF
encoded by C" is exponential (Corollary C′). So the relational theorems close one route (a
PC-NNF as polynomial *advice* for all instances of a length) and leave the per-instance
question, which is the project's question, fully open.

For the same reason, extensions of the language (Section 5) are not judged by whether they
beat the relational bound. Theorem B is a lower-bound tool and a sanity check (Section 5.1),
not a verdict.

### 1.3 Where the old constructor's space sits

The old constructor reduced a CNF ψ with m clauses to clique: G = clique graph of ψ (vertices
are literal occurrences; edges join occurrences in different clauses that are not
complementary), k = m. For this G and k the fixed-graph clique formula is exactly

  φ_{G_ψ, m}(y) = ∧_C (exactly one y_v with v ∈ C) ∧ ∧_{v, v′ complementary} (¬y_v ∨ ¬y_{v′}),

a positive exactly-one family plus a negative conflict graph; its models, read as literal
sets, are the (model, witness) pairs of ψ, and their extensions are exactly the models of
ψ. **[checked]** (`check_witness.py`, check C.)
The constructor actually enumerated the larger space M(ψ) of *maximal* consistent choices
(Section 4.2). So both the fixed-graph clique question (Section 4.1) with G a clique graph and
the M(ψ) question (Section 4.2) are the same per-instance question seen from two sides.

---

## 2. The language, satisfiability, and witness extraction

Sections 2.1 to 2.4 are the authoritative definition of the language.

### 2.1 Syntax and validity

A PC-NNF is a directed acyclic graph whose nodes ("blocks") are
- leaves: a literal `x` or `¬x`, or a constant `⊤`, `⊥`;
- internal nodes: `∧(C₁,…,C_k)` or `∨(C₁,…,C_k)` with k ≥ 1, children being nodes.

A node may have many parents. **Size** |F| = number of nodes + number of parent→child
references. For a node N, define on the DAG (equivalently on the unfolded tree):
- vars⁺(N) = variables with a positive literal leaf reachable from N,
- vars⁻(N) = variables with a negative literal leaf reachable from N,
- vars(N) = vars⁺(N) ∪ vars⁻(N); N is *impure* in x if x ∈ vars⁺(N) ∩ vars⁻(N).

**Validity (polarity consistency).** F is valid iff for every ∧-node N = ∧(C₁,…,C_k)
and every i ≠ j: vars⁺(C_i) ∩ vars⁻(C_j) = ∅. Equivalently: every variable shared by
two different children of an ∧-node occurs, under *all* children of that node, with one
single polarity. ∨-nodes are unconstrained. Since vars± are computed on the DAG, the
rule automatically counts occurrences in the unfolded tree, so `(x∨¬x) ∧ (x∨¬x)` with a
shared block is invalid, as required. Validity is decidable in O(|F|·n/w) time with
n-bit bitsets (w = word size), one bottom-up pass.

Semantics are the usual Boolean ones; ⟦F⟧ ⊆ {0,1}^vars(F) is the model set.

### 2.2 Merge lemma, the bottom-up pass, and witness extraction

**Fact (unateness).** If x ∉ vars⁻(N) then ⟦N⟧ is monotone non-decreasing in x; if
x ∉ vars⁺(N) it is non-increasing. (Induction: NNF gates are monotone in their inputs.)

**Lemma A (merge).** Let N = ∧(C₁,…,C_k) satisfy the validity rule at N. If every C_i is
satisfiable then N is satisfiable.

*Proof.* Pick models σ_i ⊨ C_i. For each variable x: (case 1) x ∈ vars(C_i) for exactly
one i: set σ(x) = σ_i(x). (case 2) x occurs in ≥ 2 children: by validity x is single-
polarity in every child containing it and the polarity is the same, say positive; set
σ(x) = 1 (or 0 for negative). In case 1, children other than C_i ignore x. In case 2,
every C_i containing x is non-decreasing in x, and σ dominates σ_i on x, so σ ⊨ C_i. ∎

**Bottom-up pass.** sat(⊥)=0, sat(⊤)=1, sat(literal)=1, sat(∨)=OR of children,
sat(∧)=AND of children. Equivalently: evaluate the circuit after setting every literal
leaf to true.

**Theorem A.** For valid F: sat(F) = 1 ⇔ F is satisfiable. *Completeness* (⇒ direction
of "satisfiable ⇒ sat=1") holds for every NNF: a model of ∧ satisfies all children, a
model of ∨ satisfies some child. *Soundness* (sat=1 ⇒ satisfiable) is induction with
Lemma A at ∧-nodes. **[checked]** Because a node's answer depends on nothing outside
its own sub-DAG, block answers are context-free and memoised; time is O(|F|).

**Lemma W (witness extraction).** Let F be valid with sat(F) = 1. Walk
top-down from the root: at an ∨-node keep one child with sat = 1, at an ∧-node keep all
children, visiting each node once. Let L be the set of literal leaves reached. Then L is
consistent (no variable occurs in L with both polarities) and every total assignment
extending L is a model of F. Time O(|F|) after the bottom-up pass. **[checked]**
(`check_witness.py`, check W.)

*Proof.* Suppose `x` and `¬x` are both reached. Take one path from the root to each in the
unfolded tree and let N be the last node common to both paths. N is not a leaf and is not an
∨-node (only one child of an ∨-node is kept), so N is an ∧-node with the two occurrences
under different children C_i ≠ C_j, giving x ∈ vars⁺(C_i) ∩ vars⁻(C_j), contrary to validity.
Hence L is consistent. The kept nodes form a sub-DAG in which every kept ∨-node has a kept
child and every kept ∧-node has all its children kept; by induction every kept node
evaluates to 1 under any assignment that makes all literals of L true. ∎

Lemma W does not replace Lemma A; it is the form of soundness the harness will implement.
The witness is a partial assignment; variables outside L are free.

### 2.3 Conditioning and forgetting

**Conditioning** F|ρ for a partial assignment ρ replaces each literal leaf over dom(ρ)
by ⊤ or ⊥. This removes literal occurrences and adds none, so vars± only shrink:
validity is preserved, size does not grow, and ⟦F|ρ⟧ = ⟦F⟧|ρ. **[checked]**
Constant simplification (⊤ in ∧, ⊥ in ∨ dropped; ⊥ in ∧ collapses the node) also only
removes occurrences.

**Forgetting (∃x F).** Replace both `x` and `¬x` leaves by ⊤. For valid F this is
exactly ∃x F, unlike for general NNF. *Proof.* Write F° for the substituted formula.
F° ≥ F|x=0 ∨ F|x=1 pointwise since NNF is monotone in its leaves. Conversely, show by
induction on nodes: σ ⊨ N° ⇒ ∃b, σ ∪ {x=b} ⊨ N. At ∨ and at leaves trivial. At a valid
∧-node, each child gives a b_i; if x lies in at most one child take its b_i; if x lies
in ≥ 2 children it is single-polarity in all of them (validity), say positive, and all
of them are non-decreasing in x, so b = 1 works for every child. ∎ **[checked]**
Forgetting preserves validity and size. Forgetting a set of variables is the same
substitution applied at once.

**Polarity renaming.** Swapping x ↔ ¬x throughout preserves validity and size. Thus
m(f) = m(f with any set of variables complemented).

**Remark (auxiliary variables never help).** If F is a valid PC-NNF over
X ∪ A with ∃A F ≡ f, forgetting A gives a valid PC-NNF over X of size ≤ |F| computing f.
So m(f) may be defined over the variables of f alone, and the exact-synthesis search of
Section 6.2 need not consider auxiliaries. (Immediate from forgetting.)

### 2.4 Queries (Darwiche–Marquis knowledge-compilation map vocabulary)

| Query | PC-NNF | Reason |
|---|---|---|
| CO consistency | O(size) | Theorem A |
| witness (a model) | O(size) | Lemma W |
| CD conditioning | O(size) | 2.3 |
| FO / SFO forgetting | O(size) | 2.3 |
| CE clausal entailment F ⊨ c | O(size) | F ⊨ c ⇔ F|¬c unsatisfiable; ¬c is a term |
| ME model enumeration | output-polynomial, O(n·size) per model | branch on variables, prune with CO |
| "can ρ be extended to a model" | O(size) | CO of F|ρ |
| CT model counting | #P-hard | monotone 2-CNF is a linear PC-NNF, #vertex covers is #P-complete (Valiant, SIAM J. Comput. 8, 1979) **[cited]** |
| VA validity, IM implicant test, SE sentential entailment, EQ equivalence | coNP-hard | every consistent-term DNF is a valid PC-NNF; tautology of DNF is coNP-complete |

Two consequences worth stating once. (i) A valid PC-NNF with no ⊥ leaf is satisfiable
(sat(F) = 1 trivially), so the substantive query really is CO after conditioning. (ii)
PC-NNF is closed under ∨ (free), under ∧ of co-unate operands (same-polarity shared
variables), under conditioning, forgetting and renaming, but not under negation: ¬ swaps
∧/∨ and the polarity rule would then be required at former ∨-nodes. A "two-sided" variant
that imposes the rule at both gate types can express only unate functions (the lowest
common ancestor of an x-occurrence and a ¬x-occurrence would violate it), so VA cannot be
bought that way.

### 2.5 Background

- Expressibility: every satisfiable CNF has an equivalent valid PC-NNF (a DNF with
  consistent terms is valid). Only size matters.
- The substantive requirement is ⟦F⟧ = ⟦φ⟧ with |F| = poly(|φ|); ⊥-freeness alone gives
  satisfiability.
- DNNF ⊆ PC-NNF (disjoint children cannot conflict), so DNNF, d-DNNF and OBDD sizes
  upper-bound m. The inclusion is strict: the monotone 2-CNF of a bounded-degree expander is
  a linear-size PC-NNF but needs DNNF size 2^Ω(n) (Bova, Capelli, Mengel, Slivovsky,
  "Expander CNFs have exponential DNNF size", arXiv:1411.1995, 2014; and "Knowledge
  compilation meets communication complexity", IJCAI 2016) **[cited]**. No PC-NNF → DNNF
  translation with polynomial blow-up exists.
- Model counting is #P-hard (table above).
- A polynomial PC-NNF per instance is not by itself advice usable by a P/poly algorithm
  (the circuit depends on the instance and cannot be verified); the advice route needs the
  universal formula U_N, which Corollary C′ rules out unconditionally.

---

## 3. What is proved, and what each result means per instance

Each item ends with one line, marked ▸, on what it says about the per-instance questions
of Section 1.1.

### 3.1 Theorem A, Lemma W, conditioning, forgetting (Section 2) [checked]

▸ These are the properties the per-instance use relies on: a compiled φ_{G,k} yields a
clique in O(size), and sub-problems (G with some vertices forced in or out) come free from
the same circuit by conditioning.

### 3.2 Theorem B (monotone collapse) [checked]

**Theorem B.** Let F be a valid PC-NNF computing a *monotone* function f. Let F↑ be F with
every negative literal leaf replaced by ⊤. Then F↑ is a monotone {∧,∨}-circuit computing f,
and its fan-in-2 size is at most |F|.

*Proof.* F↑ ≥ F pointwise. For the converse show by induction on nodes:
N↑(σ) = 1 ⇒ ∃τ ≤ σ with N(τ) = 1 (pointwise order). Leaves: a `¬x` leaf gives
τ = σ[x:=0]. ∨: take the child's τ. Valid ∧-node with children C_i and witnesses
τ_i ≤ σ: for a variable private to child C_i set τ(x) = τ_i(x); for a variable in ≥ 2
children it is single-polarity in all of them (validity); if positive set
τ(x) = max_i τ_i(x) ≤ σ(x), every such child is non-decreasing in x so stays satisfied;
if negative set τ(x) = min_i τ_i(x). So τ ≤ σ, N(τ) = 1, and by monotonicity of f,
f(σ) = 1. Converting k-ary gates to binary costs ≤ k−1 gates per node, bounded by the
reference count. ∎ **[checked]**

Since a monotone circuit is itself a valid PC-NNF, **for monotone f, m(f) equals the
monotone circuit complexity of f up to a constant factor.**

**Theorem B′ (general form).** The proof of Theorem B does not use monotonicity of f. For
any valid F computing f, F↑ computes the upward closure f↑(σ) = [∃τ ≤ σ, f(τ) = 1], so
m(f) ≥ mono(f↑), and by renaming, the same for the closure under any choice of polarities.
*Proof.* The induction above gives F↑(σ) = 1 ⇒ ∃τ ≤ σ with F(τ) = 1, i.e. F↑ ≤ f↑.
Conversely F↑ is monotone and F↑ ≥ F pointwise, so F↑(σ) ≥ F↑(τ) ≥ F(τ) = f(τ) for every
τ ≤ σ, i.e. F↑ ≥ f↑. ∎ **[checked]** (`check_witness.py`, check B′.)

**Lower-bound tool (unate projections).** Combining Theorem B with 2.3: for any f and any
valid F ≡ f, |F| ≥ mono(g) for every monotone g obtainable from f by conditioning some
variables, forgetting others, and renaming polarities. Call such g a *unate projection* of f.

▸ This is the only lower-bound technique available. It applies to φ_{G,k} only through
unate projections of φ_{G,k}, and no hard one is known (Section 4.1). It also fixes the
monotone part of φ_{G,k}: "at least k of s" has monotone circuits of size O(nk), so that
part is never the obstacle.

### 3.3 Theorem C and Corollary C′ (relational families) [cited]

**Theorem C (explicit relational families).** Each family below is one satisfiable,
poly-size CNF per n whose variables *include the edge indicators of the graph*, so
its model set is a relation (graph, witness), not the solution set of one graph.
(a) The CLIQUE and Tardos-type families have m(φ_n) ≥ 2^{n^{Ω(1)}} unconditionally.
(b) The perfect-matching family has m(φ_n) ≥ n^{Ω(log n)} from Razborov 1985, and
2^{n^{1/3−o(1)}} if the 2025 monotone matching bound (arXiv:2507.16105) holds up
**[cited via search, verify before quoting]**.

The CLIQUE encoding is used again below. The other two families are: the perfect-matching
encoding, with variables e_ij (edge of K_{n,n}) and m_ij (edge used), clauses (¬m_ij ∨ e_ij)
and exactly-one constraints on m per row and per column, so that ∃m φ = PM_n(e), with
Razborov's n^{Ω(log n)} monotone bound ("logical permanent", Mat. Zametki 37, 1985)
**[cited]**; and the Tseitin encoding of a polynomial circuit for Tardos's monotone function
in P, ∃g φ_C(x, g) = f(x), with monotone complexity exp(c·n^{1/6−o(1)}) (Tardos,
Combinatorica 8, 1988) **[cited]**. Each bound transfers to m(φ_n) by forgetting (2.3) and
Theorem B.

- **CLIQUE encoding.** Variables: e_uv for u < v ∈ [n] (edge indicators), s_u
  (vertex selected), q_u (its complement), z_{i,u} (slot i ∈ [k] picks u). Clauses:
  (q_u ∨ q_v ∨ e_uv); (s_u ∨ q_u), (¬s_u ∨ ¬q_u); (∨_u z_{i,u}) per slot;
  (¬z_{i,u} ∨ ¬z_{i,u'}); (¬z_{i,u} ∨ ¬z_{j,u}); (¬z_{i,u} ∨ s_u). Then
  ∃(s,q,z) φ_{n,k}(e,s,q,z) = CLIQUE_{n,k}(e), which is monotone in e. Razborov
  (1985) gives n^{Ω(log n)} for CLIQUE; Alon–Boppana (Combinatorica 7, 1987) give
  n^{Ω(√k)} for k ≤ (n/log n)^{2/3}, i.e. 2^{Ω((n/log n)^{1/3})} at the top of that
  range **[cited]**. Note the CNF has Θ(n²) variables, so the bound is exponential in a
  polynomial of the instance size, not in the number of variables.

**Corollary C′ (the universal formula).** Let U_N(C, x) be the poly-size CNF saying
"assignment x satisfies the size-N CNF encoded by variables C", with auxiliary Tseitin
variables a. Conditioning on C := code(φ_{n,k}) and forgetting a yields φ_{n,k} itself, so
by 2.3, m(U_N) ≥ m(φ_{n,k}) = 2^{n^{Ω(1)}} for N = |φ_{n,k}|. This is one explicit
satisfiable CNF family with exponential minimum size, with no assumption.

▸ Theorem C bounds a maximum over all graphs on n vertices plus the cost of uniformity;
φ_{G,k} = ∃(q,z) φ_{n,k}|_{e:=E(G)} gives only m(φ_{G,k}) ≤ m(φ_{n,k}). Corollary C′ closes
the "one circuit as advice for all instances" route; the per-instance route is untouched.

### 3.4 Theorem D (the maximal-choice space, relational case) [proof sketch]

M(φ) is defined in Section 4.2: over one variable y_v per literal occurrence, its models
are the consistent literal choices that decide every clause (each clause is witnessed by
exactly one chosen occurrence or falsified by chosen complements).

**Key observation.** A clause containing a literal whose complement has no occurrence in φ
cannot be falsified, so it must be witnessed. Hence for φ′ = ∧_C (C ∨ w_C) with fresh w_C,
conditioning M(φ′) on y_{w_C} = 0 for all C leaves exactly the (model, witness) pairs of φ.
Conditioning and forgetting are free (2.3), so:

**Theorem D.** m(M(φ′)) ≥ m(∃_{other y} M(φ′)|_{w=0}). Applied to φ = the CLIQUE encoding
of Theorem C (with e_uv pure positive, so its clause needs no dummy), the projection onto
the e-occurrence variables is CLIQUE_{n,k}: y_e = 1 makes e_uv the witness and imposes
nothing; y_e = 0 forces the witness q_u or q_v, i.e. not both endpoints selected. So
m(M(φ′_{n,k})) ≥ mono(CLIQUE_{n,k}) = 2^{n^{Ω(1)}}. **[proof sketch above; Lean target L9]**

▸ The maximal-choice space is not easier than the model space for the *relational* encoding.
For the clique graph of a fixed CNF the bound does not apply; whether M(ψ) and ψ (or
φ_{G_ψ,m}) have the same growth on a given instance is open (Section 4.2).

### 3.5 Families with polynomial m

Provable now:
- **Unate and renamable-unate CNFs:** m ≤ |φ| (the CNF is its own PC-NNF). Renamable
  unateness is a 2-SAT check.
- **Monotone functions with small monotone circuits:** by Theorem B this is *exactly*
  the class of monotone functions with polynomial m.
- **Anything with a small OBDD, d-DNNF or DNNF:** bounded primal treewidth gives
  DNNF ≤ 2^{O(tw)}·n (Darwiche, JACM 2001) **[cited]**; XOR/parity chains with chain
  auxiliaries have O(n) OBDDs; so parity families are easy for PC-NNF.
- **Few impure variables:** Shannon expansion on the impure variables I gives
  m(φ) ≤ 2^{|I|}·|φ|, since every cofactor is unate.
- **Closure:** polynomial m is preserved by ∨ of polynomially many formulas, by
  conditioning, forgetting, renaming, and by ∧ of co-unate formulas.
- **Clash-graph decomposition:** if the clauses of φ|ρ split into components of the clash
  graph (clauses adjacent iff they contain complementary literals), the compiled block is
  an ∧ of independent compilations. A hierarchical version gives **[conjecture]**
  m(φ) ≤ |φ|·2^{O(w)} where w is a width measure of the graph on *impure* variables only.
- **Fixed-graph clique, fixed k:** for every G and k,
  φ_{G,k} = ∨_{K a k-clique of G} ( ∧_{u∈K} s_u ∧ Conflicts|_{s_K := 1} ), where
  Conflicts = ∧_{uv ∉ E(G)} (¬s_u ∨ ¬s_v) and Conflicts|_{s_K:=1} is all-negative and
  mentions no vertex of K. This is a valid PC-NNF of size O(n^{k+2}). **[checked]**
  (`check_witness.py`, check K.) The bound does not hold for DNFs (a DNF needs one term per
  maximal clique for k = 1 already); it is the ∧ with the conditioned conflict CNF inside
  each disjunct that makes it polynomial. Two further polynomial corners: k = 0 (the conflict CNF alone,
  linear) and G complete (the threshold alone, O(nk) by the standard monotone counter).

▸ Polynomial size is known for φ_{G,k} only at fixed k. The regime of interest, k growing
with n (for a clique graph, k = number of clauses), is not covered by any item above.

### 3.6 The clash-graph compiler [checked on 3000 random CNFs]

Compile a residual CNF R to a block B(R) with these rules and a cache keyed by R:
1. R = ∅ → ⊤; empty clause ∈ R → ⊥.
2. Unit clause (l): B(R) = l ∧ B(R|l).
3. **Polarity-consistent split:** compute the connected components G₁,…,G_m of the
   clash graph of R; if m > 1, B(R) = ∧_i B(G_i). (This is the exact characterisation of
   the split condition "groups share variables only in one polarity".)
4. **Decision on x:** if x is impure in R, B(R) = (¬x ∧ B(R|x=0)) ∨ (x ∧ B(R|x=1));
   if x is pure positive, B(R) = B(R|x=0) ∨ (x ∧ B(R|x=1)); symmetrically if pure
   negative. Correctness of the pure case: R is non-decreasing in x, so
   R|x=0 ≤ R|x=1 and the ¬x guard is redundant.

**Invariant:** lits(B(R)) ⊆ lits(R). By induction over the rules (each rule only emits
literals present in R, and R|ρ ⊆ R). **Validity:** rule 2 and 4 conjoin a literal with
a block over a residual that no longer mentions its variable; rule 3 conjoins blocks
with vars⁺(B(G_i)) ⊆ vars⁺(G_i) and vars⁻(B(G_j)) ⊆ vars⁻(G_j), disjoint by
construction of the components. Caching does not affect validity because validity is
a property of the unfolded tree. **[checked on 3000 random CNFs]**

This strictly generalises decision-DNNF compilation (component decomposition is the
special case of no shared variables at all) and reproduces the unate-CNF bound (an
empty clash graph splits into single clauses). Variable-selection heuristic: prefer
variables whose removal disconnects or shrinks the clash graph (e.g. highest number
of clash edges, or a static cut of the clash graph), with dtree-style caching as in
c2d/D4. Size-optimal choice is a search problem; start with greedy plus the D4 default
heuristic for comparability.

▸ This is the candidate answer to the construction question. It is correct by
construction, so its output on φ_{G,k} needs no verification; its size on φ_{G,k} is an
upper bound on m(φ_{G,k}) and the central experimental quantity (Section 6.3). Two
caveats: it takes CNF input, so "at least k of s" must be encoded with auxiliaries, and the
encoding choice affects the output size (not m); and its variable-selection heuristic is
unspecified, so a blow-up may be heuristic rather than inherent.

---

## 4. Open questions, ranked by relevance to the goal

### 4.1 The fixed-graph clique formula

φ_{G,k}(s) = "at least k of s" ∧ ∧_{uv ∉ E(G)} (¬s_u ∨ ¬s_v), over s only (auxiliaries
never help, 2.3). Non-monotone: s is positive in the threshold and negative in the
conflicts, so the plain ∧ of the two parts is invalid.

What is known:
- Upper bounds: O(n^{k+2}) at fixed k (3.5); the Shannon bound 2^{|I|}·|φ| with I = all
  of s, useless; whatever the compiler of 3.6 produces; DNNF/OBDD sizes.
- Lower bounds: none. The unate projections found so far are thresholds, independent-set
  2-CNFs after renaming, and thresholds over a fixed clique, all with small monotone
  circuits. That these are *all* the unate projections is not proved: **[conjecture]**. If
  it holds, the unate-projection tool of 3.2 can never bound φ_{G,k}.
- A second tool (Theorem B′): m(φ_{G,k}) ≥ mono(φ_{G,k}↑), and φ_{G,k}↑ is "S contains a
  k-clique of G". This closure is not a unate projection (no conditioning, forgetting or
  renaming produces it), so it is independent of the item above. It does not separate on
  every family: for the cocktail-party graph (K_{2m} minus a perfect matching) with
  k = m = n/2, a k-clique is one vertex from each matched pair, so the closure is the
  linear monotone 2-CNF ∧_i (s_i ∨ s_{i′}).
- DNNF comparison: for k = 0 the formula is the (renamed) monotone 2-CNF of the complement
  of G, so when the complement is a bounded-degree expander the DNNF size is 2^Ω(n)
  (Bova et al. **[cited]**, Section 2.5; DNNF size is invariant under renaming) while m is
  linear in the number of non-edges. A DNNF or OBDD blow-up on such
  instances therefore says nothing about PC-NNF; the baselines in Section 6 are
  interpreted with this in mind. For k ≥ 1 the same is expected but not proved.

Open sub-questions, in order:
(a) Is there a graph family with m(φ_{G,k}) super-polynomial? **[conjecture: yes]**, with no
    candidate technique.
(b) For which families is the compiler of 3.6 polynomial, under which heuristic and which
    cardinality encoding? Experimental (Section 6.3).
(c) On the instances the old constructor blew up on: does the compiler blow up too? Requires
    those instances (Section 6.1).
(d) Clique graphs of CNFs with k = number of clauses (Section 1.3): here the threshold
    disappears into exactly-one constraints and the question is the "positive exactly-one
    plus negative conflict graph" pattern of 4.2.
(e) Is mono("S contains a k-clique of G") super-polynomial for some graph family with k
    growing? By Theorem B′ a positive answer bounds m(φ_{G,k}) from below. For fixed k the
    closure is an OR over k-cliques, polynomial; the cocktail-party family does not
    separate (above); no family is known to.

### 4.2 The maximal-choice space M(φ)

**Definition.** Over vertex-indicator variables y_v, one per literal
occurrence, define M(φ) = "the chosen vertices form a clique, i.e. at most one per triangle
and no two with opposite signs of one variable, and the clique is inclusion-maximal, i.e.
every triangle with no chosen vertex has all three of its literals negated by chosen
vertices". At the variable level this is the family of consistent literal choices, one per
used clause, that cannot be extended by choosing a literal from any unused clause without a
contradiction. This is exactly the space the previous constructor enumerated. ("Triangle"
= the three occurrences of a 3-clause, which form a triangle in the clique graph.)

**Reformulation.** Let Ḡ_φ be the complement of the clique graph: vertices
are literal occurrences, edges join occurrences in the same clause and occurrences of
complementary literals. M(φ) is exactly the set of *maximal independent sets* of Ḡ_φ,
i.e. the CNF ∧_{uv∈E} (¬y_u ∨ ¬y_v) ∧ ∧_v (y_v ∨ ∨_{u∼v} y_u). A model is a consistent
literal set ρ such that every clause is either satisfied by ρ, with exactly one ρ-true
occurrence chosen as witness, or falsified by ρ (all its literals complemented in ρ). So
M(φ) ⊋ {models of φ with witnesses}; the extra models are partial assignments that
*decide* every clause. The key observation behind Theorem D: a clause containing a literal
whose complement has no occurrence cannot be falsified, so it must be witnessed; dummies
w_C and conditioning y_{w_C} = 0 cut M down to the witnessed models.

Sub-questions: must M(φ) grow exponentially for some families, and can that be
proven? Treat the general pattern "positive at-least-one / exactly-one / at-most-c
constraints mixed with a negative conflict graph" as its own sub-question, since it is the
simplest place where the difficulty appears.

Status:
- Relational case: answered by Theorem D (3.4): not easier in the worst case.
- Per-instance case: open. Neither reduction between M(φ) and φ (or φ_{G_φ,m}) is a PC-NNF
  operation: both need an ∧ with an impure operand. Whether they have the same growth on a
  given instance is experiment E5 (Section 6).
- The general pattern is hard *relationally*
  as soon as it can encode a selector of k items whose pairwise compatibility is controlled
  by pure variables (the CLIQUE encoding uses only at-least-one groups, exactly-one pairs and
  negative 2-clauses). Per instance, if every unate projection is simple (for instance a
  single at-most-c on a conflict-free set) the compiler of 3.6 gives polynomial size;
  classifying the boundary is experiment E4.
- By Section 1.3, φ_{G_ψ,m} *is* the exactly-one instance of the pattern, so 4.1(d) and
  this item are one question.

### 4.3 The impure-block family

f_G = ∧_{uv ∈ E(G)} (H_u ∨ H_v) with H_u = (x_u ∧ y_u) ∨ (¬x_u ∧ z_u) and G a bounded-degree
expander. Every x_u is impure and shared across all edges at u, so the
natural circuit is invalid at every ∧. Unate projections: conditioning all x gives the
monotone 2-CNF of G (easy); forgetting all x gives ∧_{uv} ((y_u ∨ z_u) ∨ (y_v ∨ z_v)) (easy);
so the tool of 3.2 gives nothing. **[conjecture: m(f_G) is exponential]**. This is the
separating candidate for the shared-block exemption (Section 5.2) and is ranked here
because a per-instance separation for an extension is only meaningful if the base language
is shown, or at least observed, to blow up on something concrete.

### 4.4 Random 3-SAT

No theorem either way. Almost every variable in a random 3-CNF is impure, so
the 2^{|I|} bound is useless, and the clash graph is connected above a small
clause/variable ratio. The expander DNNF bound of Bova et al. extends to random
bounded-degree graphs as a routine consequence not stated in that paper **[verified against
the abstract]**, and says nothing about PC-NNF because the expander 2-CNF itself is linear
in PC-NNF. Graph-colouring CNFs are an instance of the 4.2 pattern (positive exactly-one plus
a negative conflict graph); with edge indicators as variables the projection is
anti-monotone in e and any monotone lower bound for non-k-colourability would transfer
(none known to cite); for a fixed graph the question is open. Ranked last because it is
not on the path to the goal; it stays in the plan as a control family.

---

## 5. Extensions

### 5.1 Criteria and the role of Theorem B

An extension is assessed on, in order:
1. **One-pass satisfiability and witness extraction.** Block answers context-free (or
   boundedly context-dependent), a Lemma-W-style witness still available.
2. **Closure under conditioning.** Sub-problems must stay free.
3. **Not polynomially simulable by base PC-NNF.** Otherwise the extension changes constants,
   not the per-instance question.
4. **Evidence it helps a per-instance family.** A concrete family (Section 4) on which the
   base language blows up, provably or experimentally, and the extension does not.

Theorem B is retained as a tool and a sanity check, not as a verdict. Observation: Theorem
B's proof uses only that every gate is monotone in its inputs and that conjunctive gates
admit the merge argument, so any extension with monotone gates and a merge lemma at
conjunctive gates collapses to monotone circuits on monotone targets. This is a proof
sketch, not checked, **[conjecture]** as a general statement. Its use here: (i) for an
extension of that kind, any per-instance advantage must come from non-monotone targets,
which φ_{G,k} is; (ii) if a prototype of such an extension produces a polynomial circuit
for a relational family of Theorem C, the prototype has a bug. The stronger statement that
any language with a context-free one-pass test and conditioning closure is no stronger
than monotone circuits on monotone targets is **[conjecture]** and is not a criterion here.

### 5.2 Candidates

**Candidate 1: shared-block exemption.** Motivation: F ∧ F is semantically safe even
when F contains both x and ¬x, yet the base rule rejects it. Candidate condition: a
conflicting pair of occurrences is exempt when both lie inside instances of one block
referenced by both children. Warning: the shortcut of replacing each shared block by a
fresh atom and then checking the ordinary rule is unsound. With H = A ∧ B, F = H,
G = (H ∧ ⊥) ∨ (¬A ∧ D), the shortcut accepts F ∧ G and the bottom-up pass says satisfiable,
but F ∧ G ≡ ⊥. **[checked]** (`check_tiny.py`: the base rule rejects it and the naive pass
would be wrong.)

Sound condition (dominator rule): at an ∧-node N, let X_bad be the variables that violate
the base rule at N. N is accepted iff every x ∈ X_bad can be assigned a block H(x) ≠ N in
the sub-DAG of N such that (i) every path from N to a leaf `x` or `¬x` passes through
H(x), and (ii) for x ≠ x′ with H(x) ≠ H(x′), x ∉ vars(H(x′)). Under this rule the bottom-up
pass is unchanged, and soundness of the pass, conditioning closure and the Theorem B
collapse hold under the rule **[reported by an earlier review; script not in repository]**
(fuzzing of 9000 accepted exempt DAGs); the proof is Lean target L8. The counterexample is
rejected by the rule because the `¬A` leaf in G is not dominated by H.
Conditioning closure: the rule is preserved (conditioning removes leaves, so dominance and
X_bad only shrink). Checkability: one dominator-tree computation per ∧-node with non-empty
X_bad, O(|F|²) worst case; a single near-linear check is open. Witness extraction under the
rule: expected to follow Lemma W's argument with H(x)'s own pruned sub-DAG shared by all
paths, not checked. Simulation: base PC-NNF simulates an exempted node by Shannon expansion
on the virtual atoms, cost 2^{(number of exempt blocks at the node)}; a polynomial
simulation would need a monotone DNNF over the virtual atoms, and monotone 2-CNFs of
expanders have no small DNNF. Separating family: f_G of 4.3. **[conjecture: exponential
separation]**

**Candidate 2: XOR / exactly-k / cardinality blocks over variable-disjoint children.**
Remark. The language needs only one satisfying answer, not an enumeration. This does not
help here: the difficulty is falsifiability of the children, not choice among answers.
sat(F ⊕ G) with disjoint variables = (sat F ∧ fals G) ∨ (fals F ∧ sat G), so the pass needs
*falsifiability* of the children, which is coNP-hard for general PC-NNF (DNF ⊆ PC-NNF). The
block is sound only if its children come from a "two-sided" sublanguage with both bits
computable and closed under conditioning, e.g. decision-DNNF/OBDD, or recursively other
XOR/cardinality blocks over such children. In addition the block's variables must be private
with respect to every ancestor ∧ (an XOR is not unate in any variable, so the merge lemma
fails: (x⊕y) ∧ x ∧ y is unsatisfiable though each conjunct is). With those restrictions the
block is sound, one-pass, and conditioning-closed, but **polynomially simulable in base
PC-NNF**: with two-sided children the negation ¬F_i is available at the same size, and
⊕_{i≤k} F_i (or exactly-k, at-most-k) is the parity/counter OBDD over virtual atoms with each
ite(h_i, A, B) expanded as (F_i ∧ A) ∨ (¬F_i ∧ B), size O(k·Σ|F_i|) (O(k²·Σ|F_i|) for
counters). It changes constants, not asymptotics.

**Candidate 3: bounded-context blocks.** **[conjecture, undefined]** Each node N carries a
context set K(N) of ≤ c variables, its answer is a table sat(N|κ) over the 2^c assignments
to K(N), and the polarity rule at N is waived for variables in K(N). Undefined: how a parent
consumes a child's table when K(child) ⊄ K(parent). The strict rule K(child) ⊆ K(parent) is
sound but makes the root's context contain every context variable, so Shannon expansion on
≤ c variables simulates it in base PC-NNF at cost 2^c: no asymptotic gain. The permissive
rule (drop a child's context variable when it is private to that child within the parent)
is where a separation might live; its soundness and base simulation are not worked out.
Not for implementation until defined.

**Candidate 4: decision nodes on impure shared variables.** Already expressible as
conditioning inside the ∨ of rule 4 in 3.6; no gain.

**Candidate 5: negation of two-sided sub-blocks** (¬H as a leaf when H is
decision-DNNF/OBDD). Sound and one-pass, but ¬H has an explicit decision-DNNF of the same
size, so no gain.

### 5.3 Ranking on the criteria of 5.1

| Rank | Extension | 1. One-pass sat + witness | 2. Conditioning | 3. Not base-simulable | 4. Per-instance evidence | Theorem B collapse extends (sanity only) |
|---|---|---|---|---|---|---|
| 1 | Shared-block exemption (dominator rule) | sat: yes, unchanged pass [sketch, L8]; witness: expected, unchecked | yes | conjectured yes (needs monotone DNNF of virtual atoms to simulate) | f_G of 4.3, conjecture only; no experiment yet | reported (5.2) |
| 2 | Bounded-context blocks, permissive rule | undefined | undefined | unknown (strict rule: no, 2^c) | none | would, if sound |
| 3 | XOR / exactly-k / cardinality over disjoint two-sided children | yes, needs fals bits | yes | **no** (parity/counter OBDD over virtual atoms) | none possible | not applicable |
| 4 | Negation of two-sided sub-blocks | yes | yes | **no** | none possible | not applicable |
| 5 | Decision nodes on impure shared variables | yes | yes | **no** (already expressible) | none possible | yes |
| — | XOR over general PC-NNF children | **no** (coNP-hard fals) | — | — | — | — |
| — | Rule at both ∧ and ∨ ("two-sided PC-NNF") | yes, both bits | yes | expresses only unate functions | — | — |

Recommendation: candidate 1 is the only one worth building, and only after the base
language has been measured on f_G and on φ_{G,k} (Section 6), so that a separation has
something to separate from. Candidates 3 to 5 are closed by criterion 3. Candidate 2
(bounded-context) stays on paper until defined. No extension design starts before E2 has
run.

---

## 6. Experiment plan, centred on the fixed-graph clique formula

### 6.1 Required input from the user

The instances on which the old constructor blew up are not in this repository and are
not substituted. Needed: the graphs G and targets k (or the CNFs ψ from which clique
graphs were built), the constructor's output sizes per instance, and, if available, the
constructor's circuits so that validity and equivalence at tiny n can be re-checked.
Experiments E1 to E3 below run without them; E6 cannot.

### 6.2 E1: exact minima at tiny n (SAT-based synthesis)

Only exact minima say anything about lower bounds, and only at tiny size. Method: SAT-based
exact synthesis (Knuth TAOCP 7.1.2 style; Kojevnikov–Kulikov–Yaroslavtsev 2009). Encode
"there is a valid PC-NNF with s nodes computing truth table t" over the s-variables only
(auxiliaries never help, 2.3): per node a type (∧/∨/literal/constant), child selectors,
per-node vars⁺/vars⁻ bitsets propagated through children, the validity constraint at
∧-nodes, and the truth-table constraint over all 2^n assignments. Solve with CaDiCaL for
s = 1, 2, … until satisfiable. Use fan-in 2 for the search and report both binary size and
the n-ary size (n-ary ≤ binary ≤ 3× n-ary, so growth rates are unaffected). Expected reach:
n ≤ 5, s ≤ ~25.

Targets, in order:
- **All graphs on n ≤ 5 vertices, all k** (34 non-isomorphic graphs at n = 5), giving a
  complete table m(φ_{G,k}). Compare against the O(n^{k+2}) construction of 3.5 and against
  the compiler of 3.6 to measure the compiler's overhead at tiny size.
- Clique graphs of the smallest CNFs: two clauses of width ≤ 2 give ≤ 4 occurrences, so
  ≤ 4 vertices, with k = 2. These are the smallest instances of the exactly-one pattern
  (4.1(d)); anything larger exceeds the n ≤ 5 reach.
- Monotone-circuit minima (same tool, positive leaves only) for the relational CLIQUE_{n,k}
  at n ≤ 4, to test tightness of the projection bound (H8, a sanity check).
- Same encoding with the dominator rule of 5.2 (dominance is expressible with per-node
  reachability bits), only for f_G at tiny G (paths, triangles), and only after E2.

Exact minima at n ≤ 5 cannot distinguish polynomial from exponential growth. Their role is
to calibrate E2 (how far above the minimum does the compiler land) and to catch bugs.

### 6.3 E2: the compiler of 3.6 on growing graph families

Compile φ_{G,k} as CNF (conflict clauses plus a cardinality encoding of "at least k": naive
∨ over k-subsets for k ≤ 3, sequential counter, totalizer; report each) with the compiler of
3.6 under heuristics (a) most clash edges, (b) minimum cut of the clash graph, (c) D4-like
dynamic decomposition on the clash graph. Log the size after each rule application to
attribute savings to splitting vs. pure decision vs. caching. Forget the cardinality
auxiliaries from the output (free) before measuring, so all sizes are over s.

Graph families, n up to the compiler's limit:
- Complete graphs and complete multipartite (Turán) graphs: cliques easy to see; control.
- Complements of perfect matchings (cocktail-party graphs): exponentially many maximal
  cliques, DNF-hard at k = 1, but conflict clauses are disjoint; control for the "DNF vs.
  PC-NNF" gap of 3.5.
- Complements of random 3-regular and 5-regular graphs (expanders w.h.p.): DNNF-hard at k = 0
  (4.1), PC-NNF linear at k = 0; the question is k growing.
- Random G(n, p) for p ∈ {0.3, 0.5, 0.7, 0.9}, with k from 2 up to the clique number.
- Clique graphs of random satisfiable 3-CNFs at clause/variable ratios {2, 3, 4, 4.26}, with
  k = number of clauses (Section 1.3); this is the family the old constructor's instances
  presumably belong to.
- Clique graphs of structured CNFs: graph-colouring, pigeonhole (unsatisfiable: the
  compiled circuit must have sat = 0, and its size measures how much search the compiler
  does before collapsing).
Per family: median and max size vs n on a log axis; fitted exponent of log(size) vs n and vs
n log n; ratio to the exact minimum where E1 reaches.

### 6.4 E3: DNNF and OBDD baselines

D4 (Lagniez–Marquis 2017; github.com/crillab/d4) and c2d (Darwiche) on the same CNFs, with
auxiliaries forgotten afterwards (free for DNNF); CUDD OBDDs built directly over s from
"threshold ∧ conflicts" with sifting. All sizes converted to the common DAG format and the
size definition of 2.1. Both upper-bound m(φ_{G,k}). Expectation from 4.1: DNNF/OBDD blow up
on complements of expanders regardless of k; so the informative comparison is where the
compiler of 3.6 tracks or beats them, and any instance where the compiler exceeds D4 is a
bug or a heuristic issue (H4).

### 6.5 Validity and partial verification of untrusted circuits

Every circuit from E2 and E3 is re-checked for validity (2.1). A circuit from an untrusted
source (the old constructor, or E1's synthesizer) can be checked at tiny n by truth table.
At larger n only one-sided checks are available: "every model of F is a clique" is the set of
O(n²) clausal-entailment queries F ⊨ (¬s_u ∨ ¬s_v) over non-edges, each O(|F|) (2.4); the
other direction (every k-clique is a model, and every model has ≥ k vertices) has no
polynomial check in general. Hence the construction question is settled only by a
correct-by-construction compiler.

### 6.6 E4 and E5: the pattern boundary and M(ψ)

E4: for the "positive at-least-one / exactly-one / at-most-c plus negative conflict graph"
pattern (4.2), vary the group structure and the conflict graph (disjoint groups vs.
overlapping, conflict graph a matching, a path, a grid, an expander) and compile; look for
the boundary between polynomial and exponential compiler growth and relate it to the width
of the impure-variable graph (H5).

E5: for the same CNFs ψ, compile φ_{G_ψ,m}(y), M(ψ) (the raw maximal-independent-set CNF),
and the w-dummied, conditioned variant of Theorem D; compare growth exponents per instance.

### 6.7 E6: the old constructor's instances

Once the input of 6.1 is available: compile each instance with the compiler of 3.6 and with
D4/c2d; report compiler size against the constructor's size; where n is tiny, exact minima.

### 6.8 Control families

Random 3-SAT (n ∈ {10,…,60}, ratios {1, 2, 3, 3.5, 4, 4.26, 5, 6}, 20 seeds each,
satisfiable instances only, filtered with a SAT solver); parity/XOR chains
x₁⊕…⊕x_n = b with chain auxiliaries and Tseitin formulas on random 3-regular graphs with
satisfiable charge; monotone 2-CNFs of expanders (random 3-regular and 5-regular graphs)
and of bounded-treewidth graphs (paths, cycles, grids); graph k-colouring for grids,
random regular and G(n, p) graphs with k = 3, 4, both as fixed-graph CNFs and with edge
indicators as variables; and the relational CLIQUE / perfect-matching encodings of
Theorem C at n ≤ 8 with their w-dummied versions for M. All generators are a C# library
with DIMACS output. These families are kept as controls where m is known or where DNNF
behaviour is known, and for a heat map of fitted growth exponent over ratio × heuristic,
but they are not on the path to the goal.

### 6.9 Hypotheses

| # | Hypothesis | Bears on | Status from theory | How the experiments move it |
|---|---|---|---|---|
| H1 | m(φ_{G,k}) is polynomial in n on the graph families of 6.3 with k growing. | Existence (1.1) | Open; known polynomial only at fixed k (3.5). | Polynomial compiler growth (E2) supports; exponential compiler growth is consistent with it but proves nothing; exact minima (E1) too small to decide. |
| H1′ | Some graph family has super-polynomial m(φ_{G,k}). | Existence (1.1) | **[conjecture]**; no technique (4.1). | Not refutable experimentally except by a polynomial upper bound on every tested family; a proof needs a new lower-bound method. |
| H2 | The compiler of 3.6, with some heuristic and encoding, is polynomial on the families of 6.3. | Construction (1.1) | Open. | E2 directly; heuristic and encoding dependence reported separately. |
| H2′ | On the old constructor's instances the compiler is polynomial, so the old blow-up was the constructor's. | Construction (1.1) | Open; the relational bounds (3.3) do not apply to fixed instances. | E6; needs the input of 6.1. Refuted for those instances only if all compilers and exact minima grow exponentially. |
| H3 | Compiler size tracks the exact minimum within a small factor at n ≤ 5. | Construction (1.1) | Hypothesis. | E1 vs E2. |
| H4 | The compiler never exceeds decision-DNNF (D4/c2d) size on the same instance and variable order. | Construction (1.1), sanity | Hypothesis: after a clash-graph split the residuals and cache behaviour differ from D4's. | E3; any violation is a bug or heuristic issue. |
| H5 | Size is governed by the structure of impure variables: m(φ) ≤ ǀφǀ·2^{O(w)} for a width w of the clash structure. | Existence (1.1), pattern of 4.2 | **[conjecture]** (3.5). | E4; a family with bounded width and exponential size refutes it. |
| H6 | M(ψ), φ_{G_ψ,m} and ψ have the same size growth on the same instances. | 4.2 | Open. | E5; divergent exponents refute. |
| H7 | The shared-block exemption gives exponential savings on f_G of 4.3. | Extensions | **[conjecture]** (5.2). | Exact minima with and without the rule at tiny G (E1, last item) that coincide weaken it; compiler growth on expanders supports it. Deferred until E2 has shown a base blow-up. |
| H8 | The projection bound is tight on tiny relational CLIQUE encodings: exact m(φ_{n,k}) equals the monotone-circuit minimum of CLIQUE_{n,k}. | Sanity check of Theorem B | Open; Theorem B is an equality only for monotone f. | E1 at n ≤ 4; an exact minimum below the monotone minimum would contradict Theorem B and indicate a bug. |
| H9 | Random 3-SAT at fixed ratio has exponential m. | Control | Open; no technique (4.4). | Polynomial compiler sizes refute; exponential sizes prove nothing. |

---

## 7. Lemmas to machine-check in Lean 4

Represent formulas as an inductive tree first (validity and semantics are properties
of the unfolded tree, so DAG sharing is a representation detail proved separately as
"unfolding preserves everything"). Variables are `Nat`, assignments `Nat → Bool`.

| # | Statement | Depends on | Effort |
|---|---|---|---|
| L1 | Unateness: `x ∉ vars⁻ N → Monotone (fun b => eval N (σ[x:=b]))`, and the negative dual. | — | small |
| L2 | Merge lemma A. | L1 | medium |
| L3 | Theorem A: for valid F, `bottomUp F = true ↔ ∃ σ, eval F σ = true`. Both directions. | L2 | medium |
| L4 | Conditioning: preserves validity, `eval (F∣ρ) σ = eval F (σ ⊕ ρ)`, size non-increasing. | — | small |
| L5 | Forgetting: `eval (F[x,¬x:=⊤]) σ = eval F σ[x:=0] ∨ eval F σ[x:=1]` for valid F; validity preserved. | L1 | medium |
| L6 | Theorems B and B′ (collapse to the upward closure) and the size bound after fan-in-2 conversion. | L1 | medium |
| L7 | Clash-graph compiler (3.6): output valid and equivalent to the input CNF (invariant lits(B(R)) ⊆ lits(R)). | L4 | medium; write the compiler in Lean directly |
| L8 | Shared-block exemption soundness (5.2) and, as a `decide`-checked example, that the naive atom shortcut accepts the A/¬A counterexample. | L2, L5 | large; the dominator formulation needs a DAG model |
| L9 | Theorem C/D projection identities: `∃ s q z, φ_{n,k}(e,s,q,z) ↔ CLIQUE_{n,k} e`, and the w-dummy / pure-literal lemma of 4.2. | — | medium |
| L10 | XOR-block soundness over two-sided children, and its polynomial simulation. | L3 | small; low priority (Section 5) |
| L11 | Lemma W: the pruned sub-DAG's literal set is consistent and every extension is a model; and the fixed-k construction of 3.5 is valid and equivalent to φ_{G,k}. | L3 | small |

Not machine-checkable here and to be cited: Razborov, Alon–Boppana, Tardos,
Harnik–Raz (monotone lower bounds), Bova–Capelli–Mengel–Slivovsky (DNNF lower bounds),
Valiant (#P-completeness). Use core Lean 4 plus Batteries; add Mathlib only if the
`Finset`/`Function.Monotone` API is needed (it likely is for L6). Priority order for the
goal: L7 (the compiler is the deliverable that needs trust), L3/L11, L4, then the rest.

---

## 8. Toolchain and dev-container changes

**Current state (2026-11-07):** `.devcontainer/Dockerfile` installs Node, git, zsh, the
Claude Code CLI and the firewall script only. None of .NET, Lean/elan, pip packages,
CaDiCaL, D4 or CUDD is present. Everything below has to be applied before any harness
work; `scripts/check_tiny.py` and `scripts/check_witness.py` run
on the system Python 3.11 without packages.

Roles: C# (.NET 8) for generators, compilers, exact synthesis driver, and metrics;
Lean 4 for Section 7; Python only for throwaway checks such as `scripts/check_tiny.py`.

Add to `.devcontainer/Dockerfile` (build-time, so the runtime firewall does not
apply):
- .NET 8 SDK via `dotnet-install.sh --channel 8.0` into `/usr/share/dotnet`, with
  `DOTNET_CLI_TELEMETRY_OPTOUT=1`.
- `elan` via `elan-init.sh -y` for user `node`, pinned to the toolchain named in the
  future `lean-toolchain` file; run `lake build` once at image build if the Lean
  project exists.
- `python3-pip python3-venv`, then `pip install python-sat networkx matplotlib pandas`
  in a venv (throwaway scripts only).
- Build tools for external compilers and solvers: `build-essential cmake ninja-build
  libgmp-dev zlib1g-dev libboost-all-dev` (D4's dependencies to be confirmed against
  its README at build time). Build CaDiCaL and Kissat from GitHub; build D4 from
  github.com/crillab/d4; c2d is a binary download from Darwiche's site with its own
  licence, so keep it out of the image and mount it from the host.
- CUDD: prefer the NuGet package `DecisionDiagrams` for the C# harness; the Python
  `dd` package with its CUDD build as a cross-check.

`.devcontainer/devcontainer.json`: add extensions `ms-dotnettools.csdevkit`,
`leanprover.lean4`, `ms-python.python`; keep prettier off for `.cs`/`.lean` files.

`init-firewall.sh` allowlist additions for runtime use: `api.nuget.org` (NuGet
restore), `pypi.org` and `files.pythonhosted.org` (pip), `release.lean-lang.org` and
`lakecache.blob.core.windows.net` (Lean toolchains and Mathlib cache, if Mathlib is
adopted). GitHub is already allowed and covers elan, Batteries, D4, CaDiCaL, Kissat.

Repository layout to create in the next step: `src/PcNnf.Core` (DAG, validity,
queries), `src/PcNnf.Compile`, `src/PcNnf.Exact`, `src/PcNnf.Bench`, `lean/PcNnf`,
`scripts/`, `data/` (git-ignored), `docs/`.

Order of work: (1) toolchain, (2) `PcNnf.Core` with validity, the
pass, Lemma W, conditioning, forgetting, (3) the compiler of 3.6 with its validity re-check,
(4) E2 on the families of 6.3 and E6 once the instances arrive, (5) E1, (6) E3, (7) Lean L7.
