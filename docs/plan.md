# PC-NNF study: definitions, assessment of Q1–Q3, experiment plan

Status: planning document, 2026-09-19. Claims marked **[checked]** were verified on tiny
cases by `scripts/check_tiny.py`; claims marked **[cited]** rest on published results;
claims marked **[conjecture]** are unproven. Nothing in this document uses the banned
argument "it would solve a hard problem, so it must be false".

**Headline.** The universal formula U_N of fact 5 ("assignment x satisfies the CNF
encoded by variables C") has *unconditionally* exponential PC-NNF size
(Corollary C'), so the hypothesis "every satisfiable CNF has a polynomial PC-NNF" is
false outright and the P/poly route of fact 5 is closed without any complexity
assumption. The proof is a new reduction to monotone circuit complexity (Theorem B)
rather than rectangle covers, applied to *relational* encodings: one CNF per n whose
variables include the edges of the graph (Theorems C, D). These bounds concern the
relational formulas only. They say nothing about *per-instance* formulas (a fixed
graph, a fixed 3-CNF), because a per-instance formula is a conditioning of the
relational one and conditioning never increases size. Whether the language blows up
on per-instance formulas, including the instances the previous constructor ran on
and random 3-SAT, is the main open question, theoretical and experimental.

---

## 1. PC-NNF: formal write-up

### 1.1 Syntax

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

### 1.2 Merge lemma and the bottom-up pass

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

### 1.3 Conditioning and forgetting

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

### 1.4 Queries (Darwiche–Marquis knowledge-compilation map vocabulary)

| Query | PC-NNF | Reason |
|---|---|---|
| CO consistency | O(size) | Theorem A |
| CD conditioning | O(size) | 1.3 |
| FO / SFO forgetting | O(size) | 1.3 |
| CE clausal entailment F ⊨ c | O(size) | F ⊨ c ⇔ F|¬c unsatisfiable; ¬c is a term |
| ME model enumeration | output-polynomial, O(n·size) per model | branch on variables, prune with CO |
| "can ρ be extended to a model" | O(size) | CO of F|ρ |
| CT model counting | #P-hard | fact 4: monotone 2-CNF is a linear PC-NNF, #vertex covers is #P-complete (Valiant 1979) **[cited]** |
| VA validity, IM implicant test, SE sentential entailment, EQ equivalence | coNP-hard | every consistent-term DNF is a valid PC-NNF; tautology of DNF is coNP-complete |

Two consequences worth stating once. (i) A valid PC-NNF with no ⊥ leaf is satisfiable
(sat(F) = 1 trivially), so the substantive query really is CO after conditioning, as
fact 2 says. (ii) PC-NNF is closed under ∨ (free), under ∧ of co-unate operands
(same-polarity shared variables), under conditioning, forgetting and renaming, but not
under negation: ¬ swaps ∧/∨ and the polarity rule would then be required at former
∨-nodes. A "two-sided" variant that imposes the rule at both gate types can express
only unate functions (the lowest common ancestor of an x-occurrence and a ¬x-occurrence
would violate it), so VA cannot be bought that way.

---

## 2. Assessment of Q1–Q3

### 2.0 The five facts

1. **Expressibility: true.** A DNF whose terms are consistent is valid (each term is an
   ∧ of literals over distinct variables; ∨ is unconstrained). Only size matters.
2. **True, with a correction of emphasis.** ⊥-free ⇒ satisfiable (Theorem A). The
   non-trivial requirement is exactly ⟦F⟧ = ⟦φ⟧ with |F| = poly(|φ|).
3. **True, and strict.** DNNF ⊆ PC-NNF since disjoint children cannot conflict, so
   DNNF, d-DNNF and OBDD sizes upper-bound m. Strictness: the monotone 2-CNF of a
   bounded-degree expander graph is a linear-size PC-NNF (it is unate), but needs
   DNNF size 2^Ω(n) (Bova, Capelli, Mengel, Slivovsky, "Expander CNFs have exponential
   DNNF size", arXiv:1411.1995, 2014; and "Knowledge compilation meets communication
   complexity", IJCAI 2016) **[cited]**. Hence no PC-NNF → DNNF translation with
   polynomial blow-up exists.
4. **True.** Vertex covers of G = models of the monotone 2-CNF of G; #monotone-2-SAT is
   #P-complete (Valiant, SIAM J. Comput. 8, 1979) **[cited]**.
5. **True, but the naive reading is not.** A poly-size PC-NNF for each φ is *not* a
   certificate usable by a P/poly algorithm, because the compiled formula depends on φ
   and cannot be verified equivalent (EQ is coNP-hard). The correct argument uses a
   *universal* formula: let U_n(C, x) be the poly-size CNF saying "assignment x
   satisfies the size-n CNF encoded by variables C". If m(U_n) = poly(n), the compiled
   U_n is advice for length n: given ψ, condition on C := ψ and run CO. So the
   hypothesis implies SAT ∈ P/poly. The conditional is moot: Corollary C' in 2.1 shows
   m(U_n) is exponential unconditionally, so the hypothesis is simply false.

### 2.1 Q1a: unconditional lower bounds

The rectangle-cover technique does not transfer: an ∧-node's model set
{σ : F(σ) = G(σ) = 1} with F, G co-unate on a shared set S is not a combinatorial
rectangle, and the balanced-node argument that starts every DNNF lower bound has no
counterpart when the shared set is large. The technique that does transfer is monotone
circuit complexity, through the following collapse theorem.

**Theorem B (monotone collapse).** Let F be a valid PC-NNF computing a *monotone*
function f. Let F↑ be F with every negative literal leaf replaced by ⊤. Then F↑ is a
monotone {∧,∨}-circuit computing f, and its fan-in-2 size is at most |F|.

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

**Lower-bound tool.** Combining Theorem B with 1.3: for any f and any valid F ≡ f,
|F| ≥ mono(g) for every monotone g obtainable from f by conditioning some variables,
forgetting others, and renaming polarities. Call such g a *unate projection* of f.

**Theorem C (explicit relational families).** Each family below is one satisfiable,
poly-size CNF per n whose variables *include the edge indicators of the graph*, so
its model set is a relation (graph, witness), not the solution set of one graph.
(a) The CLIQUE and Tardos-type families have m(φ_n) ≥ 2^{n^{Ω(1)}} unconditionally.
(b) The perfect-matching family has m(φ_n) ≥ n^{Ω(log n)} from Razborov 1985, and
2^{n^{1/3−o(1)}} if the 2025 monotone matching bound (arXiv:2507.16105) holds up
**[cited via search, verify before quoting]**.

- **CLIQUE encoding.** Variables: e_uv for u < v ∈ [n] (edge indicators), s_u
  (vertex selected), q_u (its complement), z_{i,u} (slot i ∈ [k] picks u). Clauses:
  (q_u ∨ q_v ∨ e_uv); (s_u ∨ q_u), (¬s_u ∨ ¬q_u); (∨_u z_{i,u}) per slot;
  (¬z_{i,u} ∨ ¬z_{i,u'}); (¬z_{i,u} ∨ ¬z_{j,u}); (¬z_{i,u} ∨ s_u). Then
  ∃(s,q,z) φ_{n,k}(e,s,q,z) = CLIQUE_{n,k}(e), which is monotone in e. Razborov
  (1985) gives n^{Ω(log n)} for CLIQUE; Alon–Boppana (Combinatorica 7, 1987) give
  n^{Ω(√k)} for k ≤ (n/log n)^{2/3}, i.e. 2^{Ω((n/log n)^{1/3})} at the top of that
  range **[cited]**. Note the CNF has Θ(n²) variables, so the bound is exponential in a
  polynomial of the instance size, not in the number of variables.
- **Perfect matching encoding.** Variables e_ij (edge of K_{n,n}) and m_ij (edge used);
  clauses (¬m_ij ∨ e_ij), one-per-row and one-per-column exactly-one constraints on m.
  ∃m φ = PM_n(e); Razborov ("logical permanent", Mat. Zametki 37, 1985) gives
  n^{Ω(log n)} **[cited]**. Superpolynomial, and PM ∈ P.
- **Tseitin encodings of monotone functions with an exponential monotone/non-monotone
  gap.** Tardos (Combinatorica 8, 1988) gives a monotone function in P with monotone
  complexity exp(c·n^{1/6−o(1)}) **[cited; exponent confirmed from the abstract]**.
  For explicit functions not known to be in P, Andreev 1987 and Harnik–Raz (STOC
  2000) give 2^{Ω(n^{1/3}/log n)} and Cavalar–Kumar–Rossman 2020 give
  exp(n^{1/2−o(1)}) **[cited via search]**. Encoding a poly circuit for such an f by
  Tseitin variables g gives ∃g φ_C(x, g) = f(x).

**Corollary C' (the universal formula).** Let U_N(C, x) be the poly-size CNF of fact 5
with auxiliary Tseitin variables a. Conditioning on C := code(φ_{n,k}) and forgetting
a yields φ_{n,k} itself, so by 1.3, m(U_N) ≥ m(φ_{n,k}) = 2^{n^{Ω(1)}} for
N = |φ_{n,k}|. This is one explicit satisfiable CNF family with exponential minimum
size, with no assumption. It closes the P/poly route of fact 5 outright.

*What this says about the P vs NP framing.* The CLIQUE *relation* φ_{n,k} has no
polynomial PC-NNF, regardless of whether P = NP; neither do the relations of
*polynomial-time* problems (perfect matching, Tardos's function). So relational
PC-NNF size is decoupled from decision complexity in both directions, and this
project cannot decide P vs NP with PC-NNF as the language. For a fixed graph G the
question is open: φ_{n,k}|_{e:=G} is a conditioning of φ_{n,k}, so
m(φ_G) ≤ m(φ_{n,k}) and Theorem C gives no lower bound on it. What the project can do
is map where the language fails per instance and test candidate strengthenings (Q3)
against Theorem B.

*Limits of the tool.* For functions with no hard unate projection nothing is known.
Two named open cases: (1) the **fixed-graph clique formula** over vertex selectors
s_u: "at least k of s" ∧ (¬s_u ∨ ¬s_v) for every non-edge uv. It is non-monotone; its
unate projections are thresholds, independent-set 2-CNFs after renaming, or thresholds
over a fixed clique, all with small monotone circuits; for fixed k it is a DNF of size
O(n^k). This is the honest form of "does PC-NNF blow up per instance". (2) The family
f = ∧_{uv ∈ E(G)} (H_u ∨ H_v) with impure blocks H_u = (x_u ∧ y_u) ∨ (¬x_u ∧ z_u) and
G an expander, which matters for Q3. **[conjecture: m is exponential for both]**

### 2.2 Q1b: families with polynomial m

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
- **Clash-graph decomposition (Q1c):** if the clauses of φ|ρ split into components
  of the clash graph (clauses adjacent iff they contain complementary literals), the
  compiled block is an ∧ of independent compilations. A hierarchical version gives
  **[conjecture]** m(φ) ≤ |φ|·2^{O(w)} where w is a width measure of the graph on
  *impure* variables only; the experiments test this.

Random 3-SAT: no theorem either way. Bova et al. 2014 prove the DNNF bound for an
explicit expander family only; random bounded-degree graphs are expanders w.h.p., so
the extension to random CNFs is a routine consequence but is not stated in that
paper **[verified against the abstract]**. Either way it says nothing about PC-NNF,
because the expander 2-CNF itself is linear in PC-NNF. Almost every variable in a
random 3-CNF is impure, so the 2^{|I|} bound is useless, and the clash graph is
connected above a small clause/variable ratio. This is the central experimental
unknown. Structured 3-SAT: graph-colouring CNFs have the "positive exactly-one +
negative conflict graph" shape of Section 2.4. With edge indicators as variables the
projection ∃c φ(e, c) = "G(e) is k-colourable" is *anti-monotone* in e; renaming
e ↔ ¬e (free by 1.3) makes it monotone, equivalently monotone circuit complexity is
invariant under duality, so any monotone lower bound for non-k-colourability
transfers (I know of no classical one to cite). For a fixed graph the question is
open.

### 2.3 Q1c: the clash-graph compiler is sound

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
c2d/D4. Design question for the harness: size-optimal choice is a search problem;
start with greedy plus the D4 default heuristic for comparability.

### 2.4 Q2: maximal cliques, M(φ)

**Reformulation.** Let Ḡ_φ be the complement of the clique graph: vertices are literal
occurrences, edges join occurrences in the same clause and occurrences of
complementary literals. M(φ) is exactly the set of *maximal independent sets* of Ḡ_φ,
i.e. the CNF ∧_{uv∈E} (¬y_u ∨ ¬y_v) ∧ ∧_v (y_v ∨ ∨_{u∼v} y_u). At the variable level a
model is a consistent literal set ρ (the chosen literals) such that every clause is
either satisfied by ρ, with exactly one ρ-true occurrence chosen as witness, or
falsified by ρ (all three literals complemented in ρ). So M(φ) ⊋ {models of φ with
witnesses}; the extra models are partial assignments that *decide* every clause.

**Key observation.** A clause containing a literal whose complement has no occurrence
in φ cannot be falsified, so it must be witnessed. Hence for φ' = ∧_C (C ∨ w_C) with
fresh w_C, conditioning M(φ') on y_{w_C} = 0 for all C leaves exactly the
(model, witness) pairs of φ. Conditioning and forgetting are free (1.3), so:

**Theorem D.** m(M(φ')) ≥ m(∃_{other y} M(φ')|_{w=0}). Applied to φ = the CLIQUE
encoding of Theorem C (with e_uv pure positive, so its clause needs no dummy), the
projection onto the e-occurrence variables is CLIQUE_{n,k}: y_e = 1 makes e_uv the
witness and imposes nothing; y_e = 0 forces the witness q_u or q_v, i.e. not both
endpoints selected. So m(M(φ'_{n,k})) ≥ mono(CLIQUE_{n,k}) = 2^{n^{Ω(1)}}.
**[proof sketch above; Lean target]**

So the retained-incomplete-answers space is *not* easier in the worst case for the
relational encoding. This does not explain the previous constructor's blow-up unless
it was fed edge-variable encodings; for the clique graph of a fixed 3-CNF the bound
does not apply (the fixed-graph formula is a conditioning of the relational one).
Whether M(φ) and φ have the *same* growth on a given instance is open: neither
reduction between them is a PC-NNF operation (both need an ∧ with an impure operand).
This is experiment E6.

**The general pattern** "positive at-least-one / exactly-one / at-most-c constraints
plus a negative conflict graph" is answered by the same construction: the CLIQUE
encoding uses only at-least-one groups, exactly-one pairs and negative 2-clauses, and
it already has a hard unate projection. The pattern is hard as soon as it can encode
a selector of k items whose pairwise compatibility is controlled by pure variables.
By contrast, if the positive groups and the conflict graph are such that every unate
projection is "simple" (for instance a single at-most-c on a conflict-free set), the
compiler of 2.3 gives polynomial size; classifying the boundary is experiment E5.

### 2.5 Q3: extensions

**A general obstacle first.** Theorem B's proof only used that every gate is monotone
in its inputs and that ∧-nodes admit the merge argument. Therefore any extension whose
gates are monotone (∧, ∨, at-least-k, threshold, majority) and which keeps a merge
lemma at conjunctive gates inherits the CLIQUE lower bound unchanged. Only
non-monotone gates (XOR, exactly-k, at-most-k, negation) can escape it, and those are
exactly the gates that break the one-pass sat computation unless their operands come
from a sublanguage where *falsifiability* is also computable. This is the design
tension for all of Q3.

**Candidate 1: shared-block exemption.**
Sound condition (dominator rule): at an ∧-node N, let X_bad be the variables that
violate the base rule at N. N is accepted iff every x ∈ X_bad can be assigned a block
H(x) ≠ N in the sub-DAG of N such that (i) every path from N to a leaf `x` or `¬x`
passes through H(x), i.e. H(x) dominates all x-leaves from source N; and (ii) for
x ≠ x' with H(x) ≠ H(x'), x ∉ vars(H(x')). Under this rule the bottom-up pass is
unchanged and Theorem A still holds. *Proof sketch* **[sketch, gap noted, Lean target
L8]**. First, every exempt block lies under at least two children: x ∈ X_bad is
reachable from two different children and all its paths pass through H(x), so H(x) is
reachable from both. Hence no variable of an exempt block is private to one child;
every non-bad variable of H_j is shared and therefore single-polarity everywhere
under N. Now take genuine models σ_i ⊨ C_i, replace every maximal H_j-instance under N
by a positive atom h_j with value h_j := H_j(σ_i) in child i, and run the base merge on
the resulting C_i' (they contain h_j positive-only and no X_bad variable). For the
X_bad variables of H_j take the values from any σ_i with H_j(σ_i) = 1 (consistent
across instances because H_j is one block, across blocks by (ii)); for the shared
non-bad variables take the merge value, which keeps every C_i' and every H_j true by
monotonicity. If no child has H_j(σ_i) = 1 the atom is 0 everywhere and H_j's bad
variables are irrelevant. The gap the reviewer found in the earlier version (an
independent model τ_j of H_j clashing with σ_i on variables of H_j) is closed by the
"no private variables" observation, but the ordering above is the one to formalise.
The counterexample H = A∧B, F = H, G = (H∧⊥) ∨ (¬A∧D) is rejected because the `¬A`
leaf in G is not dominated by H. **[checked that base rule rejects it, that the naive
pass would be wrong, and, by the reviewer's fuzzing of 9000 accepted exempt DAGs,
that soundness, conditioning closure and the Theorem B collapse hold under the
rule]** The rule is preserved by conditioning
(conditioning removes leaves, so dominance and X_bad only shrink).
Checkability: one dominator-tree computation (Lengauer–Tarjan, near-linear) per
∧-node that has a non-empty X_bad, so O(|F|²) worst case and near-linear when few
nodes need exemptions; a single near-linear check for all nodes at once is open.
Succinctness: base PC-NNF simulates an exempted node by Shannon expansion on the
virtual atoms, cost 2^{(number of exempt blocks at the node)}; a polynomial simulation
would need a *monotone DNNF* over the virtual atoms, and monotone 2-CNFs of expanders
have no small DNNF. So the family ∧_{uv∈E(G)} (H_u ∨ H_v) of 2.1 is the natural
separating candidate. **[conjecture: exponential separation]** But by the obstacle
above, the exemption does not touch the CLIQUE bound; the collapse proof extends to
exempted nodes.

**Candidate 2: XOR / exactly-k / cardinality blocks over variable-disjoint children.**
sat(F ⊕ G) with disjoint variables = (sat F ∧ fals G) ∨ (fals F ∧ sat G), so the pass
needs *falsifiability* of the children, which is coNP-hard for general PC-NNF (DNF ⊆
PC-NNF). The block is sound only if its children come from a "two-sided" sublanguage
with both bits computable and closed under conditioning, e.g. decision-DNNF/OBDD
(fals(F∧G) = fals F ∨ fals G, fals(ite) = fals F ∨ fals G) or, recursively, other
XOR/cardinality blocks over such children. In addition the XOR block's variables must
be private with respect to every ancestor ∧ (an XOR is not unate in any variable, so
the merge lemma fails: (x⊕y) ∧ x ∧ y is unsatisfiable though each conjunct is).
With those restrictions the block is sound, one-pass, and conditioning-closed, but it
is **polynomially simulable in base PC-NNF**: with two-sided children the negation
¬F_i is available at the same size, and ⊕_{i≤k} F_i (or exactly-k, at-most-k) is the
parity/counter OBDD over virtual atoms with each ite(h_i, A, B) expanded as
(F_i ∧ A) ∨ (¬F_i ∧ B), size O(k·Σ|F_i|) (O(k²·Σ|F_i|) for counters). So it changes
constants, not asymptotics. The user's remark that the pass only needs *one* valid
answer is correct but does not help: the difficulty is falsifiability, not choice.

**Candidate 3 (own): bounded-context blocks.** **[conjecture, undefined]** The idea:
each node N carries a context set K(N) of ≤ c variables, its answer is a table
sat(N|κ) over the 2^c assignments κ to K(N), and the polarity rule at N is waived for
variables in K(N). What is *not* yet defined is how a parent consumes a child's table
when K(child) ⊄ K(parent). The strict rule K(child) ⊆ K(parent) is sound but makes
the root's context contain every context variable, so c bounds the total and Shannon
expansion on ≤ c variables simulates it in base PC-NNF at cost 2^c: no asymptotic
gain. The permissive rule, dropping a child's context variable when it is private to
that child within the parent, is where a separation might live, but its soundness
(an OR over the dropped variable's values per child) and the size of its base
simulation have not been worked out. Monotone gates only, so Theorem B would apply
to any sound version. Not recommended for implementation until defined.

**Candidate 4 (own): decision nodes on impure shared variables** are already
expressible as conditioning inside the ∨ of rule 4 in 2.3; no gain.

**Candidate 5 (own): negation of two-sided sub-blocks** (allow ¬H as a leaf when H is
decision-DNNF/OBDD). Sound and one-pass, but ¬H has an explicit decision-DNNF of the
same size, so no gain.

Net assessment: no proposed extension is known to escape Theorem B, and the only ones
that could (non-monotone gates) are simulable whenever they are sound. The honest
conclusion is that a language with (i) a context-free one-pass sat test and
(ii) closure under conditioning is, for monotone targets, no stronger than monotone
circuits **[conjecture, stated as a research direction]**; proving or refuting this
is the theoretical question that decides whether the whole approach can progress.

---

## 3. Experiment plan

### 3.1 Hypotheses

| # | Hypothesis | Status from theory |
|---|---|---|
| H1 | The previous blow-up came from the constructor, not the language. | Refuted for relational (edge-variable) encodings (Theorems C, D); open for every per-instance family, including the instances actually used. |
| H2 | Random 3-SAT at fixed ratio α has exponential m(φ). | Open; no technique. |
| H3 | Size is governed by the structure of *impure* variables: m(φ) ≤ ǀφǀ·2^{O(w)} for a width w of the clash structure. | Conjecture (2.2). |
| H4 | The Q1c compiler never exceeds decision-DNNF (D4/c2d) size on the same instance and same variable order. | Hypothesis only: after a clash-graph split the residuals and cache behaviour differ from D4's. |
| H5 | M(φ) and φ have the same size growth on the same instances. | Open (2.4). |
| H6 | The shared-block exemption gives exponential savings on ∧_E (H_u ∨ H_v). | Conjecture (2.5). |
| H7 | The projection bound is tight on tiny CLIQUE encodings: the exact minimum of φ_{n,k} equals the monotone circuit minimum of CLIQUE_{n,k}. (Theorem B itself is an equality only for monotone f.) | Open; testable at n ≤ 4. |

### 3.2 Instance generators (C# library, DIMACS out)

- Random 3-SAT: n ∈ {10,…,60}, α ∈ {1, 2, 3, 3.5, 4, 4.26, 5, 6}, 20 seeds each,
  satisfiable instances only (filter with a SAT solver).
- Parity/XOR chains: x₁⊕…⊕x_n = b with chain auxiliaries; also XOR of random
  3-variable sums (Tseitin formulas on random 3-regular graphs, satisfiable charge).
- Graph k-colouring: grids, random regular, random G(n,p); k = 3, 4; both fixed-graph
  CNFs and the edge-indicator variant of 2.2.
- Monotone 2-CNFs of expanders (random 3-regular and 5-regular graphs) and of
  bounded-treewidth graphs (paths, cycles, grids), as controls where m is known.
- CLIQUE and perfect-matching encodings of Theorem C, n ≤ 8 (sizes to compare with
  the bounds), and their w-dummied versions for M.
- Clique encodings of the above 3-CNFs: φ over x, and M(φ) over y (both the raw
  maximal-independent-set CNF and the w-dummied, conditioned variant).
- ∧_E (H_u ∨ H_v) with impure H_u, G expander or path (H6).

### 3.3 Exact minimum size for tiny instances

Only exact minima say anything about lower bounds, and only at n ≤ 6 or so. Method:
SAT-based exact synthesis (Knuth TAOCP 7.1.2 style; Kojevnikov–Kulikov–Yaroslavtsev
2009). Encode "there is a PC-NNF with s nodes computing truth table t": per node a
type (∧/∨/literal/constant), child selectors, per-node vars⁺/vars⁻ bitsets as SAT
variables propagated through children, the validity constraint at ∧-nodes, and the
truth-table constraint over all 2^n assignments. Solve with CaDiCaL for s = 1, 2, …
until satisfiable. Use fan-in 2 for the search and report both binary size and the
n-ary size (n-ary ≤ binary ≤ 3× n-ary, so growth rates are unaffected). Expected
reach: n ≤ 5, s ≤ ~25. Same encoding with the exemption rule of 2.5 (dominance is
expressible with per-node reachability bits) gives exact minima for H6 at tiny size.
For the monotone side of H7 compute exact monotone-circuit minima with the same tool
restricted to positive leaves.

### 3.4 Upper-bound compilers (C#)

1. Plain Shannon expansion with caching by residual CNF (baseline).
2. The Q1c clash-graph compiler (2.3), with variable heuristics: (a) most clash edges,
   (b) minimum-cut of the clash graph, (c) D4-like dynamic decomposition on the
   *clash* graph instead of the primal graph. Log the size after each rule application
   to attribute savings to splitting vs. pure-decision vs. caching.
3. The same compiler with the shared-block exemption enabled as an optional
   post-pass (merge nodes that become identical up to exemption).
Outputs: nodes, references, size, wall time, cache hit rate, and a validity re-check.

### 3.5 Baselines

- D4 (Lagniez–Marquis 2017; github.com/crillab/d4) and c2d (Darwiche) for
  decision-DNNF/d-DNNF sizes; both upper-bound m.
- CUDD OBDDs via the .NET `DecisionDiagrams` package or the Python `dd` package,
  with sifting; OBDD size upper-bounds m.
- Sizes are compared as PC-NNF sizes after parsing the compiler output into the
  common DAG format, so all counts use the same size definition.

### 3.6 Metrics, plots, decisions

- Per family: median and max size vs n on a log axis; fitted exponent of log(size)
  vs n and vs n·log n; ratio compiler/baseline; ratio to exact minimum where available.
- Random 3-SAT: heat map of fitted growth exponent over α × heuristic.
- Outcomes → hypotheses: H1 supported if the compiler is polynomial on the instances
  the constructor blew up on; refuted for those instances if all compilers and exact
  minima grow exponentially. H2: polynomial compiler sizes refute it; exponential
  sizes are consistent with it but prove nothing. H3: compare growth against the
  width measure; a family with bounded width and exponential size refutes it. H4:
  any instance where the Q1c compiler exceeds D4 size is a bug or a heuristic issue.
  H5: divergent exponents on the same instances refute it. H6: exact minima at tiny
  size that coincide with and without exemption weaken it; compiler growth on the
  expander family supports it. H7: exact minima below the monotone minimum would
  contradict Theorem B and indicate a bug. In addition, compile the fixed-graph
  clique formula of 2.1 (open case 1) for graph families of growing size; polynomial
  growth there would settle the per-instance question in the language's favour.

---

## 4. Ranked Q3 extensions

| Rank | Extension | One-pass sat | Conditioning | Base can simulate in poly? | Escapes Theorem B? |
|---|---|---|---|---|---|
| 1 | Shared-block exemption (dominator rule, 2.5) | yes, unchanged pass | yes | unknown; conjectured no | no |
| 2 | XOR / exactly-k / cardinality over disjoint two-sided children | yes, needs fals bits | yes | yes (parity/counter OBDD over virtual atoms) | not applicable (simulable) |
| 3 | Negation of two-sided sub-blocks | yes | yes | yes | not applicable |
| — | Bounded-context blocks | undefined (2.5) | undefined | strict version: yes at 2^c | no |
| — | XOR over general PC-NNF children | **no** (coNP-hard fals) | — | — | — |
| — | Rule at both ∧ and ∨ ("two-sided PC-NNF") | yes, both bits | yes | expresses only unate functions | — |

Recommendation: implement 1 (as a compiler post-pass and in the exact-synthesis
encoding). Do not build 2 or 3 beyond a correctness note; they cannot change
asymptotics. Bounded-context blocks stay on paper until the combination rule is
defined and proved sound.

---

## 5. Lemmas to machine-check in Lean 4

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
| L6 | Theorem B (monotone collapse) and the size bound after fan-in-2 conversion. | L1 | medium |
| L7 | Q1c compiler: output valid and equivalent to the input CNF (invariant lits(B(R)) ⊆ lits(R)). | L4 | medium; write the compiler in Lean directly |
| L8 | Shared-block exemption soundness (2.5) and, as a `decide`-checked example, that the naive atom shortcut accepts the A/¬A counterexample. | L2, L5 | large; the dominator formulation needs a DAG model |
| L9 | Theorem C/D projection identities: `∃ s q z, φ_{n,k}(e,s,q,z) ↔ CLIQUE_{n,k} e`, and the w-dummy / pure-literal lemma of 2.4. | — | medium |
| L10 | XOR-block soundness over two-sided children, and its polynomial simulation. | L3 | small; low priority (Section 4) |

Not machine-checkable here and to be cited: Razborov, Alon–Boppana, Tardos,
Harnik–Raz (monotone lower bounds), Bova–Capelli–Mengel–Slivovsky (DNNF lower bounds),
Valiant (#P-completeness). Use core Lean 4 plus Batteries; add Mathlib only if the
`Finset`/`Function.Monotone` API is needed (it likely is for L6).

---

## 6. Toolchain and dev-container changes

Roles: C# (.NET 8) for generators, compilers, exact synthesis driver, and metrics;
Lean 4 for Section 5; Python only for throwaway checks such as `scripts/check_tiny.py`.

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

