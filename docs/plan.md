# PC-NNF study: definitions, assessment of Q1–Q3, experiment plan

Status: planning document, 2026-09-19. Claims marked **[checked]** were verified on tiny
cases by `scripts/check_tiny.py`; claims marked **[cited]** rest on published results;
claims marked **[conjecture]** are unproven. Nothing in this document uses the banned
argument "it would solve a hard problem, so it must be false".

**Headline.** PC-NNF admits an *unconditional* exponential lower bound on explicit,
satisfiable, polynomial-size CNF families (Section 2, Theorem C), obtained by a new
reduction to monotone circuit complexity (Theorem B) rather than by rectangle covers.
The same reduction applies to the maximal-clique formulation M(φ) of Q2 (Theorem D)
and to any Q3 extension whose gates are monotone in their inputs. So the previous
blow-up is, for some instance families, a property of the language and not of the
constructor; whether it is also a property of the language on *random* 3-SAT is the
main open experimental question.

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
   hypothesis implies SAT ∈ P/poly. This is stated only to fix the formulation; it is
   not used anywhere below, because Section 2.1 gives unconditional bounds.

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

**Theorem C (explicit exponential families).** Each of the following satisfiable,
poly-size CNF families has m(φ_n) ≥ 2^{n^{Ω(1)}} unconditionally.

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
  complexity 2^{Ω((n/log n)^{1/3})} (Harnik–Raz, STOC 2000, and later Pitassi–Robere,
  STOC 2017, and Cavalar–Kumar–Rossman 2020 improve exponents for other explicit
  functions; exact statements to be checked before quoting) **[cited, exponents to
  verify]**. Encoding a poly circuit for such an f by Tseitin variables g gives
  ∃g φ_C(x, g) = f(x).

*What this says about the P vs NP framing.* The answer set of a satisfiable CLIQUE
instance family has no polynomial PC-NNF, regardless of whether P = NP. The answer set
of a *polynomial-time* problem (perfect matching, Tardos's function) also has none. So
PC-NNF size is decoupled from decision complexity in both directions, and this project
cannot decide P vs NP with PC-NNF as the language; what it can do is map exactly where
the language fails and test candidate strengthenings (Q3) against Theorem B.

*Limits of the tool.* For functions with no hard unate projection nothing is known. The
open case that matters for Q3 is f = ∧_{uv ∈ E(G)} (H_u ∨ H_v) with impure blocks
H_u = (x_u ∧ y_u) ∨ (¬x_u ∧ z_u) and G an expander: every unate projection has a small
monotone circuit, and no other technique is available. **[conjecture: m is
exponential for this family]**

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

Random 3-SAT: no theorem either way. DNNF lower bounds for random k-CNF (they are
expanders w.h.p., Bova et al. 2014) say nothing about PC-NNF because the expander
2-CNF itself is linear in PC-NNF. Almost every variable in a random 3-CNF is impure,
so the 2^{|I|} bound is useless, and the clash graph is connected above a small
clause/variable ratio. This is the central experimental unknown. Structured 3-SAT:
graph-colouring CNFs have the "positive exactly-one + negative conflict graph" shape
of Section 2.3 and inherit its lower bound when edge indicators are variables;
for a fixed graph the question is open.

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

So the retained-incomplete-answers space is *not* easier in the worst case, and the
previous constructor, which enumerated exactly this space, had to blow up on such
inputs. Whether M(φ) and φ have the *same* growth on a given instance is open: neither
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
unchanged and Theorem A still holds. *Proof sketch.* Replace every maximal H_j-instance
under N by a fresh positive atom h_j; each child becomes C_i' with h_j positive-only
and no X_bad variables, so the base merge lemma applies to ∧ C_i'. If sat(H_j) = 1 pick
a model τ_j of H_j and set the X_bad variables of H_j from τ_j (consistent across
instances because H_j is one block, and across blocks by (ii)); non-bad variables of
H_j that are shared across children are single-polarity everywhere under N, so
raising them to the merge value keeps H_j true; if sat(H_j) = 0 the atom is ⊥ and
τ_j is not needed. The counterexample H = A∧B, F = H, G = (H∧⊥) ∨ (¬A∧D) is rejected
because the `¬A` leaf in G is not dominated by H. **[checked that base rule rejects it
and that the naive pass would be wrong]** The rule is preserved by conditioning
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

**Candidate 3 (own): bounded-context blocks.** Let each node carry a designated set of
≤ c context variables and compute sat as a table over their 2^c assignments; the
polarity rule is waived for context variables. Sound, one-pass with boundedly
context-dependent answers, conditioning-closed. Base simulation: Shannon-expand the
whole DAG on the union of all context variables, which can be exponential even for
c = 1, so a separation is possible. **[conjecture, untested]** Monotone gates only, so
Theorem B still applies to it; it can only help on non-unate-hard functions.

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
| H1 | The previous blow-up came from the constructor, not the language. | Refuted *for some families* (Theorems C, D). Open for the actual instances used. |
| H2 | Random 3-SAT at fixed ratio α has exponential m(φ). | Open; no technique. |
| H3 | Size is governed by the structure of *impure* variables: m(φ) ≤ ǀφǀ·2^{O(w)} for a width w of the clash structure. | Conjecture (2.2). |
| H4 | The Q1c compiler never exceeds decision-DNNF (D4/c2d) size on the same instance and same variable order. | Provable by construction; check the implementation. |
| H5 | M(φ) and φ have the same size growth on the same instances. | Open (2.4). |
| H6 | The shared-block exemption gives exponential savings on ∧_E (H_u ∨ H_v). | Conjecture (2.5). |
| H7 | Theorem B is tight: on tiny CLIQUE encodings the exact minimum equals the monotone circuit minimum of the projection. | Open; testable at n ≤ 4. |

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
  contradict Theorem B and indicate a bug.

---

## 4. Ranked Q3 extensions

| Rank | Extension | One-pass sat | Conditioning | Base can simulate in poly? | Escapes Theorem B? |
|---|---|---|---|---|---|
| 1 | Shared-block exemption (dominator rule, 2.5) | yes, unchanged pass | yes | unknown; conjectured no | no |
| 2 | Bounded-context blocks (c context variables per node) | yes, 2^c-entry answers | yes | unknown; conjectured no for growing total context | no |
| 3 | XOR / exactly-k / cardinality over disjoint two-sided children | yes, needs fals bits | yes | yes (parity/counter OBDD over virtual atoms) | not applicable (simulable) |
| 4 | Negation of two-sided sub-blocks | yes | yes | yes | not applicable |
| — | XOR over general PC-NNF children | **no** (coNP-hard fals) | — | — | — |
| — | Rule at both ∧ and ∨ ("two-sided PC-NNF") | yes, both bits | yes | expresses only unate functions | — |

Recommendation: implement 1 (as a compiler post-pass and in the exact-synthesis
encoding) and 2 (exact synthesis only, c = 1, 2). Do not build 3 or 4 beyond a
correctness note; they cannot change asymptotics.

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

