# Testing the language on small cases: evaluation of two designs and a recommended strategy

Status: evaluation, 2026-11-09. Companion to `docs/plan.md` (sections 2, 6.2, 8), which is
not modified here; section 7 below proposes edits to it. Tags as in plan.md: **[checked]**
names the script, **[cited]** names the source, **[conjecture]** is unproven, **[estimate]**
is an extrapolation from measurements and should be re-measured, not quoted.

The two designs under evaluation:

- **Design A (the dictionary).** A persistent table keyed by truth table, grown bottom-up
  from literals and constants by ∧ / ∨ of existing entries, storing for each function the
  smallest circuit found, with dominance pruning and, later, symmetry reduction. Proposed by
  the project owner; the goal stated for it is "test whether every small logic circuit can be
  expressed by a small PC-NNF circuit".
- **Design B (SAT exact synthesis).** Per-target SAT encoding of "a valid PC-NNF with s gates
  computes f", solved for s = 1, 2, … with CaDiCaL, with the accompanying Core library, CLI,
  proof logging and verification. Proposed by the brief a previous agent wrote for plan 6.2.

Short verdict: they answer different halves of one question and the harness needs both. A
computes exact minimum **formula** (tree) size for **every** function at n ≤ 4 in seconds;
B computes exact minimum **DAG** size for **one** function at a time and is the only route to
m(f) as plan 2.1 defines it. Neither alone covers plan 6.2, and the owner's question is not
in plan 6.2 at all, which is why the brief dropped it (section 3.3).

---

## 1. What the small-case test can and cannot show

Two quantities, kept distinct throughout:

- **m(f)**: minimum plan-2.1 size over valid PC-NNF **DAGs** computing f (plan 1.1). Needs a
  DAG search (SAT or DAG enumeration).
- **m_tree(f)**: the same minimum over valid PC-NNF **formulas** (trees whose literal leaves
  may be shared). m(f) ≤ m_tree(f). A function-indexed dynamic programme computes m_tree
  exactly and cannot compute m (2.2, item 3).

Both are reported in fan-in-2 gate count k, from which the 2.1 size follows: for a tree with
shared literal leaves, size = 3k + |vars⁺| + |vars⁻| (k gate nodes, 2k references, one leaf per
literal used); for a DAG, nodes + references read off the circuit. Every number in this
document and in the harness output names its measure.

What tiny n shows. Every function on n variables has an OBDD of O(2ⁿ/n) nodes and hence a
PC-NNF of that order (plan 2.5, 3.5), so at n ≤ 5 *every* function has a small PC-NNF and the
whole-space scan can only quantify constants: "how many extra gates does the polarity rule
cost, at worst, at n = 4?" Plan 6.2 already states that tiny minima cannot distinguish
polynomial from exponential growth. The scan still earns its place for three reasons: it is
the cheapest complete ground truth available for differential testing of Core, the compiler
of 3.6 and the SAT tool; it gives the clique table of 6.2 at n = 4 as a by-product; and it
names the functions on which the rule costs most, which is the right place to look for
families to carry into E2 (section 5.1).

The owner's refinement "3-SAT is not needed" is correct: a Tseitin encoding of a circuit adds
auxiliaries, and forgetting auxiliaries is free in PC-NNF (plan 2.3, remark), so the object
to measure is the function over the circuit's own inputs.

---

## 2. Design A: the dictionary

### 2.1 What was measured

`scripts/spikes/enum_tree_minima.c` (and the slower `.py` twin, used to cross-check n = 3)
implements the dictionary as a size-stratified dynamic programme (2.2) and computes, for every
function on n ≤ 4 variables, the minimum fan-in-2 gate count of (i) a valid PC-NNF tree keyed
on (truth table, vars⁺, vars⁻) with Pareto dominance, (ii) the same keyed on truth table only,
and (iii) an unrestricted NNF tree. **[checked]** Build and run:

    gcc -O2 -o /tmp/enum scripts/spikes/enum_tree_minima.c && /tmp/enum 4

Results at n = 4, all 65,536 functions, 2.9 s per table in C on one core:

| quantity | value |
|---|---|
| entries added per gate count 0…17 (PC-NNF, Pareto) | 10, 48, 256, 940, 1664, 4960, 7232, 9992, 11824, 12080, 6880, 5648, 2128, 1376, 192, 210, 64, 32 |
| total Pareto entries | 65,536 (one per function; no frontier has two entries) |
| minima changed by keying on truth table only | 0 |
| max k over all functions: NNF tree / PC-NNF tree | 15 / 17 |
| k_pc − k_nnf = 0 / 1 / 2 (functions) | 51,792 / 12,800 / 944 |
| k_pc − k_nnf ≥ 3 | none |

At n = 3 the two trees coincide on all 256 functions (max k = 9). Gate counts for the
fixed-graph clique formulas φ_{G,k} on 4 vertices, tree minima, PC-NNF (NNF in brackets):

| G (edges) | k=0 | k=1 | k=2 | k=3 | k=4 |
|---|---|---|---|---|---|
| ∅ | 7 (7) | 11 (11) | ⊥ | ⊥ | ⊥ |
| 01 | 5 (5) | 9 (9) | 3 (3) | ⊥ | ⊥ |
| 01,02 | 5 (5) | 9 (9) | 5 (5) | ⊥ | ⊥ |
| 01,02,03 (star) | 4 (4) | 8 (8) | 8 (8) | ⊥ | ⊥ |
| 01,02,12 (triangle) | 3 (3) | 7 (7) | 5 (5) | 3 (3) | ⊥ |
| 03,12 (matching) | 3 (3) | 7 (7) | 7 (7) | ⊥ | ⊥ |
| 01,03,12 (path) | 4 (4) | 8 (8) | **9 (8)** | ⊥ | ⊥ |
| 01,02,03,12 | 2 (2) | 6 (6) | **9 (8)** | 3 (3) | ⊥ |
| 02,03,12,13 (4-cycle) | 3 (3) | **9 (7)** | 7 (7) | ⊥ | ⊥ |
| 01,02,03,12,13 | 1 (1) | 5 (5) | 7 (7) | 5 (5) | ⊥ |
| K₄ | ⊤ | 3 (3) | 7 (7) | 7 (7) | 3 (3) |

These are tree minima and therefore upper bounds on m(φ_{G,k}); the DAG minima come from
Design B. The 4-cycle at k = 1 is the smallest instance where the polarity rule costs two
gates: (s₀∨s₁∨s₂∨s₃) ∧ (¬s₀∨¬s₁) ∧ (¬s₂∨¬s₃) is 7 gates and invalid; the best valid tree has 9.

NP equivalence classes (input permutation and input complementation, no output negation,
the symmetry group that preserves m by plan 2.3), by Burnside's lemma **[checked]**
(`enum_tree_minima.py`, `burnside_np_classes`): n = 3: 22; n = 4: 402; n = 5: 1,228,158.
For comparison the NPN counts are 222 and 616,126 (OEIS A000370) **[cited]**.

### 2.2 Corrections to the design as described

1. **Growth order.** "Pick a wire added last iteration and combine it with any other wire"
   does not produce entries in order of size, so a stored entry can later be undercut and
   everything built on it is then stale. The standard fix is stratification by gate count:
   level s is built from all pairs (level a, level s−1−a) with a ≤ b, and the first time a key
   appears it is its minimum. Levels do not grow monotonically and an empty level does not end
   the run: at n = 3 nothing needs exactly 6 or 8 gates while 16 functions need 7 and two need
   9 (the 7-gate minima have two 3-gate operands). Stop when every truth table is reached
   (or at a size cap, reporting the unreached functions as "> cap").
2. **Dominance, and the "clean but larger component" question.** The design keeps, per
   function, circuits that are larger but use fewer literal polarities, on the expectation
   that a valid ∧ higher up may need the cleaner operand. Section 2.3 proves this never
   happens: every size-minimal valid PC-NNF for f, tree or DAG, uses exactly the essential
   polarities of f, and every valid circuit for f uses at least those. So the Pareto
   frontier of every function is a single entry, the dictionary can key on the truth table
   alone, and the validity test for ∧(g, h) can use polarity sets computed from the truth
   tables of g and h rather than stored ones. Measured: at n ≤ 4 no frontier ever has two
   entries, keying on the truth table alone changes no minimum, and the stored minimal tree
   has exactly the essential polarities for all 65,536 functions (table above). This also
   removes the reason for the non-size-ordered growth rule of item 1.
3. **Trees, not DAGs.** A function-indexed table composes operands by their functions, so
   it counts a shared sub-circuit once per use. It computes m_tree, not m. This cannot be
   patched by storing "which wires it uses": two operands that share an internal wire are
   still charged twice. Knuth's footprint method (TAOCP 4A §7.1.2) **[cited]** recovers exact
   DAG cost for all 4-variable functions over the full binary basis by tracking, per
   function, the set of possible first gates of optimal chains; it is a substantial extra
   mechanism and the SAT route gives the same DAG minima per target with far less code. The
   recommendation is: the dictionary reports m_tree and is labelled as such.
4. **Measure.** Store k; derive 3k + |P| + |N|. Do not store the 2.1 size directly, since
   the leaf term depends on (P, N), which is already in the key.
5. **Constants.** Keep ⊤ and ⊥ at level 0 with empty polarity sets. They are needed only to
   represent ⊥ itself (x ∧ ¬x is invalid) and ⊤ with empty sets; no minimal tree of a
   non-constant function uses a constant (⊤ in ∧ and ⊥ in ∨ are droppable, the other two
   collapse the gate), so they add no entries beyond level 0.
6. **Symmetry reduction.** Not needed at n ≤ 4: the full table is 65,536 entries and 3 s.
   At n = 5 it does not rescue a full table (2.4). If a class-reduced table is built anyway,
   the standard scheme is Knuth's: store one canonical representative per class, and when
   combining two entries fix the left operand canonical and range the right operand over
   all 2ⁿ·n! group images; applying a group element to a whole formula shows this covers
   every pair. That answers the "(a ∧ b) is canonical for (¬b ∧ c), but the ∨ needs both"
   concern: the non-canonical operand is produced on the fly as an image, never stored. The
   canonical form must be of the triple (tt, P, N) under the group, not of tt alone (two
   entries with the same canonical tt can have incomparable (P, N)); canonise tt first and
   break ties among the automorphisms of tt by the image of (P, N). For polarity flips alone
   brute force over 2ⁿ masks, each a sequence of ≤ n block swaps on a 2ⁿ-bit word, is a few
   hundred word operations at n = 6 and needs no sub-quadratic algorithm; the coset
   structure (the stabiliser of a table under XOR-translation is a linear subspace, so its
   minimisers form a coset) is what makes faster methods possible, but at this scale it is
   not worth implementing.

### 2.3 Lemma: minimal circuits use exactly the essential polarities

Write P_ess(f) = {x : f is not non-increasing in x} and N_ess(f) = {x : f is not
non-decreasing in x} (so x ∈ P_ess ∩ N_ess iff f is non-unate in x). By the unateness fact
of plan 2.2, every NNF circuit F computing f has vars⁺(F) ⊇ P_ess(f) and vars⁻(F) ⊇ N_ess(f).

**Lemma E (per-variable closure).** Let F be a valid PC-NNF computing f and let f be
non-decreasing in x. Then F[¬x := ⊤], obtained by replacing every ¬x leaf by ⊤, is valid, no
larger, and computes f. Dually, if f is non-increasing in x then F[x := ⊤] computes f.

*Proof.* Validity and size: a leaf is replaced by a leaf and vars± only shrink. Write F° for
F[¬x := ⊤]. F° ≥ F pointwise, since NNF is monotone in its leaves. For the converse show by
induction on the nodes of the DAG: N°(σ) = 1 ⇒ ∃ b ≤ σ(x) with N(σ[x := b]) = 1. Leaves: a
¬x leaf gives b = 0; others are unchanged. ∨: take the child's b. Valid ∧-node with children
C_i and values b_i: if x occurs in at most one child take its b_i (the others ignore x); if x
occurs in two or more children then by validity it has one polarity in all of them. If
positive, every C_i is non-decreasing in x and b = max b_i ≤ σ(x) satisfies all of them; if
negative, every C_i is non-increasing in x and b = min b_i does. At the root, F°(σ) = 1 gives
F(σ[x := b]) = 1 for some b ≤ σ(x), hence f(σ) = 1 because f is non-decreasing in x. So
F° ≤ f ≤ F°. The dual statement is the same proof with the order reversed. ∎
This is the argument of plan 3.2 (Theorem B′) run for one variable instead of all of them.
**[checked]** (`scripts/check_essential.py`, check P1: random valid DAGs with shared nodes,
n = 4, both directions.)

**Corollary E1 (essential polarities).** Every size-minimal valid PC-NNF F for a
non-constant f, in gate count or in plan-2.1 size, tree or DAG, has vars⁺(F) = P_ess(f) and
vars⁻(F) = N_ess(f).

*Proof.* If x ∈ vars⁻(F) \ N_ess(f) then f is non-decreasing in x and Lemma E applies; the
new ⊤ leaf sits under some gate (F is not a single leaf), and propagating it removes that
gate (⊤ in ∧ is dropped, ⊤ in ∨ collapses the gate), so the result is a valid circuit for f
with fewer gates and smaller 2.1 size, contradicting minimality. Dually for vars⁺. ∎
**[checked]** (`check_essential.py`, check P2, on random DAGs; `enum_tree_minima.c`,
exhaustively for minimal trees at n = 3, 4.)

**Corollary E2 (the dictionary).** For formulas, a dynamic programme keyed on the truth table
alone, storing one minimal tree per function, is exact. Induction on k: a minimal tree
op(A, B) for f has A computing g and B computing h; replace A and B by the stored minimal
trees G and H. By E1 the polarity sets of G and H are the essential ones, which are subsets
of those of A and B, so op(G, H) is still valid, is no larger, and computes f. The stored
polarity sets are determined by the truth table and need not be stored.

**Corollary E3 (the SAT encoding).** The constraints vars⁺(root) = P_ess(f) and
vars⁻(root) = N_ess(f) lose no minimal circuit, so they are safe symmetry breaking, and the
leaf set can be restricted to the |P_ess| + |N_ess| essential literals. For monotone f this
is Theorem B's "positive leaves only" and the lower-bound start of 3.2 item 3 is exact in L.

What E1 does *not* say. It constrains the root. An internal gate of a minimal DAG may use a
polarity that is redundant for its own function, because the leaf also serves another parent
through a shared node and cannot be replaced in isolation. So two gates with the same truth
table and different polarity sets may coexist in a minimal DAG, and the exact-synthesis
constraint "no two gates compute the same function" stays unsafe (3.2 item 2). Whether such a
DAG is ever minimal is open **[conjecture: no]**; the harness should record any minimal
circuit from Exact with two gates of equal truth table.

On the owner's framing. Every function can be computed with polarity-pure components by
Shannon expansion on its non-unate variables (plan 3.5, 2^{|I|}·|φ|), which suggests a
trade-off between cleaner components and size. Lemma E says the trade-off does not exist at
the level of whole circuits: the smallest circuit is already as clean as any circuit for
that function can be. Where polarity does cost size is at an ∧ whose operands are non-unate
in a shared variable; the remedy there is a different decomposition of f (which the search
explores), not a cleaner circuit for the same operand function.

### 2.4 Reach

| n | functions | NP classes | full m_tree table | notes |
|---|---|---|---|---|
| 3 | 256 | 22 | instant | all PC-NNF = NNF tree minima **[checked]** |
| 4 | 65,536 | 402 | 3 s (C), seconds in C# | complete; max 17 gates **[checked]** |
| 5 | 2³² ≈ 4.3·10⁹ | 1,228,158 | not feasible on this machine | pair loop ≈ (entries)²/2 ≥ 10¹⁸ even class-reduced (≈ (1.2·10⁶)²/2 · 3840 pairs); a size-capped shell of ≤ 7 gates fits in 7 GB **[estimate]** |
| 6 | 2⁶⁴ | — | not feasible | shell of ≤ 6 gates **[estimate]**; a 64-bit key is right, but the table covers a vanishing fraction of functions |

Knuth reports the 5-variable table (cost ≤ 12 over the full binary basis for all 616,126 NPN
classes) as a long computation needing methods beyond the function-indexed programme that
suffices for n = 4 **[cited: TAOCP 4A §7.1.2; verify the wording before quoting]**. The
conclusion for this project: the dictionary is the complete tool at n ≤ 4 and an upper-bound
tool (shells) at n = 5, 6; it is not the tool for m(φ_{G,k}) at n = 5.

---

## 3. Design B: the SAT exact-synthesis brief

### 3.1 What is right

The brief is a faithful design brief for plan 6.2 and its technical content is sound:
the DAG-vs-tree pitfall is real; the (tt, vars⁺, vars⁻) pitfall is real for internal gates of
a DAG but, by Corollary E1 (2.3), void for whole circuits and for formulas; restricting the search to the
n input variables is justified by plan 2.3; NP rather than NPN classes is right because
PC-NNF is not closed under negation; fan-in-2 search with n-ary size derived afterwards is
right, and the derivation is safe because a binary ∧-tree is valid iff the flattened n-ary
∧ is (vars± of the intermediate nodes are unions of the children's); DRAT proofs for the
UNSAT half are the right trust mechanism; the Python oracles as differential tests of Core
are right.

### 3.2 What is missing or needs correction

1. **Expected reach.** Plan 6.2 says "n ≤ 5, s ≤ ~25" without a measure. If s is gates, 25
   is far beyond what SAT exact synthesis proves UNSAT: the literature works at roughly 10 to
   12 gates for 5-input functions over the full binary basis, and the UNSAT step at s = m−1
   dominates (Kojevnikov, Kulikov, Yaroslavtsev, SAT 2009; Haaswijk, Soeken, Mishchenko,
   De Micheli, IEEE TCAD 2020) **[cited]**. If s is 2.1 size, 25 is about 6 gates, which the
   n = 4 table already exceeds (11 gates for the empty graph at k = 1). The PC-NNF search is
   easier than the general one (two gate types instead of sixteen, polarity constraints
   prune), by an unmeasured factor. Expect: all 402 classes at n = 4 in minutes to hours;
   at n = 5 the clique targets will need 12 to 20 gates **[estimate from the n = 4 table]**,
   so some will end as brackets [s_unsat + 1, m_tree]. The plan should say so.
2. **Symmetry breaking that is unsafe here.** The standard exact-synthesis constraint "no two
   gates compute the same function" assumes a duplicate gate can be removed. In a valid
   PC-NNF two gates with the same truth table but incomparable (vars⁺, vars⁻) may both be
   needed (the DAG form of pitfall (a)), so that constraint must be weakened to "no two
   gates with the same (tt, vars⁺, vars⁻)" or dropped. Safe in the {∧, ∨} basis with literal
   leaves: colexicographic gate ordering, every gate used, no gate equal to a literal or a
   constant (the leaf has smaller polarity sets), and no operand reuse (x∧(x∧y), x∨(x∧y),
   x∧(x∨y), x∨(x∨y) all simplify without enlarging polarity sets).
3. **Lower bound to start the loop, and the leaf set.** By Corollary E1 (2.3) a minimal
   circuit's leaves are exactly the L = |P_ess(f)| + |N_ess(f)| essential literals, so the
   encoding can offer only those literals as leaves, and a fan-in-2 circuit joining L leaves
   has at least L − 1 gates. Start at that s instead of 1.
4. **Upper bound to stop the loop.** Feed m_tree(f) from the dictionary (or the 3.5
   construction, or the compiler) as the known-feasible size; the SAT loop then only has to
   run for s < m_tree, and a timeout yields a bracket, as the brief asks.
5. **The whole-space scan is absent.** The brief's targets are those of plan 6.2. The
   owner's question ("every small circuit has a small PC-NNF?") is a scan over all functions
   at n = 4 against a baseline, which 6.2 does not list. Add it (section 7).
6. **Baseline for "small logic circuit".** The natural baseline is C(f), the minimum general
   circuit size (any binary gate, DAG), which is ≤ 7 for every 4-variable function (Knuth,
   TAOCP 4A §7.1.2) **[cited]**. The same SAT tool in a "general circuit" mode computes it
   for the 402 classes trivially, so the harness can report m(f), m_tree(f) and C(f) side by
   side. The spike used NNF tree size as baseline because that is what a tree dictionary
   can compute; the ratio against C(f) will be larger and is the one the owner's question
   asks about.

### 3.3 Why the brief dropped the owner's hints

The brief was told that plan.md is authoritative and designed for 6.2. The dictionary
approach is, in exact-synthesis terms, "enumeration of all minimal circuits by size", which
the brief does list as an alternative method and asks the designer to assess; it then
subordinates it to per-target SAT because 6.2's targets are specific functions and its
quantity is the DAG minimum. Nothing in the brief contradicts the hints; it serves a
document that does not contain the experiment the hints are for. The fix is in the plan,
not in the brief.

---

## 4. Recommended architecture

Four components, in the layout of plan section 8, with the dictionary added as its own
project:

1. **PcNnf.Core** (as in the brief): DAG, validity, evaluation, bottom-up pass, Lemma W
   witness, conditioning, forgetting, essential polarities of a truth table, text
   interchange format matching the oracles' node format. Differentially tested against
   `check_tiny.py` and `check_witness.py` on random formulas.
2. **PcNnf.Enum** (Design A, corrected per 2.2): size-stratified dictionary keyed on the
   truth table, with polarity sets computed from the table (Corollary E2, 2.3) and an
   assertion that every stored minimal tree has exactly those sets; three rule modes:
   PC-NNF, unrestricted NNF, and monotone
   (positive leaves only, for H8 and for Theorem B sanity checks). Complete tables at n ≤ 4
   written to `data/` as flat arrays (tt → k, P, N, and a back-pointer pair so the tree can
   be reconstructed and re-verified by Core); size-capped shells at n = 5, 6. Emits the
   clique table (tree measure) for all graphs on ≤ 4 vertices and all k, and a "gap report":
   the distribution of k_pc − k_nnf and the list of maximum-gap functions by NP class.
3. **PcNnf.Exact** (Design B, corrected per 3.2): DIMACS out, CaDiCaL as a child process,
   DRAT proof file per UNSAT step, drat-trim on a sample. Modes: PC-NNF, monotone, general
   circuit (for C(f)). Inputs: a truth table, a start bound from Core's essential polarities,
   a stop bound from Enum or from a construction; output: a circuit (re-verified by Core and
   by the Python oracle through the interchange format) or a bracket. Incremental solving is
   not needed: the loop is at most ~20 independent solves per target and the last UNSAT
   dominates.
4. **PcNnf.Bench / CLI**: one command per table. `enum --n 4 --rule pc|nnf|mono`;
   `exact --tt <hex> --n <n> [--upper k] [--rule …]`; `clique-table --n 4|5` (joins Enum's
   tree minima, the 3.5 construction size, the compiler of 3.6 once it exists, and Exact's
   DAG minima or brackets, one row per (G, k) with every number labelled by measure);
   `scan --n 4` (all 402 NP classes: C(f), m_tree(f), m(f), gap statistics).

Cross-checks that each run performs and records:
- for every function at n = 4: m(f) ≤ m_tree(f), and m(f) ≥ |vars⁺_ess| + |vars⁻_ess| − 1;
- every circuit from Exact passes Core's validity check and equals the target table;
- every tree from Enum, reconstructed through back-pointers, passes the same two checks;
- for monotone f: Exact in PC-NNF mode and in monotone mode agree up to the fan-in
  conversion of plan 3.2 (Theorem B, equality for monotone f); a strict violation is a bug;
- the spike's n = 4 table (section 2.1) is the regression fixture for Enum.

What each component proves. Enum: exact m_tree at n ≤ 4, upper bounds at n = 5, 6. Exact:
exact m where the loop closes, brackets otherwise, proof-logged. The clique table of 6.2 at
n = 4 is complete and exact (DAG) once `scan --n 4` has run, because every target is one of
the 402 classes; at n = 5 it is exact where SAT closes and bracketed elsewhere.

---

## 5. What to do with the results

### 5.1 The gap functions as family candidates

The n = 4 scan gives 944 functions (a handful of NP classes) where the polarity rule costs
two extra gates in the tree measure and none where it costs three. The next step is not a
larger scan but to look at those classes: if they are instances of the "positive constraint
plus negative conflict graph" pattern of plan 4.2 (the 4-cycle at k = 1 is), that is
evidence for where to point E2; if they are something else, that is a new candidate family.
The owner's question "does every small circuit have a small PC-NNF" is answered at n = 4
by the gap histogram in the tree measure; the DAG measure from `scan --n 4` completes it.

### 5.2 Calibrating E2

Plan 6.2's purpose for E1 is to measure how far the compiler of 3.6 lands above the minimum.
The clique table at n = 4 is available now in the tree measure (section 2.1); when the
compiler exists its output on the same 11 graphs × 5 values of k is compared row by row.

---

## 6. Open decisions, with recommendations

1. **Build Enum as its own project or fold it into Exact as "the upper-bound provider"?**
   Recommendation: own project. It has an independent correctness argument (size-stratified
   dynamic programme over Pareto entries) and its own regression fixture; the coupling to
   Exact is one number per target.
2. **Baseline for the scan: C(f) by SAT, NNF tree by Enum, or both?** Recommendation: both;
   C(f) is the baseline the question asks about, the NNF tree is free.
3. **Attempt a class-reduced full table at n = 5?** Recommendation: no. Size-capped shells
   only; the clique targets at n = 5 go through Exact.
4. **Which standard symmetry breaks to enable in Exact?** Recommendation: colex ordering,
   all gates used, no literal/constant gates, no operand reuse; weaken "distinct functions"
   to "distinct (tt, vars⁺, vars⁻)" (3.2 item 2). Fix the root's polarity sets to the
   essential ones and offer only essential literals as leaves: safe by Corollary E3 (2.3),
   on by default.
5. **Where to record measures.** Recommendation: every results row carries three columns per
   quantity, gates / 2.1 size / n-ary size, and a status column exact | bracket | upper.

---

## 7. Proposed edits to docs/plan.md (not applied)

- 6.2, method paragraph: replace "Expected reach: n ≤ 5, s ≤ ~25" by "Expected reach: all
  402 NP classes at n = 4 exactly; at n = 5 exact where the UNSAT step closes within the
  timeout (roughly 10 to 12 gates in the literature for general gates, more for PC-NNF by an
  unmeasured factor), otherwise a bracket [s + 1, m_tree]."
- 6.2, targets: add as the first target "All 402 NP classes of 4-variable functions: C(f),
  m_tree(f), m(f); gap distribution; maximum-gap classes listed. Every φ_{G,k} on 4 vertices
  is one of these." Keep the graph table as the second target for n = 5.
- 6.2, add a method sentence: "m_tree is computed for all functions at n ≤ 4 by a
  size-stratified dictionary over (truth table, vars⁺, vars⁻); it upper-bounds m and seeds
  the SAT loop."
- 8, layout: add `src/PcNnf.Enum`; order of work: Core, Enum (one day; the fixture exists),
  Exact, then the compiler.
- 2.3 or 3.2: add Lemma E and Corollary E1 of section 2.3 above (per-variable closure;
  minimal circuits use exactly the essential polarities) as **[checked]** items naming
  `scripts/check_essential.py`, with the proof. Add to section 7 a Lean target "L12: Lemma E
  and Corollary E1; depends on L1" (small; it is L6's induction for one variable).
- 6.9: add a row "H10: no minimal PC-NNF DAG contains two gates with the same truth table.
  Status: **[conjecture]**; cannot be settled by Corollary E1, which constrains the root only.
  Refuted by any minimal circuit from E1's synthesizer with two equal-function gates."
