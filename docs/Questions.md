

## Questions

**Q1 (answer sets).** For a satisfiable CNF φ, let m(φ) be the minimum PC-NNF size of
a formula equivalent to φ. Given fact 5:
  a. Can we prove an *unconditional* exponential lower bound on m for an explicit
     family, and with which technique? The rectangle-cover argument used for DNNF
     does not obviously transfer, because ∧-children may share same-polarity
     variables. Say whether it can be adapted, or whether a PC-NNF → DNNF translation
     with polynomial blow-up exists; fact 3 suggests it does not.
  b. Which families provably have polynomial m: anything with a small OBDD or DNNF,
     unate CNFs, what else? Where do random and structured 3-SAT instances fall?
  c. A compiler to evaluate and, if sound, build as the main upper-bound tool:
     DPLL-style compilation with caching, where the residual CNF is split whenever
     its clauses partition into groups that share variables only in one polarity,
     not merely into variable-disjoint components, and where a variable occurring in
     only one polarity, say positive, is decided as R|x=0 ∨ (x ∧ R|x=1) instead of
     (¬x ∧ R|x=0) ∨ (x ∧ R|x=1), so a compiled block never introduces a polarity
     its CNF did not have. Check that this invariant makes the polarity-consistent
     split sound. This strictly generalises decision-DNNF compilation.

**Q2 (maximal cliques).** Over vertex-indicator variables y_v, one per literal
occurrence, define M(φ) = "the chosen vertices form a clique, i.e. at most one per
triangle and no two with opposite signs of one variable, and the clique is
inclusion-maximal, i.e. every triangle with no chosen vertex has all three of its
literals negated by chosen vertices". At the variable level this is the family of
consistent literal choices, one per used clause, that cannot be extended by choosing
a literal from any unused clause without a contradiction. This is exactly the space
my constructor enumerated. Does this version of the problem where the incomplete
answers are retained provide the same bounds as Q1. Thishas the same sub-questions
as Q1: must M(φ) grow exponentially for some families, and can that be proven? Treat
the general pattern "positive at-least-one / exactly-one / at-most-c constraints
mixed with a negative conflict graph" as its own sub-question, since it is the
simplest place where the difficulty appears.

**Q3 (strengthening).** Propose extensions of PC-NNF that keep (i) satisfiability
decidable in one bottom-up pass with context-free, or boundedly context-dependent,
block answers, and (ii) closure under conditioning. An extension only matters
asymptotically if the base language cannot simulate it with polynomial blow-up, so
say for each candidate whether it can. Candidates, plus your own:
  - Shared-block exemption. F ∧ F is semantically safe even when F contains
    both x and ¬x, yet the base rule rejects it. Candidate condition: a conflicting
    pair of occurrences is exempt when both occurrences lie inside instances of one
    block referenced by both children. Warning: the shortcut of replacing each shared
    block by a fresh atom and then checking the ordinary rule is unsound. With
    H = A ∧ B, F = H, G = (H ∧ ⊥) ∨ (¬A ∧ D), the shortcut accepts F ∧ G and the
    bottom-up pass says satisfiable, but F ∧ G ≡ ⊥. Work out the exact sound
    condition and whether validity under it is checkable in near-linear time.
  - XOR, exactly-k or cardinality blocks over variable-disjoint children. The language 
   is to compute any valid answer, even if enumerating all potentials is exponential 
   that does not cause an issue if any of the exponential options can be chosen freely.
