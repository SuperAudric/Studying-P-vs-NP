using PcNnf.Core;

namespace PcNnf.Tests;

public class CoreTests
{
    private const int N = 4;

    /// <summary>The shortcut counterexample of plan 5.2 / check_tiny.py: invalid, pass says 1, function is ⊥.</summary>
    private static Dag ShortcutCounterexample()
    {
        var d = new Dag();
        int a = d.AddLiteral(0, true), b = d.AddLiteral(1, true);
        int h = d.AddAnd(a, b);
        int f = d.AddFalse();
        int hf = d.AddAnd(h, f);
        int na = d.AddLiteral(0, false), dd = d.AddLiteral(3, true);
        int nad = d.AddAnd(na, dd);
        int g = d.AddOr(hf, nad);
        d.Root = d.AddAnd(h, g);
        return d;
    }

    [Fact]
    public void Counterexample_IsInvalid_PassIsUnsound()
    {
        var d = ShortcutCounterexample();
        Assert.False(d.IsValid());
        Assert.Equal(9, d.FindViolation());
        Assert.True(d.Sat());
        Assert.True(d.TruthTable(N).IsFalse);
    }

    [Fact]
    public void Measures_MatchPlan21()
    {
        var d = ShortcutCounterexample();
        Assert.Equal(10, d.NodeCount);
        Assert.Equal(10, d.ReferenceCount);
        Assert.Equal(20, d.Size);
        Assert.Equal(5, d.NaryGateCount);
        Assert.Equal(5, d.BinaryGateCount);
        var e = new Dag();
        e.Root = e.AddAnd(e.AddLiteral(0, true), e.AddLiteral(1, true), e.AddLiteral(2, true));
        Assert.Equal(1, e.NaryGateCount);
        Assert.Equal(2, e.BinaryGateCount);
        Assert.Equal(4 + 3, e.Size);
    }

    [Fact]
    public void PolaritySets_SharedBlockCountsBothPolarities()
    {
        // (x ∨ ¬x) ∧ (x ∨ ¬x) with a shared block is invalid (plan 2.1)
        var d = new Dag();
        int blk = d.AddOr(d.AddLiteral(0, true), d.AddLiteral(0, false));
        d.Root = d.AddAnd(blk, blk);
        Assert.False(d.IsValid());
        Assert.Equal(VarSet.Of(0), d.VarsPositive);
        Assert.Equal(VarSet.Of(0), d.VarsNegative);
    }

    [Fact]
    public void Validity_AllowsSharedSinglePolarity()
    {
        // (x ∨ y) ∧ (x ∨ z): x shared positively, valid
        var d = new Dag();
        int x = d.AddLiteral(0, true);
        d.Root = d.AddAnd(d.AddOr(x, d.AddLiteral(1, true)), d.AddOr(x, d.AddLiteral(2, true)));
        Assert.True(d.IsValid());
    }

    [Fact]
    public void Validity_ChildMayBeImpureOnItsOwn()
    {
        // ((x ∧ ¬x) ∨ y) ∧ z is valid: the impurity is inside one child
        var d = new Dag();
        int impure = d.AddOr(d.AddAnd(d.AddLiteral(0, true), d.AddLiteral(0, false)), d.AddLiteral(1, true));
        d.Root = d.AddAnd(impure, d.AddLiteral(2, true));
        Assert.Equal(2, d.FindViolation()); // node 2 is the inner x ∧ ¬x (nodes 0, 1 are its leaves)
        var e = new Dag();
        int imp2 = e.AddOr(e.AddLiteral(0, true), e.AddLiteral(0, false)); // x ∨ ¬x, fine
        e.Root = e.AddAnd(imp2, e.AddLiteral(2, true));
        Assert.True(e.IsValid());
    }

    [Fact]
    public void TheoremA_LemmaW_OnRandomValidFormulas()
    {
        var rng = new Random(7);
        int valid = 0;
        for (int trial = 0; trial < 3000; trial++)
        {
            var d = TestEnv.RandomFormula(rng, N, rng.Next(11, 19));
            if (!d.IsValid()) continue;
            valid++;
            var tt = d.TruthTable(N);
            Assert.Equal(!tt.IsFalse, d.Sat());
            var w = d.ExtractWitness();
            if (w is null) { Assert.True(tt.IsFalse); continue; }
            Assert.True(w.Value.IsConsistent);
            for (ulong s = 0; s < 16; s++) if (w.Value.Extends(s)) Assert.True(tt[s]);
        }
        Assert.True(valid > 500, $"only {valid} valid formulas drawn");
    }

    [Fact]
    public void Conditioning_Forgetting_Renaming_MatchTableSemantics()
    {
        var rng = new Random(11);
        int checkedCount = 0;
        for (int trial = 0; trial < 2000; trial++)
        {
            var d = TestEnv.RandomFormula(rng, N, rng.Next(11, 19));
            if (!d.IsValid()) continue;
            checkedCount++;
            var tt = d.TruthTable(N);
            for (int x = 0; x < N; x++)
            {
                // conditioning on x := b
                foreach (var b in new[] { false, true })
                {
                    var c = d.Condition(VarSet.Single(x), b ? 1UL << x : 0UL);
                    Assert.True(c.IsValid());
                    Assert.True(c.Size <= d.Size);
                    Assert.Equal(tt.Cofactor(x, b), c.TruthTable(N));
                }
                // forgetting: exact for valid F
                var f = d.Forget(VarSet.Single(x));
                Assert.True(f.IsValid());
                Assert.Equal(tt.Forget(x), f.TruthTable(N));
                // renaming
                var r = d.Rename(VarSet.Single(x));
                Assert.True(r.IsValid());
                Assert.Equal(r.Size, d.Size);
                Assert.Equal(tt.FlipInputs(VarSet.Single(x)), r.TruthTable(N));
            }
            // simplification and flattening preserve the function; simplification never grows
            var s = d.Simplify();
            Assert.True(s.IsValid());
            Assert.Equal(tt, s.TruthTable(N));
            Assert.True(s.Size <= d.Reachable().Size);
            var fl = d.Flatten();
            Assert.Equal(tt, fl.TruthTable(N));
            Assert.Equal(d.IsValid(), fl.IsValid());
            Assert.True(fl.NaryGateCount <= d.Reachable().NaryGateCount);
            // Theorem B′: F[neg := ⊤] is the upward closure
            var up = d.SubstituteLiterals((_, positive) => positive ? null : true).TruthTable(N);
            var closure = TruthTable.FromPredicate(N, sigma => Enumerable.Range(0, 16).Any(tau => ((ulong)tau & ~sigma) == 0 && tt[(ulong)tau]));
            Assert.Equal(closure, up);
        }
        Assert.True(checkedCount > 300);
    }

    [Fact]
    public void EssentialPolarities_Examples()
    {
        // x0 ∧ ¬x1: P = {0}, N = {1}
        var t = TruthTable.Literal(N, 0, true).And(TruthTable.Literal(N, 1, false));
        Assert.Equal(VarSet.Of(0), t.EssentialPositive);
        Assert.Equal(VarSet.Of(1), t.EssentialNegative);
        Assert.False(t.IsMonotone);
        // parity: everything both ways
        var parity = TruthTable.FromPredicate(N, s => (System.Numerics.BitOperations.PopCount(s) & 1) == 1);
        Assert.Equal(VarSet.Range(N), parity.EssentialPositive);
        Assert.Equal(VarSet.Range(N), parity.EssentialNegative);
        // threshold ≥ 2 is monotone with full positive support
        var thr = TruthTable.FromPredicate(N, s => System.Numerics.BitOperations.PopCount(s) >= 2);
        Assert.True(thr.IsMonotone);
        Assert.Equal(VarSet.Range(N), thr.EssentialPositive);
        Assert.Equal(VarSet.Empty, thr.EssentialNegative);
        // essential sets are lower bounds for every NNF circuit (unateness fact)
        var rng = new Random(3);
        for (int i = 0; i < 500; i++)
        {
            var d = TestEnv.RandomFormula(rng, N, rng.Next(11, 19));
            var tt = d.TruthTable(N);
            var (pos, neg) = d.PolaritySets();
            Assert.True(tt.EssentialPositive.IsSubsetOf(pos[d.Root]));
            Assert.True(tt.EssentialNegative.IsSubsetOf(neg[d.Root]));
        }
    }

    [Fact]
    public void Interchange_RoundTrips()
    {
        var rng = new Random(5);
        for (int i = 0; i < 200; i++)
        {
            var d = TestEnv.RandomFormula(rng, N, rng.Next(11, 19));
            var text = Interchange.Write(d, N);
            var (back, n) = Interchange.Read(text);
            Assert.Equal(N, n);
            Assert.Equal(text, Interchange.Write(back, n));
            Assert.Equal(d.TruthTable(N), back.TruthTable(N));
            Assert.Equal(d.IsValid(), back.IsValid());
        }
    }

    [Fact]
    public void Cnf_TabulatesTseitinParityAfterForgettingAuxiliaries()
    {
        // 4 = x1 ⊕ x2, 5 = 4 ⊕ x3, output 5 asserted; forgetting 4, 5 gives parity of x1, x2, x3
        const string dimacs = """
            c parity x1 xor x2 xor x3 via Tseitin
            p cnf 5 9
            -4 1 2 0
            -4 -1 -2 0
            4 -1 2 0
            4 1 -2 0
            -5 4 3 0
            -5 -4 -3 0
            5 -4 3 0
            5 4 -3 0
            5 0
            """;
        var cnf = Cnf.ReadDimacs(new StringReader(dimacs));
        var (tt, map) = cnf.Tabulate(new HashSet<int> { 4, 5 });
        Assert.Equal(new[] { 1, 2, 3 }, map);
        Assert.Equal(TruthTable.FromPredicate(3, s => (System.Numerics.BitOperations.PopCount(s) & 1) == 1), tt);
        // the encoding itself (nothing forgotten) has 5 variables and is a different object
        var (full, _) = cnf.Tabulate(new HashSet<int>());
        Assert.Equal(5, full.N);
        Assert.Equal(4, full.ModelCount);
        // refusal above 6 non-auxiliary variables
        var big = new Cnf(7, new[] { new[] { 1, 2, 3, 4, 5, 6, 7 } });
        Assert.Throws<InvalidOperationException>(() => big.Tabulate(new HashSet<int>()));
        Assert.Equal(6, big.Tabulate(new HashSet<int> { 7 }).Table.N);
    }

    [Fact]
    public void Cnf_TabulateMatchesBruteForceOnRandomCnfs()
    {
        var rng = new Random(13);
        for (int trial = 0; trial < 300; trial++)
        {
            int vars = 6, m = rng.Next(1, 8);
            var clauses = new List<int[]>();
            for (int i = 0; i < m; i++)
            {
                var lits = Enumerable.Range(1, vars).SelectMany(v => new[] { v, -v }).OrderBy(_ => rng.Next()).Take(rng.Next(1, 4)).ToArray();
                if (lits.Any(l => lits.Contains(-l))) continue;
                clauses.Add(lits);
            }
            var cnf = new Cnf(vars, clauses);
            var aux = new HashSet<int> { 5, 6 };
            var (tt, map) = cnf.Tabulate(aux);
            Assert.Equal(new[] { 1, 2, 3, 4 }, map);
            for (int s = 0; s < 16; s++)
            {
                bool expect = false;
                for (int a = 0; a < 4 && !expect; a++)
                {
                    int full = s | (a << 4);
                    expect = clauses.All(c => c.Any(l => ((full >> (Math.Abs(l) - 1)) & 1) == (l > 0 ? 1 : 0)));
                }
                Assert.Equal(expect, tt[(ulong)s]);
            }
        }
    }
}
