using PcNnf.Core;
using PcNnf.Enum;

namespace PcNnf.Tests;

/// <summary>Every tree reconstructed from Enum passes Core's validity check and equals its table (strategy 4.4).</summary>
public class ReconstructionTests
{
    private static void CheckAll(TreeDictionary d, bool requireValid)
    {
        int n = d.N;
        foreach (var e in d.Entries)
        {
            var tt = new TruthTable(n, e.Tt);
            var dag = d.Reconstruct(tt);
            Assert.Equal(tt, dag.TruthTable(n));
            if (requireValid) Assert.True(dag.IsValid(), $"invalid tree for {tt.ToHex()}: {dag.ToFormulaString()}");
            Assert.Equal(e.Gates, dag.BinaryGateCount);
            Assert.Equal(e.Gates, dag.NaryGateCount); // reconstructed as a fan-in-2 tree
            var (pos, neg) = dag.PolaritySets();
            Assert.Equal(e.Pos, pos[dag.Root]);
            Assert.Equal(e.Neg, neg[dag.Root]);
            Assert.Equal(tt.EssentialPositive, e.Pos);
            Assert.Equal(tt.EssentialNegative, e.Neg);
            // tree size with shared literal leaves: 3k + |P| + |N| (+ constant leaves only for ⊤/⊥ themselves)
            if (!tt.IsConstant) Assert.Equal(3 * e.Gates + e.Pos.Count + e.Neg.Count, dag.Size);
            if (d.Rule == Rule.Mono) Assert.True(neg[dag.Root].IsEmpty);
        }
    }

    [Fact] public void Pc3_AllTreesValidAndCorrect() => CheckAll(TestEnv.Pc3.Value, requireValid: true);
    [Fact] public void Pc4_AllTreesValidAndCorrect() => CheckAll(TestEnv.Pc4.Value, requireValid: true);
    [Fact] public void Mono4_AllTreesValidAndCorrect() => CheckAll(TestEnv.Mono4.Value, requireValid: true);

    [Fact]
    public void Nnf4_AllTreesCorrect_InvalidOnesAreExactlyTheGapFunctions()
    {
        var nnf = TestEnv.Nnf4.Value;
        var pc = TestEnv.Pc4.Value;
        CheckAll(nnf, requireValid: false);
        int invalid = 0;
        foreach (var e in nnf.Entries)
        {
            var tt = new TruthTable(4, e.Tt);
            bool valid = nnf.Reconstruct(tt).IsValid();
            if (!valid) invalid++;
            // a valid NNF tree is a PC-NNF tree, so the pc minimum cannot exceed it
            if (valid) Assert.Equal(pc.Gates(tt), e.Gates);
            // a function with a gap cannot have a valid minimal NNF tree
            if (pc.Gates(tt) > e.Gates) Assert.False(valid);
        }
        Assert.True(invalid >= 12_800 + 944, $"only {invalid} invalid NNF minimal trees");
    }

    [Fact]
    public void Reconstructed_FlattenedTrees_StayValidAndCorrect()
    {
        var pc = TestEnv.Pc4.Value;
        foreach (var e in pc.Entries)
        {
            var tt = new TruthTable(4, e.Tt);
            var flat = pc.Reconstruct(tt).Flatten();
            Assert.True(flat.IsValid());
            Assert.Equal(tt, flat.TruthTable(4));
            Assert.Equal(e.Gates, flat.BinaryGateCount);
            Assert.True(flat.NaryGateCount <= e.Gates);
        }
    }
}
