using System.Text;
using PcNnf.Core;

namespace PcNnf.Enum;

/// <summary>
/// k_pc − k_nnf over all functions at n ≤ 4 (tree measure, fan-in-2 gates), and the
/// maximum-gap functions grouped by NP class (strategy 4.2, 5.1).
/// </summary>
public sealed class GapReport
{
    public sealed record GapClass(TruthTable Representative, int ClassSize, int GatesNnf, int GatesPc, VarSet PEss, VarSet NEss, string PcTree, string NnfTree);

    public int N { get; }
    public int MaxGatesPc { get; }
    public int MaxGatesNnf { get; }
    public int MaxGap { get; }

    /// <summary>Histogram[g] = number of functions with k_pc − k_nnf = g.</summary>
    public IReadOnlyList<int> Histogram { get; }

    public int NpClassCount { get; }
    public IReadOnlyList<GapClass> MaxGapClasses { get; }

    public GapReport(TreeDictionary pc, TreeDictionary nnf)
    {
        if (pc.Rule != Rule.Pc || nnf.Rule != Rule.Nnf) throw new ArgumentException("needs a pc and an nnf dictionary");
        if (pc.N != nnf.N || pc.N > 4) throw new ArgumentException("same n ≤ 4 required");
        if (pc.Capped || nnf.Capped) throw new ArgumentException("both dictionaries must be complete");
        N = pc.N;
        int total = 1 << (1 << N);
        var hist = new List<int>();
        int maxGap = 0;
        var gaps = new int[total];
        for (int tt = 0; tt < total; tt++)
        {
            int kp = pc.Gates((ulong)tt)!.Value, kn = nnf.Gates((ulong)tt)!.Value;
            if (kp < kn) throw new InvalidOperationException($"k_pc < k_nnf at {tt:x}: the NNF dictionary missed a tree");
            int g = kp - kn;
            gaps[tt] = g;
            while (hist.Count <= g) hist.Add(0);
            hist[g]++;
            maxGap = Math.Max(maxGap, g);
        }
        Histogram = hist;
        MaxGap = maxGap;
        MaxGatesPc = pc.MaxGates;
        MaxGatesNnf = nnf.MaxGates;

        var classes = new NpClasses(N);
        NpClassCount = classes.ClassCount;
        var list = new List<GapClass>();
        foreach (var rep in classes.Representatives())
        {
            if (gaps[rep] != maxGap) continue;
            var t = new TruthTable(N, (ulong)rep);
            list.Add(new GapClass(t, classes.ClassSize(rep), nnf.Gates(t)!.Value, pc.Gates(t)!.Value,
                t.EssentialPositive, t.EssentialNegative,
                pc.Reconstruct(t).ToFormulaString(), nnf.Reconstruct(t).ToFormulaString()));
        }
        MaxGapClasses = list;
    }

    public string Render()
    {
        var sb = new StringBuilder();
        sb.AppendLine($"== gap report, n={N}: k_pc − k_nnf over all {1 << (1 << N)} functions [measure: fan-in-2 gates, tree minima] ==");
        sb.AppendLine($"  max k_nnf = {MaxGatesNnf} gates, max k_pc = {MaxGatesPc} gates");
        sb.Append("  gap histogram (k_pc − k_nnf → functions):");
        for (int g = 0; g < Histogram.Count; g++) if (Histogram[g] > 0) sb.Append($" {g}:{Histogram[g]}");
        sb.AppendLine();
        sb.AppendLine($"  NP classes (permutation + complementation of inputs): {NpClassCount}");
        sb.AppendLine($"  classes with the maximum gap {MaxGap}: {MaxGapClasses.Count} classes, {MaxGapClasses.Sum(c => c.ClassSize)} functions");
        foreach (var c in MaxGapClasses)
        {
            sb.AppendLine($"    {c.Representative.ToHex()}  class size {c.ClassSize,3}  k_nnf {c.GatesNnf} → k_pc {c.GatesPc} gates  P_ess={c.PEss} N_ess={c.NEss}");
            sb.AppendLine($"       pc : {c.PcTree}");
            sb.AppendLine($"       nnf: {c.NnfTree}");
        }
        return sb.ToString();
    }
}
