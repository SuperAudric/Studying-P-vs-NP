using System.Text;
using PcNnf.Core;

namespace PcNnf.Enum;

/// <summary>
/// Tree minima for the fixed-graph clique formulas φ_{G,k}(s) = "S is a clique of G with
/// |S| ≥ k" (plan 1.1, 4.1) for every graph on n vertices up to isomorphism and every
/// k = 0..n. The numbers are upper bounds on m(φ_{G,k}) (strategy 2.1): status "upper".
/// </summary>
public static class CliqueTable
{
    public sealed record Row(
        int N, string Edges, int K, TruthTable Table,
        int? GatesPc, int? Size21Pc, int? NaryGatesPc, int? NarySize21Pc,
        int? GatesNnf, int? Size21Nnf)
    {
        public bool IsConstant => Table.IsConstant;
        public string Status => "upper";
    }

    /// <summary>All graphs on n vertices up to isomorphism, as edge bitmasks over pairs in lexicographic order.</summary>
    public static IReadOnlyList<int> GraphsUpToIsomorphism(int n)
    {
        var pairs = Pairs(n);
        int graphs = 1 << pairs.Count;
        var seen = new bool[graphs];
        var reps = new List<int>();
        var perms = Permutations(n).ToList();
        for (int m = 0; m < graphs; m++)
        {
            if (seen[m]) continue;
            reps.Add(m);
            foreach (var p in perms)
            {
                int img = 0;
                for (int idx = 0; idx < pairs.Count; idx++)
                    if (((m >> idx) & 1) == 1) img |= 1 << PairIndex(pairs, p[pairs[idx].u], p[pairs[idx].v]);
                seen[img] = true;
            }
        }
        return reps;
    }

    /// <summary>Truth table of φ_{G,k} over s_0..s_{n-1}.</summary>
    public static TruthTable CliqueFormula(int n, int edgeMask, int k)
    {
        var pairs = Pairs(n);
        return TruthTable.FromPredicate(n, s =>
        {
            if (System.Numerics.BitOperations.PopCount(s) < k) return false;
            for (int idx = 0; idx < pairs.Count; idx++)
            {
                var (u, v) = pairs[idx];
                if (((s >> u) & 1UL) == 1 && ((s >> v) & 1UL) == 1 && ((edgeMask >> idx) & 1) == 0) return false;
            }
            return true;
        });
    }

    public static string EdgeLabel(int n, int edgeMask)
    {
        var pairs = Pairs(n);
        var parts = new List<string>();
        for (int idx = 0; idx < pairs.Count; idx++) if (((edgeMask >> idx) & 1) == 1) parts.Add($"{pairs[idx].u}{pairs[idx].v}");
        return parts.Count == 0 ? "∅" : string.Join(",", parts);
    }

    public static List<Row> Rows(TreeDictionary pc, TreeDictionary nnf)
    {
        if (pc.N != nnf.N) throw new ArgumentException("dictionaries over different n");
        int n = pc.N;
        var rows = new List<Row>();
        foreach (var g in GraphsUpToIsomorphism(n))
        {
            for (int k = 0; k <= n; k++)
            {
                var tt = CliqueFormula(n, g, k);
                if (tt.IsConstant)
                {
                    rows.Add(new Row(n, EdgeLabel(n, g), k, tt, null, null, null, null, null, null));
                    continue;
                }
                var pcTree = pc.TryGetEntry(tt, out _) ? pc.Reconstruct(tt) : null;
                var nnfTree = nnf.TryGetEntry(tt, out _) ? nnf.Reconstruct(tt) : null;
                var flat = pcTree?.Flatten();
                rows.Add(new Row(n, EdgeLabel(n, g), k, tt,
                    pcTree?.BinaryGateCount, pcTree?.Size, flat?.NaryGateCount, flat?.Size,
                    nnfTree?.BinaryGateCount, nnfTree?.Size));
            }
        }
        return rows;
    }

    /// <summary>One line per (G, k), every number labelled by its measure, status column "upper".</summary>
    public static string Render(IEnumerable<Row> rows)
    {
        var sb = new StringBuilder();
        sb.AppendLine("n | G (edges) | k | status | k_pc [gates, fan-in-2 tree] | size_pc [plan 2.1, fan-in-2 tree] | gates_pc [n-ary, flattened tree] | size_pc [plan 2.1, flattened tree] | k_nnf [gates, fan-in-2 tree] | size_nnf [plan 2.1, fan-in-2 tree]");
        foreach (var r in rows)
        {
            if (r.IsConstant)
            {
                sb.AppendLine($"{r.N} | {r.Edges} | {r.K} | {(r.Table.IsTrue ? "⊤" : "⊥")} | - | - | - | - | - | -");
                continue;
            }
            string Cell(int? v, string unit) => v is int x ? $"{x} {unit}" : "> cap";
            sb.AppendLine($"{r.N} | {r.Edges} | {r.K} | {r.Status} | {Cell(r.GatesPc, "gates")} | {Cell(r.Size21Pc, "size")} | {Cell(r.NaryGatesPc, "gates")} | {Cell(r.NarySize21Pc, "size")} | {Cell(r.GatesNnf, "gates")} | {Cell(r.Size21Nnf, "size")}");
        }
        return sb.ToString();
    }

    // ---- helpers --------------------------------------------------------------------------------

    public static List<(int u, int v)> Pairs(int n)
    {
        var p = new List<(int, int)>();
        for (int a = 0; a < n; a++) for (int b = a + 1; b < n; b++) p.Add((a, b));
        return p;
    }

    private static int PairIndex(List<(int u, int v)> pairs, int u, int v)
    {
        if (u > v) (u, v) = (v, u);
        return pairs.IndexOf((u, v));
    }

    private static IEnumerable<int[]> Permutations(int n)
    {
        var p = Enumerable.Range(0, n).ToArray();
        return Permute(p, 0);

        static IEnumerable<int[]> Permute(int[] p, int i)
        {
            if (i == p.Length) { yield return (int[])p.Clone(); yield break; }
            for (int j = i; j < p.Length; j++)
            {
                (p[i], p[j]) = (p[j], p[i]);
                foreach (var q in Permute(p, i + 1)) yield return q;
                (p[i], p[j]) = (p[j], p[i]);
            }
        }
    }
}
