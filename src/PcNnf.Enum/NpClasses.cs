using PcNnf.Core;

namespace PcNnf.Enum;

/// <summary>
/// NP equivalence classes of all functions on n ≤ 4 variables: input permutation and input
/// complementation, no output negation (the group that preserves m, plan 2.3). Built by
/// union-find over the generators (adjacent transpositions and single-variable flips); the
/// class representative is its smallest truth table. Expected counts: n=3: 22, n=4: 402
/// (strategy 2.1, Burnside).
/// </summary>
public sealed class NpClasses
{
    private readonly int[] _parent;

    public int N { get; }

    public NpClasses(int n)
    {
        if (n < 1 || n > 4) throw new ArgumentOutOfRangeException(nameof(n), "classes are enumerated for n ≤ 4 only");
        N = n;
        int total = 1 << (1 << n);
        _parent = new int[total];
        for (int i = 0; i < total; i++) _parent[i] = i;

        for (int tt = 0; tt < total; tt++)
        {
            var t = new TruthTable(n, (ulong)tt);
            for (int v = 0; v < n; v++)
            {
                Union(tt, (int)t.FlipInputs(VarSet.Single(v)).Bits);
                if (v + 1 < n)
                {
                    var perm = Enumerable.Range(0, n).ToArray();
                    (perm[v], perm[v + 1]) = (perm[v + 1], perm[v]);
                    Union(tt, (int)t.PermuteInputs(perm).Bits);
                }
            }
        }
        // make every root the minimum of its class
        var min = new int[total];
        Array.Fill(min, int.MaxValue);
        for (int i = 0; i < total; i++) min[Find(i)] = Math.Min(min[Find(i)], i);
        var rep = new int[total];
        for (int i = 0; i < total; i++) rep[i] = min[Find(i)];
        _parent = rep;
        ClassCount = rep.Distinct().Count();
    }

    public int ClassCount { get; }

    /// <summary>Smallest truth table in the class of <paramref name="tt"/>.</summary>
    public int Representative(int tt) => _parent[tt];

    public IEnumerable<int> Representatives() => _parent.Distinct().Order();

    public int ClassSize(int representative) => _parent.Count(r => r == representative);

    private int Find(int i)
    {
        while (_parent[i] != i) { _parent[i] = _parent[_parent[i]]; i = _parent[i]; }
        return i;
    }

    private void Union(int a, int b)
    {
        a = Find(a); b = Find(b);
        if (a == b) return;
        if (a < b) _parent[b] = a; else _parent[a] = b;
    }
}
