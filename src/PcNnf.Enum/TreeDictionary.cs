using System.Diagnostics;
using PcNnf.Core;

namespace PcNnf.Enum;

public enum EntryOp : byte
{
    Literal = 1,
    True = 2,
    False = 3,
    And = 4,
    Or = 5,
}

/// <summary>
/// One stored minimal tree. For a gate, <see cref="Left"/> and <see cref="Right"/> are entry
/// indices (back-pointers); for a literal, <see cref="Variable"/> and <see cref="Positive"/>.
/// <see cref="Pos"/>/<see cref="Neg"/> are the essential polarity sets of the truth table
/// (strategy 2.3), which by Corollary E1 equal the tree's own vars⁺/vars⁻; the build asserts it.
/// </summary>
public readonly record struct Entry(ulong Tt, byte Gates, EntryOp Op, int Left, int Right, byte Variable, bool Positive, VarSet Pos, VarSet Neg)
{
    public bool IsGate => Op == EntryOp.And || Op == EntryOp.Or;
}

/// <summary>
/// The size-stratified dictionary of strategy 2.2: for every Boolean function on n variables
/// reached, the minimum fan-in-2 gate count of a tree under <see cref="Rule"/>, keyed on the
/// truth table alone (Corollary E2). Level s is built from all operand pairs at levels
/// (a, s−1−a); the first time a table appears it is at its minimum. Reports m_tree, not m
/// (strategy 2.2 item 3).
/// </summary>
public sealed class TreeDictionary
{
    private readonly List<Entry> _entries = new();
    private readonly List<int> _levelStart = new(); // _levelStart[k] .. _levelStart[k+1]-1 is level k
    private readonly TableIndex _index;

    private TreeDictionary(int n, Rule rule)
    {
        N = n;
        Rule = rule;
        _index = new TableIndex(n);
    }

    public int N { get; }
    public Rule Rule { get; }
    public IReadOnlyList<Entry> Entries => _entries;
    public int Count => _entries.Count;

    /// <summary>Number of distinct truth tables reached (= Count, since keying is on the table).</summary>
    public long Reached => _entries.Count;

    /// <summary>Number of functions the run is trying to reach, when known (all, or all monotone).</summary>
    public long? TargetCount { get; private set; }

    /// <summary>Highest gate count stored.</summary>
    public int MaxGates => _levelStart.Count - 2;

    /// <summary>Entries added per level 0..MaxGates.</summary>
    public int[] LevelCounts
    {
        get
        {
            var c = new int[_levelStart.Count - 1];
            for (int k = 0; k < c.Length; k++) c[k] = _levelStart[k + 1] - _levelStart[k];
            return c;
        }
    }

    /// <summary>Stored trees whose actual (vars⁺, vars⁻) differ from the essential sets of their table. Zero under Pc/Mono (asserted).</summary>
    public int PolarityMismatches { get; private set; }

    /// <summary>True when the run stopped at the gate cap before reaching every target function.</summary>
    public bool Capped { get; private set; }

    public TimeSpan BuildTime { get; private set; }

    // ---- lookup ---------------------------------------------------------------------------------

    public bool TryGetEntry(ulong tt, out Entry entry)
    {
        if (_index.TryGet(tt, out int idx)) { entry = _entries[idx]; return true; }
        entry = default;
        return false;
    }

    public bool TryGetEntry(TruthTable tt, out Entry entry) => TryGetEntry(RequireN(tt), out entry);

    /// <summary>Minimum gate count of the function, or null if not reached (beyond the cap).</summary>
    public int? Gates(TruthTable tt) => TryGetEntry(tt, out var e) ? e.Gates : null;

    public int? Gates(ulong tt) => TryGetEntry(tt, out var e) ? e.Gates : null;

    private ulong RequireN(TruthTable tt)
    {
        if (tt.N != N) throw new ArgumentException($"table over {tt.N} variables, dictionary over {N}");
        return tt.Bits;
    }

    /// <summary>
    /// Rebuild the stored minimal tree as a Core DAG with shared literal leaves, so that
    /// plan-2.1 size = 3k + |P| + |N| for a tree with k gates.
    /// </summary>
    public Dag Reconstruct(TruthTable tt)
    {
        if (!TryGetEntry(tt, out _)) throw new KeyNotFoundException($"{tt} not reached");
        _index.TryGet(tt.Bits, out int idx);
        var dag = new Dag();
        var leaves = new Dictionary<(EntryOp, int, bool), int>();
        dag.Root = Build(idx, dag, leaves);
        return dag;
    }

    private int Build(int idx, Dag dag, Dictionary<(EntryOp, int, bool), int> leaves)
    {
        var e = _entries[idx];
        switch (e.Op)
        {
            case EntryOp.Literal:
                return Leaf(leaves, (EntryOp.Literal, e.Variable, e.Positive), () => dag.AddLiteral(e.Variable, e.Positive));
            case EntryOp.True:
                return Leaf(leaves, (EntryOp.True, 0, false), dag.AddTrue);
            case EntryOp.False:
                return Leaf(leaves, (EntryOp.False, 0, false), dag.AddFalse);
            default:
                int l = Build(e.Left, dag, leaves);
                int r = Build(e.Right, dag, leaves);
                return dag.AddGate(e.Op == EntryOp.And ? NodeKind.And : NodeKind.Or, new[] { l, r });
        }
    }

    private static int Leaf(Dictionary<(EntryOp, int, bool), int> leaves, (EntryOp, int, bool) key, Func<int> add)
    {
        if (!leaves.TryGetValue(key, out int id)) { id = add(); leaves[key] = id; }
        return id;
    }

    // ---- build ------------------------------------------------------------------------------------

    /// <param name="n">Number of variables (1..6).</param>
    /// <param name="rule">Tree class.</param>
    /// <param name="maxGates">Stop after this level even if functions remain (required for n ≥ 5).</param>
    /// <param name="log">Optional per-level progress line.</param>
    public static TreeDictionary Build(int n, Rule rule, int maxGates = 40, Action<string>? log = null)
    {
        if (n < 1 || n > TruthTable.MaxVariables) throw new ArgumentOutOfRangeException(nameof(n));
        if (n >= 5 && maxGates > 8) throw new ArgumentException("n ≥ 5 needs a size cap (strategy 2.4); pass --max-gates ≤ 8", nameof(maxGates));
        var sw = Stopwatch.StartNew();
        var d = new TreeDictionary(n, rule);
        d.TargetCount = n <= 4 ? (rule == Rule.Mono ? CountMonotone(n) : 1L << (1 << n)) : null;

        // level 0: literals (positive only under Mono), then ⊥ and ⊤, as in the spike
        d._levelStart.Add(0);
        for (int v = 0; v < n; v++)
        {
            d.Add(new Entry(TruthTable.Literal(n, v, true).Bits, 0, EntryOp.Literal, -1, -1, (byte)v, true, VarSet.Single(v), VarSet.Empty), VarSet.Single(v), VarSet.Empty);
            if (rule != Rule.Mono)
                d.Add(new Entry(TruthTable.Literal(n, v, false).Bits, 0, EntryOp.Literal, -1, -1, (byte)v, false, VarSet.Empty, VarSet.Single(v)), VarSet.Empty, VarSet.Single(v));
        }
        d.Add(new Entry(0UL, 0, EntryOp.False, -1, -1, 0, false, VarSet.Empty, VarSet.Empty), VarSet.Empty, VarSet.Empty);
        d.Add(new Entry(TruthTable.FullMask(n), 0, EntryOp.True, -1, -1, 0, false, VarSet.Empty, VarSet.Empty), VarSet.Empty, VarSet.Empty);
        d._levelStart.Add(d._entries.Count);
        log?.Invoke($"  level  0: +{d.LevelCounts[0],8} entries, {d.Reached,10}{Target(d)} functions reached");

        bool allowAllAnd = rule != Rule.Pc;
        for (int s = 1; s <= maxGates; s++)
        {
            if (d.TargetCount is long target && d.Reached >= target) break;
            int before = d._entries.Count;
            for (int a = 0; a <= s - 1 - a; a++)
            {
                int b = s - 1 - a;
                int a0 = d._levelStart[a], a1 = d._levelStart[a + 1];
                int b0 = d._levelStart[b], b1 = d._levelStart[b + 1];
                for (int i = a0; i < a1; i++)
                {
                    var x = d._entries[i];
                    int jStart = a == b ? i : b0;
                    for (int j = jStart; j < b1; j++)
                    {
                        var y = d._entries[j];
                        ulong orTt = x.Tt | y.Tt;
                        if (!d._index.Contains(orTt))
                            d.AddGate(orTt, s, EntryOp.Or, i, j, x, y);
                        // the polarity rule at ∧(x, y): vars⁺(x) ∩ vars⁻(y) = ∅ and vice versa
                        if (allowAllAnd || (!x.Pos.Intersects(y.Neg) && !y.Pos.Intersects(x.Neg)))
                        {
                            ulong andTt = x.Tt & y.Tt;
                            if (!d._index.Contains(andTt))
                                d.AddGate(andTt, s, EntryOp.And, i, j, x, y);
                        }
                    }
                }
            }
            d._levelStart.Add(d._entries.Count);
            log?.Invoke($"  level {s,2}: +{d._entries.Count - before,8} entries, {d.Reached,10}{Target(d)} functions reached");
            if (s == maxGates && (d.TargetCount is not long t2 || d.Reached < t2)) d.Capped = true;
        }
        if (d.TargetCount is long t3 && d.Reached < t3) d.Capped = true;
        d.BuildTime = sw.Elapsed;
        return d;
    }

    private static string Target(TreeDictionary d) => d.TargetCount is long t ? $"/{t}" : "";

    // Actual polarity sets of each stored tree (unions along the back-pointers), kept only
    // for the build-time assertion against the essential sets computed from the table.
    private readonly List<VarSet> _actualPos = new();
    private readonly List<VarSet> _actualNeg = new();

    private void AddGate(ulong tt, int gates, EntryOp op, int left, int right, Entry x, Entry y)
    {
        var table = new TruthTable(N, tt);
        var entry = new Entry(tt, (byte)gates, op, left, right, 0, false, table.EssentialPositive, table.EssentialNegative);
        Add(entry, _actualPos[left] | _actualPos[right], _actualNeg[left] | _actualNeg[right]);
    }

    private void Add(Entry entry, VarSet actualPos, VarSet actualNeg)
    {
        int idx = _entries.Count;
        _entries.Add(entry);
        _actualPos.Add(actualPos);
        _actualNeg.Add(actualNeg);
        _index.Set(entry.Tt, idx);
        if (actualPos != entry.Pos || actualNeg != entry.Neg)
        {
            PolarityMismatches++;
            if (Rule != Rule.Nnf)
                throw new InvalidOperationException(
                    $"Corollary E1 violated under rule {Rule}: minimal tree for {new TruthTable(N, entry.Tt).ToHex()} with {entry.Gates} gates has " +
                    $"vars⁺={actualPos} vars⁻={actualNeg} but P_ess={entry.Pos} N_ess={entry.Neg}");
        }
    }

    /// <summary>Number of monotone functions on n ≤ 4 variables (Dedekind numbers 3, 6, 20, 168).</summary>
    public static long CountMonotone(int n)
    {
        long c = 0;
        ulong full = TruthTable.FullMask(n);
        for (ulong tt = 0; tt <= full; tt++) if (new TruthTable(n, tt).IsMonotone) c++;
        return c;
    }

    /// <summary>tt → entry index; a flat array for n ≤ 4, a hash table above.</summary>
    private sealed class TableIndex
    {
        private readonly int[]? _dense;
        private readonly Dictionary<ulong, int>? _sparse;

        public TableIndex(int n)
        {
            if (n <= 4) { _dense = new int[1 << (1 << n)]; Array.Fill(_dense, -1); }
            else _sparse = new Dictionary<ulong, int>(new MixedHash());
        }

        /// <summary>
        /// .NET hashes a ulong as (low 32 bits) XOR (high 32 bits). At n = 6 every table that
        /// does not depend on x5 has equal halves and hashes to 0, so the dictionary degenerates
        /// to one bucket. A 64-bit mixing finaliser (splitmix64) avoids that.
        /// </summary>
        private sealed class MixedHash : IEqualityComparer<ulong>
        {
            public bool Equals(ulong a, ulong b) => a == b;

            public int GetHashCode(ulong z)
            {
                z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9UL;
                z = (z ^ (z >> 27)) * 0x94D049BB133111EBUL;
                z ^= z >> 31;
                return (int)z ^ (int)(z >> 32);
            }
        }

        public bool Contains(ulong tt) => _dense != null ? _dense[tt] >= 0 : _sparse!.ContainsKey(tt);

        public bool TryGet(ulong tt, out int idx)
        {
            if (_dense != null)
            {
                if (tt >= (ulong)_dense.Length) { idx = -1; return false; }
                idx = _dense[tt];
                return idx >= 0;
            }
            return _sparse!.TryGetValue(tt, out idx);
        }

        public void Set(ulong tt, int idx)
        {
            if (_dense != null) _dense[tt] = idx; else _sparse![tt] = idx;
        }
    }
}
