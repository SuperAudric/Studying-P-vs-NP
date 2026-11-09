using System.Globalization;
using System.Numerics;

namespace PcNnf.Core;

/// <summary>
/// Truth table of a Boolean function on n ≤ 6 variables as a 2ⁿ-bit vector in one ulong:
/// bit s is f(s) where assignment s has bit v = value of x_v.
/// </summary>
public readonly record struct TruthTable(int N, ulong Bits)
{
    public const int MaxVariables = 6;

    public static ulong FullMask(int n)
    {
        CheckN(n);
        return n == MaxVariables ? ulong.MaxValue : (1UL << (1 << n)) - 1;
    }

    private static void CheckN(int n)
    {
        if (n < 0 || n > MaxVariables) throw new ArgumentOutOfRangeException(nameof(n), $"n must be 0..{MaxVariables}");
    }

    public static TruthTable True(int n) => new(n, FullMask(n));
    public static TruthTable False(int n) => new(n, 0);

    /// <summary>Table of x_v (positive) or ¬x_v.</summary>
    public static TruthTable Literal(int n, int v, bool positive)
    {
        CheckN(n);
        if (v < 0 || v >= n) throw new ArgumentOutOfRangeException(nameof(v));
        return new TruthTable(n, positive ? PositiveLiteralMask(n, v) : PositiveLiteralMask(n, v) ^ FullMask(n));
    }

    /// <summary>Positions s with bit v set, i.e. the table of x_v.</summary>
    public static ulong PositiveLiteralMask(int n, int v)
    {
        ulong m = 0;
        for (int s = 0; s < (1 << n); s++) if (((s >> v) & 1) == 1) m |= 1UL << s;
        return m;
    }

    public static TruthTable FromPredicate(int n, Func<ulong, bool> f)
    {
        CheckN(n);
        ulong bits = 0;
        for (int s = 0; s < (1 << n); s++) if (f((ulong)s)) bits |= 1UL << s;
        return new TruthTable(n, bits);
    }

    public int AssignmentCount => 1 << N;
    public bool this[ulong assignment] => ((Bits >> (int)assignment) & 1UL) == 1UL;
    public bool Evaluate(ulong assignment) => this[assignment];

    public bool IsTrue => Bits == FullMask(N);
    public bool IsFalse => Bits == 0;
    public bool IsConstant => IsTrue || IsFalse;
    public int ModelCount => BitOperations.PopCount(Bits);

    public TruthTable And(TruthTable o) => new(Same(o), Bits & o.Bits);
    public TruthTable Or(TruthTable o) => new(Same(o), Bits | o.Bits);
    public TruthTable Not() => new(N, Bits ^ FullMask(N));

    private int Same(TruthTable o)
    {
        if (o.N != N) throw new ArgumentException($"tables over different n: {N} vs {o.N}");
        return N;
    }

    // ---- unateness and essential polarities (strategy 2.3) ---------------------------------

    /// <summary>Positions s with x_v = 0 (the lower half of every x_v-edge of the cube).</summary>
    private ulong LowMask(int v) => PositiveLiteralMask(N, v) ^ FullMask(N);

    /// <summary>f restricted to x_v = 0 and x_v = 1, both indexed by the positions with x_v = 0.</summary>
    private (ulong Low, ulong High) Halves(int v)
    {
        ulong low = LowMask(v);
        return (Bits & low, (Bits >> (1 << v)) & low);
    }

    /// <summary>f is non-decreasing in x_v (never 1 → 0 when x_v goes 0 → 1).</summary>
    public bool IsNonDecreasingIn(int v) { var (lo, hi) = Halves(v); return (lo & ~hi) == 0; }

    /// <summary>f is non-increasing in x_v.</summary>
    public bool IsNonIncreasingIn(int v) { var (lo, hi) = Halves(v); return (~lo & hi & LowMask(v)) == 0; }

    public bool DependsOn(int v) { var (lo, hi) = Halves(v); return lo != hi; }

    /// <summary>P_ess(f) = {x : f is not non-increasing in x} (strategy 2.3).</summary>
    public VarSet EssentialPositive
    {
        get
        {
            var s = VarSet.Empty;
            for (int v = 0; v < N; v++) if (!IsNonIncreasingIn(v)) s = s.Add(v);
            return s;
        }
    }

    /// <summary>N_ess(f) = {x : f is not non-decreasing in x} (strategy 2.3).</summary>
    public VarSet EssentialNegative
    {
        get
        {
            var s = VarSet.Empty;
            for (int v = 0; v < N; v++) if (!IsNonDecreasingIn(v)) s = s.Add(v);
            return s;
        }
    }

    /// <summary>Variables f depends on.</summary>
    public VarSet Support => EssentialPositive | EssentialNegative;

    public bool IsMonotone => EssentialNegative.IsEmpty;

    // ---- operations on tables ---------------------------------------------------------------

    /// <summary>Cofactor f|x_v = b, as a table over the same n variables (independent of x_v).</summary>
    public TruthTable Cofactor(int v, bool b)
    {
        var (lo, hi) = Halves(v);
        ulong half = b ? hi : lo;
        return new TruthTable(N, half | (half << (1 << v)));
    }

    /// <summary>∃x_v f.</summary>
    public TruthTable Forget(int v) => Cofactor(v, false).Or(Cofactor(v, true));

    /// <summary>f with variable x_v complemented for each v in <paramref name="flips"/>.</summary>
    public TruthTable FlipInputs(VarSet flips)
    {
        var self = this;
        ulong mask = flips.Bits & (ulong)((1 << N) - 1);
        return FromPredicate(N, s => self[s ^ mask]);
    }

    /// <summary>The table of g(x_0..x_{n-1}) = f(y) where y_{π(v)} = x_v, for a permutation given as an array.</summary>
    public TruthTable PermuteInputs(int[] perm)
    {
        if (perm.Length != N) throw new ArgumentException("permutation length must be n", nameof(perm));
        var self = this;
        int n = N;
        return FromPredicate(n, s =>
        {
            ulong t = 0;
            for (int v = 0; v < n; v++) if (((s >> v) & 1UL) == 1UL) t |= 1UL << perm[v];
            return self[t];
        });
    }

    /// <summary>The table seen over n' ≥ n variables, ignoring the extra ones.</summary>
    public TruthTable Extend(int n2)
    {
        CheckN(n2);
        if (n2 < N) throw new ArgumentException("cannot shrink", nameof(n2));
        var self = this;
        return FromPredicate(n2, s => self[s & (ulong)((1 << self.N) - 1)]);
    }

    // ---- text -------------------------------------------------------------------------------

    /// <summary>Hex with the full 2ⁿ bits, e.g. "0x8000" for x0∧x1∧x2∧x3.</summary>
    public string ToHex() => "0x" + Bits.ToString("x" + Math.Max(1, (1 << N) / 4));

    public static TruthTable ParseHex(int n, string hex)
    {
        CheckN(n);
        var s = hex.Trim();
        if (s.StartsWith("0x", StringComparison.OrdinalIgnoreCase)) s = s[2..];
        ulong bits = ulong.Parse(s, NumberStyles.HexNumber, CultureInfo.InvariantCulture);
        if ((bits & ~FullMask(n)) != 0) throw new FormatException($"table has bits beyond 2^{n}");
        return new TruthTable(n, bits);
    }

    /// <summary>Bit string f(0) f(1) … f(2ⁿ−1), as the Python oracles print tuples.</summary>
    public string ToBitString()
    {
        var chars = new char[1 << N];
        for (int s = 0; s < chars.Length; s++) chars[s] = this[(ulong)s] ? '1' : '0';
        return new string(chars);
    }

    public override string ToString() => $"tt(n={N}, {ToHex()})";
}
