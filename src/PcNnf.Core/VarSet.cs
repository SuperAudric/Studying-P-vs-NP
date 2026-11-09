using System.Collections;
using System.Numerics;

namespace PcNnf.Core;

/// <summary>
/// A set of variables indexed 0..63, stored as one 64-bit mask. Used for vars⁺/vars⁻ (plan 2.1),
/// essential polarity sets (strategy 2.3), and partial-assignment domains.
/// </summary>
public readonly record struct VarSet(ulong Bits) : IEnumerable<int>
{
    public const int MaxVariables = 64;

    public static readonly VarSet Empty = new(0UL);

    public static VarSet Of(params int[] vars)
    {
        ulong bits = 0;
        foreach (var v in vars) bits |= Bit(v);
        return new VarSet(bits);
    }

    public static VarSet Single(int v) => new(Bit(v));

    /// <summary>All variables 0..n-1.</summary>
    public static VarSet Range(int n) => new(n == 64 ? ulong.MaxValue : (1UL << n) - 1);

    private static ulong Bit(int v)
    {
        if (v < 0 || v >= MaxVariables)
            throw new ArgumentOutOfRangeException(nameof(v), $"variable index {v} outside 0..{MaxVariables - 1}");
        return 1UL << v;
    }

    public bool Contains(int v) => v >= 0 && v < MaxVariables && (Bits & (1UL << v)) != 0;
    public bool IsEmpty => Bits == 0;
    public int Count => BitOperations.PopCount(Bits);

    public VarSet Add(int v) => new(Bits | Bit(v));
    public VarSet Remove(int v) => new(Bits & ~Bit(v));
    public VarSet Union(VarSet o) => new(Bits | o.Bits);
    public VarSet Intersect(VarSet o) => new(Bits & o.Bits);
    public VarSet Except(VarSet o) => new(Bits & ~o.Bits);
    public bool Intersects(VarSet o) => (Bits & o.Bits) != 0;
    public bool IsSubsetOf(VarSet o) => (Bits & ~o.Bits) == 0;

    public static VarSet operator |(VarSet a, VarSet b) => a.Union(b);
    public static VarSet operator &(VarSet a, VarSet b) => a.Intersect(b);

    public IEnumerator<int> GetEnumerator()
    {
        ulong rest = Bits;
        while (rest != 0)
        {
            int v = BitOperations.TrailingZeroCount(rest);
            yield return v;
            rest &= rest - 1;
        }
    }

    IEnumerator IEnumerable.GetEnumerator() => GetEnumerator();

    public override string ToString() => "{" + string.Join(",", this.Select(v => "x" + v)) + "}";
}
