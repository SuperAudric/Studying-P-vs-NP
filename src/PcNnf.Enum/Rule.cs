namespace PcNnf.Enum;

/// <summary>Which trees the dictionary enumerates (strategy 4.2).</summary>
public enum Rule
{
    /// <summary>Valid PC-NNF trees: ∧ only over operands with no clashing polarity (plan 2.1).</summary>
    Pc,

    /// <summary>Unrestricted NNF trees.</summary>
    Nnf,

    /// <summary>Monotone trees: positive literal leaves only (no rule needed; for H8 and Theorem B checks).</summary>
    Mono,
}

public static class RuleExtensions
{
    public static Rule Parse(string s) => s.ToLowerInvariant() switch
    {
        "pc" => Rule.Pc,
        "nnf" => Rule.Nnf,
        "mono" => Rule.Mono,
        _ => throw new ArgumentException($"unknown rule '{s}'; expected pc, nnf or mono"),
    };

    public static string Name(this Rule r) => r switch { Rule.Pc => "pc", Rule.Nnf => "nnf", Rule.Mono => "mono", _ => throw new ArgumentOutOfRangeException() };
}
