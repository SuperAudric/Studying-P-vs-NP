namespace PcNnf.Core;

public enum NodeKind : byte
{
    True,
    False,
    Literal,
    And,
    Or,
}

/// <summary>
/// One node of a <see cref="Dag"/>: a leaf (⊤, ⊥, or a literal) or an n-ary ∧/∨ gate whose
/// children are indices of earlier nodes in the same DAG (plan 2.1).
/// </summary>
public sealed class Node
{
    internal Node(NodeKind kind, int variable, bool positive, int[] children)
    {
        Kind = kind;
        Variable = variable;
        Positive = positive;
        Children = children;
    }

    public NodeKind Kind { get; }

    /// <summary>Variable index for a literal; -1 otherwise.</summary>
    public int Variable { get; }

    /// <summary>Polarity for a literal; true for anything else.</summary>
    public bool Positive { get; }

    /// <summary>Child indices for a gate; empty for a leaf.</summary>
    public IReadOnlyList<int> Children { get; }

    public bool IsLeaf => Kind != NodeKind.And && Kind != NodeKind.Or;
    public bool IsGate => !IsLeaf;
    public bool IsConstant => Kind == NodeKind.True || Kind == NodeKind.False;

    public override string ToString() => Kind switch
    {
        NodeKind.True => "T",
        NodeKind.False => "F",
        NodeKind.Literal => (Positive ? "x" : "~x") + Variable,
        NodeKind.And => "and(" + string.Join(",", Children) + ")",
        NodeKind.Or => "or(" + string.Join(",", Children) + ")",
        _ => throw new InvalidOperationException(),
    };
}
