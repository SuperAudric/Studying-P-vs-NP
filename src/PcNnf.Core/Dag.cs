using System.Text;

namespace PcNnf.Core;

/// <summary>
/// A PC-NNF / NNF circuit as in plan 2.1: a DAG of leaves (literal, ⊤, ⊥) and n-ary ∧/∨ gates
/// with shared children. Nodes are stored in topological order (every child index is smaller
/// than its parent's), and <see cref="Root"/> names the output node.
///
/// All measures and checks (size, gate counts, validity, polarity sets) range over every node
/// in the DAG, whether or not it is reachable from the root; <see cref="Reachable"/> prunes.
/// This matches the Python oracles, whose <c>valid(nodes)</c> inspects every node.
/// </summary>
public sealed class Dag
{
    private readonly List<Node> _nodes = new();
    private int _root = -1;

    public Dag() { }

    public int Count => _nodes.Count;
    public IReadOnlyList<Node> Nodes => _nodes;
    public Node this[int index] => _nodes[index];

    /// <summary>Index of the output node. Must be set before semantic queries.</summary>
    public int Root
    {
        get => _root >= 0 ? _root : throw new InvalidOperationException("root not set");
        set
        {
            if (value < 0 || value >= _nodes.Count) throw new ArgumentOutOfRangeException(nameof(value));
            _root = value;
        }
    }

    public bool HasRoot => _root >= 0;

    // ---- construction --------------------------------------------------------------------

    public int AddTrue() => Add(new Node(NodeKind.True, -1, true, Array.Empty<int>()));
    public int AddFalse() => Add(new Node(NodeKind.False, -1, true, Array.Empty<int>()));

    public int AddLiteral(int variable, bool positive)
    {
        if (variable < 0 || variable >= VarSet.MaxVariables)
            throw new ArgumentOutOfRangeException(nameof(variable));
        return Add(new Node(NodeKind.Literal, variable, positive, Array.Empty<int>()));
    }

    public int AddAnd(params int[] children) => AddGate(NodeKind.And, children);
    public int AddOr(params int[] children) => AddGate(NodeKind.Or, children);
    public int AddAnd(IEnumerable<int> children) => AddGate(NodeKind.And, children.ToArray());
    public int AddOr(IEnumerable<int> children) => AddGate(NodeKind.Or, children.ToArray());

    public int AddGate(NodeKind kind, int[] children)
    {
        if (kind != NodeKind.And && kind != NodeKind.Or) throw new ArgumentException("gate kind must be And or Or", nameof(kind));
        if (children.Length == 0) throw new ArgumentException("a gate needs at least one child (plan 2.1, k ≥ 1)", nameof(children));
        foreach (var c in children)
            if (c < 0 || c >= _nodes.Count)
                throw new ArgumentOutOfRangeException(nameof(children), $"child {c} is not an earlier node (have {_nodes.Count})");
        return Add(new Node(kind, -1, true, (int[])children.Clone()));
    }

    private int Add(Node node)
    {
        _nodes.Add(node);
        return _nodes.Count - 1;
    }

    // ---- measures (plan 2.1) -------------------------------------------------------------

    public int NodeCount => _nodes.Count;

    /// <summary>Number of parent→child references.</summary>
    public int ReferenceCount => _nodes.Sum(n => n.Children.Count);

    /// <summary>Plan 2.1 size: nodes plus parent→child references.</summary>
    public int Size => NodeCount + ReferenceCount;

    /// <summary>Number of ∧/∨ nodes as stored (n-ary gates).</summary>
    public int NaryGateCount => _nodes.Count(n => n.IsGate);

    /// <summary>Fan-in-2 gate count: a gate with k children counts as k−1 binary gates (plan 3.2).</summary>
    public int BinaryGateCount => _nodes.Where(n => n.IsGate).Sum(n => n.Children.Count - 1);

    /// <summary>Number of distinct variables mentioned by literal leaves.</summary>
    public VarSet Variables
    {
        get
        {
            var s = VarSet.Empty;
            foreach (var n in _nodes) if (n.Kind == NodeKind.Literal) s = s.Add(n.Variable);
            return s;
        }
    }

    // ---- polarity sets and validity (plan 2.1) ---------------------------------------------

    /// <summary>vars⁺ and vars⁻ of every node, computed in one bottom-up pass over the DAG.</summary>
    public (VarSet[] Positive, VarSet[] Negative) PolaritySets()
    {
        var pos = new VarSet[_nodes.Count];
        var neg = new VarSet[_nodes.Count];
        for (int i = 0; i < _nodes.Count; i++)
        {
            var n = _nodes[i];
            switch (n.Kind)
            {
                case NodeKind.Literal:
                    if (n.Positive) pos[i] = VarSet.Single(n.Variable); else neg[i] = VarSet.Single(n.Variable);
                    break;
                case NodeKind.And:
                case NodeKind.Or:
                    foreach (var c in n.Children) { pos[i] |= pos[c]; neg[i] |= neg[c]; }
                    break;
            }
        }
        return (pos, neg);
    }

    public VarSet VarsPositive => PolaritySets().Positive[Root];
    public VarSet VarsNegative => PolaritySets().Negative[Root];

    /// <summary>
    /// Polarity consistency: for every ∧-node and every pair of distinct children C_i, C_j,
    /// vars⁺(C_i) ∩ vars⁻(C_j) = ∅. Returns the index of the first violating ∧-node, or -1.
    /// </summary>
    public int FindViolation()
    {
        var (pos, neg) = PolaritySets();
        for (int i = 0; i < _nodes.Count; i++)
        {
            var n = _nodes[i];
            if (n.Kind != NodeKind.And || n.Children.Count < 2) continue;
            // negOthers[j] = union of vars⁻ over children other than j, via prefix and suffix unions
            int k = n.Children.Count;
            var suffix = new VarSet[k + 1];
            for (int j = k - 1; j >= 0; j--) suffix[j] = suffix[j + 1] | neg[n.Children[j]];
            var prefix = VarSet.Empty;
            for (int j = 0; j < k; j++)
            {
                int c = n.Children[j];
                if (pos[c].Intersects(prefix | suffix[j + 1])) return i;
                prefix |= neg[c];
            }
        }
        return -1;
    }

    public bool IsValid() => FindViolation() < 0;

    // ---- semantics --------------------------------------------------------------------------

    /// <summary>Evaluate every node under a total assignment given as a bitmask (bit v = value of x_v).</summary>
    public bool[] EvaluateAll(ulong assignment)
    {
        var val = new bool[_nodes.Count];
        for (int i = 0; i < _nodes.Count; i++)
        {
            var n = _nodes[i];
            val[i] = n.Kind switch
            {
                NodeKind.True => true,
                NodeKind.False => false,
                NodeKind.Literal => ((assignment >> n.Variable) & 1UL) == 1UL == n.Positive,
                NodeKind.And => n.Children.All(c => val[c]),
                NodeKind.Or => n.Children.Any(c => val[c]),
                _ => throw new InvalidOperationException(),
            };
        }
        return val;
    }

    public bool Evaluate(ulong assignment) => EvaluateAll(assignment)[Root];

    /// <summary>Truth table of the root over variables 0..n-1 (n ≤ 6), one bit per assignment.</summary>
    public TruthTable TruthTable(int n)
    {
        var tables = TruthTablesOfAllNodes(n);
        return tables[Root];
    }

    /// <summary>Truth tables of every node, computed bitwise-parallel (one ulong per node).</summary>
    public TruthTable[] TruthTablesOfAllNodes(int n)
    {
        var t = new TruthTable[_nodes.Count];
        for (int i = 0; i < _nodes.Count; i++)
        {
            var node = _nodes[i];
            switch (node.Kind)
            {
                case NodeKind.True: t[i] = Core.TruthTable.True(n); break;
                case NodeKind.False: t[i] = Core.TruthTable.False(n); break;
                case NodeKind.Literal:
                    if (node.Variable >= n) throw new ArgumentException($"literal over x{node.Variable} but n = {n}", nameof(n));
                    t[i] = Core.TruthTable.Literal(n, node.Variable, node.Positive);
                    break;
                case NodeKind.And:
                    t[i] = Core.TruthTable.True(n);
                    foreach (var c in node.Children) t[i] = t[i].And(t[c]);
                    break;
                case NodeKind.Or:
                    t[i] = Core.TruthTable.False(n);
                    foreach (var c in node.Children) t[i] = t[i].Or(t[c]);
                    break;
            }
        }
        return t;
    }

    // ---- the bottom-up pass and Lemma W (plan 2.2) ------------------------------------------

    /// <summary>
    /// The bottom-up pass: sat(⊥)=0, sat(⊤)=1, sat(literal)=1, sat(∨)=OR, sat(∧)=AND, for every
    /// node. For a valid DAG, sat(root) is satisfiability (Theorem A).
    /// </summary>
    public bool[] BottomUp()
    {
        var sat = new bool[_nodes.Count];
        for (int i = 0; i < _nodes.Count; i++)
        {
            var n = _nodes[i];
            sat[i] = n.Kind switch
            {
                NodeKind.True => true,
                NodeKind.False => false,
                NodeKind.Literal => true,
                NodeKind.And => n.Children.All(c => sat[c]),
                NodeKind.Or => n.Children.Any(c => sat[c]),
                _ => throw new InvalidOperationException(),
            };
        }
        return sat;
    }

    public bool Sat() => BottomUp()[Root];

    /// <summary>
    /// Lemma W: after the bottom-up pass, walk top-down from the root keeping one sat child at
    /// each ∨-node (the first, as the oracle does) and all children at each ∧-node, visiting
    /// each node once; return the literal leaves reached. Null if sat(root) = 0.
    /// For a valid DAG the result is consistent and every extension is a model.
    /// </summary>
    public Witness? ExtractWitness()
    {
        var sat = BottomUp();
        if (!sat[Root]) return null;
        var seen = new bool[_nodes.Count];
        var pos = VarSet.Empty;
        var neg = VarSet.Empty;
        var stack = new Stack<int>();
        stack.Push(Root);
        while (stack.Count > 0)
        {
            int i = stack.Pop();
            if (seen[i]) continue;
            seen[i] = true;
            var n = _nodes[i];
            if (!sat[i]) throw new InvalidOperationException($"witness walk reached node {i} with sat = 0");
            switch (n.Kind)
            {
                case NodeKind.Literal:
                    if (n.Positive) pos = pos.Add(n.Variable); else neg = neg.Add(n.Variable);
                    break;
                case NodeKind.And:
                    // push in reverse so children are visited in order
                    for (int j = n.Children.Count - 1; j >= 0; j--) stack.Push(n.Children[j]);
                    break;
                case NodeKind.Or:
                    stack.Push(n.Children.First(c => sat[c]));
                    break;
            }
        }
        return new Witness(pos, neg);
    }

    // ---- transformations (plan 2.3) ---------------------------------------------------------

    /// <summary>
    /// Substitute literal leaves: <paramref name="replace"/> returns null to keep a literal,
    /// or true/false to replace it by ⊤/⊥. Gates and constants are copied unchanged, so size
    /// never grows and validity is preserved.
    /// </summary>
    public Dag SubstituteLiterals(Func<int, bool, bool?> replace)
    {
        var d = new Dag();
        foreach (var n in _nodes)
        {
            switch (n.Kind)
            {
                case NodeKind.Literal:
                    var r = replace(n.Variable, n.Positive);
                    if (r is null) d.AddLiteral(n.Variable, n.Positive);
                    else if (r.Value) d.AddTrue();
                    else d.AddFalse();
                    break;
                case NodeKind.True: d.AddTrue(); break;
                case NodeKind.False: d.AddFalse(); break;
                default: d.AddGate(n.Kind, n.Children.ToArray()); break;
            }
        }
        if (HasRoot) d.Root = Root;
        return d;
    }

    /// <summary>Conditioning F|ρ: literals over dom(ρ) become ⊤ or ⊥ according to ρ.</summary>
    public Dag Condition(VarSet domain, ulong values) =>
        SubstituteLiterals((v, positive) => domain.Contains(v) ? (((values >> v) & 1UL) == 1UL) == positive : null);

    /// <summary>Forgetting ∃X F: both literals of each x ∈ X become ⊤ (exact for valid F).</summary>
    public Dag Forget(VarSet variables) =>
        SubstituteLiterals((v, _) => variables.Contains(v) ? true : null);

    /// <summary>Polarity renaming: swap x ↔ ¬x for every x in <paramref name="flips"/>.</summary>
    public Dag Rename(VarSet flips)
    {
        var d = new Dag();
        foreach (var n in _nodes)
        {
            switch (n.Kind)
            {
                case NodeKind.Literal: d.AddLiteral(n.Variable, flips.Contains(n.Variable) ? !n.Positive : n.Positive); break;
                case NodeKind.True: d.AddTrue(); break;
                case NodeKind.False: d.AddFalse(); break;
                default: d.AddGate(n.Kind, n.Children.ToArray()); break;
            }
        }
        if (HasRoot) d.Root = Root;
        return d;
    }

    /// <summary>
    /// Constant simplification on the reachable part: ⊤ in ∧ and ⊥ in ∨ are dropped, ⊥ in ∧ and
    /// ⊤ in ∨ collapse the gate, duplicate references are merged, and a one-child gate becomes
    /// its child. Only removes occurrences, so validity is preserved and size does not grow.
    /// The result contains only nodes reachable from the root.
    /// </summary>
    public Dag Simplify()
    {
        var d = new Dag();
        var map = new int[_nodes.Count];
        Array.Fill(map, -1);
        var order = ReachableIndices();
        foreach (var i in order)
        {
            var n = _nodes[i];
            switch (n.Kind)
            {
                case NodeKind.True: map[i] = d.AddTrue(); break;
                case NodeKind.False: map[i] = d.AddFalse(); break;
                case NodeKind.Literal: map[i] = d.AddLiteral(n.Variable, n.Positive); break;
                default:
                    var absorb = n.Kind == NodeKind.And ? NodeKind.False : NodeKind.True;
                    var neutral = n.Kind == NodeKind.And ? NodeKind.True : NodeKind.False;
                    var kids = n.Children.Select(c => map[c]).ToList();
                    if (kids.Any(k => d[k].Kind == absorb))
                    {
                        map[i] = absorb == NodeKind.False ? d.AddFalse() : d.AddTrue();
                        break;
                    }
                    kids = kids.Where(k => d[k].Kind != neutral).Distinct().ToList();
                    if (kids.Count == 0) map[i] = neutral == NodeKind.True ? d.AddTrue() : d.AddFalse();
                    else if (kids.Count == 1) map[i] = kids[0];
                    else map[i] = d.AddGate(n.Kind, kids.ToArray());
                    break;
            }
        }
        d.Root = map[Root];
        return d.Reachable();
    }

    /// <summary>
    /// Merge a gate into its parent when both have the same kind and the child has exactly one
    /// parent. Turns a binary tree into its n-ary form without changing the function, validity
    /// (vars± of the merged node are unions of the children's) or sharing.
    /// </summary>
    public Dag Flatten()
    {
        var parents = new int[_nodes.Count];
        foreach (var n in _nodes) foreach (var c in n.Children) parents[c]++;
        var d = new Dag();
        var map = new int[_nodes.Count];
        var flattenedChildren = new int[_nodes.Count][];
        Array.Fill(map, -1);
        foreach (var i in ReachableIndices())
        {
            var n = _nodes[i];
            if (n.IsLeaf)
            {
                map[i] = n.Kind switch
                {
                    NodeKind.True => d.AddTrue(),
                    NodeKind.False => d.AddFalse(),
                    _ => d.AddLiteral(n.Variable, n.Positive),
                };
                continue;
            }
            var kids = new List<int>();
            foreach (var c in n.Children)
            {
                if (_nodes[c].Kind == n.Kind && parents[c] == 1) kids.AddRange(flattenedChildren[c]);
                else kids.Add(map[c]);
            }
            flattenedChildren[i] = kids.ToArray();
            map[i] = d.AddGate(n.Kind, flattenedChildren[i]);
        }
        d.Root = map[Root];
        // Merged nodes were still emitted; drop the ones no longer referenced.
        return d.Reachable();
    }

    /// <summary>The sub-DAG reachable from the root, re-indexed in topological order.</summary>
    public Dag Reachable()
    {
        var d = new Dag();
        var map = new int[_nodes.Count];
        Array.Fill(map, -1);
        foreach (var i in ReachableIndices())
        {
            var n = _nodes[i];
            map[i] = n.Kind switch
            {
                NodeKind.True => d.AddTrue(),
                NodeKind.False => d.AddFalse(),
                NodeKind.Literal => d.AddLiteral(n.Variable, n.Positive),
                _ => d.AddGate(n.Kind, n.Children.Select(c => map[c]).ToArray()),
            };
        }
        d.Root = map[Root];
        return d;
    }

    /// <summary>Indices reachable from the root, in increasing (topological) order.</summary>
    public IReadOnlyList<int> ReachableIndices()
    {
        var seen = new bool[_nodes.Count];
        var stack = new Stack<int>();
        stack.Push(Root);
        while (stack.Count > 0)
        {
            int i = stack.Pop();
            if (seen[i]) continue;
            seen[i] = true;
            foreach (var c in _nodes[i].Children) stack.Push(c);
        }
        var list = new List<int>();
        for (int i = 0; i < seen.Length; i++) if (seen[i]) list.Add(i);
        return list;
    }

    // ---- display ----------------------------------------------------------------------------

    /// <summary>Infix rendering of the root's unfolded tree, e.g. <c>(x0 ∧ (¬x1 ∨ x2))</c>.</summary>
    public string ToFormulaString()
    {
        var sb = new StringBuilder();
        Render(Root, sb);
        return sb.ToString();
    }

    private void Render(int i, StringBuilder sb)
    {
        var n = _nodes[i];
        switch (n.Kind)
        {
            case NodeKind.True: sb.Append('⊤'); break;
            case NodeKind.False: sb.Append('⊥'); break;
            case NodeKind.Literal: sb.Append(n.Positive ? "x" : "¬x").Append(n.Variable); break;
            default:
                sb.Append('(');
                for (int j = 0; j < n.Children.Count; j++)
                {
                    if (j > 0) sb.Append(n.Kind == NodeKind.And ? " ∧ " : " ∨ ");
                    Render(n.Children[j], sb);
                }
                sb.Append(')');
                break;
        }
    }
}

/// <summary>The literal set reached by the Lemma W walk, as positive and negative variable sets.</summary>
public readonly record struct Witness(VarSet Positive, VarSet Negative)
{
    /// <summary>No variable occurs with both polarities (Lemma W guarantees this for valid F).</summary>
    public bool IsConsistent => !Positive.Intersects(Negative);

    /// <summary>Does the total assignment (bitmask) extend this literal set?</summary>
    public bool Extends(ulong assignment) =>
        (assignment & Positive.Bits) == Positive.Bits && (assignment & Negative.Bits) == 0;
}
