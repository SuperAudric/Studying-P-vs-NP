namespace PcNnf.Core;

/// <summary>
/// A CNF in DIMACS conventions (variables 1..m, literals ±v). Used only as an input format: the
/// object measured is the Boolean function over the non-auxiliary variables, obtained by
/// forgetting the auxiliaries (∃) and tabulating (plan 6.2).
/// </summary>
public sealed class Cnf
{
    public Cnf(int variableCount, IReadOnlyList<int[]> clauses)
    {
        if (variableCount < 0) throw new ArgumentOutOfRangeException(nameof(variableCount));
        foreach (var c in clauses)
            foreach (var l in c)
                if (l == 0 || Math.Abs(l) > variableCount)
                    throw new ArgumentException($"literal {l} outside 1..{variableCount}", nameof(clauses));
        VariableCount = variableCount;
        Clauses = clauses;
    }

    public int VariableCount { get; }
    public IReadOnlyList<int[]> Clauses { get; }

    // ---- DIMACS -----------------------------------------------------------------------------

    public static Cnf ReadDimacs(string path)
    {
        using var r = new StreamReader(path);
        return ReadDimacs(r);
    }

    public static Cnf ReadDimacs(TextReader reader)
    {
        int declaredVars = -1;
        var clauses = new List<int[]>();
        var current = new List<int>();
        int maxVar = 0;
        string? line;
        while ((line = reader.ReadLine()) != null)
        {
            var t = line.Trim();
            if (t.Length == 0 || t[0] == 'c' || t[0] == '%') continue;
            if (t[0] == 'p')
            {
                var parts = t.Split(' ', StringSplitOptions.RemoveEmptyEntries);
                if (parts.Length < 4 || parts[1] != "cnf") throw new FormatException("bad problem line: " + line);
                declaredVars = int.Parse(parts[2]);
                continue;
            }
            foreach (var tok in t.Split(' ', StringSplitOptions.RemoveEmptyEntries))
            {
                int l = int.Parse(tok);
                if (l == 0)
                {
                    clauses.Add(current.ToArray());
                    current.Clear();
                }
                else
                {
                    current.Add(l);
                    maxVar = Math.Max(maxVar, Math.Abs(l));
                }
            }
        }
        if (current.Count > 0) clauses.Add(current.ToArray()); // tolerate a missing final 0
        int n = declaredVars >= 0 ? Math.Max(declaredVars, maxVar) : maxVar;
        return new Cnf(n, clauses);
    }

    // ---- a tiny DPLL for the existential projection -----------------------------------------

    /// <summary>
    /// Is the CNF satisfiable under the given assumptions (literals forced true)? Unit
    /// propagation plus branching, enough for the sizes this harness tabulates (every
    /// Tseitin encoding with all inputs fixed is decided by propagation alone).
    /// </summary>
    public bool IsSatisfiable(IEnumerable<int> assumptions)
    {
        var value = new sbyte[VariableCount + 1]; // 0 unknown, +1 true, -1 false
        foreach (var l in assumptions)
        {
            int v = Math.Abs(l);
            sbyte want = (sbyte)(l > 0 ? 1 : -1);
            if (value[v] == -want) return false;
            value[v] = want;
        }
        return Solve(value);
    }

    private bool Solve(sbyte[] value)
    {
        // unit propagation to fixpoint
        bool changed = true;
        while (changed)
        {
            changed = false;
            foreach (var clause in Clauses)
            {
                int unassigned = 0, unit = 0;
                bool satisfied = false;
                foreach (var l in clause)
                {
                    var val = value[Math.Abs(l)];
                    if (val == 0) { unassigned++; unit = l; }
                    else if ((val > 0) == (l > 0)) { satisfied = true; break; }
                }
                if (satisfied) continue;
                if (unassigned == 0) return false;
                if (unassigned == 1)
                {
                    value[Math.Abs(unit)] = (sbyte)(unit > 0 ? 1 : -1);
                    changed = true;
                }
            }
        }
        // branch on the first unassigned variable that still matters
        for (int v = 1; v <= VariableCount; v++)
        {
            if (value[v] != 0) continue;
            var copy = (sbyte[])value.Clone();
            copy[v] = 1;
            if (Solve(copy)) return true;
            copy = (sbyte[])value.Clone();
            copy[v] = -1;
            return Solve(copy);
        }
        return true; // every clause satisfied
    }

    // ---- projection and tabulation ----------------------------------------------------------

    /// <summary>
    /// Forget the auxiliary variables and tabulate the rest: the result is the function
    /// g(x) = ∃aux. CNF(x, aux) over the non-auxiliary variables, which are sorted ascending and
    /// mapped to table positions 0..n−1 (the map is returned). Refuses n > 6.
    /// </summary>
    public (TruthTable Table, int[] VariableMap) Tabulate(IReadOnlySet<int> auxiliaries)
    {
        foreach (var a in auxiliaries)
            if (a < 1 || a > VariableCount)
                throw new ArgumentException($"auxiliary variable {a} outside 1..{VariableCount}", nameof(auxiliaries));
        var kept = Enumerable.Range(1, VariableCount).Where(v => !auxiliaries.Contains(v)).ToArray();
        if (kept.Length > TruthTable.MaxVariables)
            throw new InvalidOperationException(
                $"{kept.Length} non-auxiliary variables ({string.Join(",", kept)}); at most {TruthTable.MaxVariables} can be tabulated. Declare more auxiliaries.");
        int n = kept.Length;
        ulong bits = 0;
        for (int s = 0; s < (1 << n); s++)
        {
            var assumptions = new int[n];
            for (int i = 0; i < n; i++) assumptions[i] = ((s >> i) & 1) == 1 ? kept[i] : -kept[i];
            if (IsSatisfiable(assumptions)) bits |= 1UL << s;
        }
        return (new TruthTable(n, bits), kept);
    }

    /// <summary>Parse an auxiliary-variable list such as "5,6,8-12".</summary>
    public static HashSet<int> ParseVariableList(string text)
    {
        var set = new HashSet<int>();
        if (string.IsNullOrWhiteSpace(text)) return set;
        foreach (var part in text.Split(new[] { ',', ' ' }, StringSplitOptions.RemoveEmptyEntries))
        {
            var dash = part.IndexOf('-', 1);
            if (dash > 0)
            {
                int lo = int.Parse(part[..dash]), hi = int.Parse(part[(dash + 1)..]);
                if (hi < lo) throw new FormatException("bad range " + part);
                for (int v = lo; v <= hi; v++) set.Add(v);
            }
            else set.Add(int.Parse(part));
        }
        return set;
    }
}
