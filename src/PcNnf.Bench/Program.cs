using System.Diagnostics;
using PcNnf.Core;
using PcNnf.Enum;

namespace PcNnf.Bench;

/// <summary>
/// Command line for the research harness (strategy 4.4). Every number printed names its
/// measure; everything from Enum is a tree minimum and therefore an upper bound on m.
/// </summary>
public static class Program
{
    private const string Usage = """
        usage:
          pcnnf enum --n N --rule pc|nnf|mono [--max-gates K] [--data DIR] [--no-write]
              Build the size-stratified dictionary (minimum fan-in-2 tree gates per function),
              print the level counts and the maximum, write data/enum-nN-RULE.bin (n ≤ 4).
              With --rule pc at n ≤ 4 the NNF dictionary is built too and the gap report
              (k_pc − k_nnf histogram, maximum-gap NP classes) is printed.
              n ≥ 5 requires --max-gates ≤ 8 and produces a size-capped shell.
          pcnnf clique-table --n N
              Tree minima of the fixed-graph clique formulas φ_{G,k} for every graph on
              1..N vertices up to isomorphism and every k (status: upper bound on m).
          pcnnf tabulate --cnf FILE [--aux VARS]
              Forget the auxiliary variables (e.g. "5,6,9-20") of a DIMACS CNF and tabulate
              the function over the remaining ≤ 6 variables.
        """;

    public static int Main(string[] args)
    {
        try
        {
            if (args.Length == 0 || args[0] is "-h" or "--help" or "help") { Console.WriteLine(Usage); return 0; }
            var opts = ParseOptions(args.Skip(1));
            switch (args[0])
            {
                case "enum": return RunEnum(opts);
                case "clique-table": return RunCliqueTable(opts);
                case "tabulate": return RunTabulate(opts);
                default:
                    Console.Error.WriteLine($"unknown command '{args[0]}'\n{Usage}");
                    return 2;
            }
        }
        catch (Exception ex) when (ex is ArgumentException or FormatException or InvalidOperationException or IOException)
        {
            Console.Error.WriteLine("error: " + ex.Message);
            return 1;
        }
    }

    // ---- enum ---------------------------------------------------------------------------------

    private static int RunEnum(Dictionary<string, string> o)
    {
        int n = int.Parse(Req(o, "n"));
        var rule = RuleExtensions.Parse(Req(o, "rule"));
        int maxGates = o.TryGetValue("max-gates", out var mg) ? int.Parse(mg) : (n >= 5 ? 6 : 40);
        string dataDir = o.TryGetValue("data", out var dd) ? dd : "data";
        bool write = !o.ContainsKey("no-write");

        var d = BuildWithLog(n, rule, maxGates);
        if (write && n <= 4)
        {
            var path = TableFile.DefaultPath(dataDir, n, rule);
            TableFile.Write(d, path);
            Console.WriteLine($"  wrote {path} ({new FileInfo(path).Length:N0} bytes, flat arrays indexed by truth table)");
        }

        if (rule == Rule.Pc && n <= 4)
        {
            Console.WriteLine();
            var nnf = BuildWithLog(n, Rule.Nnf, maxGates);
            Console.WriteLine();
            Console.Write(new GapReport(d, nnf).Render());
        }
        return 0;
    }

    private static TreeDictionary BuildWithLog(int n, Rule rule, int maxGates)
    {
        Console.WriteLine($"== enum: n={n}, rule={rule.Name()}, cap {maxGates} gates [measure: fan-in-2 gates, tree minima, keyed on truth table] ==");
        var d = TreeDictionary.Build(n, rule, maxGates, Console.WriteLine);
        Console.WriteLine($"  time {d.BuildTime.TotalSeconds:F2}s; entries per level (gates 0..{d.MaxGates}): {string.Join(" ", d.LevelCounts)}");
        Console.WriteLine($"  total entries {d.Count:N0}; functions reached {d.Reached:N0}{(d.TargetCount is long t ? $" of {t:N0}" : "")}; max {d.MaxGates} gates{(d.Capped ? " (capped: shell only)" : "")}");
        Console.WriteLine(rule == Rule.Nnf
            ? $"  stored minimal trees whose (vars⁺, vars⁻) differ from the essential polarities: {d.PolarityMismatches} (no assertion under nnf)"
            : $"  asserted: every stored minimal tree has exactly the essential polarity sets (Corollary E1); mismatches {d.PolarityMismatches}");
        return d;
    }

    // ---- clique-table -------------------------------------------------------------------------

    private static int RunCliqueTable(Dictionary<string, string> o)
    {
        int n = int.Parse(Req(o, "n"));
        if (n < 1 || n > 4) throw new ArgumentException("clique-table covers n = 1..4 in this run (tree measure)");
        Console.WriteLine($"== fixed-graph clique formulas φ_(G,k), all graphs on 1..{n} vertices up to isomorphism, all k ==");
        Console.WriteLine("   measure: tree minima from Enum; every row is an upper bound on m(φ_{G,k}) (status 'upper'); DAG minima need PcNnf.Exact");
        var sw = Stopwatch.StartNew();
        var rows = new List<CliqueTable.Row>();
        for (int m = 1; m <= n; m++)
        {
            var pc = TreeDictionary.Build(m, Rule.Pc);
            var nnf = TreeDictionary.Build(m, Rule.Nnf);
            rows.AddRange(CliqueTable.Rows(pc, nnf));
        }
        Console.Write(CliqueTable.Render(rows));
        Console.WriteLine($"   {rows.Count} rows ({rows.Count(r => !r.IsConstant)} non-constant), {sw.Elapsed.TotalSeconds:F2}s including dictionary builds");
        return 0;
    }

    // ---- tabulate -----------------------------------------------------------------------------

    private static int RunTabulate(Dictionary<string, string> o)
    {
        var path = Req(o, "cnf");
        var aux = Cnf.ParseVariableList(o.TryGetValue("aux", out var a) ? a : "");
        var cnf = Cnf.ReadDimacs(path);
        var (tt, map) = cnf.Tabulate(aux);
        Console.WriteLine($"== tabulate: {path}, {cnf.VariableCount} variables, {cnf.Clauses.Count} clauses, {aux.Count} auxiliary forgotten ==");
        Console.WriteLine($"  non-auxiliary variables (DIMACS) → table positions: {string.Join(" ", map.Select((v, i) => $"{v}→x{i}"))}");
        Console.WriteLine($"  n = {tt.N}; truth table {tt.ToHex()} (bits f(0..2^n−1), assignment bit i = x_i): {tt.ToBitString()}");
        Console.WriteLine($"  models {tt.ModelCount} of {tt.AssignmentCount}; P_ess = {tt.EssentialPositive}, N_ess = {tt.EssentialNegative}; {(tt.IsMonotone ? "monotone" : "not monotone")}");
        if (tt.N <= 4 && !tt.IsConstant)
        {
            var pc = TreeDictionary.Build(tt.N, Rule.Pc);
            var nnf = TreeDictionary.Build(tt.N, Rule.Nnf);
            var tree = pc.Reconstruct(tt);
            Console.WriteLine($"  tree minima [fan-in-2 gates, upper bound on m]: k_pc = {pc.Gates(tt)}, k_nnf = {nnf.Gates(tt)}; plan-2.1 size of the pc tree {tree.Size}");
            Console.WriteLine($"  minimal pc tree: {tree.ToFormulaString()}");
        }
        return 0;
    }

    // ---- helpers ------------------------------------------------------------------------------

    private static Dictionary<string, string> ParseOptions(IEnumerable<string> args)
    {
        var o = new Dictionary<string, string>();
        var list = args.ToList();
        for (int i = 0; i < list.Count; i++)
        {
            if (!list[i].StartsWith("--")) throw new ArgumentException($"unexpected argument '{list[i]}'");
            var key = list[i][2..];
            if (i + 1 < list.Count && !list[i + 1].StartsWith("--")) o[key] = list[++i];
            else o[key] = "";
        }
        return o;
    }

    private static string Req(Dictionary<string, string> o, string key) =>
        o.TryGetValue(key, out var v) && v.Length > 0 ? v : throw new ArgumentException($"--{key} is required");
}
