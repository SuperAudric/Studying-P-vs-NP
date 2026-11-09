using System.Globalization;

namespace PcNnf.Core;

/// <summary>
/// Text interchange format shared with the Python oracles (scripts/pcnnf_io.py). It is a
/// line-per-node rendering of the oracle node format
/// <c>('lit', var, pos) | ('T',) | ('F',) | ('and', [ids]) | ('or', [ids])</c> with a root index:
/// <code>
/// pcnnf 1
/// n 4
/// root 5
/// 0 lit 0 1
/// 1 lit 1 0
/// 2 T
/// 3 F
/// 4 and 0 1
/// 5 or 4 2
/// </code>
/// Node ids are consecutive from 0 and every child id is smaller than its node's id.
/// </summary>
public static class Interchange
{
    public const int Version = 1;

    public static string Write(Dag dag, int n)
    {
        using var w = new StringWriter(CultureInfo.InvariantCulture);
        Write(dag, n, w);
        return w.ToString();
    }

    public static void Write(Dag dag, int n, TextWriter w)
    {
        w.WriteLine($"pcnnf {Version}");
        w.WriteLine($"n {n}");
        w.WriteLine($"root {dag.Root}");
        for (int i = 0; i < dag.Count; i++)
        {
            var node = dag[i];
            switch (node.Kind)
            {
                case NodeKind.True: w.WriteLine($"{i} T"); break;
                case NodeKind.False: w.WriteLine($"{i} F"); break;
                case NodeKind.Literal: w.WriteLine($"{i} lit {node.Variable} {(node.Positive ? 1 : 0)}"); break;
                case NodeKind.And: w.WriteLine($"{i} and {string.Join(" ", node.Children)}"); break;
                case NodeKind.Or: w.WriteLine($"{i} or {string.Join(" ", node.Children)}"); break;
            }
        }
    }

    public static void WriteFile(Dag dag, int n, string path)
    {
        using var w = new StreamWriter(path);
        Write(dag, n, w);
    }

    public static (Dag Dag, int N) Read(string text)
    {
        using var r = new StringReader(text);
        return Read(r);
    }

    public static (Dag Dag, int N) ReadFile(string path)
    {
        using var r = new StreamReader(path);
        return Read(r);
    }

    public static (Dag Dag, int N) Read(TextReader r)
    {
        var dag = new Dag();
        int n = -1, root = -1, expectedId = 0;
        string? line;
        int lineNo = 0;
        while ((line = r.ReadLine()) != null)
        {
            lineNo++;
            var t = line.Trim();
            if (t.Length == 0 || t[0] == '#') continue;
            var parts = t.Split(' ', StringSplitOptions.RemoveEmptyEntries);
            switch (parts[0])
            {
                case "pcnnf":
                    if (parts.Length != 2 || int.Parse(parts[1]) != Version) throw new FormatException($"line {lineNo}: unsupported header '{t}'");
                    continue;
                case "n":
                    n = int.Parse(parts[1]);
                    continue;
                case "root":
                    root = int.Parse(parts[1]);
                    continue;
            }
            int id = int.Parse(parts[0]);
            if (id != expectedId) throw new FormatException($"line {lineNo}: expected node id {expectedId}, got {id}");
            expectedId++;
            if (parts.Length < 2) throw new FormatException($"line {lineNo}: missing node kind");
            switch (parts[1])
            {
                case "T": dag.AddTrue(); break;
                case "F": dag.AddFalse(); break;
                case "lit":
                    if (parts.Length != 4) throw new FormatException($"line {lineNo}: lit needs var and polarity");
                    dag.AddLiteral(int.Parse(parts[2]), ParsePolarity(parts[3], lineNo));
                    break;
                case "and":
                case "or":
                    var kids = parts.Skip(2).Select(int.Parse).ToArray();
                    if (kids.Any(k => k >= id)) throw new FormatException($"line {lineNo}: child id must be smaller than node id {id}");
                    dag.AddGate(parts[1] == "and" ? NodeKind.And : NodeKind.Or, kids);
                    break;
                default:
                    throw new FormatException($"line {lineNo}: unknown node kind '{parts[1]}'");
            }
        }
        if (root < 0) throw new FormatException("missing root line");
        dag.Root = root;
        if (n < 0) n = dag.Variables.IsEmpty ? 0 : dag.Variables.Max() + 1;
        return (dag, n);
    }

    private static bool ParsePolarity(string s, int lineNo) => s switch
    {
        "1" or "true" or "True" => true,
        "0" or "false" or "False" => false,
        _ => throw new FormatException($"line {lineNo}: bad polarity '{s}'"),
    };
}
