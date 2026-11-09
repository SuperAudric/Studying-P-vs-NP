using System.Diagnostics;
using PcNnf.Core;
using PcNnf.Enum;

namespace PcNnf.Tests;

/// <summary>Repository paths, the Python interpreter, and dictionaries shared across test classes.</summary>
public static class TestEnv
{
    public static string RepoRoot { get; } = FindRepoRoot();

    public static string Scripts => Path.Combine(RepoRoot, "scripts");

    private static string FindRepoRoot()
    {
        var dir = new DirectoryInfo(AppContext.BaseDirectory);
        while (dir != null)
        {
            if (File.Exists(Path.Combine(dir.FullName, "scripts", "oracle.py"))) return dir.FullName;
            dir = dir.Parent;
        }
        throw new InvalidOperationException("repository root (containing scripts/oracle.py) not found above " + AppContext.BaseDirectory);
    }

    public static string Python { get; } = FindPython();

    private static string FindPython()
    {
        foreach (var candidate in new[] { "python", "python3", "/opt/venv/bin/python" })
        {
            try
            {
                var p = Process.Start(new ProcessStartInfo(candidate, "--version") { RedirectStandardOutput = true, RedirectStandardError = true });
                p!.WaitForExit();
                if (p.ExitCode == 0) return candidate;
            }
            catch (System.ComponentModel.Win32Exception) { }
        }
        throw new InvalidOperationException("no Python interpreter found; the differential tests need the venv's python on PATH");
    }

    /// <summary>Run a process, return (exit code, stdout, stderr).</summary>
    public static (int ExitCode, string Stdout, string Stderr) Run(string file, IEnumerable<string> args, string? workingDir = null, int timeoutMs = 600_000)
    {
        var psi = new ProcessStartInfo(file) { RedirectStandardOutput = true, RedirectStandardError = true, WorkingDirectory = workingDir ?? RepoRoot };
        foreach (var a in args) psi.ArgumentList.Add(a);
        using var p = Process.Start(psi)!;
        var stdout = p.StandardOutput.ReadToEndAsync();
        var stderr = p.StandardError.ReadToEndAsync();
        if (!p.WaitForExit(timeoutMs)) { p.Kill(true); throw new TimeoutException($"{file} did not finish in {timeoutMs} ms"); }
        return (p.ExitCode, stdout.Result, stderr.Result);
    }

    // Dictionaries are built once per test run (n = 4 takes a few seconds each).
    public static readonly Lazy<TreeDictionary> Pc3 = new(() => TreeDictionary.Build(3, Rule.Pc));
    public static readonly Lazy<TreeDictionary> Nnf3 = new(() => TreeDictionary.Build(3, Rule.Nnf));
    public static readonly Lazy<TreeDictionary> Pc4 = new(() => TreeDictionary.Build(4, Rule.Pc));
    public static readonly Lazy<TreeDictionary> Nnf4 = new(() => TreeDictionary.Build(4, Rule.Nnf));
    public static readonly Lazy<TreeDictionary> Mono4 = new(() => TreeDictionary.Build(4, Rule.Mono));

    /// <summary>
    /// Random formulas exactly as check_tiny.py / check_witness.py draw them: nodes start with
    /// ⊤, ⊥ and the 2n literals; each new gate takes 2 or 3 distinct earlier nodes and a random
    /// kind; the root is the last node. Validity is not enforced.
    /// </summary>
    public static Dag RandomFormula(Random rng, int n, int size)
    {
        var d = new Dag();
        d.AddTrue();
        d.AddFalse();
        for (int v = 0; v < n; v++) { d.AddLiteral(v, true); d.AddLiteral(v, false); }
        while (d.Count < size)
        {
            int k = rng.Next(2, 4);
            var kids = Enumerable.Range(0, d.Count).OrderBy(_ => rng.Next()).Take(k).ToArray();
            d.AddGate(rng.Next(2) == 0 ? NodeKind.And : NodeKind.Or, kids);
        }
        d.Root = d.Count - 1;
        return d;
    }
}
