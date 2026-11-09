using System.Text.Json;
using PcNnf.Core;

namespace PcNnf.Tests;

/// <summary>
/// Differential tests against the Python oracle (scripts/oracle.py, which runs the functions of
/// scripts/check_witness.py): validity, truth table, bottom-up answer and Lemma W witness must
/// agree with Core's on random formulas, in both directions of the interchange format.
/// </summary>
public class DifferentialTests
{
    private const int N = 4;

    private sealed record OracleResult(string file, bool valid, string table, int bottom_up, List<List<int>>? witness);

    private static List<OracleResult> RunOracle(IEnumerable<string> files)
    {
        var args = new List<string> { "-I", Path.Combine(TestEnv.Scripts, "oracle.py"), "check" };
        args.AddRange(files);
        var (code, stdout, stderr) = TestEnv.Run(TestEnv.Python, args);
        Assert.True(code == 0, $"oracle failed ({code}): {stderr}");
        return stdout.Split('\n', StringSplitOptions.RemoveEmptyEntries)
            .Select(line => JsonSerializer.Deserialize<OracleResult>(line)!)
            .ToList();
    }

    private static void Compare(Dag dag, OracleResult o)
    {
        Assert.Equal(o.valid, dag.IsValid());
        Assert.Equal(o.table, dag.TruthTable(N).ToBitString());
        Assert.Equal(o.bottom_up == 1, dag.Sat());
        var w = dag.ExtractWitness();
        if (o.witness is null)
        {
            Assert.Null(w);
            return;
        }
        Assert.NotNull(w);
        var mine = w.Value.Positive.Select(v => (v, 1)).Concat(w.Value.Negative.Select(v => (v, 0))).OrderBy(p => p).ToList();
        var theirs = o.witness.Select(p => (p[0], p[1])).OrderBy(p => p).ToList();
        Assert.Equal(theirs, mine);
        if (o.valid)
        {
            // Lemma W: consistent and every extension is a model (checked against the oracle's table)
            Assert.True(w.Value.IsConsistent);
            for (ulong s = 0; s < 16; s++) if (w.Value.Extends(s)) Assert.Equal('1', o.table[(int)s]);
        }
    }

    [Fact]
    public void CoreWrites_OracleReads_AllAgree()
    {
        var dir = Directory.CreateTempSubdirectory("pcnnf-diff-");
        try
        {
            var rng = new Random(2026);
            var dags = new List<Dag>();
            var files = new List<string>();
            for (int i = 0; i < 600; i++)
            {
                var d = TestEnv.RandomFormula(rng, N, rng.Next(11, 19));
                var path = Path.Combine(dir.FullName, $"c_{i:D4}.txt");
                Interchange.WriteFile(d, N, path);
                dags.Add(d);
                files.Add(path);
            }
            var results = RunOracle(files);
            Assert.Equal(files.Count, results.Count);
            int valid = 0;
            for (int i = 0; i < files.Count; i++)
            {
                Assert.Equal(files[i], results[i].file);
                Compare(dags[i], results[i]);
                if (results[i].valid) valid++;
            }
            Assert.True(valid > 100, $"only {valid} valid formulas in the sample");
        }
        finally { dir.Delete(true); }
    }

    [Fact]
    public void OracleWrites_CoreReads_AllAgree()
    {
        var dir = Directory.CreateTempSubdirectory("pcnnf-diff-");
        try
        {
            const int count = 400;
            var (code, stdout, stderr) = TestEnv.Run(TestEnv.Python,
                new[] { "-I", Path.Combine(TestEnv.Scripts, "oracle.py"), "gen", "--count", count.ToString(), "--seed", "17", "--out", dir.FullName, "--n", N.ToString() });
            Assert.True(code == 0, $"oracle gen failed ({code}): {stderr}");
            Assert.Equal(count.ToString(), stdout.Trim());
            var files = Directory.GetFiles(dir.FullName, "f_*.txt").Order().ToList();
            Assert.Equal(count, files.Count);
            var results = RunOracle(files);
            for (int i = 0; i < files.Count; i++)
            {
                var (dag, n) = Interchange.ReadFile(files[i]);
                Assert.Equal(N, n);
                Compare(dag, results[i]);
                // and the file Core writes back is byte-identical
                Assert.Equal(File.ReadAllText(files[i]), Interchange.Write(dag, n));
            }
        }
        finally { dir.Delete(true); }
    }
}
