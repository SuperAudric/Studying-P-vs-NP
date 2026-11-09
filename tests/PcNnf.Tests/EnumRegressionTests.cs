using System.Text.RegularExpressions;
using PcNnf.Core;
using PcNnf.Enum;

namespace PcNnf.Tests;

/// <summary>
/// Enum must reproduce the spike's numbers (strategy 2.1) exactly, both as hard-coded
/// fixtures and by diffing against a fresh build of scripts/spikes/enum_tree_minima.c.
/// </summary>
public class EnumRegressionTests
{
    private static readonly int[] Pc4Levels = { 10, 48, 256, 940, 1664, 4960, 7232, 9992, 11824, 12080, 6880, 5648, 2128, 1376, 192, 210, 64, 32 };
    private static readonly int[] Pc3Levels = { 8, 24, 64, 30, 80, 32, 0, 16, 0, 2 };

    /// <summary>Strategy 2.1 clique table at n = 4: edges → (k_pc, k_nnf) per k, null = constant.</summary>
    private static readonly (string Edges, (int Pc, int Nnf)?[] Ks)[] Clique4 =
    {
        ("∅",              new (int, int)?[] { (7, 7), (11, 11), null, null, null }),
        ("01",             new (int, int)?[] { (5, 5), (9, 9), (3, 3), null, null }),
        ("01,02",          new (int, int)?[] { (5, 5), (9, 9), (5, 5), null, null }),
        ("01,02,03",       new (int, int)?[] { (4, 4), (8, 8), (8, 8), null, null }),
        ("01,02,12",       new (int, int)?[] { (3, 3), (7, 7), (5, 5), (3, 3), null }),
        ("03,12",          new (int, int)?[] { (3, 3), (7, 7), (7, 7), null, null }),
        ("01,03,12",       new (int, int)?[] { (4, 4), (8, 8), (9, 8), null, null }),
        ("01,02,03,12",    new (int, int)?[] { (2, 2), (6, 6), (9, 8), (3, 3), null }),
        ("02,03,12,13",    new (int, int)?[] { (3, 3), (9, 7), (7, 7), null, null }),
        ("01,02,03,12,13", new (int, int)?[] { (1, 1), (5, 5), (7, 7), (5, 5), null }),
        ("01,02,03,12,13,23", new (int, int)?[] { null, (3, 3), (7, 7), (7, 7), (3, 3) }),
    };

    [Fact]
    public void N3_AllFunctionsReached_LevelsMatch_NoGap()
    {
        var pc = TestEnv.Pc3.Value;
        var nnf = TestEnv.Nnf3.Value;
        Assert.Equal(256, pc.Count);
        Assert.Equal(Pc3Levels, pc.LevelCounts);
        Assert.Equal(Pc3Levels, nnf.LevelCounts);
        Assert.Equal(9, pc.MaxGates);
        var gap = new GapReport(pc, nnf);
        Assert.Equal(new[] { 256 }, gap.Histogram);
        Assert.Equal(22, gap.NpClassCount);
        Assert.Equal(0, pc.PolarityMismatches);
    }

    [Fact]
    public void N4_EntriesLevelsMaxAndGapsMatchTheSpike()
    {
        var pc = TestEnv.Pc4.Value;
        var nnf = TestEnv.Nnf4.Value;
        Assert.Equal(65_536, pc.Count);
        Assert.Equal(65_536L, pc.Reached);
        Assert.False(pc.Capped);
        Assert.Equal(Pc4Levels, pc.LevelCounts);
        Assert.Equal(17, pc.MaxGates);
        Assert.Equal(15, nnf.MaxGates);
        Assert.Equal(0, pc.PolarityMismatches);
        var gap = new GapReport(pc, nnf);
        Assert.Equal(new[] { 51_792, 12_800, 944 }, gap.Histogram);
        Assert.Equal(2, gap.MaxGap);
        Assert.Equal(402, gap.NpClassCount);
        Assert.Equal(944, gap.MaxGapClasses.Sum(c => c.ClassSize));
        Assert.True(pc.BuildTime < TimeSpan.FromSeconds(60), $"n = 4 took {pc.BuildTime}");
    }

    [Fact]
    public void N4_CliqueTable_ElevenRowsMatchStrategy21()
    {
        var rows = CliqueTable.Rows(TestEnv.Pc4.Value, TestEnv.Nnf4.Value);
        var graphs = rows.Select(r => r.Edges).Distinct().ToList();
        Assert.Equal(11, graphs.Count);
        Assert.Equal(Clique4.Select(c => c.Edges), graphs);
        foreach (var (edges, ks) in Clique4)
        {
            for (int k = 0; k <= 4; k++)
            {
                var row = rows.Single(r => r.Edges == edges && r.K == k);
                if (ks[k] is null) { Assert.True(row.IsConstant, $"{edges} k={k} should be constant"); continue; }
                Assert.False(row.IsConstant);
                Assert.Equal("upper", row.Status);
                Assert.Equal(ks[k]!.Value.Pc, row.GatesPc);
                Assert.Equal(ks[k]!.Value.Nnf, row.GatesNnf);
                // tree size per strategy 1: 3k + |P| + |N|
                var tt = row.Table;
                Assert.Equal(3 * ks[k]!.Value.Pc + tt.EssentialPositive.Count + tt.EssentialNegative.Count, row.Size21Pc);
                Assert.True(row.NaryGatesPc <= row.GatesPc);
            }
        }
    }

    [Fact]
    public void Mono4_ReachesExactlyTheMonotoneFunctions()
    {
        var mono = TestEnv.Mono4.Value;
        Assert.Equal(168, mono.Count); // Dedekind number M(4)
        Assert.False(mono.Capped);
        Assert.Equal(0, mono.PolarityMismatches);
        var pc = TestEnv.Pc4.Value;
        for (int tt = 0; tt < 65_536; tt++)
        {
            var t = new TruthTable(4, (ulong)tt);
            var km = mono.Gates(t);
            Assert.Equal(t.IsMonotone, km.HasValue);
            // Theorem B: for monotone f the PC-NNF minimum equals the monotone minimum (tree measure here)
            if (km.HasValue) Assert.Equal(pc.Gates(t), km);
        }
    }

    [Fact]
    public void TableFile_RoundTrips()
    {
        var pc = TestEnv.Pc4.Value;
        var path = Path.Combine(Path.GetTempPath(), $"pcnnf-test-{Guid.NewGuid():N}.bin");
        try
        {
            TableFile.Write(pc, path);
            var l = TableFile.Read(path);
            Assert.Equal(4, l.N);
            Assert.Equal(Rule.Pc, l.Rule);
            Assert.Equal(65_536, l.Gates.Length);
            for (int tt = 0; tt < 65_536; tt++)
            {
                Assert.True(pc.TryGetEntry((ulong)tt, out var e));
                Assert.Equal(e.Gates, l.Gates[tt]);
                Assert.Equal((byte)e.Op, l.Op[tt]);
                Assert.Equal((byte)e.Pos.Bits, l.Pos[tt]);
                if (e.IsGate)
                {
                    Assert.Equal((uint)pc.Entries[e.Left].Tt, l.Left[tt]);
                    Assert.Equal((uint)pc.Entries[e.Right].Tt, l.Right[tt]);
                    ulong combined = e.Op == EntryOp.And ? l.Left[tt] & l.Right[tt] : l.Left[tt] | l.Right[tt];
                    Assert.Equal((ulong)tt, combined);
                    Assert.Equal(e.Gates, 1 + l.Gates[l.Left[tt]] + l.Gates[l.Right[tt]]);
                }
            }
        }
        finally { File.Delete(path); }
    }

    // ---- diff against a fresh build of the C spike ------------------------------------------------

    private sealed record SpikeOutput(int[] PcLevels, int[] NnfLevels, Dictionary<int, int> Gaps, Dictionary<(string Edges, int K), (int Pc, int Nnf)?> Clique);

    private static SpikeOutput? RunSpike(int n)
    {
        var gcc = TestEnv.Run("sh", new[] { "-c", "command -v gcc" });
        if (gcc.ExitCode != 0) return null;
        var exe = Path.Combine(Path.GetTempPath(), $"pcnnf-spike-{Guid.NewGuid():N}");
        try
        {
            var build = TestEnv.Run("gcc", new[] { "-O2", "-o", exe, Path.Combine(TestEnv.Scripts, "spikes", "enum_tree_minima.c") });
            Assert.True(build.ExitCode == 0, "spike did not compile: " + build.Stderr);
            var run = TestEnv.Run(exe, new[] { n.ToString() });
            Assert.True(run.ExitCode == 0, "spike failed: " + run.Stderr);
            return Parse(run.Stdout);
        }
        finally { if (File.Exists(exe)) File.Delete(exe); }
    }

    private static SpikeOutput Parse(string stdout)
    {
        var levelLines = Regex.Matches(stdout, @"entries per level:((?: \d+)+)").Select(m => m.Groups[1].Value.Trim().Split(' ').Select(int.Parse).ToArray()).ToList();
        Assert.Equal(2, levelLines.Count); // first is the Pareto PC-NNF run, second the NNF run
        var gaps = Regex.Match(stdout, @"gap histogram \(k_pc - k_nnf -> count\):((?: \d+:\d+)+)").Groups[1].Value.Trim()
            .Split(' ').Select(p => p.Split(':')).ToDictionary(p => int.Parse(p[0]), p => int.Parse(p[1]));
        var clique = new Dictionary<(string, int), (int, int)?>();
        foreach (Match m in Regex.Matches(stdout, @"edges \{([0-9,]*)\}:((?:\s+k=\d+:(?:\d+\(\d+\)|T|F))+)"))
        {
            var edges = m.Groups[1].Value.Length == 0 ? "∅" : m.Groups[1].Value;
            foreach (Match k in Regex.Matches(m.Groups[2].Value, @"k=(\d+):(?:(\d+)\((\d+)\)|([TF]))"))
            {
                int kk = int.Parse(k.Groups[1].Value);
                clique[(edges, kk)] = k.Groups[4].Success ? null : (int.Parse(k.Groups[2].Value), int.Parse(k.Groups[3].Value));
            }
        }
        return new SpikeOutput(levelLines[0], levelLines[1], gaps, clique);
    }

    [Theory]
    [InlineData(3)]
    [InlineData(4)]
    public void Enum_DiffsCleanAgainstTheCSpike(int n)
    {
        var spike = RunSpike(n);
        Assert.True(spike != null, "gcc not available; the spike diff needs a C compiler");
        var pc = n == 3 ? TestEnv.Pc3.Value : TestEnv.Pc4.Value;
        var nnf = n == 3 ? TestEnv.Nnf3.Value : TestEnv.Nnf4.Value;
        Assert.Equal(spike!.PcLevels, pc.LevelCounts);
        Assert.Equal(spike.NnfLevels, nnf.LevelCounts);
        var gap = new GapReport(pc, nnf);
        var mine = gap.Histogram.Select((c, g) => (g, c)).Where(p => p.c > 0).ToDictionary(p => p.g, p => p.c);
        Assert.Equal(spike.Gaps, mine);
        var rows = CliqueTable.Rows(pc, nnf);
        Assert.Equal(spike.Clique.Count, rows.Count);
        foreach (var row in rows)
        {
            var s = spike.Clique[(row.Edges, row.K)];
            if (s is null) Assert.True(row.IsConstant);
            else
            {
                Assert.Equal(s.Value.Pc, row.GatesPc);
                Assert.Equal(s.Value.Nnf, row.GatesNnf);
            }
        }
    }
}
