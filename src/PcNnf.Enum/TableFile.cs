using System.Text;
using PcNnf.Core;

namespace PcNnf.Enum;

/// <summary>
/// Flat-array file for a complete n ≤ 4 table (strategy 4.2): one record per truth table,
/// indexed by the table's integer value.
/// <code>
/// magic   "PCNNFTAB"          8 bytes
/// version int32 = 1
/// n       int32
/// rule    int32               0 pc, 1 nnf, 2 mono
/// count   int64 = 2^(2^n)
/// gates   byte[count]         minimum fan-in-2 gate count; 255 = not reached
/// op      byte[count]         EntryOp: 1 literal, 2 ⊤, 3 ⊥, 4 and, 5 or; 0 = not reached
/// pos     byte[count]         essential vars⁺ as a bitmask over variables
/// neg     byte[count]         essential vars⁻ as a bitmask over variables
/// left    uint32[count]       back-pointer: truth table of the left operand (variable index for a literal)
/// right   uint32[count]       back-pointer: truth table of the right operand (polarity 0/1 for a literal)
/// </code>
/// Back-pointers are truth tables rather than entry indices because the table is keyed on
/// the truth table alone (Corollary E2), so they identify the operand entry uniquely.
/// </summary>
public static class TableFile
{
    private const string Magic = "PCNNFTAB";
    private const int Version = 1;

    public static string DefaultPath(string dataDir, int n, Rule rule) => Path.Combine(dataDir, $"enum-n{n}-{rule.Name()}.bin");

    public static void Write(TreeDictionary d, string path)
    {
        if (d.N > 4) throw new ArgumentException("flat tables are written for n ≤ 4 only");
        long count = 1L << (1 << d.N);
        var gates = new byte[count];
        var op = new byte[count];
        var pos = new byte[count];
        var neg = new byte[count];
        var left = new uint[count];
        var right = new uint[count];
        Array.Fill(gates, (byte)255);
        foreach (var e in d.Entries)
        {
            gates[e.Tt] = e.Gates;
            op[e.Tt] = (byte)e.Op;
            pos[e.Tt] = (byte)e.Pos.Bits;
            neg[e.Tt] = (byte)e.Neg.Bits;
            if (e.IsGate)
            {
                left[e.Tt] = (uint)d.Entries[e.Left].Tt;
                right[e.Tt] = (uint)d.Entries[e.Right].Tt;
            }
            else if (e.Op == EntryOp.Literal)
            {
                left[e.Tt] = e.Variable;
                right[e.Tt] = e.Positive ? 1u : 0u;
            }
        }
        Directory.CreateDirectory(Path.GetDirectoryName(Path.GetFullPath(path))!);
        using var w = new BinaryWriter(File.Create(path));
        w.Write(Encoding.ASCII.GetBytes(Magic));
        w.Write(Version);
        w.Write(d.N);
        w.Write((int)d.Rule);
        w.Write(count);
        w.Write(gates);
        w.Write(op);
        w.Write(pos);
        w.Write(neg);
        foreach (var x in left) w.Write(x);
        foreach (var x in right) w.Write(x);
    }

    public sealed record Loaded(int N, Rule Rule, byte[] Gates, byte[] Op, byte[] Pos, byte[] Neg, uint[] Left, uint[] Right);

    public static Loaded Read(string path)
    {
        using var r = new BinaryReader(File.OpenRead(path));
        if (Encoding.ASCII.GetString(r.ReadBytes(8)) != Magic) throw new FormatException("not a PcNnf table file");
        if (r.ReadInt32() != Version) throw new FormatException("unsupported table version");
        int n = r.ReadInt32();
        var rule = (Rule)r.ReadInt32();
        long count = r.ReadInt64();
        var gates = r.ReadBytes((int)count);
        var op = r.ReadBytes((int)count);
        var pos = r.ReadBytes((int)count);
        var neg = r.ReadBytes((int)count);
        var left = new uint[count];
        var right = new uint[count];
        for (long i = 0; i < count; i++) left[i] = r.ReadUInt32();
        for (long i = 0; i < count; i++) right[i] = r.ReadUInt32();
        return new Loaded(n, rule, gates, op, pos, neg, left, right);
    }
}
