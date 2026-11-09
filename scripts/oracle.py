"""Differential-test oracle for PcNnf.Core, driven by the C# tests (tests/PcNnf.Tests).

The checking functions (pols, valid, table, bottom_up, witness, rand_formula) are the ones in
scripts/check_witness.py, loaded from that file so that the oracle is literally the script's
code; only its final line, which runs the script's own checks, is skipped.

Usage:
    python scripts/oracle.py check FILE...
        One JSON object per input file, in order, with keys
          valid      bool   check_witness.valid(nodes) over every node of the DAG
          table      str    f(s) for s = 0..2^n-1 as '0'/'1' characters, where assignment s has
                            bit v = value of x_v (PcNnf.Core.TruthTable convention; the script's
                            own tuples put x_0 first, the mapping is done here)
          bottom_up  0|1    sat(root) from the bottom-up pass
          witness    list   [[var, pos], ...] literal leaves reached by the Lemma W walk, sorted,
                            or null when sat(root) = 0
    python scripts/oracle.py gen --count K --seed S --out DIR [--n N]
        Writes K random formulas f_0000.txt ... as check_witness.rand_formula draws them
        (size uniform in 11..18), for the Core-reads-Python direction of the round trip.
"""
import argparse, itertools, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from pcnnf_io import read_formula, write_formula  # noqa: E402


def load_check_witness():
    """Execute check_witness.py minus its final self-check line; return its namespace."""
    src = open(os.path.join(HERE, 'check_witness.py')).read()
    lines = src.splitlines()
    last = lines[-1].strip()
    assert last.startswith('check_witness();'), "check_witness.py layout changed; adjust oracle.py"
    ns = {}
    exec(compile('\n'.join(lines[:-1]), 'check_witness.py', 'exec'), ns)
    return ns


def cmd_check(args):
    cw = load_check_witness()
    for path in args.files:
        nodes, root, n = read_formula(path)
        assigns = list(itertools.product([0, 1], repeat=n))
        t = cw['table'](nodes, root, assigns)
        bits = ['?'] * (1 << n)
        for s, val in zip(assigns, t):
            pos = sum(b << v for v, b in enumerate(s))
            bits[pos] = '1' if val else '0'
        w = cw['witness'](nodes, root)
        out = {
            'file': path,
            'valid': bool(cw['valid'](nodes)),
            'table': ''.join(bits),
            'bottom_up': int(cw['bottom_up'](nodes, root)[0]),
            'witness': None if w is None else sorted([list(x) for x in w]),
        }
        print(json.dumps(out))


def cmd_gen(args):
    cw = load_check_witness()
    import random
    random.seed(args.seed)
    cw['random'].seed(args.seed)
    os.makedirs(args.out, exist_ok=True)
    for i in range(args.count):
        nodes, root = cw['rand_formula'](args.n, random.randint(11, 18))
        write_formula(os.path.join(args.out, f"f_{i:04d}.txt"), nodes, root, args.n)
    print(args.count)


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest='cmd', required=True)
    c = sub.add_parser('check'); c.add_argument('files', nargs='+'); c.set_defaults(fn=cmd_check)
    g = sub.add_parser('gen')
    g.add_argument('--count', type=int, required=True)
    g.add_argument('--seed', type=int, default=1)
    g.add_argument('--out', required=True)
    g.add_argument('--n', type=int, default=4)
    g.set_defaults(fn=cmd_gen)
    args = p.parse_args()
    args.fn(args)


if __name__ == '__main__':
    main()
