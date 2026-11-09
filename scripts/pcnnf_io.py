"""Reader/writer for the text interchange format of PcNnf.Core (src/PcNnf.Core/Interchange.cs).

A formula is (nodes, root) in the node format of check_tiny.py / check_witness.py:
    ('lit', var, pos) | ('T',) | ('F',) | ('and', [ids]) | ('or', [ids])
The file format is one node per line, ids consecutive from 0, children before parents:

    pcnnf 1
    n 4
    root 5
    0 lit 0 1
    1 lit 1 0
    2 T
    3 F
    4 and 0 1
    5 or 4 2

read_formula returns (nodes, root, n); write_formula takes (nodes, root, n).
"""

VERSION = 1


def read_formula(path):
    nodes, root, n = [], None, None
    with open(path) as f:
        for lineno, line in enumerate(f, 1):
            t = line.strip()
            if not t or t.startswith('#'):
                continue
            parts = t.split()
            if parts[0] == 'pcnnf':
                if int(parts[1]) != VERSION:
                    raise ValueError(f"{path}:{lineno}: unsupported version {parts[1]}")
                continue
            if parts[0] == 'n':
                n = int(parts[1]); continue
            if parts[0] == 'root':
                root = int(parts[1]); continue
            nid = int(parts[0])
            if nid != len(nodes):
                raise ValueError(f"{path}:{lineno}: expected node id {len(nodes)}, got {nid}")
            kind = parts[1]
            if kind == 'T':
                nodes.append(('T',))
            elif kind == 'F':
                nodes.append(('F',))
            elif kind == 'lit':
                nodes.append(('lit', int(parts[2]), int(parts[3])))
            elif kind in ('and', 'or'):
                kids = [int(x) for x in parts[2:]]
                if any(k >= nid for k in kids):
                    raise ValueError(f"{path}:{lineno}: child id must be smaller than node id")
                nodes.append((kind, kids))
            else:
                raise ValueError(f"{path}:{lineno}: unknown node kind {kind}")
    if root is None:
        raise ValueError(f"{path}: missing root line")
    if n is None:
        n = 1 + max((nd[1] for nd in nodes if nd[0] == 'lit'), default=-1)
    return nodes, root, n


def write_formula(path, nodes, root, n):
    with open(path, 'w') as f:
        f.write(f"pcnnf {VERSION}\nn {n}\nroot {root}\n")
        for i, nd in enumerate(nodes):
            if nd[0] == 'lit':
                f.write(f"{i} lit {nd[1]} {1 if nd[2] else 0}\n")
            elif nd[0] in ('T', 'F'):
                f.write(f"{i} {nd[0]}\n")
            else:
                f.write(f"{i} {nd[0]} {' '.join(str(k) for k in nd[1])}\n")
