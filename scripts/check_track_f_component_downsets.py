"""Independent check: successor closure equals SCC saturation and downset."""
from itertools import combinations, product
import json

def check(out):
    n = len(out)
    reach = [(1 << i) | out[i] for i in range(n)]
    for k in range(n):
        for i in range(n):
            if reach[i] & (1 << k):
                reach[i] |= reach[k]
    components = [sum(1 << j for j in range(n)
                      if (reach[i] >> j & 1) and (reach[j] >> i & 1))
                  for i in range(n)]
    tests = 0
    for s in range(1 << n):
        closed = all((out[i] & ~s) == 0
                     for i in range(n) if s >> i & 1)
        saturated = all((components[i] & ~s) == 0
                        for i in range(n) if s >> i & 1)
        downward = all(not (s >> u & 1) or bool(s >> v & 1)
                       for u in range(n) for v in range(n)
                       if (reach[u] >> v & 1) and not (reach[v] >> u & 1))
        assert closed == (saturated and downward), (out, s)
        tests += 1
    return tests

def run():
    graphs = tests = 0
    for n in range(6):
        pairs = tuple(combinations(range(n), 2))
        for choices in product(range(3), repeat=len(pairs)):
            out = [0] * n
            for (a, b), direction in zip(pairs, choices):
                if direction == 1:
                    out[a] |= 1 << b
                elif direction == 2:
                    out[b] |= 1 << a
            if any(s.bit_count() > 2 for s in out):
                continue
            graphs += 1
            tests += check(out)
    assert graphs == 30887 and tests == 977655
    return {"status": "PASS", "orientations": graphs,
            "vertex_subsets": tests, "scope": "finite only"}

if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
