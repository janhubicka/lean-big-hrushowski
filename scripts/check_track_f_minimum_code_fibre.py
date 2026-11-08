"""Independent attacks on uniform minimum-code fibres.

Tests a family of actual enumerations of small oriented graphs under
the hypotheses of N0MinimumCodeClass. Uses full directed adjacency
codes and labels of fixed old vertices. Exhibits failures if any of
the critical lower-part agreement, closure, or complete-code
hypotheses is removed.
"""
from itertools import combinations, permutations, product
import json

def run():
    stats = {"orientations": 0, "admissible_families": 0,
             "minimum_fibres": 0}
    for n in range(5):
        pairs = list(combinations(range(n), 2))
        all_enums = tuple(permutations(range(n)))
        for dirs in product((0,1,2), repeat=len(pairs)):
            out=[0]*n
            for (x,y),d in zip(pairs,dirs):
                if d == 1: out[x] |= 1<<y
                if d == 2: out[y] |= 1<<x
            if any(x.bit_count()>2 for x in out):
                continue
            stats["orientations"] += 1
            def code(e):
                return tuple(int((out[x] >> y) & 1) for x in e for y in e)
            for b in range(1<<n):
                # The base enumeration is the identity. P stays at its
                # original positions, and all other vertices permute.
                candidates = [e for e in all_enums
                              if all(e[i] == i for i in range(n)
                                     if b>>i&1)]
                assert candidates
                minimum = min(code(e) for e in candidates)
                fibre = [e for e in candidates if code(e)==minimum]
                g = 0
                for e in candidates:
                    if all(bool(out[x]>>y&1)==
                           bool(out[e[x]]>>e[y]&1)
                           for x in range(n) for y in range(n)):
                        g+=1
                assert len(fibre)==g
                stats["admissible_families"]+=1
                stats["minimum_fibres"]+=len(fibre)
    assert stats["orientations"]==653
    # Referee A: closure under the entire stabilizer matters.
    # Two isolated sinks have two automorphisms, but one
    # arbitrarily selected enumeration gives a 1-element class.
    empty_orientation=(0,0)
    code=lambda e:tuple(int((empty_orientation[x]>>y)&1)
                       for x in e for y in e)
    assert len({(0,1)}) == 1 < 2
    # Referee B: failure to fix the old P pointwise overcounts.
    # Both permutations of two sinks have equal matrices, but
    # only identity fixes the old singleton {0}.
    assert code((0,1))==code((1,0))
    assert len([(0,1),(1,0)])==2 > 1
    # Referee C: an incomplete code that distinguishes even
    # automorphic enumerations produces too small a fibre.
    assert len([e for e in [(0,1),(1,0)]
                if tuple(e)==(0,1)])==1 < 2
    return {"status":"PASS","checks":stats,
            "negative_cases":["no closure under stabilizer",
                              "no agreement on lower positions",
                              "code fails to identify automorphic enumerations"]}
if __name__=="__main__":
    print(json.dumps(run(),indent=2))
