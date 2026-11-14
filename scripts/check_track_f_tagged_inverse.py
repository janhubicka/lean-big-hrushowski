#!/usr/bin/env python3
"""Independent finite audit of actual tagged SCC-order history reconstruction.

Exercise all orientations of up to four labelled vertices, all SCC
rankings (legal or otherwise), and every family of internal SCC orders.
The rank-prefix execution must agree with the original order on all
components in the prefix. A full execution must give the exact family.
"""
from itertools import permutations, product
from check_track_f_canonical_local import orientations, components


def build_prefix(rank, choices, n):
    """A list of tagged actual orders, newest first."""
    return tuple((B, choices[B]) for B in reversed(rank[:n]))


def execute(hist, defaults):
    state = list(defaults)
    for B, order in reversed(hist):
        state[B] = order
    return tuple(state)


def main():
    structs = prefixes = complete = 0
    for nv in range(5):
        for out in orientations(nv):
            cc = components(out)
            options = [tuple(permutations(sorted(B))) for B, _ in cc]
            default = tuple(opts[0] for opts in options)
            for rank in permutations(range(len(cc))):
                for choices in product(*options):
                    for n in range(len(cc) + 1):
                        hist = build_prefix(rank, choices, n)
                        assert len(hist) == n
                        executed = execute(hist, default)
                        for B in rank[:n]:
                            assert executed[B] == choices[B]
                        prefixes += 1
                        if n == len(cc):
                            assert executed == choices
                            complete += 1
            structs += 1
    # Repeating a tag makes chronological direction observable;
    # the current tag must override an earlier choice of the same SCC.
    assert execute(((0, (1, 0)), (0, (0, 1))),
                   ((0, 1),)) == ((1, 0),)
    assert structs == 653 and prefixes > 0 and complete > 0
    print(f"PASS: {structs} orientations, {prefixes} rank prefixes, "
          f"{complete} full tagged histories; reverse chronological "
          "update and repeated-SCC negative control")


if __name__ == "__main__":
    main()
