"""Independent adversarial check: labelled orders versus enumerations."""
from itertools import permutations
from math import factorial
import json

def signature(e):
    return frozenset((x, y) for i, x in enumerate(e)
                     for j, y in enumerate(e) if i < j)

def run():
    tests = 0
    for n in range(8):
        orders = list(permutations(range(n)))
        images = [signature(e) for e in orders]
        assert len(images) == len(set(images)) == factorial(n)
        for e, r in zip(orders, images):
            assert all((x, y) not in r for x in range(n) for y in range(n) if x == y)
        tests += len(images)
    # Swapping two identically situated sinks preserves the orientation
    # but changes the labelled order on the same domain.
    assert signature((0, 1, 2)) != signature((1, 0, 2))
    return dict(status="PASS", tested_enumerations=tests,
                negative_case="graph automorphism changes a labelled order",
                scope="finite labelled order relations, not image-copy degrees")

if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
