#!/usr/bin/env python3
"""Construct an explicit π-tie in the manuscript's pointed closure host W.

Two permitted pointed closures of different cardinalities may give the
chosen generator the same natural coordinate, so the binary relation
u ◁ v :↔ π(u)<π(v) is NOT globally total. On any individually
increasing labelled coordinate assignment the comparison is total.
"""


def pointed_code(vertices, arrows, point, coordinate):
    assert point in vertices
    assert set(coordinate) == set(vertices)
    assert len(set(coordinate.values())) == len(vertices)
    assert all(x in vertices and y in vertices for x,y in arrows)
    assert all(x != y for x,y in arrows)
    # Outgoing sets and their (finite) successor closure are consistent.
    reached={point}
    while True:
        new=reached|{y for x,y in arrows if x in reached}
        if reached==new:
            break
        reached=new
    assert reached==set(vertices)
    return (frozenset(vertices),frozenset(arrows),point,dict(coordinate))


def pi(code):
    return code[3][code[2]]


def triangleleft(left,right):
    return pi(left)<pi(right)


def check_tie():
    single=pointed_code(
        vertices={"a"},arrows=set(),point="a",
        coordinate={"a":1})
    edge=pointed_code(
        vertices={"a","b"},arrows={("a","b")},point="a",
        coordinate={"a":1,"b":0})
    # Different cardinality prevents any pointed closure isomorphism.
    assert len(single[0])!=len(edge[0])
    assert pi(single)==pi(edge)==1
    assert not triangleleft(single,edge)
    assert not triangleleft(edge,single)


def check_restricted_order():
    # In a finite increasing image, each vertex is represented by its
    # complete pointed closure and receives its chosen distinct rank.
    singleton_0=pointed_code({"u"},set(),"u",{"u":0})
    singleton_1=pointed_code({"v"},set(),"v",{"v":1})
    assert triangleleft(singleton_0,singleton_1)
    assert not triangleleft(singleton_1,singleton_0)
    assert pi(singleton_0)!=pi(singleton_1)
    # One connected one-generated closure has two coordinates, and the
    # lower successor is before the top generator in its valid ordering.
    lower=pointed_code({"b"},set(),"b",{"b":0})
    upper=pointed_code({"a","b"},{("a","b")},"a",{"a":1,"b":0})
    assert triangleleft(lower,upper)


def main():
    check_tie()
    check_restricted_order()
    print("PASS: π is not injective on W; tied distinct pointed closures "
          "witness failure of global trichotomy; comparisons remain "
          "strict and ordered on increasing finite images.")


if __name__=="__main__":
    main()
