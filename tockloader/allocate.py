"""
Solves the problem of positioning apps in the board's memory.

This is an example of the cutting stock problem:
https://en.wikipedia.org/wiki/Cutting_stock_problem

which is similar to the knapsack problem.
It can be solved in the general case using a SAT solver
by just providing the constraints,
rather than trying to solve the specific instance of the problem.

With a SAT solver, modifications to requirements
don't change the way to reach the solution, just the constraints.
"""

# Useful resources for the z3 solver:
# https://ericpony.github.io/z3py-tutorial/guide-examples.htm
# http://theory.stanford.edu/~nikolaj/programmingz3.html#sec-optimization
# https://z3prover.github.io/api/html/namespacez3py.html

from dataclasses import dataclass
import functools
from itertools import product
import z3
from z3 import *

@dataclass
class App:
    name: str
    start: int
    size: int
    fixed: bool

def ceildiv(a, b):
    return -(a // -b)

def is_power_of_two(x):
    powers = [ 2**i for i in range(32) ]
    return Or([ x == p for p in powers ])

"""For cortex-m, align should be 256, because that's the minimum region size, and tock assigns the entire region to the app."""
def solve(free_memory_start, free_memory_end, align, apps):
    free_memory_start //= align
    free_memory_end //= align
    s = Optimize()

    # Free variables: we want to find them.
    starts = [Int("start/" + a.name) for a in apps]
    sizes = [Int("size/" + a.name) for a in apps]

    # constraints
    def within_memory(start, size):
        return And(
            start >= free_memory_start,
            start + size <= free_memory_end,
        )

    def cortex_m_region_aligned(start, size):
        return And(
            start % size == 0,
            is_power_of_two(size),
        )

    c_placement = [
        And(within_memory(start, size), cortex_m_region_aligned(start, size))
        for start, size in zip(starts, sizes)
    ]

    c_size = [ceildiv(a.size, align) <= size for a, size in zip(apps, sizes)]

    c_start = [
        a.start // align >= start
        for a, start in zip(apps, starts) if a.fixed
    ]
    
    c_overlap = [
        Or(
            a_start >= b_start + b_end,
            b_start >= a_start + a_end,
        )
        for (a, (a_start, a_end)), (b, (b_start, b_end))
        in product(
            enumerate(zip(starts, sizes)),
            enumerate(zip(starts, sizes)),
        )
        if a < b
    ]

    constraints = (c_placement + c_size + c_start + c_overlap)
    s.add(*constraints)

    s.minimize(functools.reduce(lambda x, y: x + y, sizes))

    if s.check() == unknown:
        raise ValueError("Solution unknown")
    elif s.check() == unsat:
        return None
    else:
        return s.model()

def test():
    apps = [App('a', 0, 10, False), App('b', 0, 10, True)]
    model = solve(0,100, 1, apps)

    assert(model[Int('start/a')].as_long() % 16 == 0)
    assert(model[Int('size/a')] == 16)
    
    assert(model[Int('start/b')] == 0)
    assert(model[Int('size/b')] == 16)
    