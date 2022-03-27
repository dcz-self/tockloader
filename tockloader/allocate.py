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
    """Base dataclass for apps which can be placed anywhere."""
    name: str
    size: int
    already_flashed: bool

    def get_fixed_starts(self):
        """Empty list if and only if the start can be placed anywhere."""
        return []


@dataclass
class FixedApp(App):
    # Applications that really deliver multiple binaries
    # have one size for all versions. Choose the maximum?
    # The solver *could* probably include a proper algorithm for that,
    # including sorting, but finding the sorting formula
    # each time the sorting needs to change is not worth the effort.
    # Multiple versions are a hack anyway.
    starts: [int]

    def get_fixed_starts(self):
        if len(self.starts) == 0:
            raise ValueError("No starts provided")
        return self.starts


@dataclass
class Solution:
    """Wraps the model for convenience of accessing the results."""
    align: int
    model: ModelRef

    def get_placement(self, name):
        """Returns start and size"""
        return (
            self.model[Int('start/' + name)].as_long() * self.align,
            self.model[Int('size/' + name)].as_long() * self.align,
        )


def ceildiv(a, b):
    return -(a // -b)


def is_power_of_two(x):
    powers = [ 2**i for i in range(32) ]
    return Or([ x == p for p in powers ])

"""For cortex-m, align should be 256, because that's the minimum region size, and tock assigns the entire region to the app."""
def solve_flash(free_memory_start, free_memory_end, align, apps):
    # Divide all constant values by alignment.
    # Remainders don't serve any purpose,
    # and this way variables will be aligned for free (after multiplying back).
    free_memory_start = ceildiv(free_memory_start, align)
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

    c_fixed = [
        Or(*[
            And(
                app_start // align >= start,
                ceildiv(app_start + a.size, align) <= start + size
            )
            for app_start in a.get_fixed_starts()
        ])
        for a, start, size in zip(apps, starts, sizes)
        if a.get_fixed_starts()
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

    constraints = (c_placement + c_size + c_fixed + c_overlap)
    s.add(*constraints)

    # Don't let apps reserve arbitrary amounts of space.
    s.minimize(sum(sizes))
    # Nudge apps towards the beginning.
    # This should fill the gaps and effectively sort them small-to-large.
    # Calculating ends to ensure that the largest app is not left at the end
    # if it could swap with an earlier one.
    s.minimize(sum(start + size for start, size in zip(starts, sizes)))
    # TODO: try to keep installed PIC apps where they already are.
    if s.check() == unknown:
        raise ValueError("Solution unknown")
    elif s.check() == unsat:
        return None
    else:
        return Solution(align, s.model())


"""For cortex-m, align should be 256, because that's the minimum region size, and tock assigns the entire region to the app."""
def solve_ram(free_memory_start, free_memory_end, align, apps):
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
        Or(*[app_start // align >= start for app_start in a.get_fixed_starts()])
        for a, start in zip(apps, starts)
        if a.get_fixed_starts()
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
        return Solution(align, s.model())

def test_ram():
    apps = [App('a', 10, False), FixedApp('b', 10, False, [0])]
    model = solve_ram(0,100, 1, apps).model

    assert(model[Int('start/a')].as_long() % 16 == 0)
    assert(model[Int('size/a')] == 16)
    
    assert(model[Int('start/b')] == 0)
    assert(model[Int('size/b')] == 16)
    
    apps = [FixedApp('a', 10, False, [10]), FixedApp('b', 10, False, [10])]
    solution = solve_ram(0, 100, 1, apps)
    assert(solution is None)
    
    apps = [FixedApp('a', 10, False, [0x10]), FixedApp('b', 10, False, [0, 10])]
    model = solve_ram(0, 100, 1, apps).model
    assert(model[Int('start/a')] == 0x10)
    assert(model[Int('size/a')] == 16)
    
    assert(model[Int('start/b')] == 0)
    assert(model[Int('size/b')] == 16)


def test_flash():
    apps = [FixedApp('a', 10, False, [0x10]), FixedApp('b', 10, False, [2048])]
    assert(solve_flash(0, 2048, 1024, apps) is None)

    apps = [FixedApp('a', 10, False, [0x10]), FixedApp('b', 10, False, [1020])]
    assert(solve_flash(0, 2048, 1024, apps) is None)
    
    apps = [FixedApp('a', 10, False, [0x10]), FixedApp('b', 10, False, [2040])]
    solution = solve_flash(0, 0x1000, 1024, apps)
    assert(solution.get_placement("b") == (1024, 2048))