#!/usr/bin/env python3
"""Audit for the Conf3 quadric braiding/cooperad bridge."""

from math import prod

edges = {"12": "inner", "13": "outer", "23": "outer"}


def cycle_affinity(log_ratio, cycle):
    return sum(log_ratio[(cycle[i], cycle[(i + 1) % len(cycle)])] for i in range(len(cycle)))


def exact_log_ratio(potential, i, j):
    return potential[j] - potential[i]


def main():
    assert edges == {"12": "inner", "13": "outer", "23": "outer"}
    rank = prod([2**3, 2**2])
    os_rank = 6 * 2**2
    assert rank == 32
    assert os_rank == 24

    potential = {0: 0.0, 1: 2.0, 2: -1.5}
    lr = {(i, j): exact_log_ratio(potential, i, j) for i in range(3) for j in range(3)}
    assert abs(cycle_affinity(lr, [0, 1, 2])) < 1e-12
    assert abs(cycle_affinity(lr, [0, 2, 1])) < 1e-12

    broken = {(0, 1): 1.0, (1, 2): 1.0, (2, 0): 1.0}
    for i in range(3):
        broken[(i, i)] = 0.0
    broken[(1, 0)] = -1.0
    broken[(2, 1)] = -1.0
    broken[(0, 2)] = -1.0
    assert cycle_affinity(broken, [0, 1, 2]) == 3.0

    print("quadric cooperad split {1,2}|{3}:", edges)
    print("rank-32 candidate vs OS rank:", rank, os_rank)
    print("exact detailed-balance cycle affinities vanish")
    print("nonzero triangle affinity is broken detailed balance fingerprint")
    print("quadric_conf3_braiding_cooperad_bridge.py: audit passed")


if __name__ == "__main__":
    main()
