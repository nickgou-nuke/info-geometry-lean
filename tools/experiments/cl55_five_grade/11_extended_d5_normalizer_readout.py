"""Finite signed-permutation readout for the extended D5 normalizer."""

from __future__ import annotations

import itertools
import json
import math
from pathlib import Path


Indices = tuple[int, int, int, int, int]
Signs = tuple[int, int, int, int, int]
Element = tuple[Signs, Indices]


def compose(left: Element, right: Element) -> Element:
    """Composition for H_i |-> sign_i H_perm(i)."""
    left_signs, left_perm = left
    right_signs, right_perm = right
    signs = tuple(left_signs[right_perm[i]] * right_signs[i]
                  for i in range(5))
    perm = tuple(left_perm[right_perm[i]] for i in range(5))
    return signs, perm


identity: Element = ((1, 1, 1, 1, 1), (0, 1, 2, 3, 4))
all_elements = {
    (signs, perm)
    for signs in itertools.product((-1, 1), repeat=5)
    for perm in itertools.permutations(range(5))
}
assert len(all_elements) == 2 ** 5 * math.factorial(5)


def inverse(element: Element) -> Element:
    for candidate in all_elements:
        if compose(element, candidate) == identity and \
                compose(candidate, element) == identity:
            return candidate
    raise AssertionError("inverse not found")


def adjacent_swap(index: int) -> Element:
    perm = list(range(5))
    perm[index], perm[index + 1] = perm[index + 1], perm[index]
    return (1, 1, 1, 1, 1), tuple(perm)


def sign_reflection(index: int) -> Element:
    signs = [1] * 5
    signs[index] = -1
    return tuple(signs), (0, 1, 2, 3, 4)


def generated_by(generators: list[Element]) -> set[Element]:
    generated = {identity}
    changed = True
    while changed:
        changed = False
        for left in list(generated):
            for right in generators:
                candidate = compose(left, right)
                if candidate not in generated:
                    generated.add(candidate)
                    changed = True
    return generated


s = [adjacent_swap(i) for i in range(4)]
r = sign_reflection(4)
generators = s + [r]
generated = generated_by(generators)
assert generated == all_elements

def power(element: Element, exponent: int) -> Element:
    result = identity
    for _ in range(exponent):
        result = compose(result, element)
    return result


assert all(power(generator, 2) == identity for generator in generators)
assert all(power(compose(s[i], s[i + 1]), 3) == identity
           for i in range(3))
assert power(compose(s[3], r), 4) == identity
assert all(power(compose(s[i], s[j]), 2) == identity
           for i in range(4) for j in range(i + 1, 4) if j - i > 1)

positive_N = tuple(1 for _ in range(5))
negative_N = tuple(-1 for _ in range(5))


def image_of_vector(element: Element, vector: tuple[int, ...]) -> tuple[int, ...]:
    signs, perm = element
    image = [0] * 5
    for i in range(5):
        image[perm[i]] += signs[i] * vector[i]
    return tuple(image)


stabilizer_N = {
    element for element in all_elements
    if image_of_vector(element, positive_N) == positive_N
}
stabilizer_line_N = {
    element for element in all_elements
    if image_of_vector(element, positive_N) in {positive_N, negative_N}
}
assert len(stabilizer_N) == math.factorial(5)
assert len(stabilizer_line_N) == 2 * math.factorial(5)

report = {
    "coefficient_field": "combinatorial_exact",
    "ambient_group": "(Z/2Z)^5 semidirect S5",
    "order": len(generated),
    "generators": ["s1", "s2", "s3", "s4", "r5"],
    "coxeter_relations": True,
    "stabilizer_N_order": len(stabilizer_N),
    "stabilizer_RN_order": len(stabilizer_line_N),
    "pin_lift_identified": False,
    "weyl_isomorphism_proved": False,
    "scope": "finite_signed_cartan_readout",
}

output = Path("tools/experiments/cl55_five_grade/export/extended_d5_normalizer.json")
output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
print("PYTHON:signed_normalizer_order=%d" % len(generated))
print("PYTHON:coxeter_relations=true")
print("PYTHON:stabilizer_N_order=%d" % len(stabilizer_N))
print("PYTHON:stabilizer_RN_order=%d" % len(stabilizer_line_N))
print("PYTHON:report=%s" % output)
