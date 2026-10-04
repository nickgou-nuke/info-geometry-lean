#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Run independent finite examples from the former attention/fluid narrative.

This script checks numerical instances of softmax normalization, the
log-partition covariance formula, and the divergence of a chosen linear vector
field. It does not derive a causal connection among attention, KMS states,
Clifford operators, and fluid dynamics.
"""

import numpy as np


def softmax(logits: np.ndarray) -> np.ndarray:
    shifted = logits - np.max(logits, axis=-1, keepdims=True)
    weights = np.exp(shifted)
    return weights / np.sum(weights, axis=-1, keepdims=True)


def main() -> None:
    print("Independent finite checks (numerical examples, not theorem proofs)")

    logits = np.array([[0.4, -0.7, 1.1], [0.2, 0.8, -0.3]])
    probabilities = softmax(logits)
    print("\nSoftmax rows:")
    print(probabilities)
    print("row sums:", probabilities.sum(axis=1))
    assert np.all(probabilities > 0)
    assert np.allclose(probabilities.sum(axis=1), 1.0)

    p = probabilities[0]
    hessian = np.diag(p) - np.outer(p, p)
    direction = np.array([0.3, -1.0, 0.6])
    mean = np.dot(p, direction)
    variance = np.dot(p, (direction - mean) ** 2)
    quadratic_form = direction @ hessian @ direction
    print("\nCovariance Hessian quadratic form:", quadratic_form)
    print("Weighted variance:", variance)
    assert np.allclose(quadratic_form, variance)

    shift = 7.25
    shifted_probabilities = softmax(logits + shift)
    print("\nUniform-logit-shift invariance:",
          np.allclose(probabilities, shifted_probabilities))
    assert np.allclose(probabilities, shifted_probabilities)

    # A separate linear vector field u(x)=A x has divergence trace(A).
    # For this chosen skew-symmetric A, both quantities vanish.
    A = np.array([[0.0, -1.0], [1.0, 0.0]])
    divergence = np.trace(A)
    print("\nChosen skew matrix trace / linear-field divergence:", divergence)
    assert np.isclose(divergence, 0.0)

    print("\nAll finite examples passed. No attention-to-fluid, KMS, or physical-limit theorem is asserted.")


if __name__ == "__main__":
    main()
