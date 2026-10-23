"""Exact CAS navigation evidence; Lean is the proof authority.

Carrier: AttentionFrameCorrections.Mat2 = Matrix (Fin 2) (Fin 2) ℝ.
Keys and ordering are copied from AttentionFrameCorrections.key, column action.
"""
import json
import sympy as s

keys = [s.Matrix([1, 0]), s.Matrix([0, 1]),
        s.Matrix([s.Rational(3, 5), s.Rational(4, 5)])]
identity = s.eye(2)
frame = sum((v * v.T for v in keys), s.zeros(2))
whitening = identity + (s.sqrt(2) / 2 - 1) * keys[2] * keys[2].T
vectors = [whitening * v for v in keys]
effects = [v * v.T for v in vectors]
assert s.simplify(whitening * frame * whitening) == identity
assert s.simplify(sum(effects, s.zeros(2))) == identity
readouts = [s.simplify(e.trace() / 2) for e in effects]
assert readouts == [s.Rational(41, 100), s.Rational(17, 50), s.Rational(1, 4)]
print(json.dumps({
    "owner": "InfoGeometry.LLM.AttentionFrameWhitening",
    "carrier": "Matrix (Fin 2) (Fin 2) ℝ",
    "basis_order": [0, 1], "key_order": [0, 1, 2],
    "action": "matrix times column", "frame": str(frame),
    "whitened_effect_sum": "identity",
    "maximally_mixed_readouts": list(map(str, readouts)),
    "authority": "CAS evidence only; kernel checks required"
}, indent=2))
