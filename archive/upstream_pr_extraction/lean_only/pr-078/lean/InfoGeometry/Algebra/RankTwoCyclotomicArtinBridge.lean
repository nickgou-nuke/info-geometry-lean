/- SPDX-License-Identifier: Apache-2.0 -/

import Mathlib

namespace InfoGeometry.Algebra.RankTwoCyclotomicArtinBridge

variable {K : Type*} [DivisionRing K]

/-- The rank-two quantum-integer parameter.  Its interpretation as a Coxeter
    parameter is supplied by a later representation-specific owner. -/
def quantumInteger (q : K) : K := q + q⁻¹

@[simp] theorem quantumInteger_apply (q : K) :
    quantumInteger q = q + q⁻¹ := rfl

/-- Polynomial form of the Fibonacci/I₂(5) parameter equation. -/
theorem quantumInteger_five
    (q φ : K) (hφ : φ ^ 2 = φ + 1)
    (hq : quantumInteger q = φ) :
    (quantumInteger q) ^ 2 = quantumInteger q + 1 := by
  rw [hq, hφ]

/-- Polynomial form of the G₂/I₂(6) parameter equation. -/
theorem quantumInteger_six
    (q d : K) (hd : d ^ 2 = 3)
    (hq : quantumInteger q = d) :
    (quantumInteger q) ^ 2 = 3 := by
  rw [hq, hd]

/-- The two rank-two polynomial regimes are propositions about the parameter;
    no equivalence between their representation or categorical realizations is
    asserted here. -/
structure RankTwoCyclotomicDatum where
  q : K
  parameter : K
  parameter_eq : parameter = quantumInteger q

theorem datum_parameter_sq_eq_three
    (D : RankTwoCyclotomicDatum (K := K))
    (h : D.parameter ^ 2 = 3) :
    D.parameter ^ 2 = 3 := h

end InfoGeometry.Algebra.RankTwoCyclotomicArtinBridge
