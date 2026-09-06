import InfoGeometry.Projective.TwistorConfigurationSpace

/-!
# Concrete three-point Arnold form packet

This owner supplies the finite algebraic shadow of the three logarithmic
forms on the Arnold--Cohen quotient.  The symbols below are quotient images
of exterior generators; they are not yet analytic `d log Q` differential
forms on a configuration manifold.  In particular, this file does not
construct a KZ connection, its monodromy, or a de Rham comparison.
-/

namespace InfoGeometry.Projective.Conf3ArnoldDifferentialForms

open InfoGeometry.Projective.Amplituhedron

noncomputable section

abbrev Conf3ArnoldExterior := ExteriorAlgebra ℂ ((Fin 3 × Fin 3) →₀ ℂ)

/-- The three ordered edge generators in the finite Arnold quotient. -/
def ω12 : Conf3ArnoldExterior := w ℂ (Fin 3) 0 1

def ω23 : Conf3ArnoldExterior := w ℂ (Fin 3) 1 2

def ω31 : Conf3ArnoldExterior := w ℂ (Fin 3) 2 0

@[simp] theorem ω12_eq_formalLogForm :
    ω12 = w ℂ (Fin 3) 0 1 := rfl

@[simp] theorem ω23_eq_formalLogForm :
    ω23 = w ℂ (Fin 3) 1 2 := rfl

@[simp] theorem ω31_eq_formalLogForm :
    ω31 = w ℂ (Fin 3) 2 0 := rfl

/-- The mixed Arnold relation in the finite quotient algebra. -/
theorem concrete_arnold_relation :
    (RingQuot.mkRingHom (ArnoldRel ℂ (Fin 3)))
        (ω12 * ω23 + ω23 * ω31 + ω31 * ω12) =
      (RingQuot.mkRingHom (ArnoldRel ℂ (Fin 3))) 0 := by
  simpa [ω12, ω23, ω31] using
    (arnold_mixed_relation_quotient_zero (R := ℂ) (ι := Fin 3) 0 1 2)

/-! The following research boundary is intentional: the quotient relation is
the proven algebraic datum, while analytic `d log Q` realization remains a
separate owner obligation. -/

end
end InfoGeometry.Projective.Conf3ArnoldDifferentialForms
