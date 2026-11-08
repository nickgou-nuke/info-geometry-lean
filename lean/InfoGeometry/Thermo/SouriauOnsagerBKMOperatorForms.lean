import InfoGeometry.Canonical.SouriauOnsagerBKMRealForm
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.SouriauOnsagerBKMPositivity
import InfoGeometry.OperatorAlgebra.OperatorExteriorAlgebra

/-!
# BKM readouts on operator-valued one-forms

This is the finite operator-form bridge between the BKM Hessian and the
Onsager one-form interface.  It does not identify the BKM pairing with a
Maurer--Cartan form or with a spinor expectation: those require additional
geometric and representation-theoretic data.
-/

noncomputable section

namespace InfoGeometry.Thermo.SouriauOnsagerBKMOperatorForms

open InfoGeometry.OperatorAlgebra.ExteriorAlgebra
open SouriauOnsagerBKM

variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The BKM Onsager readout of two operator-valued one-forms on a test vector. -/
def bkmOperator1Form
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (α β : Op1Form ℝ V (FiniteOperatorAlgebra n)) (u : V) : ℝ :=
  D.bkmRealBilinForm h (α u) (β u)

theorem bkmOperator1Form_swap
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (α β : Op1Form ℝ V (FiniteOperatorAlgebra n)) (u : V) :
    bkmOperator1Form D h α β u = bkmOperator1Form D h β α u := by
  unfold bkmOperator1Form
  exact (D.bkmRealBilinForm_symm h).eq (α u) (β u)

theorem bkmOperator1Form_nonneg
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (α : Op1Form ℝ V (FiniteOperatorAlgebra n)) (u : V) :
    0 ≤ bkmOperator1Form D h α α u := by
  unfold bkmOperator1Form
  exact D.kuboMoriPairing_self_re_nonneg (α u) h

theorem bkmOperator1Form_eq_onsager_dissipative_readout
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (α β : Op1Form ℝ V (FiniteOperatorAlgebra n)) (u : V) :
    bkmOperator1Form D h α β u =
      D.bkmRealBilinForm h (α u) (β u) := by
  rfl

/- The mixed Onsager response is the polarization of the BKM quadratic
   response.  This is the finite operator-form version of the Dikin metric
   polarization identity. -/
theorem bkmOperator1Form_polarization
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (α β : Op1Form ℝ V (FiniteOperatorAlgebra n)) (u : V) :
    bkmOperator1Form D h α β u =
      (bkmOperator1Form D h (α + β) (α + β) u -
        bkmOperator1Form D h α α u -
        bkmOperator1Form D h β β u) / 2 := by
  unfold bkmOperator1Form
  have hs := (D.bkmRealBilinForm_symm h).eq (α u) (β u)
  change D.bkmRealBilinForm h (α u) (β u) =
    (D.bkmRealBilinForm h ((α + β) u) ((α + β) u) -
      D.bkmRealBilinForm h (α u) (α u) -
      D.bkmRealBilinForm h (β u) (β u)) / 2
  rw [show (α + β) u = α u + β u by rfl]
  rw [map_add, map_add]
  simp only [LinearMap.add_apply]
  rw [hs]
  ring

/-! ## Curvature-form readouts -/

/- A BKM probe readout of an operator-valued alternating two-form. -/
def bkmProbeReadout
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (Q : FiniteOperatorAlgebra n)
    (ω : Op2Form ℝ V (FiniteOperatorAlgebra n)) (u v : V) : ℝ :=
  D.bkmRealBilinForm h (ω u v) Q

@[simp] theorem bkmProbeReadout_zero
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (Q : FiniteOperatorAlgebra n) (u v : V) :
    bkmProbeReadout D h Q
        (Zero.zero : Op2Form ℝ V (FiniteOperatorAlgebra n)) u v = 0 := by
  unfold bkmProbeReadout
  change D.bkmRealBilinForm h 0 Q = 0
  simp

theorem bkmProbeReadout_skew
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (Q : FiniteOperatorAlgebra n)
    (ω : Op2Form ℝ V (FiniteOperatorAlgebra n)) (u v : V) :
    bkmProbeReadout D h Q ω u v =
      - bkmProbeReadout D h Q ω v u := by
  unfold bkmProbeReadout
  rw [ω.skew, map_neg]
  rfl

theorem bkmProbeReadout_wedge_self
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (Q : FiniteOperatorAlgebra n)
    (α : Op1Form ℝ V (FiniteOperatorAlgebra n)) (u v : V) :
    bkmProbeReadout D h Q (wedge α α) u v =
      D.bkmRealBilinForm h (α u * α v - α v * α u) Q := by
  rfl

theorem bkmProbeReadout_wedge_self_diag_zero
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (Q : FiniteOperatorAlgebra n)
    (α : Op1Form ℝ V (FiniteOperatorAlgebra n)) (u : V) :
    bkmProbeReadout D h Q (wedge α α) u u = 0 := by
  unfold bkmProbeReadout
  simp

theorem bkmProbeReadout_add_left
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (Q : FiniteOperatorAlgebra n)
    (ω₁ ω₂ : Op2Form ℝ V (FiniteOperatorAlgebra n)) (u v : V) :
    bkmProbeReadout D h Q (ω₁ + ω₂) u v =
      bkmProbeReadout D h Q ω₁ u v +
        bkmProbeReadout D h Q ω₂ u v := by
  unfold bkmProbeReadout
  change
    D.bkmRealBilinForm h
        (ω₁.toBilin u v + ω₂.toBilin u v) Q =
      D.bkmRealBilinForm h (ω₁.toBilin u v) Q +
        D.bkmRealBilinForm h (ω₂.toBilin u v) Q
  rw [(D.bkmRealBilinForm h).map_add]
  rfl

theorem bkmProbeReadout_smul_left
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (Q : FiniteOperatorAlgebra n)
    (c : ℝ) (ω : Op2Form ℝ V (FiniteOperatorAlgebra n)) (u v : V) :
    bkmProbeReadout D h Q (c • ω) u v =
      c * bkmProbeReadout D h Q ω u v := by
  unfold bkmProbeReadout
  change
    D.bkmRealBilinForm h (c • (ω.toBilin u v)) Q =
      c * D.bkmRealBilinForm h (ω.toBilin u v) Q
  rw [(D.bkmRealBilinForm h).map_smul]
  rfl

@[simp] theorem bkmProbeReadout_neg_left
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (Q : FiniteOperatorAlgebra n) (ω : Op2Form ℝ V (FiniteOperatorAlgebra n))
    (u v : V) :
    bkmProbeReadout D h Q (-ω) u v =
      -bkmProbeReadout D h Q ω u v := by
  unfold bkmProbeReadout
  change D.bkmRealBilinForm h (-(ω.toBilin u v)) Q =
    -D.bkmRealBilinForm h (ω.toBilin u v) Q
  rw [(D.bkmRealBilinForm h).map_neg]
  rfl

theorem bkmProbeReadout_sub_left
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (Q : FiniteOperatorAlgebra n)
    (ω₁ ω₂ : Op2Form ℝ V (FiniteOperatorAlgebra n)) (u v : V) :
    bkmProbeReadout D h Q (ω₁ - ω₂) u v =
      bkmProbeReadout D h Q ω₁ u v -
        bkmProbeReadout D h Q ω₂ u v := by
  unfold bkmProbeReadout
  change D.bkmRealBilinForm h
      (ω₁.toBilin u v - ω₂.toBilin u v) Q =
    D.bkmRealBilinForm h (ω₁.toBilin u v) Q -
      D.bkmRealBilinForm h (ω₂.toBilin u v) Q
  rw [(D.bkmRealBilinForm h).map_sub]
  rfl

/- The probed self-wedge is an alternating scalar two-form on the finite
    tangent carrier.  The two components are kept explicit so downstream
    exterior-calculus owners need no pointwise reinterpretation. -/
theorem bkmProbeReadout_wedge_self_alternating
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (Q : FiniteOperatorAlgebra n)
    (α : Op1Form ℝ V (FiniteOperatorAlgebra n)) :
    (∀ u v : V,
      bkmProbeReadout D h Q (wedge α α) u v =
        - bkmProbeReadout D h Q (wedge α α) v u) ∧
      (∀ u : V, bkmProbeReadout D h Q (wedge α α) u u = 0) := by
  constructor
  · intro u v
    exact bkmProbeReadout_skew D h Q (wedge α α) u v
  · intro u
    exact bkmProbeReadout_wedge_self_diag_zero D h Q α u

end InfoGeometry.Thermo.SouriauOnsagerBKMOperatorForms

end noncomputable section
