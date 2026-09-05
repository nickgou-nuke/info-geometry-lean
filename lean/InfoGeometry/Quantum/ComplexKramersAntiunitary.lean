import Mathlib

/-!
# The canonical complex Kramers antiunitary on `ℂ²`

The repository already owns a real-linear Kramers interface on a doubled Krein
carrier.  This file supplies the missing complex conjugate-semilinear model.

The map

`T(z₀,z₁) = (-conj z₁, conj z₀)`

is bundled as a native Mathlib star-linear equivalence.  Its square is `-1`,
it reverses the standard Hermitian pairing, and every vector is orthogonal to
its Kramers partner.  No spacetime quotient or physical time evolution is
inferred from this finite operator.
-/

noncomputable section

namespace InfoGeometry.Quantum.ComplexKramersAntiunitary

open scoped ComplexConjugate

/-- The standard two-component complex carrier. -/
abbrev H2 := Fin 2 → ℂ

/-- Standard Hermitian pairing, conjugate-linear in its first argument. -/
def standardInner (u v : H2) : ℂ :=
  star (u 0) * v 0 + star (u 1) * v 1

@[simp] theorem standardInner_zero_left (v : H2) :
    standardInner 0 v = 0 := by
  simp [standardInner]

@[simp] theorem standardInner_zero_right (u : H2) :
    standardInner u 0 = 0 := by
  simp [standardInner]

@[simp] theorem standardInner_add_left (u v w : H2) :
    standardInner (u + v) w = standardInner u w + standardInner v w := by
  simp [standardInner]
  ring

@[simp] theorem standardInner_add_right (u v w : H2) :
    standardInner u (v + w) = standardInner u v + standardInner u w := by
  simp [standardInner]
  ring

@[simp] theorem standardInner_smul_left (c : ℂ) (u v : H2) :
    standardInner (c • u) v = star c * standardInner u v := by
  simp [standardInner, Pi.smul_apply]
  ring

@[simp] theorem standardInner_smul_right (c : ℂ) (u v : H2) :
    standardInner u (c • v) = c * standardInner u v := by
  simp [standardInner, Pi.smul_apply]
  ring

@[simp] theorem standardInner_conj_symm (u v : H2) :
    star (standardInner u v) = standardInner v u := by
  simp [standardInner]
  ring

/-- The canonical fermionic time-reversal map, bundled as a conjugate-linear
bijection. -/
def timeReversal : H2 ≃ₗ⋆[ℂ] H2 where
  toFun v := ![-star (v 1), star (v 0)]
  invFun v := ![star (v 1), -star (v 0)]
  left_inv v := by
    ext i
    fin_cases i <;> simp
  right_inv v := by
    ext i
    fin_cases i <;> simp
  map_add' u v := by
    ext i
    fin_cases i <;> simp
  map_smul' c v := by
    ext i
    fin_cases i <;> simp [Pi.smul_apply] <;> ring

@[simp] theorem timeReversal_apply_zero (v : H2) :
    timeReversal v 0 = -star (v 1) := rfl

@[simp] theorem timeReversal_apply_one (v : H2) :
    timeReversal v 1 = star (v 0) := rfl

@[simp] theorem timeReversal_add (u v : H2) :
    timeReversal (u + v) = timeReversal u + timeReversal v := by
  exact map_add timeReversal u v

@[simp] theorem timeReversal_smul (c : ℂ) (v : H2) :
    timeReversal (c • v) = star c • timeReversal v := by
  exact map_smulₛₗ timeReversal c v

/-- Quaternionic/Kramers square law. -/
@[simp] theorem timeReversal_sq (v : H2) :
    timeReversal (timeReversal v) = -v := by
  ext i
  fin_cases i <;> simp [timeReversal]

@[simp] theorem timeReversal_fourth (v : H2) :
    timeReversal (timeReversal (timeReversal (timeReversal v))) = v := by
  simp

/-- Antiunitarity in inner-product form. -/
theorem timeReversal_antiunitary (u v : H2) :
    standardInner (timeReversal u) (timeReversal v) =
      standardInner v u := by
  simp [standardInner, timeReversal]
  ring

/-- Every vector is orthogonal to its Kramers partner. -/
@[simp] theorem timeReversal_kramers_orthogonal (v : H2) :
    standardInner v (timeReversal v) = 0 := by
  simp [standardInner, timeReversal]
  ring

/-- A nonzero vector cannot be fixed by the square-minus-one map. -/
theorem timeReversal_ne_self_of_ne_zero {v : H2} (hv : v ≠ 0) :
    timeReversal v ≠ v := by
  intro hfixed
  have htwice : timeReversal (timeReversal v) = timeReversal v :=
    congrArg timeReversal hfixed
  have hneg : -v = v := by
    simpa [hfixed] using htwice
  have htwo : (2 : ℂ) • v = 0 := by
    calc
      (2 : ℂ) • v = v + v := by simp [two_smul]
      _ = -v + v := by rw [hneg]
      _ = 0 := neg_add_cancel v
  exact hv ((smul_eq_zero.mp htwo).resolve_left (by norm_num))

/-- If a complex-linear operator commutes with `T`, the Kramers partner of an
eigenvector with real eigenvalue is another eigenvector with the same
eigenvalue. -/
theorem timeReversal_preserves_real_eigenvalue
    (A : Module.End ℂ H2)
    (hcomm : ∀ v, A (timeReversal v) = timeReversal (A v))
    (λ : ℝ) (v : H2)
    (hv : A v = (λ : ℂ) • v) :
    A (timeReversal v) = (λ : ℂ) • timeReversal v := by
  rw [hcomm, hv, timeReversal_smul]
  simp

/-- Finite Kramers-pair packet for a symmetry-compatible eigenspace. -/
theorem kramers_eigenpair_packet
    (A : Module.End ℂ H2)
    (hcomm : ∀ v, A (timeReversal v) = timeReversal (A v))
    (λ : ℝ) (v : H2) (hv0 : v ≠ 0)
    (hv : A v = (λ : ℂ) • v) :
    A (timeReversal v) = (λ : ℂ) • timeReversal v ∧
      standardInner v (timeReversal v) = 0 ∧
      timeReversal v ≠ v := by
  exact ⟨timeReversal_preserves_real_eigenvalue A hcomm λ v hv,
    timeReversal_kramers_orthogonal v,
    timeReversal_ne_self_of_ne_zero hv0⟩

end InfoGeometry.Quantum.ComplexKramersAntiunitary
