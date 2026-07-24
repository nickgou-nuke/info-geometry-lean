import Mathlib.Data.Complex.Basic
import InfoGeometry.GrandUnification.HodgeCartanTrifactor

/-!
# Centered-coordinate reflection and Cartan sign readouts

This module proves two elementary algebraic facts: the affine coordinate
`1/2 + u + iv` sends the map `(u,v) ↦ (-u,-v)` to `s ↦ 1 - s`, and the declared
Cartan involution fixes the harmonic sector while negating the exact/coexact
sectors under the supplied projection hypotheses.  It does not prove a
Riemann-zero localization theorem.
-/

namespace InfoGeometry.GrandUnification.UVSymmetry

/-- The centered holomorphic coordinate chart at s = 1/2. -/
structure UVChart where
  u : ℝ
  v : ℝ

/-- Map the centered (u, v) coordinates back to the classical complex plane `s = 1/2 + u + iv`. -/
noncomputable def UVChart.toComplex (z : UVChart) : ℂ :=
  ⟨(1 / 2 : ℝ) + z.u, z.v⟩

/-- The geometric central inversion (Parity + Time reversal). -/
def central_inversion (z : UVChart) : UVChart :=
  ⟨-z.u, -z.v⟩

/-- The affine coordinate reflection `s ↦ 1 - s` is central inversion in
centered `(u, v)` coordinates. -/
theorem functional_equation_isomorphism (z : UVChart) :
    (1 : ℂ) - z.toComplex = (central_inversion z).toComplex := by
  unfold UVChart.toComplex central_inversion
  apply Complex.ext
  · dsimp
    ring
  · dsimp
    ring

/-! ### Topological Annihilation on the Klein Bottle Seam -/

open InfoGeometry.GrandUnification.HodgeCartan
open InfoGeometry.Canonical.TrifactorDecomposition

section Basic

variable {R : Type*} [CommRing R]
variable (T : R)

/-- A state `ρ` survives the non-orientable boundary if it is invariant under the Cartan Involution. -/
def survives_topology (ρ : R) : Prop :=
  cartan_involution T * ρ = ρ

/-- If `ρ` is fixed by the harmonic operator, then it is fixed by the declared
Cartan involution. -/
theorem harmonic_trap_survives (hT : T ^ 3 = T) (ρ : R) (h_harmonic : harmonic_op T * ρ = ρ) :
    survives_topology T ρ := by
  unfold survives_topology
  calc
    cartan_involution T * ρ = cartan_involution T * (harmonic_op T * ρ) := congrArg (fun x => cartan_involution T * x) h_harmonic.symm
    _ = (cartan_involution T * harmonic_op T) * ρ := by rw [mul_assoc]
    _ = harmonic_op T * ρ := by rw [cartan_symmetric_harmonic T hT]
    _ = ρ := h_harmonic

end Basic

section WithHalf

variable {R : Type*} [CommRing R] [Invertible (2 : R)]
variable (T : R)

/-- If `ρ` is fixed by the exact operator, then the declared Cartan involution
acts by negation. -/
theorem exact_annihilation (hT : T ^ 3 = T) (ρ : R) (h_exact : exact_op T * ρ = ρ) :
    cartan_involution T * ρ = -ρ := by
  calc
    cartan_involution T * ρ = cartan_involution T * (exact_op T * ρ) := congrArg (fun x => cartan_involution T * x) h_exact.symm
    _ = (cartan_involution T * exact_op T) * ρ := by rw [mul_assoc]
    _ = (- exact_op T) * ρ := by rw [cartan_antisymmetric_exact T hT]
    _ = - (exact_op T * ρ) := by ring
    _ = -ρ := by rw [h_exact]

/-- If `ρ` is fixed by the coexact operator, then the declared Cartan involution
acts by negation. -/
theorem coexact_annihilation (hT : T ^ 3 = T) (ρ : R) (h_coexact : coexact_op T * ρ = ρ) :
    cartan_involution T * ρ = -ρ := by
  calc
    cartan_involution T * ρ = cartan_involution T * (coexact_op T * ρ) := congrArg (fun x => cartan_involution T * x) h_coexact.symm
    _ = (cartan_involution T * coexact_op T) * ρ := by rw [mul_assoc]
    _ = (- coexact_op T) * ρ := by rw [cartan_antisymmetric_coexact T hT]
    _ = - (coexact_op T * ρ) := by ring
    _ = -ρ := by rw [h_coexact]

end WithHalf

end InfoGeometry.GrandUnification.UVSymmetry
