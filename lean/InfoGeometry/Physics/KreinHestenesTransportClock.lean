import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Finite Krein/Hestenes transport and parabolic clock

The doubled carrier has a cross (indefinite) pairing, a swap fundamental
symmetry, and a positive realization obtained by applying that symmetry in
the second slot.  A separate square-zero linear operator supplies an exact
additive parabolic clock.

This owner does not assert an infinite-dimensional Wasserstein theorem.  It
provides the finite operator identities on which such a construction could be
based.
-/

namespace InfoGeometry.Physics.KreinHestenesTransportClock

noncomputable section

open InfoGeometry.Krein

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E

/-- The real carrier's component exchange (not a separate geometric sheet). -/
noncomputable abbrev sheetSwap : H₂ →L[ℝ] H₂ := modular_j (E := E)

/-- The sign involution used as the Krein fundamental symmetry. -/
noncomputable abbrev fundamentalSymmetry : H₂ →L[ℝ] H₂ :=
  spectral_epsilon (E := E)

/-- The internal Hestenes complex structure. -/
noncomputable abbrev internalComplexStructure : H₂ →L[ℝ] H₂ :=
  complex_i (E := E)

theorem sheetSwap_sq :
    (sheetSwap (E := E)).comp sheetSwap =
      ContinuousLinearMap.id ℝ H₂ := by
  exact modular_j_involution E

theorem fundamentalSymmetry_sq :
    (fundamentalSymmetry (E := E)).comp fundamentalSymmetry =
      ContinuousLinearMap.id ℝ H₂ := by
  exact spectral_epsilon_involution E

theorem internalComplexStructure_sq :
    (internalComplexStructure (E := E)).comp internalComplexStructure =
      -(ContinuousLinearMap.id ℝ H₂) := by
  exact complex_i_sq E

theorem sheetSwap_internalComplex_anticommute :
    (sheetSwap (E := E)).comp internalComplexStructure =
      -(internalComplexStructure.comp sheetSwap) := by
  rw [modular_j_comp_complex_i (E := E),
    complex_i_comp_modular_j (E := E)]
  simp

theorem sheetSwap_fundamental_anticommute :
    (sheetSwap (E := E)).comp fundamentalSymmetry =
      -(fundamentalSymmetry.comp sheetSwap) := by
  exact modular_j_spectral_epsilon_anticommute E

/-- The cross-pairing of the two isotropic components. -/
noncomputable def crossPairing : LinearMap.BilinForm ℝ H₂ :=
  LinearMap.mk₂ ℝ
    (fun u v =>
      inner ℝ (WithLp.fst u) (WithLp.snd v) +
        inner ℝ (WithLp.snd u) (WithLp.fst v))
    (by
      intro u₁ u₂ v
      simp [inner_add_left, inner_add_right, add_assoc, add_left_comm, add_comm])
    (by
      intro c u v
      simp [real_inner_smul_left]
      ring)
    (by
      intro u v₁ v₂
      simp [inner_add_left, inner_add_right, add_assoc, add_left_comm, add_comm])
    (by
      intro c u v
      simp [real_inner_smul_right]
      ring)

theorem crossPairing_swap_eq_hilbert (u v : H₂) :
    crossPairing u (modular_j v) = doubledHilbertBilin u v := by
  simp [crossPairing, modular_j, doubledHilbertBilin,
    WithLp.prod_inner_apply, add_comm]

theorem crossPairing_isotropic_left (u v : E) :
    crossPairing (to_doubled u 0) (to_doubled v 0) = 0 := by
  simp [crossPairing]

theorem crossPairing_isotropic_right (u v : E) :
    crossPairing (to_doubled 0 u) (to_doubled 0 v) = 0 := by
  simp [crossPairing]

/-- Applying the swap to the cross-pairing gives the positive doubled Hilbert form. -/
noncomputable def positivePairing : LinearMap.BilinForm ℝ H₂ :=
  LinearMap.mk₂ ℝ (fun u v => crossPairing u (modular_j v))
    (by intro u₁ u₂ v; simp [map_add, add_assoc])
    (by intro c u v; simp [map_smul])
    (by intro u v₁ v₂; simp [map_add, add_assoc])
    (by intro c u v; simp [map_smul])

theorem positivePairing_eq_hilbert (u v : H₂) :
    positivePairing u v = doubledHilbertBilin u v := by
  rfl

theorem positivePairing_self_nonnegative (u : H₂) :
    0 ≤ positivePairing u u := by
  rw [positivePairing_eq_hilbert]
  exact real_inner_self_nonneg (x := u)

/-! ## Exact additive parabolic clock -/

def affineClockFlow
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (N : V →ₗ[ℝ] V) (τ : ℝ) : V →ₗ[ℝ] V :=
  LinearMap.id + τ • N

theorem affineClockFlow_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (N : V →ₗ[ℝ] V) :
    affineClockFlow N 0 = LinearMap.id := by
  ext v
  simp [affineClockFlow]

theorem affineClockFlow_add
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (N : V →ₗ[ℝ] V) (hN : N.comp N = 0) (τ₁ τ₂ : ℝ) :
    (affineClockFlow N τ₁).comp (affineClockFlow N τ₂) =
      affineClockFlow N (τ₁ + τ₂) := by
  ext v
  simp [affineClockFlow, LinearMap.comp_apply]
  have hNv : N (N v) = 0 := by
    have h := congrArg (fun f : V →ₗ[ℝ] V => f v) hN
    simpa [LinearMap.comp_apply] using h
  rw [hNv]
  module

theorem affineClockFlow_inverse
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (N : V →ₗ[ℝ] V) (hN : N.comp N = 0) (τ : ℝ) :
    (affineClockFlow N τ).comp (affineClockFlow N (-τ)) = LinearMap.id := by
  simpa [affineClockFlow_zero] using affineClockFlow_add N hN τ (-τ)

end
end InfoGeometry.Physics.KreinHestenesTransportClock
