import Mathlib
import InfoGeometry.Canonical.ThreeColorCyclotomicChargeProjectors

/-!
# Cubic charge covariance for integer-labelled modes

The integer label of a mode is read in `ZMod 3`.  The cubic weight is then
defined using only the representatives `0, 1, 2`; no negative powers or
division are required.  The shift theorem below is consequently valid over
an arbitrary commutative ring.

This owner records a charged mode representation.  A Heisenberg cocycle can
be supplied by the `heisenberg` field, but is not inferred from covariance.
-/

namespace InfoGeometry.Canonical.HeisenbergCyclotomicChargeRepresentation

noncomputable section

open InfoGeometry.Canonical

variable {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]

/-- The scalar carried by a degree in `ZMod 3`. -/
def cubicWeight (ω : K) (r : ZMod 3) : K := ω ^ r.val

@[simp] theorem cubicWeight_zero (ω : K) :
    cubicWeight ω 0 = 1 := by
  simp [cubicWeight]

theorem cubicWeight_add (ω : K) (hω : ω ^ 3 = 1)
    (r s : ZMod 3) :
    cubicWeight ω (r + s) = cubicWeight ω r * cubicWeight ω s := by
  have hrlt : r.val < 3 := r.val_lt
  have hslt : s.val < 3 := s.val_lt
  have hr : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 := by omega
  have hs : s.val = 0 ∨ s.val = 1 ∨ s.val = 2 := by omega
  have hω3 : ω * ω * ω = 1 := by
    simpa [pow_three, mul_assoc] using hω
  rcases hr with hr | hr | hr <;> rcases hs with hs | hs | hs
  all_goals
    simp [cubicWeight, ZMod.val_add, hr, hs, hω, pow_two, pow_succ]
  all_goals try { simpa [pow_three, mul_assoc] using hω.symm }
  · calc
      ω = ω ^ 4 := by
        calc
          ω = ω * 1 := by rw [mul_one]
          _ = ω * (ω ^ 3) := by rw [hω]
          _ = ω ^ 4 := by ring
      _ = ω * ω * (ω * ω) := by ring

/-- A mode family together with its cubic charge covariance law. -/
structure CubicChargedHeisenbergRepresentation where
  omega : K
  omega_cube : omega ^ 3 = 1
  charge : V ≃ₗ[K] V
  mode : ℤ → Module.End K V
  central : Module.End K V
  heisenberg : ∀ m n,
    mode m * mode n - mode n * mode m =
      if m + n = 0 then m • central else 0
  mode_charge_covariant : ∀ n,
    charge.toLinearMap * mode n =
      (cubicWeight omega (n : ZMod 3)) •
        (mode n * charge.toLinearMap)
  central_charge_invariant :
    charge.toLinearMap * central = central * charge.toLinearMap

namespace CubicChargedHeisenbergRepresentation

variable (H : CubicChargedHeisenbergRepresentation (K := K) (V := V))

/-- The cubic eigenspace of the charge at degree `r`. -/
def IsCubicEigenspace (r : ZMod 3) (v : V) : Prop :=
  H.charge v = cubicWeight H.omega r • v

theorem mode_shifts_cubic_eigenspace
    (r : ZMod 3) (n : ℤ) (v : V)
    (hv : H.IsCubicEigenspace r v) :
    H.IsCubicEigenspace (r + (n : ZMod 3)) (H.mode n v) := by
  dsimp [IsCubicEigenspace] at hv ⊢
  calc
    H.charge (H.mode n v) =
        (H.charge.toLinearMap * H.mode n) v := rfl
    _ = ((cubicWeight H.omega (n : ZMod 3)) •
        (H.mode n * H.charge.toLinearMap)) v := by
          rw [H.mode_charge_covariant n]
    _ = cubicWeight H.omega (n : ZMod 3) •
        H.mode n (H.charge v) := by rfl
    _ = cubicWeight H.omega (n : ZMod 3) •
        H.mode n (cubicWeight H.omega r • v) := by rw [hv]
    _ = (cubicWeight H.omega (n : ZMod 3) *
        cubicWeight H.omega r) • H.mode n v := by
          rw [map_smul, smul_smul]
    _ = cubicWeight H.omega (r + (n : ZMod 3)) • H.mode n v := by
          rw [cubicWeight_add H.omega H.omega_cube]
          simp [mul_comm]

end CubicChargedHeisenbergRepresentation

end
end InfoGeometry.Canonical.HeisenbergCyclotomicChargeRepresentation
