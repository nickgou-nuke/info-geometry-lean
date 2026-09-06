import Mathlib
import InfoGeometry.Physics.Algebra.LinearTripotentTrifactor

/-!
# Invariant zero-mode carriers for tripotent endomorphisms

For an endomorphism `T` with `T^3 = T`, the polynomial projector
`P₀ = 1 - T²` has range equal to `ker T`.  This file packages the reusable
restriction lemma needed by later braid, Hodge, parabolic, and modular
owners: any endomorphism commuting with `P₀` preserves that zero-mode
carrier.  No common physical operator is postulated here; concrete packets
must provide the corresponding commutation hypotheses.

## Key Theorems:
- `zeroModeCarrier_eq_range_endProjZero`: `ker T = range P₀`.
- `endT_apply_eq_zero_of_mem_zeroModeCarrier`: `T x = 0` for all `x ∈ ker T`.
- `endProjZero_apply_of_mem_zeroModeCarrier`: `P₀ x = x` on `ker T`.
- `endProjPos_apply_eq_zero_of_mem_zeroModeCarrier`: `P₊ x = 0` on `ker T`.
- `endProjNeg_apply_eq_zero_of_mem_zeroModeCarrier`: `P₋ x = 0` on `ker T`.
- `zeroModeRestriction`: Packaged native endomorphism in `Module.End ℝ (zeroModeCarrier T)`.
- `zeroModeRestriction_mul`: Restriction preserves operator composition `(A * B)|_{H₀} = A|_{H₀} * B|_{H₀}`.
-/

set_option linter.unusedVariables false

noncomputable section

namespace InfoGeometry.Physics.Algebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The tripotent zero-mode carrier. -/
def zeroModeCarrier (T : Module.End ℝ V) : Submodule ℝ V := LinearMap.ker T

/-- The polynomial projector and the kernel define the same zero-mode carrier. -/
theorem zeroModeCarrier_eq_range_endProjZero
    (T : Module.End ℝ V) (hT : T ^ 3 = T) :
    zeroModeCarrier T = LinearMap.range (endProjZero T) := by
  exact (endProjZero_range_eq_ker T hT).symm

/-- 🏆 THEOREM: Pointwise action of T on its zero-mode carrier is identically zero. -/
@[simp] theorem endT_apply_eq_zero_of_mem_zeroModeCarrier
    (T : Module.End ℝ V) {x : V} (hx : x ∈ zeroModeCarrier T) :
    T x = 0 := by
  simpa [zeroModeCarrier] using hx

/-- 🏆 THEOREM: Pointwise action of P₀ on the zero-mode carrier is the identity. -/
@[simp] theorem endProjZero_apply_of_mem_zeroModeCarrier
    (T : Module.End ℝ V) {x : V} (hx : x ∈ zeroModeCarrier T) :
    endProjZero T x = x := by
  change x - T (T x) = x
  have hxT : T x = 0 := endT_apply_eq_zero_of_mem_zeroModeCarrier T hx
  rw [hxT, map_zero, sub_zero]

/-- 🏆 THEOREM: Pointwise action of P₊ on the zero-mode carrier vanishes. -/
@[simp] theorem endProjPos_apply_eq_zero_of_mem_zeroModeCarrier
    (T : Module.End ℝ V) {x : V} (hx : x ∈ zeroModeCarrier T) :
    endProjPos T x = 0 := by
  change (1 / 2 : ℝ) • (T (T x) + T x) = 0
  have hxT : T x = 0 := endT_apply_eq_zero_of_mem_zeroModeCarrier T hx
  rw [hxT, map_zero, add_zero, smul_zero]

/-- 🏆 THEOREM: Pointwise action of P₋ on the zero-mode carrier vanishes. -/
@[simp] theorem endProjNeg_apply_eq_zero_of_mem_zeroModeCarrier
    (T : Module.End ℝ V) {x : V} (hx : x ∈ zeroModeCarrier T) :
    endProjNeg T x = 0 := by
  change (1 / 2 : ℝ) • (T (T x) - T x) = 0
  have hxT : T x = 0 := endT_apply_eq_zero_of_mem_zeroModeCarrier T hx
  rw [hxT, map_zero, sub_zero, smul_zero]

/-- A commuting endomorphism preserves the tripotent zero-mode carrier. -/
theorem endomorphism_preserves_zeroModeCarrier
    (T A : Module.End ℝ V) (hT : T ^ 3 = T)
    (hA : A * endProjZero T = endProjZero T * A) :
    ∀ x, x ∈ zeroModeCarrier T → A x ∈ zeroModeCarrier T := by
  intro x hx
  have hxP : endProjZero T x = x := endProjZero_apply_of_mem_zeroModeCarrier T hx
  have hcomm : endProjZero T (A x) = A (endProjZero T x) := by
    have h := congrArg (fun F : Module.End ℝ V => F x) hA
    simpa only [Module.End.mul_apply] using h.symm
  change A x ∈ LinearMap.ker T
  rw [LinearMap.mem_ker]
  change T (A x) = 0
  have hzero : T * endProjZero T = 0 := by
    change T * projZero T = 0
    simpa using (mul_projZero (T := T) (by simpa [pow_three] using hT))
  calc
    T (A x) = T (endProjZero T (A x)) := by rw [hcomm, hxP]
    _ = (T * endProjZero T) (A x) := rfl
    _ = 0 := by rw [hzero]; simp

/-- The zero-mode carrier is preserved by compositions of commuting operators. -/
theorem composition_preserves_zeroModeCarrier
    (T A B : Module.End ℝ V) (hT : T ^ 3 = T)
    (hA : A * endProjZero T = endProjZero T * A)
    (hB : B * endProjZero T = endProjZero T * B) :
    ∀ x, x ∈ zeroModeCarrier T → (A * B) x ∈ zeroModeCarrier T := by
  intro x hx
  exact endomorphism_preserves_zeroModeCarrier T A hT hA
    (B x) (endomorphism_preserves_zeroModeCarrier T B hT hB x hx)

/-- The tripotent itself commutes with its zero-mode projector. -/
theorem endT_commutes_endProjZero
    (T : Module.End ℝ V) (hT : T ^ 3 = T) :
    T * endProjZero T = endProjZero T * T := by
  have hT' : T * T * T = T := by simpa [pow_three] using hT
  calc
    T * endProjZero T = 0 := by
      simpa [endProjZero] using (mul_projZero (T := T) hT')
    _ = endProjZero T * T := by
      symm
      simpa [endProjZero] using (projZero_mul (T := T) hT')

/-- The zero-mode projector commutes with itself. -/
theorem endProjZero_idempotent
    (T : Module.End ℝ V) (hT : T ^ 3 = T) :
    endProjZero T * endProjZero T = endProjZero T := by
  simpa [endProjZero] using (projZero_idempotent (T := T)
    (by simpa [pow_three] using hT))

/-- The positive and zero Peirce projectors commute (both products vanish). -/
theorem endProjPos_commutes_endProjZero
    (T : Module.End ℝ V) (hT : T ^ 3 = T) :
    endProjPos T * endProjZero T = endProjZero T * endProjPos T := by
  calc
    endProjPos T * endProjZero T = 0 :=
      endProjPos_mul_endProjZero_eq_zero T hT
    _ = endProjZero T * endProjPos T := by
      symm
      exact endProjZero_mul_endProjPos_eq_zero T hT

/-- The negative and zero Peirce projectors commute (both products vanish). -/
theorem endProjNeg_commutes_endProjZero
    (T : Module.End ℝ V) (hT : T ^ 3 = T) :
    endProjNeg T * endProjZero T = endProjZero T * endProjNeg T := by
  calc
    endProjNeg T * endProjZero T = 0 :=
      endProjNeg_mul_endProjZero_eq_zero T hT
    _ = endProjZero T * endProjNeg T := by
      symm
      exact endProjZero_mul_endProjNeg_eq_zero T hT

theorem endT_preserves_zeroModeCarrier
    (T : Module.End ℝ V) (hT : T ^ 3 = T) :
    ∀ x, x ∈ zeroModeCarrier T → T x ∈ zeroModeCarrier T :=
  endomorphism_preserves_zeroModeCarrier T T hT (endT_commutes_endProjZero T hT)

theorem endProjZero_preserves_zeroModeCarrier
    (T : Module.End ℝ V) (hT : T ^ 3 = T) :
    ∀ x, x ∈ zeroModeCarrier T → endProjZero T x ∈ zeroModeCarrier T :=
  endomorphism_preserves_zeroModeCarrier T (endProjZero T) hT
    (by rfl)

theorem endProjPos_preserves_zeroModeCarrier
    (T : Module.End ℝ V) (hT : T ^ 3 = T) :
    ∀ x, x ∈ zeroModeCarrier T → endProjPos T x ∈ zeroModeCarrier T :=
  endomorphism_preserves_zeroModeCarrier T (endProjPos T) hT
    (endProjPos_commutes_endProjZero T hT)

theorem endProjNeg_preserves_zeroModeCarrier
    (T : Module.End ℝ V) (hT : T ^ 3 = T) :
    ∀ x, x ∈ zeroModeCarrier T → endProjNeg T x ∈ zeroModeCarrier T :=
  endomorphism_preserves_zeroModeCarrier T (endProjNeg T) hT
    (endProjNeg_commutes_endProjZero T hT)

/-- 🏆 THEOREM: Packaged native endomorphism restriction to the zero-mode carrier. -/
def zeroModeRestriction
    (T A : Module.End ℝ V) (hT : T ^ 3 = T)
    (hA : A * endProjZero T = endProjZero T * A) :
    Module.End ℝ (zeroModeCarrier T) where
  toFun x :=
    ⟨A x.1,
      endomorphism_preserves_zeroModeCarrier
        T A hT hA x.1 x.2⟩
  map_add' := by
    intro x y
    ext
    simp
  map_smul' := by
    intro c x
    ext
    simp

@[simp] theorem zeroModeRestriction_apply
    (T A : Module.End ℝ V) (hT : T ^ 3 = T)
    (hA : A * endProjZero T = endProjZero T * A)
    (x : zeroModeCarrier T) :
    (zeroModeRestriction T A hT hA x).1 = A x.1 :=
  rfl

/-- 🏆 THEOREM: Restriction preserves endomorphism multiplication (composition). -/
theorem zeroModeRestriction_mul
    (T A B : Module.End ℝ V) (hT : T ^ 3 = T)
    (hA : A * endProjZero T = endProjZero T * A)
    (hB : B * endProjZero T = endProjZero T * B)
    (hAB : (A * B) * endProjZero T = endProjZero T * (A * B)) :
    zeroModeRestriction T (A * B) hT hAB =
      zeroModeRestriction T A hT hA * zeroModeRestriction T B hT hB := by
  ext x
  simp [zeroModeRestriction, Module.End.mul_apply]

/-- Commutation with `P₀` is closed under composition, so the explicit
compatibility witness for a product is not needed by callers. -/
theorem commute_endProjZero_mul
    (T A B : Module.End ℝ V)
    (hA : A * endProjZero T = endProjZero T * A)
    (hB : B * endProjZero T = endProjZero T * B) :
    (A * B) * endProjZero T = endProjZero T * (A * B) := by
  calc
    (A * B) * endProjZero T = A * (B * endProjZero T) := by simp [mul_assoc]
    _ = A * (endProjZero T * B) := by rw [hB]
    _ = (A * endProjZero T) * B := by simp [mul_assoc]
    _ = (endProjZero T * A) * B := by rw [hA]
    _ = endProjZero T * (A * B) := by simp [mul_assoc]

/-- Composition restriction with the canonical product-commutation witness. -/
theorem zeroModeRestriction_mul_of_commuting
    (T A B : Module.End ℝ V) (hT : T ^ 3 = T)
    (hA : A * endProjZero T = endProjZero T * A)
    (hB : B * endProjZero T = endProjZero T * B) :
    zeroModeRestriction T (A * B) hT (commute_endProjZero_mul T A B hA hB) =
      zeroModeRestriction T A hT hA * zeroModeRestriction T B hT hB := by
  exact zeroModeRestriction_mul T A B hT hA hB
    (commute_endProjZero_mul T A B hA hB)

/-- 🏆 THEOREM: Restriction preserves addition. -/
theorem zeroModeRestriction_add
    (T A B : Module.End ℝ V) (hT : T ^ 3 = T)
    (hA : A * endProjZero T = endProjZero T * A)
    (hB : B * endProjZero T = endProjZero T * B)
    (hAB : (A + B) * endProjZero T = endProjZero T * (A + B)) :
    zeroModeRestriction T (A + B) hT hAB =
      zeroModeRestriction T A hT hA + zeroModeRestriction T B hT hB := by
  ext x
  simp [zeroModeRestriction]

/-- 🏆 THEOREM: Restriction preserves scalar multiplication. -/
theorem zeroModeRestriction_smul
    (T A : Module.End ℝ V) (c : ℝ) (hT : T ^ 3 = T)
    (hA : A * endProjZero T = endProjZero T * A)
    (hcA : (c • A) * endProjZero T = endProjZero T * (c • A)) :
    zeroModeRestriction T (c • A) hT hcA =
      c • zeroModeRestriction T A hT hA := by
  ext x
  simp [zeroModeRestriction]

/-- 🏆 THEOREM: Restriction of the identity is the identity. -/
theorem zeroModeRestriction_one
    (T : Module.End ℝ V) (hT : T ^ 3 = T)
    (h1 : (1 : Module.End ℝ V) * endProjZero T = endProjZero T * 1) :
    zeroModeRestriction T 1 hT h1 = 1 := by
  ext x
  simp [zeroModeRestriction]

/-- 🏆 THEOREM: Restriction of the zero map is zero. -/
theorem zeroModeRestriction_zero
    (T : Module.End ℝ V) (hT : T ^ 3 = T)
    (h0 : (0 : Module.End ℝ V) * endProjZero T = endProjZero T * 0) :
    zeroModeRestriction T 0 hT h0 = 0 := by
  ext x
  simp [zeroModeRestriction]

/-- 🏆 THEOREM: Commuting ambient endomorphisms restrict to commuting endomorphisms on the zero-mode carrier. -/
theorem zeroModeRestriction_commute
    (T A B : Module.End ℝ V) (hT : T ^ 3 = T)
    (hA : A * endProjZero T = endProjZero T * A)
    (hB : B * endProjZero T = endProjZero T * B)
    (hComm : A * B = B * A) :
    zeroModeRestriction T A hT hA * zeroModeRestriction T B hT hB =
      zeroModeRestriction T B hT hB * zeroModeRestriction T A hT hA := by
  ext x
  show (A * B) x.1 = (B * A) x.1
  rw [hComm]

/-- 🏆 THEOREM: The tripotent itself restricts to the zero map on the zero-mode carrier. -/
theorem zeroModeRestriction_T_eq_zero
    (T : Module.End ℝ V) (hT : T ^ 3 = T) :
    zeroModeRestriction T T hT (endT_commutes_endProjZero T hT) = 0 := by
  ext x
  exact endT_apply_eq_zero_of_mem_zeroModeCarrier T x.2

/-! ### The `P₀`-commutant as a native restriction representation -/

/-- Endomorphisms commuting with the tripotent zero-mode projector. -/
def zeroModeCommutant (T : Module.End ℝ V) : Submonoid (Module.End ℝ V) where
  carrier := {A : Module.End ℝ V | A * endProjZero T = endProjZero T * A}
  one_mem' := by simp
  mul_mem' := by
    intro A B hA hB
    exact commute_endProjZero_mul T A B hA hB

/-- Restriction of the `P₀`-commutant to the zero-mode carrier. -/
def zeroModeCommutantRestriction (T : Module.End ℝ V) (hT : T ^ 3 = T) :
    zeroModeCommutant T →* Module.End ℝ (zeroModeCarrier T) where
  toFun A := zeroModeRestriction T A.1 hT A.2
  map_one' := by
    ext x
    rfl
  map_mul' := by
    intro A B
    ext x
    rfl

@[simp] theorem zeroModeCommutantRestriction_apply
    (T : Module.End ℝ V) (hT : T ^ 3 = T)
    (A : zeroModeCommutant T) (x : zeroModeCarrier T) :
    (zeroModeCommutantRestriction T hT A x).1 = A.1 x.1 :=
  rfl

end InfoGeometry.Physics.Algebra
