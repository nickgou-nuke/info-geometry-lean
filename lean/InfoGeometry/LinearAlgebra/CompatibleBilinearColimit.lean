/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Colimit.DirectLimit
import InfoGeometry.Categorical.CompatibleEndomorphisms
import InfoGeometry.LinearAlgebra.PositiveRadicalQuotient

/-!
# Compatible real bilinear forms on the native algebraic direct limit

The common-stage construction is Mathlib's `DirectLimit.lift₂`. Its representative
independence is reused, and linearity is proved on common-stage representatives.
This generalizes the real pairing pattern in `Clifford/RealFockInfinityPairing`
without introducing another carrier or a positivity assumption into the form.

Exact form compatibility preserves positive semidefiniteness in both directions
and preserves every negative stage witness, including in the native radical
quotient. No topology, analytic limit, or arithmetic evaluation map is asserted.

For compatible operators, native adjoint-pair, self-adjoint and skew-adjoint
relations, and positivity of the operator quadratic are detected exactly on
the stages. An adjoint partner is supplied and transported, not constructed
for an arbitrary operator on the algebraic limit.
-/

noncomputable section

namespace InfoGeometry.LinearAlgebra.CompatibleBilinearColimit

open InfoGeometry.Categorical.CompatibleEndomorphisms

variable {I : Type*} [Preorder I] [IsDirectedOrder I] [Nonempty I]
variable {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
variable {H : ∀ ⦃i j : I⦄, i ≤ j → Type*}
variable [∀ i j (h : i ≤ j), FunLike (H h) (V i) (V j)]
variable [∀ i j (h : i ≤ j), LinearMapClass (H h) ℝ (V i) (V j)]
variable (f : ∀ i j (h : i ≤ j), H h) [DirectedSystem V (f · · ·)]
variable (B : ∀ i, LinearMap.BilinForm ℝ (V i))
variable (hB : ∀ i j h x y, B j (f i j h x) (f i j h y) = B i x y)

private def pairingValue : _root_.DirectLimit V f → _root_.DirectLimit V f → ℝ :=
  DirectLimit.lift₂ f f (fun i x y => B i x y)
    (fun i j h x y => (hB i j h x y).symm)

omit [Nonempty I] [∀ i j (h : i ≤ j), LinearMapClass (H h) ℝ (V i) (V j)] in
private theorem pairingValue_mk (i : I) (x y : V i) :
    pairingValue f B hB ⟦⟨i, x⟩⟧ ⟦⟨i, y⟩⟧ = B i x y :=
  DirectLimit.lift₂_def f f _ _ i x y

/-- The real bilinear form constructed on the existing native direct limit. -/
def form : LinearMap.BilinForm ℝ (_root_.DirectLimit V f) where
  toFun x :=
    { toFun := pairingValue f B hB x
      map_add' y z := by
        induction x, y, z using DirectLimit.induction₃ with
        | _ i x y z =>
          simpa only [DirectLimit.add_def, pairingValue_mk] using (B i x).map_add y z
      map_smul' r y := by
        induction x, y using DirectLimit.induction₂ with
        | _ i x y =>
          simpa only [DirectLimit.smul_def, pairingValue_mk, RingHom.id_apply] using
            (B i x).map_smul r y }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change pairingValue f B hB (x + y) z =
      pairingValue f B hB x z + pairingValue f B hB y z
    induction x, y, z using DirectLimit.induction₃ with
    | _ i x y z =>
      simpa only [DirectLimit.add_def, pairingValue_mk, LinearMap.add_apply] using
        LinearMap.congr_fun ((B i).map_add x y) z
  map_smul' r x := by
    apply LinearMap.ext
    intro y
    change pairingValue f B hB (r • x) y = r • pairingValue f B hB x y
    induction x, y using DirectLimit.induction₂ with
    | _ i x y =>
      simpa only [DirectLimit.smul_def, pairingValue_mk, LinearMap.smul_apply,
        RingHom.id_apply] using LinearMap.congr_fun ((B i).map_smul r x) y

/-- Same-stage evaluation recovers exactly the supplied finite-stage form. -/
@[simp]
theorem form_of (i : I) (x y : V i) :
    form f B hB (DirectLimit.Module.of ℝ I V f i x)
      (DirectLimit.Module.of ℝ I V f i y) = B i x y :=
  pairingValue_mk f B hB i x y

/-- A bilinear form with the prescribed stage values is unique. -/
theorem form_unique (C : LinearMap.BilinForm ℝ (_root_.DirectLimit V f))
    (hC : ∀ i x y, C (DirectLimit.Module.of ℝ I V f i x)
      (DirectLimit.Module.of ℝ I V f i y) = B i x y) :
    C = form f B hB := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  induction x, y using DirectLimit.induction₂ with
  | _ i x y => exact (hC i x y).trans (form_of f B hB i x y).symm

/-- Symmetry is inherited from every stage. -/
theorem form_isSymm (hSymm : ∀ i, (B i).IsSymm) : (form f B hB).IsSymm := by
  constructor
  intro x y
  induction x, y using DirectLimit.induction₂ with
  | _ i x y =>
    change form f B hB (DirectLimit.Module.of ℝ I V f i x)
      (DirectLimit.Module.of ℝ I V f i y) =
      form f B hB (DirectLimit.Module.of ℝ I V f i y)
        (DirectLimit.Module.of ℝ I V f i x)
    rw [form_of, form_of]
    exact (hSymm i).eq x y

/-- The limit form is nonnegative exactly when every stage form is nonnegative. -/
theorem form_nonneg_iff :
    (∀ x, 0 ≤ form f B hB x x) ↔ ∀ i x, 0 ≤ B i x x := by
  constructor
  · intro h i x
    simpa only [form_of] using h (DirectLimit.Module.of ℝ I V f i x)
  · intro h x
    induction x using DirectLimit.induction with
    | _ i x =>
      change 0 ≤ form f B hB (DirectLimit.Module.of ℝ I V f i x)
        (DirectLimit.Module.of ℝ I V f i x)
      simpa only [form_of] using h i x

/-- A negative stage vector has a nonzero negative image in the direct limit. -/
theorem negative_survives (i : I) (x : V i) (hNeg : B i x x < 0) :
    DirectLimit.Module.of ℝ I V f i x ≠ 0 ∧
      form f B hB (DirectLimit.Module.of ℝ I V f i x)
        (DirectLimit.Module.of ℝ I V f i x) < 0 := by
  have h : form f B hB (DirectLimit.Module.of ℝ I V f i x)
      (DirectLimit.Module.of ℝ I V f i x) < 0 := by
    simpa only [form_of] using hNeg
  refine ⟨?_, h⟩
  intro hz
  rw [hz, map_zero] at h
  exact (lt_irrefl 0) h

/-- Radical reduction of the limit also preserves every negative stage witness. -/
theorem negative_survives_quotient (hSymm : ∀ i, (B i).IsSymm)
    (i : I) (x : V i) (hNeg : B i x x < 0) :
    (Submodule.Quotient.mk (DirectLimit.Module.of ℝ I V f i x) :
      _root_.DirectLimit V f ⧸ LinearMap.ker (form f B hB)) ≠ 0 ∧
    PositiveRadicalQuotient.quotientForm (form f B hB) (form_isSymm f B hB hSymm)
      (Submodule.Quotient.mk (DirectLimit.Module.of ℝ I V f i x))
      (Submodule.Quotient.mk (DirectLimit.Module.of ℝ I V f i x)) < 0 :=
  PositiveRadicalQuotient.negative_survives_radical_quotient
    (form f B hB) (form_isSymm f B hB hSymm)
    (DirectLimit.Module.of ℝ I V f i x) (negative_survives f B hB i x hNeg).2

/-- Positivity after radical reduction is equivalent to positivity at every stage. -/
theorem quotient_nonneg_iff (hSymm : ∀ i, (B i).IsSymm) :
    (∀ x, 0 ≤ PositiveRadicalQuotient.quotientForm
      (form f B hB) (form_isSymm f B hB hSymm) x x) ↔
      ∀ i x, 0 ≤ B i x x :=
  (PositiveRadicalQuotient.quotientForm_nonneg_iff
    (form f B hB) (form_isSymm f B hB hSymm)).trans (form_nonneg_iff f B hB)

variable (T : ∀ i, Module.End ℝ (V i))
variable (hT : ∀ i j h x, T j (f i j h x) = f i j h (T i x))

/-- Adjoint pairs on the limit are equivalent to adjoint pairs at every stage. -/
-- theorem-class: transport
theorem form_isAdjointPair_iff (U : ∀ i, Module.End ℝ (V i))
    (hU : ∀ i j h x, U j (f i j h x) = f i j h (U i x)) :
    LinearMap.IsAdjointPair (form f B hB) (form f B hB)
      (liftEnd f T hT) (liftEnd f U hU) ↔
      ∀ i, LinearMap.IsAdjointPair (B i) (B i) (T i) (U i) := by
  constructor
  · intro h i x y
    simpa only [liftEnd_of, form_of] using
      h (DirectLimit.Module.of ℝ I V f i x) (DirectLimit.Module.of ℝ I V f i y)
  · intro h x y
    induction x, y using DirectLimit.induction₂ with
    | _ i x y =>
      change form f B hB (liftEnd f T hT (DirectLimit.Module.of ℝ I V f i x))
          (DirectLimit.Module.of ℝ I V f i y) =
        form f B hB (DirectLimit.Module.of ℝ I V f i x)
          (liftEnd f U hU (DirectLimit.Module.of ℝ I V f i y))
      simpa only [liftEnd_of, form_of] using h i x y

/-- Self-adjointness is detected exactly on the supplied stage operators. -/
-- theorem-class: transport
theorem form_isSelfAdjoint_iff :
    (form f B hB).IsSelfAdjoint (liftEnd f T hT) ↔
      ∀ i, (B i).IsSelfAdjoint (T i) :=
  form_isAdjointPair_iff f B hB T hT T hT

/-- Skew-adjointness is detected exactly on the supplied stage operators. -/
-- theorem-class: transport
theorem form_isSkewAdjoint_iff :
    (form f B hB).IsSkewAdjoint (liftEnd f T hT) ↔
      ∀ i, (B i).IsSkewAdjoint (T i) := by
  constructor
  · intro h i x y
    simpa only [Pi.neg_apply, liftEnd_of, map_neg, form_of] using
      h (DirectLimit.Module.of ℝ I V f i x) (DirectLimit.Module.of ℝ I V f i y)
  · intro h x y
    induction x, y using DirectLimit.induction₂ with
    | _ i x y =>
      change form f B hB (liftEnd f T hT (DirectLimit.Module.of ℝ I V f i x))
          (DirectLimit.Module.of ℝ I V f i y) =
        form f B hB (DirectLimit.Module.of ℝ I V f i x)
          (-(liftEnd f T hT (DirectLimit.Module.of ℝ I V f i y)))
      simpa only [Pi.neg_apply, liftEnd_of, map_neg, form_of] using h i x y

/-- The dissipative quadratic is nonnegative exactly when it is so at every stage. -/
-- theorem-class: transport
theorem form_apply_liftEnd_nonneg_iff :
    (∀ x, 0 ≤ form f B hB x (liftEnd f T hT x)) ↔
      ∀ i x, 0 ≤ B i x (T i x) := by
  constructor
  · intro h i x
    simpa only [liftEnd_of, form_of] using h (DirectLimit.Module.of ℝ I V f i x)
  · intro h x
    induction x using DirectLimit.induction with
    | _ i x =>
      change 0 ≤ form f B hB (DirectLimit.Module.of ℝ I V f i x)
        (liftEnd f T hT (DirectLimit.Module.of ℝ I V f i x))
      simpa only [liftEnd_of, form_of] using h i x

end InfoGeometry.LinearAlgebra.CompatibleBilinearColimit
