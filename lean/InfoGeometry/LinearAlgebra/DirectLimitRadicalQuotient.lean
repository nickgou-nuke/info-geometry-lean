/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.LinearAlgebra.DirectLimitBilinear
import InfoGeometry.LinearAlgebra.PositiveRadicalQuotient
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
# Radical reduction of a native direct-limit pairing

The limit carrier is Mathlib's root `DirectLimit`, and its pairing is the
constructed `DirectLimitBilinear.form`.  Radical quotients are native submodule
quotients.  Neither stage-map injectivity nor a supplied colimit universal
property is assumed.

Exact form preservation transfers positivity and negative witnesses to the
limit.  Symmetry permits radical reduction, which preserves all self-pairings.
A stage vector lies in the limit radical exactly when every later image lies
in that stage's radical; this characterization needs no symmetry or stability.
If the transitions preserve the radicals, the preimage of the limit radical
at every stage is exactly the stage radical.  Native `Submodule.mapQ` and
`DirectLimit.Module.lift` then construct a bijective linear map from the direct
limit of the stage quotients to the quotient of the direct limit.

Symmetric positive semidefinite target forms imply radical stability. A
concrete isotropic-line inclusion into the real hyperbolic plane shows why
form preservation alone does not imply it.  No Hilbert completion or spectral
identification is asserted.
-/

noncomputable section

namespace InfoGeometry.LinearAlgebra.DirectLimitRadicalQuotient

open DirectLimitBilinear
open PositiveRadicalQuotient

variable {I : Type*} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
variable (f : ∀ i j, i ≤ j → V i →ₗ[ℝ] V j)
variable [DirectedSystem V (fun i j h x => f i j h x)]
variable (B : ∀ i, LinearMap.BilinForm ℝ (V i))
variable (hB : ∀ i j (h : i ≤ j) (x y : V i),
  B j (f i j h x) (f i j h y) = B i x y)

/-- Radical reduction of the limit form is nonnegative exactly when every
stage form is nonnegative. No radical-stability assumption is needed. -/
theorem quotient_form_nonneg_iff (hSym : ∀ i, LinearMap.IsSymm (B i)) :
    (∀ q : _root_.DirectLimit V f ⧸ LinearMap.ker (form f B hB),
      0 ≤ quotientForm (form f B hB) (form_isSymm f B hB hSym) q q) ↔
      ∀ i (x : V i), 0 ≤ B i x x :=
  (quotientForm_nonneg_iff (form f B hB) (form_isSymm f B hB hSym)).trans
    (form_nonneg_iff f B hB)

/-- Every negative stage witness has a nonzero, negative class in the radical
quotient of the limit. No transition-map injectivity is required. -/
theorem negative_survives_limit_radical_quotient
    (hSym : ∀ i, LinearMap.IsSymm (B i)) (i : I) (x : V i) (hx : B i x x < 0) :
    (Submodule.Quotient.mk (DirectLimit.Module.of ℝ I V f i x) :
      _root_.DirectLimit V f ⧸ LinearMap.ker (form f B hB)) ≠ 0 ∧
      quotientForm (form f B hB) (form_isSymm f B hB hSym)
        (Submodule.Quotient.mk (DirectLimit.Module.of ℝ I V f i x))
        (Submodule.Quotient.mk (DirectLimit.Module.of ℝ I V f i x)) < 0 :=
  negative_survives_radical_quotient (form f B hB) (form_isSymm f B hB hSym)
    (DirectLimit.Module.of ℝ I V f i x) (by
      rw [form_of f B hB i x x]
      exact hx)

section
include hB
omit [Nonempty I] [IsDirectedOrder I] [DirectedSystem V fun i j h x => f i j h x]

/-- A form-preserving transition into a symmetric PSD target preserves the
radical, even without a positivity hypothesis on the source. -/
theorem radical_stable_of_target_nonneg (i j : I) (hij : i ≤ j)
    (hSym : LinearMap.IsSymm (B j)) (hPSD : ∀ y : V j, 0 ≤ B j y y) :
    LinearMap.ker (B i) ≤ (LinearMap.ker (B j)).comap (f i j hij) := by
  intro x hx
  change f i j hij x ∈ LinearMap.ker (B j)
  apply ((B j).apply_apply_same_eq_zero_iff hPSD hSym).mp
  rw [hB i j hij x x, LinearMap.mem_ker.mp hx, LinearMap.zero_apply]

/-- A family of symmetric PSD forms supplies all radical-stability premises. -/
theorem radical_stable_of_nonneg (hSym : ∀ i, LinearMap.IsSymm (B i))
    (hPSD : ∀ i (x : V i), 0 ≤ B i x x) :
    ∀ i j (hij : i ≤ j),
      LinearMap.ker (B i) ≤ (LinearMap.ker (B j)).comap (f i j hij) :=
  fun i j hij => radical_stable_of_target_nonneg f B hB i j hij (hSym j) (hPSD j)

end

/-- A stage vector belongs to the limit radical exactly when every later image
belongs to the corresponding stage radical. This uses only exact preservation
of the forms, with no symmetry, radical stability, or injectivity hypothesis. -/
theorem of_mem_ker_form_iff_persistent (i : I) (x : V i) :
    DirectLimit.Module.of ℝ I V f i x ∈ LinearMap.ker (form f B hB) ↔
      ∀ j (hij : i ≤ j), f i j hij x ∈ LinearMap.ker (B j) := by
  constructor
  · intro hx j hij
    rw [LinearMap.mem_ker] at hx ⊢
    apply LinearMap.ext
    intro y
    change B j (f i j hij x) y = 0
    rw [← form_of f B hB j (f i j hij x) y,
      DirectLimit.Module.of_f, hx, LinearMap.zero_apply]
  · intro h
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro z
    change form f B hB (DirectLimit.Module.of ℝ I V f i x) z = 0
    obtain ⟨j, y, hy⟩ := DirectLimit.exists_eq_mk (f := f) z
    have hy' : z = DirectLimit.Module.of ℝ I V f j y := hy
    rw [hy']
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    rw [form_of_of f B hB i j k hik hjk x y]
    have hk : B k (f i k hik x) = 0 := LinearMap.mem_ker.mp (h k hik)
    rw [hk, LinearMap.zero_apply]

section StableRadicals

variable (hStable : ∀ i j (hij : i ≤ j),
  LinearMap.ker (B i) ≤ (LinearMap.ker (B j)).comap (f i j hij))

section
include hB hStable
omit [Nonempty I] [IsDirectedOrder I] [DirectedSystem V fun i j h x => f i j h x]

/-- With radical stability, the transition preimage of the target radical is
exactly the source radical. Inclusion into the source radical follows from
form preservation. -/
theorem ker_comap_transition (i j : I) (hij : i ≤ j) :
    (LinearMap.ker (B j)).comap (f i j hij) = LinearMap.ker (B i) := by
  apply le_antisymm
  · intro x hx
    change f i j hij x ∈ LinearMap.ker (B j) at hx
    rw [LinearMap.mem_ker] at hx ⊢
    apply LinearMap.ext
    intro y
    change B i x y = 0
    rw [← hB i j hij x y, hx, LinearMap.zero_apply]
  · exact hStable i j hij

end

include hStable in
/-- The preimage of the actual limit radical at a stage is exactly the stage
radical: stability makes every stage-radical vector persistent. -/
theorem ker_form_comap_of (i : I) :
    (LinearMap.ker (form f B hB)).comap (DirectLimit.Module.of ℝ I V f i) =
      LinearMap.ker (B i) := by
  apply le_antisymm
  · intro x hx
    change DirectLimit.Module.of ℝ I V f i x ∈ LinearMap.ker (form f B hB) at hx
    rw [LinearMap.mem_ker] at hx ⊢
    apply LinearMap.ext
    intro y
    change B i x y = 0
    rw [← form_of f B hB i x y, hx, LinearMap.zero_apply]
  · intro x hx
    change DirectLimit.Module.of ℝ I V f i x ∈ LinearMap.ker (form f B hB)
    exact (of_mem_ker_form_iff_persistent f B hB i x).mpr
      (fun j hij => hStable i j hij hx)

/-- The native linear map induced between stage radical quotients. -/
def quotientMap (i j : I) (hij : i ≤ j) :
    (V i ⧸ LinearMap.ker (B i)) →ₗ[ℝ] (V j ⧸ LinearMap.ker (B j)) :=
  (LinearMap.ker (B i)).mapQ (LinearMap.ker (B j)) (f i j hij) (hStable i j hij)

omit [Nonempty I] [IsDirectedOrder I] [DirectedSystem V fun i j h x => f i j h x] in
@[simp]
theorem quotientMap_mk (i j : I) (hij : i ≤ j) (x : V i) :
    quotientMap f B hStable i j hij (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (f i j hij x) :=
  rfl

/-- Quotient transition maps satisfy the native directed-system laws. -/
instance quotientDirectedSystem :
    DirectedSystem (fun i => V i ⧸ LinearMap.ker (B i))
      (fun i j hij x => quotientMap f B hStable i j hij x) where
  map_self := by
    intro i q
    refine Submodule.Quotient.induction_on _ q ?_
    intro x
    change (Submodule.Quotient.mk (f i i le_rfl x) : V i ⧸ LinearMap.ker (B i)) =
      Submodule.Quotient.mk x
    rw [DirectedSystem.map_self' f x]
  map_map := by
    intro k j i hij hjk q
    refine Submodule.Quotient.induction_on _ q ?_
    intro x
    change (Submodule.Quotient.mk (f j k hjk (f i j hij x)) :
      V k ⧸ LinearMap.ker (B k)) =
      Submodule.Quotient.mk (f i k (hij.trans hjk) x)
    rw [DirectedSystem.map_map' f hij hjk x]

section
include hB
omit [Nonempty I] [IsDirectedOrder I] [DirectedSystem V fun i j h x => f i j h x]

/-- The induced quotient transitions are injective even when the original
transitions are not: their kernel is the quotient of the source radical. -/
theorem quotientMap_injective (i j : I) (hij : i ≤ j) :
    Function.Injective (quotientMap f B hStable i j hij) := by
  apply LinearMap.ker_eq_bot.mp
  unfold quotientMap
  rw [Submodule.ker_mapQ, ker_comap_transition f B hB hStable i j hij,
    Submodule.mkQ_map_self]

end

include hStable in
/-- Each stage quotient maps canonically into the quotient of the actual limit. -/
def quotientToLimit (i : I) :
    (V i ⧸ LinearMap.ker (B i)) →ₗ[ℝ]
      (_root_.DirectLimit V f ⧸ LinearMap.ker (form f B hB)) :=
  (LinearMap.ker (B i)).mapQ (LinearMap.ker (form f B hB))
    (DirectLimit.Module.of ℝ I V f i) (ker_form_comap_of f B hB hStable i).ge

@[simp]
theorem quotientToLimit_mk (i : I) (x : V i) :
    quotientToLimit f B hB hStable i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (DirectLimit.Module.of ℝ I V f i x) :=
  rfl

/-- The quotient injections respect the native quotient transition maps. -/
theorem quotientToLimit_transition (i j : I) (hij : i ≤ j)
    (q : V i ⧸ LinearMap.ker (B i)) :
    quotientToLimit f B hB hStable j (quotientMap f B hStable i j hij q) =
      quotientToLimit f B hB hStable i q := by
  refine Submodule.Quotient.induction_on _ q ?_
  intro x
  change (Submodule.Quotient.mk (DirectLimit.Module.of ℝ I V f j (f i j hij x)) :
    _root_.DirectLimit V f ⧸ LinearMap.ker (form f B hB)) =
    Submodule.Quotient.mk (DirectLimit.Module.of ℝ I V f i x)
  rw [DirectLimit.Module.of_f]

/-- Construct the comparison map with Mathlib's linear universal property. -/
def quotientColimitMap :
    _root_.DirectLimit (fun i => V i ⧸ LinearMap.ker (B i))
      (quotientMap f B hStable) →ₗ[ℝ]
        (_root_.DirectLimit V f ⧸ LinearMap.ker (form f B hB)) :=
  DirectLimit.Module.lift ℝ I (fun i => V i ⧸ LinearMap.ker (B i))
    (quotientMap f B hStable) (quotientToLimit f B hB hStable)
    (quotientToLimit_transition f B hB hStable)

/-- Evaluation on a stage quotient representative is definitional. -/
@[simp]
theorem quotientColimitMap_of_mk (i : I) (x : V i) :
    quotientColimitMap f B hB hStable
      (DirectLimit.Module.of ℝ I (fun j => V j ⧸ LinearMap.ker (B j))
        (quotientMap f B hStable) i (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk (DirectLimit.Module.of ℝ I V f i x) :=
  rfl

/-- A comparison-map kernel element is represented by a stage radical and
therefore is already zero in the stage quotient. -/
theorem quotientColimitMap_injective :
    Function.Injective (quotientColimitMap f B hB hStable) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  obtain ⟨i, q, rfl⟩ :=
    DirectLimit.exists_eq_mk (f := quotientMap f B hStable) z
  obtain ⟨x, rfl⟩ := (LinearMap.ker (B i)).mkQ_surjective q
  change (Submodule.Quotient.mk (DirectLimit.Module.of ℝ I V f i x) :
    _root_.DirectLimit V f ⧸ LinearMap.ker (form f B hB)) = 0 at hz
  have hxInf : DirectLimit.Module.of ℝ I V f i x ∈ LinearMap.ker (form f B hB) :=
    (Submodule.Quotient.mk_eq_zero _).mp hz
  have hx : x ∈ LinearMap.ker (B i) := by
    have hmem : x ∈ (LinearMap.ker (form f B hB)).comap
        (DirectLimit.Module.of ℝ I V f i) := hxInf
    rwa [ker_form_comap_of f B hB hStable i] at hmem
  have hq : (Submodule.Quotient.mk x : V i ⧸ LinearMap.ker (B i)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hx
  change DirectLimit.Module.of ℝ I (fun j => V j ⧸ LinearMap.ker (B j))
    (quotientMap f B hStable) i (Submodule.Quotient.mk x) = 0
  rw [hq, map_zero]

/-- Every class has a stage representative, giving surjectivity. -/
theorem quotientColimitMap_surjective :
    Function.Surjective (quotientColimitMap f B hB hStable) := by
  intro q
  obtain ⟨z, rfl⟩ := (LinearMap.ker (form f B hB)).mkQ_surjective q
  obtain ⟨i, x, rfl⟩ := DirectLimit.exists_eq_mk (f := f) z
  refine ⟨DirectLimit.Module.of ℝ I (fun j => V j ⧸ LinearMap.ker (B j))
    (quotientMap f B hStable) i (Submodule.Quotient.mk x), ?_⟩
  rfl

/-- The actual canonical linear equivalence between the colimit of the radical
quotients and the radical quotient of the colimit. -/
def quotientColimitEquiv :
    _root_.DirectLimit (fun i => V i ⧸ LinearMap.ker (B i))
      (quotientMap f B hStable) ≃ₗ[ℝ]
        (_root_.DirectLimit V f ⧸ LinearMap.ker (form f B hB)) :=
  LinearEquiv.ofBijective (quotientColimitMap f B hB hStable)
    ⟨quotientColimitMap_injective f B hB hStable,
      quotientColimitMap_surjective f B hB hStable⟩

/-- The equivalence sends the class of a stage vector to the class of its
original limit image. This fixes the canonical comparison map completely. -/
@[simp]
theorem quotientColimitEquiv_of_mk (i : I) (x : V i) :
    quotientColimitEquiv f B hB hStable
      (DirectLimit.Module.of ℝ I (fun j => V j ⧸ LinearMap.ker (B j))
        (quotientMap f B hStable) i (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk (DirectLimit.Module.of ℝ I V f i x) :=
  rfl

end StableRadicals

namespace HyperbolicCounterexample

/-- The native real hyperbolic plane form with Gram matrix `[[0,1],[1,0]]`. -/
def hyperbolicForm : LinearMap.BilinForm ℝ (ℝ × ℝ) :=
  LinearMap.mk₂ ℝ (fun x y : ℝ × ℝ => x.1 * y.2 + x.2 * y.1)
    (by
      intro x y z
      change (x.1 + y.1) * z.2 + (x.2 + y.2) * z.1 =
        (x.1 * z.2 + x.2 * z.1) + (y.1 * z.2 + y.2 * z.1)
      simp only [add_mul]
      abel)
    (by
      intro r x y
      change (r * x.1) * y.2 + (r * x.2) * y.1 =
        r * (x.1 * y.2 + x.2 * y.1)
      simp only [mul_add, mul_assoc])
    (by
      intro x y z
      change x.1 * (y.2 + z.2) + x.2 * (y.1 + z.1) =
        (x.1 * y.2 + x.2 * y.1) + (x.1 * z.2 + x.2 * z.1)
      simp only [mul_add]
      abel)
    (by
      intro r x y
      change x.1 * (r * y.2) + x.2 * (r * y.1) =
        r * (x.1 * y.2 + x.2 * y.1)
      simp only [mul_add, mul_left_comm x.1 r y.2, mul_left_comm x.2 r y.1])

/-- Include the zero-form line as the first isotropic coordinate axis. -/
def isotropicLine : ℝ →ₗ[ℝ] (ℝ × ℝ) where
  toFun x := (x, 0)
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

theorem hyperbolicForm_isSymm : LinearMap.IsSymm hyperbolicForm := by
  constructor
  intro x y
  change x.1 * y.2 + x.2 * y.1 = y.1 * x.2 + y.2 * x.1
  rw [mul_comm x.1 y.2, mul_comm x.2 y.1, add_comm]

/-- The inclusion preserves the complete source pairing, which is zero. -/
theorem isotropicLine_preserves_form (x y : ℝ) :
    hyperbolicForm (isotropicLine x) (isotropicLine y) =
      (0 : LinearMap.BilinForm ℝ ℝ) x y := by
  simp [hyperbolicForm, isotropicLine]

/-- The old radical vector `1` pairs nontrivially with the newly available
second coordinate, so exact form preservation does not imply radical stability. -/
theorem isotropicLine_not_radical_stable :
    ¬ LinearMap.ker (0 : LinearMap.BilinForm ℝ ℝ) ≤
      (LinearMap.ker hyperbolicForm).comap isotropicLine := by
  intro h
  have hx : isotropicLine 1 ∈ LinearMap.ker hyperbolicForm :=
    h (by simp : (1 : ℝ) ∈ LinearMap.ker (0 : LinearMap.BilinForm ℝ ℝ))
  have hpair := LinearMap.congr_fun (LinearMap.mem_ker.mp hx) (0, 1)
  norm_num [hyperbolicForm, isotropicLine] at hpair

end HyperbolicCounterexample

end InfoGeometry.LinearAlgebra.DirectLimitRadicalQuotient

end
