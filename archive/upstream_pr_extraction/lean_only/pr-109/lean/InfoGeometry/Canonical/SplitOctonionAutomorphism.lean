import Mathlib.Data.Real.Basic
import InfoGeometry.Canonical.ZornSpinor
import InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge

/-!
# Real split-octonion automorphisms on the canonical Zorn carrier

This file starts the canonical real automorphism lane for
`Aut(𝕆_s(ℝ))`, using the repository's canonical Zorn carrier
`InfoGeometry.Canonical.ZornMatrix ℝ`.

Closed here:
* the real split-octonion carrier abbreviation;
* external predicates for unit, product, and determinant preservation;
* the data-level automorphism group as the subgroup of real linear equivalences
  preserving `1` and the Zorn product;
* real theorems showing every group element preserves `1`, product, determinant,
  and the null cone.

Open debt, deliberately not hidden in structure fields:
* derivation/Lie-algebra identification with split real `𝔤₂`;
* future group-level target: identify this automorphism group with the split real
  form `G_{2(2)}` after the Lie/derivation layer is constructed.
-/

noncomputable section

namespace InfoGeometry.Canonical

variable {R : Type} [CommRing R]

/-- The canonical split-octonion carrier over `ℝ`. -/
abbrev SplitOctonionReal : Type := ZornMatrix ℝ

/-- Linear candidates for split-octonion automorphisms over a commutative ring. -/
abbrev SplitOctonionAutCandidate (R : Type) [CommRing R] : Type :=
  ZornMatrix R ≃ₗ[R] ZornMatrix R

/-- The candidate fixes the Zorn unit. -/
def PreservesZornOne (f : SplitOctonionAutCandidate R) : Prop :=
  f (1 : ZornMatrix R) = 1

/-- The candidate preserves the Zorn product. -/
def PreservesZornMul (f : SplitOctonionAutCandidate R) : Prop :=
  ∀ x y : ZornMatrix R, f (x * y) = f x * f y

/-- The candidate preserves the Zorn determinant/norm.

This is an external predicate, not part of the automorphism definition: it is
proved below from the native canonical Zorn composition owner.
-/
def PreservesDetZ (f : SplitOctonionAutCandidate R) : Prop :=
  ∀ x : ZornMatrix R,
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ (f x) =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ x

/-- Exact predicate for Zorn algebra automorphism candidates. -/
def IsSplitOctonionAut (f : SplitOctonionAutCandidate R) : Prop :=
  PreservesZornOne f ∧ PreservesZornMul f

/-- The set of linear Zorn algebra automorphisms. -/
def SplitOctonionAutSet : Set (SplitOctonionAutCandidate R) :=
  {f | IsSplitOctonionAut f}

/-- The subgroup of linear Zorn algebra automorphisms. -/
def splitOctonionAutSubgroup : Subgroup (SplitOctonionAutCandidate R) where
  carrier := SplitOctonionAutSet (R := R)
  one_mem' := by
    constructor
    · rfl
    · intro x y
      rfl
  mul_mem' := by
    intro f g hf hg
    rcases hf with ⟨hf1, hfmul⟩
    rcases hg with ⟨hg1, hgmul⟩
    constructor
    · change (f * g) (1 : ZornMatrix R) = 1
      rw [LinearEquiv.mul_apply, hg1, hf1]
    · intro x y
      calc
        f (g (x * y)) = f (g x * g y) := by rw [hgmul]
        _ = f (g x) * f (g y) := by rw [hfmul]
        _ = (f * g) x * (f * g) y := by simp [LinearEquiv.mul_apply]
  inv_mem' := by
    intro f hf
    rcases hf with ⟨hf1, hfmul⟩
    constructor
    · change f.symm (1 : ZornMatrix R) = 1
      apply f.injective
      rw [hf1]
      exact f.apply_symm_apply 1
    · intro x y
      change f.symm (x * y) = f.symm x * f.symm y
      apply f.injective
      calc
        f (f.symm (x * y)) = x * y := by exact f.apply_symm_apply (x * y)
        _ = f (f.symm x * f.symm y) := by
          have h : f (f.symm x * f.symm y) = x * y := by
            rw [hfmul, f.apply_symm_apply, f.apply_symm_apply]
          exact h.symm

/-- The real split-octonion automorphism group on the canonical Zorn carrier. -/
abbrev RealSplitOctonionAut : Type :=
  ↥(splitOctonionAutSubgroup (R := ℝ))

/-! A composition automorphism is already a real split-octonion
automorphism.  The unit-preservation proof is supplied by the native
composition owner; this definition is the canonical transport used by the
adjoint layer. -/
noncomputable def realSplitOctonionAutOfComposition
    (φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut) :
    RealSplitOctonionAut :=
  ⟨φ.1, ⟨
    InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut_fix_one φ,
    fun x y =>
      InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut_preserves_mul φ x y⟩⟩

@[simp] theorem realSplitOctonionAutOfComposition_apply
    (φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut)
    (x : SplitOctonionReal) :
    (realSplitOctonionAutOfComposition φ : SplitOctonionAutCandidate ℝ) x =
      (φ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.CanonicalLinearAut) x := rfl

instance : Group RealSplitOctonionAut := by
  infer_instance

/-- Membership in the automorphism subgroup is exactly unit and product preservation. -/
theorem mem_splitOctonionAutSubgroup_iff (f : SplitOctonionAutCandidate R) :
    f ∈ splitOctonionAutSubgroup (R := R) ↔
      PreservesZornOne f ∧ PreservesZornMul f := by
  rfl

/-- Any real split-octonion automorphism preserves the unit. -/
theorem RealSplitOctonionAut.preserves_one (φ : RealSplitOctonionAut) :
    (φ : SplitOctonionAutCandidate ℝ) (1 : SplitOctonionReal) = 1 :=
  φ.2.1

/-- Any real split-octonion automorphism preserves the Zorn product. -/
theorem RealSplitOctonionAut.preserves_mul
    (φ : RealSplitOctonionAut) (x y : SplitOctonionReal) :
    (φ : SplitOctonionAutCandidate ℝ) (x * y) =
      (φ : SplitOctonionAutCandidate ℝ) x * (φ : SplitOctonionAutCandidate ℝ) y :=
  φ.2.2 x y

/-- The identity candidate preserves the determinant. -/
theorem preservesDetZ_one :
    PreservesDetZ (R := R) (1 : SplitOctonionAutCandidate R) := by
  intro x
  rfl

/-- Every real split-octonion automorphism preserves the Zorn determinant. -/
@[simp] theorem RealSplitOctonionAut.preserves_detZ
    (φ : RealSplitOctonionAut) (x : SplitOctonionReal) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
        ((φ : SplitOctonionAutCandidate ℝ) x) =
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ x := by
  let ψ : InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut :=
    ⟨(φ : SplitOctonionAutCandidate ℝ), by
      intro X Y
      simpa [InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.IsRealZornCompositionAut,
        InfoGeometry.Canonical.ZornMatrix.mul]
        using φ.2.2 X Y⟩
  exact InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge.realZornCompositionAut_preserves_det
    (φ := ψ) x

/-- Any real split-octonion automorphism preserves the Zorn null cone. -/
@[simp] theorem RealSplitOctonionAut.preserves_null
    (φ : RealSplitOctonionAut) (x : SplitOctonionReal) :
    InfoGeometry.Algebra.Zorn.ZornMatrix.IsNull
      ((φ : SplitOctonionAutCandidate ℝ) x) ↔
      InfoGeometry.Algebra.Zorn.ZornMatrix.IsNull x := by
  unfold InfoGeometry.Algebra.Zorn.ZornMatrix.IsNull
  constructor
  · intro h
    calc
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ x =
          InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
            ((φ : SplitOctonionAutCandidate ℝ) x) := by
        symm
        exact RealSplitOctonionAut.preserves_detZ φ x
      _ = 0 := h
  · intro h
    calc
      InfoGeometry.Algebra.Zorn.ZornMatrix.detZ
          ((φ : SplitOctonionAutCandidate ℝ) x) =
          InfoGeometry.Algebra.Zorn.ZornMatrix.detZ x := by
        exact RealSplitOctonionAut.preserves_detZ φ x
      _ = 0 := h

end InfoGeometry.Canonical
