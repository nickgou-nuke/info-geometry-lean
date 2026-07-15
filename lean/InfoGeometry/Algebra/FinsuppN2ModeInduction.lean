import InfoGeometry.Algebra.FiniteN2Induction

/-!
# Finitely supported infinite-mode N=2 supercharge transport

This file follows the external Virasoro package methodology more literally than
an arbitrary-family formulation: the infinite mode carrier is an algebraic
direct sum `ι →₀ A`, so finite support is built into the type, exactly as the
Witt algebra uses `ℤ →₀ 𝕜`.

No analytic limit is asserted.  No wrapper/certificate/law fields are used.
-/

namespace FinsuppN2ModeInduction

open FiniteN2Induction

variable {ι A : Type*} [Ring A]

/-- A finitely supported infinite-mode family of coefficients. -/
abbrev ModeFamily (ι A : Type*) [Zero A] := ι →₀ A

/--
The finite-support odd-odd anticommutator mode family.

The support is contained in `Q.support ∪ R.support`, so the result is again
an algebraic direct-sum element.
-/
noncomputable def anticommutatorMode
    [DecidableEq ι] (Q R : ModeFamily ι A) : ModeFamily ι A :=
  Finsupp.onFinset (Q.support ∪ R.support)
    (fun i => anticommutator (Q i) (R i))
    (by
      intro i hi
      by_contra hmem
      rw [Finset.mem_union] at hmem
      push_neg at hmem
      have hQ : Q i = 0 := by
        simpa [Finsupp.mem_support_iff] using hmem.1
      have hR : R i = 0 := by
        simpa [Finsupp.mem_support_iff] using hmem.2
      exact hi (by simp [anticommutator, hQ, hR]))

@[simp]
theorem anticommutatorMode_apply
    [DecidableEq ι] (Q R : ModeFamily ι A) (i : ι) :
    anticommutatorMode Q R i = anticommutator (Q i) (R i) := by
  simp [anticommutatorMode]

/-- The anticommutator mode support is controlled by the input supports. -/
theorem support_anticommutatorMode_subset
    [DecidableEq ι] (Q R : ModeFamily ι A) :
    (anticommutatorMode Q R).support ⊆ Q.support ∪ R.support := by
  intro i hi
  rw [Finsupp.mem_support_iff] at hi
  by_contra hmem
  rw [Finset.mem_union] at hmem
  push_neg at hmem
  have hQ : Q i = 0 := by
    simpa [Finsupp.mem_support_iff] using hmem.1
  have hR : R i = 0 := by
    simpa [Finsupp.mem_support_iff] using hmem.2
  exact hi (by simp [anticommutatorMode_apply, anticommutator, hQ, hR])

/-- Transport a finitely supported mode family by a ring endomorphism. -/
noncomputable def mapModeFamily (φ : A →+* A) (F : ModeFamily ι A) : ModeFamily ι A :=
  F.mapRange φ φ.map_zero

/-- Transport a finitely supported mode family by the finite iterate `φ^[n]`. -/
noncomputable def iterateModeFamily (φ : A →+* A) (n : ℕ) (F : ModeFamily ι A) : ModeFamily ι A :=
  mapModeFamily (iterateEnd φ n) F

@[simp]
theorem mapModeFamily_apply (φ : A →+* A) (F : ModeFamily ι A) (i : ι) :
    mapModeFamily φ F i = φ (F i) := by
  simp [mapModeFamily]

@[simp]
theorem iterateModeFamily_apply (φ : A →+* A) (n : ℕ) (F : ModeFamily ι A) (i : ι) :
    iterateModeFamily φ n F i = (iterateEnd φ n) (F i) := by
  simp [iterateModeFamily]

/-- Modewise N=2 closure on a finitely supported infinite-mode direct sum. -/
def ModeN2Closure (Q R H Z : ModeFamily ι A) : Prop :=
  ∀ i : ι, anticommutator (Q i) (R i) = H i + Z i

/-- N=2 closure as equality of finite-support mode objects. -/
def ModeN2ClosureEq [DecidableEq ι] (Q R H Z : ModeFamily ι A) : Prop :=
  anticommutatorMode Q R = H + Z

/-- Equality-form closure is equivalent to pointwise closure. -/
theorem modeN2ClosureEq_iff_modeN2Closure
    [DecidableEq ι] (Q R H Z : ModeFamily ι A) :
    ModeN2ClosureEq Q R H Z ↔ ModeN2Closure Q R H Z := by
  constructor
  · intro h i
    exact congrFun (congrArg DFunLike.coe h) i
  · intro h
    ext i
    exact h i

/-- Modewise square-zero condition on a finitely supported mode family. -/
def ModeSquareZero (Q : ModeFamily ι A) : Prop :=
  ∀ i : ι, Q i * Q i = 0

/-- Transported modewise N=2 closure after `n` finite bonding/symmetry steps. -/
def IteratedModeN2Closure
    (φ : A →+* A) (n : ℕ) (Q R H Z : ModeFamily ι A) : Prop :=
  ∀ i : ι,
    anticommutator ((iterateModeFamily φ n Q) i) ((iterateModeFamily φ n R) i) =
      (iterateModeFamily φ n H) i + (iterateModeFamily φ n Z) i

/-- Transported modewise square closure after `n` finite bonding/symmetry steps. -/
def IteratedModeN2SquareClosure
    (φ : A →+* A) (n : ℕ) (Q R H Z : ModeFamily ι A) : Prop :=
  ∀ i : ι,
    (iterateEnd φ n) (Q i + R i) * (iterateEnd φ n) (Q i + R i) =
      (iterateModeFamily φ n H) i + (iterateModeFamily φ n Z) i

/--
Direct-sum infinite-mode odd-odd closure transport.

The infinite mode carrier is finitely supported by construction (`ι →₀ A`), and
the proof is pointwise from the finite N=2 transport theorem.
-/
theorem iterateModeFamily_preserves_n2_closure
    (φ : A →+* A)
    (n : ℕ)
    (Q R H Z : ModeFamily ι A)
    (hQR : ModeN2Closure Q R H Z) :
    IteratedModeN2Closure φ n Q R H Z := by
  intro i
  exact iterateEnd_preserves_n2_closure φ n (Q i) (R i) (H i) (Z i) (hQR i)

/--
Direct-sum infinite-mode odd-odd closure transport as an equality of
finite-support mode objects.
-/
theorem iterateModeFamily_preserves_n2_closure_eq
    [DecidableEq ι]
    (φ : A →+* A)
    (n : ℕ)
    (Q R H Z : ModeFamily ι A)
    (hQR : ModeN2ClosureEq Q R H Z) :
    ModeN2ClosureEq
      (iterateModeFamily φ n Q)
      (iterateModeFamily φ n R)
      (iterateModeFamily φ n H)
      (iterateModeFamily φ n Z) := by
  rw [modeN2ClosureEq_iff_modeN2Closure] at hQR ⊢
  exact iterateModeFamily_preserves_n2_closure φ n Q R H Z hQR

/--
Direct-sum infinite-mode full supercharge-square closure transport.

For each mode `i`, the finite theorem gives
`(φ^[n] (Qᵢ + Rᵢ))² = φ^[n] Hᵢ + φ^[n] Zᵢ`.
-/
theorem iterateModeFamily_preserves_n2_square_closure
    (φ : A →+* A)
    (n : ℕ)
    (Q R H Z : ModeFamily ι A)
    (hQ : ModeSquareZero Q)
    (hR : ModeSquareZero R)
    (hQR : ModeN2Closure Q R H Z) :
    IteratedModeN2SquareClosure φ n Q R H Z := by
  intro i
  exact
    iterateEnd_preserves_n2_square_closure
      φ n (Q i) (R i) (H i) (Z i) (hQ i) (hR i) (hQR i)

/--
The finitely supported infinite-mode N=2 transport theorem.

This is the exact algebraic-direct-sum analogue of the Virasoro/Witt `ℤ →₀ 𝕜`
methodology: the mode set may be infinite, but every element is finitely
supported by construction.
-/
theorem finsuppMode_preserves_n2_closures
    (φ : A →+* A)
    (n : ℕ)
    (Q R H Z : ModeFamily ι A)
    (hQ : ModeSquareZero Q)
    (hR : ModeSquareZero R)
    (hQR : ModeN2Closure Q R H Z) :
    IteratedModeN2Closure φ n Q R H Z ∧
      IteratedModeN2SquareClosure φ n Q R H Z := by
  exact
    ⟨iterateModeFamily_preserves_n2_closure φ n Q R H Z hQR,
      iterateModeFamily_preserves_n2_square_closure φ n Q R H Z hQ hR hQR⟩

/--
The finitely supported infinite-mode N=2 transport theorem in equality form.

This is the closest match to the external Virasoro construction style: closure
is an equality in the direct-sum carrier `ι →₀ A`.
-/
theorem finsuppMode_preserves_n2_closures_eq
    [DecidableEq ι]
    (φ : A →+* A)
    (n : ℕ)
    (Q R H Z : ModeFamily ι A)
    (hQ : ModeSquareZero Q)
    (hR : ModeSquareZero R)
    (hQR : ModeN2ClosureEq Q R H Z) :
    ModeN2ClosureEq
      (iterateModeFamily φ n Q)
      (iterateModeFamily φ n R)
      (iterateModeFamily φ n H)
      (iterateModeFamily φ n Z) ∧
      IteratedModeN2SquareClosure φ n Q R H Z := by
  rw [modeN2ClosureEq_iff_modeN2Closure] at hQR
  exact
    ⟨iterateModeFamily_preserves_n2_closure_eq φ n Q R H Z
        ((modeN2ClosureEq_iff_modeN2Closure Q R H Z).2 hQR),
      iterateModeFamily_preserves_n2_square_closure φ n Q R H Z hQ hR hQR⟩

end FinsuppN2ModeInduction
