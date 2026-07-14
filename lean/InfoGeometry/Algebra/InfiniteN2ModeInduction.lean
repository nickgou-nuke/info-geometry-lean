import InfoGeometry.Algebra.FiniteN2Induction

/-!
# Infinite-mode N=2 supercharge transport

This is the SOP-compliant infinite-mode extension of
`InfoGeometry.Algebra.FiniteN2Induction`.

No analytic limit is asserted.  The infinite object is a mode-indexed family,
and finite-support/local direct-sum discipline is represented by the predicate
`HasFiniteModeSupport`.  All closure theorems are proved pointwise from the
finite N=2 theorem, and finite support is transported by the endomorphism
because ring homomorphisms map `0` to `0`.

Thus the transition is:

```text
finite N=2 closure theorem
→ infinitely indexed mode family
→ pointwise mode theorem
→ optional finite-support/direct-sum preservation
```

There are no wrappers, witness fields, law fields, certificates, guards, or
hidden convergence assumptions.
-/

namespace InfiniteN2ModeInduction

open InfoGeometry.Algebra.FiniteN2Induction

variable {ι A : Type*} [Ring A]

/-- The nonzero support of a mode family. -/
def modeSupport (F : ι → A) : Set ι :=
  {i | F i ≠ 0}

/-- A mode family has finite support, i.e. it is an algebraic direct-sum element. -/
def HasFiniteModeSupport (F : ι → A) : Prop :=
  (modeSupport F).Finite

/-- Pointwise transport of a mode family by a ring endomorphism. -/
def mapModeFamily (φ : A →+* A) (F : ι → A) : ι → A :=
  fun i => φ (F i)

/-- Pointwise transport by the finite iterate `φ^[n]`. -/
def iterateModeFamily (φ : A →+* A) (n : ℕ) (F : ι → A) : ι → A :=
  mapModeFamily (iterateEnd φ n) F

@[simp]
theorem mapModeFamily_apply (φ : A →+* A) (F : ι → A) (i : ι) :
    mapModeFamily φ F i = φ (F i) :=
  rfl

@[simp]
theorem iterateModeFamily_apply (φ : A →+* A) (n : ℕ) (F : ι → A) (i : ι) :
    iterateModeFamily φ n F i = (iterateEnd φ n) (F i) :=
  rfl

/-- Ring endomorphisms cannot create support outside the original mode support. -/
theorem support_mapModeFamily_subset
    (φ : A →+* A) (F : ι → A) :
    modeSupport (mapModeFamily φ F) ⊆ modeSupport F := by
  intro i hi
  have hne : φ (F i) ≠ 0 := by
    simpa [modeSupport, mapModeFamily] using hi
  by_contra hFi
  have hzero : F i = 0 := by
    simpa [modeSupport] using hFi
  exact hne (by rw [hzero, map_zero])

/-- Finite mode support is preserved by one endomorphism step. -/
theorem hasFiniteModeSupport_mapModeFamily
    (φ : A →+* A) {F : ι → A}
    (hF : HasFiniteModeSupport F) :
    HasFiniteModeSupport (mapModeFamily φ F) := by
  exact hF.subset (support_mapModeFamily_subset φ F)

/-- Finite mode support is preserved by every finite endomorphism iterate. -/
theorem hasFiniteModeSupport_iterateModeFamily
    (φ : A →+* A) (n : ℕ) {F : ι → A}
    (hF : HasFiniteModeSupport F) :
    HasFiniteModeSupport (iterateModeFamily φ n F) := by
  exact hasFiniteModeSupport_mapModeFamily (iterateEnd φ n) hF

/-- Modewise N=2 closure relation. -/
def ModeN2Closure (Q R H Z : ι → A) : Prop :=
  ∀ i : ι, anticommutator (Q i) (R i) = H i + Z i

/-- Modewise square-zero condition for a supercharge family. -/
def ModeSquareZero (Q : ι → A) : Prop :=
  ∀ i : ι, Q i * Q i = 0

/-- Modewise transported N=2 closure at finite stage `n`. -/
def IteratedModeN2Closure
    (φ : A →+* A) (n : ℕ) (Q R H Z : ι → A) : Prop :=
  ∀ i : ι,
    anticommutator ((iterateModeFamily φ n Q) i) ((iterateModeFamily φ n R) i) =
      (iterateModeFamily φ n H) i + (iterateModeFamily φ n Z) i

/-- Modewise transported square closure at finite stage `n`. -/
def IteratedModeN2SquareClosure
    (φ : A →+* A) (n : ℕ) (Q R H Z : ι → A) : Prop :=
  ∀ i : ι,
    (iterateEnd φ n) (Q i + R i) * (iterateEnd φ n) (Q i + R i) =
      (iterateModeFamily φ n H) i + (iterateModeFamily φ n Z) i

/--
Infinite-mode odd-odd closure transport.

This is the direct-sum/mode-family extension of the finite theorem: each mode
is closed by the finite N=2 transport lemma, with no analytic limit.
-/
theorem iterateModeFamily_preserves_n2_closure
    (φ : A →+* A)
    (n : ℕ)
    (Q R H Z : ι → A)
    (hQR : ModeN2Closure Q R H Z) :
    IteratedModeN2Closure φ n Q R H Z := by
  intro i
  exact iterateEnd_preserves_n2_closure φ n (Q i) (R i) (H i) (Z i) (hQR i)

/--
Infinite-mode full supercharge-square closure transport.

For every mode `i`, the finite-stage transported total supercharge satisfies
`(φ^[n] (Qᵢ + Rᵢ))² = φ^[n] Hᵢ + φ^[n] Zᵢ`.
-/
theorem iterateModeFamily_preserves_n2_square_closure
    (φ : A →+* A)
    (n : ℕ)
    (Q R H Z : ι → A)
    (hQ : ModeSquareZero Q)
    (hR : ModeSquareZero R)
    (hQR : ModeN2Closure Q R H Z) :
    IteratedModeN2SquareClosure φ n Q R H Z := by
  intro i
  exact
    iterateEnd_preserves_n2_square_closure
      φ n (Q i) (R i) (H i) (Z i) (hQ i) (hR i) (hQR i)

/--
SOP-compliant infinite-mode finite-support theorem.

If the four initial mode families are finitely supported direct-sum elements,
then every finite bonding/symmetry iterate remains finitely supported and
preserves both the odd-odd N=2 closure and the total-supercharge square closure.
-/
theorem finiteSupport_iterateModeFamily_preserves_n2_closures
    (φ : A →+* A)
    (n : ℕ)
    (Q R H Z : ι → A)
    (hQ0 : ModeSquareZero Q)
    (hR0 : ModeSquareZero R)
    (hQR : ModeN2Closure Q R H Z)
    (hQsupp : HasFiniteModeSupport Q)
    (hRsupp : HasFiniteModeSupport R)
    (hHsupp : HasFiniteModeSupport H)
    (hZsupp : HasFiniteModeSupport Z) :
    HasFiniteModeSupport (iterateModeFamily φ n Q) ∧
      HasFiniteModeSupport (iterateModeFamily φ n R) ∧
      HasFiniteModeSupport (iterateModeFamily φ n H) ∧
      HasFiniteModeSupport (iterateModeFamily φ n Z) ∧
      IteratedModeN2Closure φ n Q R H Z ∧
      IteratedModeN2SquareClosure φ n Q R H Z := by
  exact
    ⟨hasFiniteModeSupport_iterateModeFamily φ n hQsupp,
      hasFiniteModeSupport_iterateModeFamily φ n hRsupp,
      hasFiniteModeSupport_iterateModeFamily φ n hHsupp,
      hasFiniteModeSupport_iterateModeFamily φ n hZsupp,
      iterateModeFamily_preserves_n2_closure φ n Q R H Z hQR,
      iterateModeFamily_preserves_n2_square_closure φ n Q R H Z hQ0 hR0 hQR⟩

/-! ## Finsupp direct-sum mode algebra -/

section FinsuppDirectSum

variable [DecidableEq ι]

/--
Finitely supported N=2 mode families, matching the external Virasoro package's
`ℤ →₀ 𝕜` direct-sum discipline.
-/
abbrev FinsuppModeFamily (ι A : Type*) [Zero A] :=
  ι →₀ A

/--
The finitely supported pointwise odd-odd anticommutator.

Its support is contained in the union of the two input supports.
-/
noncomputable def finsuppAnticommutator
    (Q R : FinsuppModeFamily ι A) : FinsuppModeFamily ι A :=
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
theorem finsuppAnticommutator_apply
    (Q R : FinsuppModeFamily ι A) (i : ι) :
    finsuppAnticommutator Q R i = anticommutator (Q i) (R i) := by
  simp [finsuppAnticommutator]

/--
The support of the finitely supported anticommutator is controlled by the two
input supports.
-/
theorem support_finsuppAnticommutator_subset
    (Q R : FinsuppModeFamily ι A) :
    (finsuppAnticommutator Q R).support ⊆ Q.support ∪ R.support := by
  intro i hi
  rw [Finsupp.mem_support_iff] at hi
  by_contra hmem
  rw [Finset.mem_union] at hmem
  push_neg at hmem
  have hQ : Q i = 0 := by
    simpa [Finsupp.mem_support_iff] using hmem.1
  have hR : R i = 0 := by
    simpa [Finsupp.mem_support_iff] using hmem.2
  exact hi (by simp [finsuppAnticommutator_apply, anticommutator, hQ, hR])

/-- Transport a finite-support mode family by a ring endomorphism. -/
noncomputable def mapFinsuppModeFamily
    (φ : A →+* A) (F : FinsuppModeFamily ι A) : FinsuppModeFamily ι A :=
  F.mapRange φ (map_zero φ)

omit [DecidableEq ι] in
@[simp]
theorem mapFinsuppModeFamily_apply
    (φ : A →+* A) (F : FinsuppModeFamily ι A) (i : ι) :
    mapFinsuppModeFamily φ F i = φ (F i) := by
  simp [mapFinsuppModeFamily]

/-- Transport a finite-support mode family by the finite iterate `φ^[n]`. -/
noncomputable def iterateFinsuppModeFamily
    (φ : A →+* A) (n : ℕ) (F : FinsuppModeFamily ι A) :
    FinsuppModeFamily ι A :=
  mapFinsuppModeFamily (iterateEnd φ n) F

omit [DecidableEq ι] in
@[simp]
theorem iterateFinsuppModeFamily_apply
    (φ : A →+* A) (n : ℕ) (F : FinsuppModeFamily ι A) (i : ι) :
    iterateFinsuppModeFamily φ n F i = (iterateEnd φ n) (F i) := by
  simp [iterateFinsuppModeFamily]

/-- Finsupp-mode N=2 closure relation. -/
def FinsuppModeN2Closure
    (Q R H Z : FinsuppModeFamily ι A) : Prop :=
  finsuppAnticommutator Q R = H + Z

/-- Finsupp-mode square-zero condition. -/
def FinsuppModeSquareZero (Q : FinsuppModeFamily ι A) : Prop :=
  ∀ i : ι, Q i * Q i = 0

/--
Transport of the finitely supported anticommutator by a ring endomorphism.
-/
theorem mapFinsuppModeFamily_anticommutator
    (φ : A →+* A)
    (Q R : FinsuppModeFamily ι A) :
    mapFinsuppModeFamily φ (finsuppAnticommutator Q R) =
      finsuppAnticommutator (mapFinsuppModeFamily φ Q) (mapFinsuppModeFamily φ R) := by
  ext i
  exact map_anticommutator φ (Q i) (R i)

/--
Ring endomorphisms preserve Finsupp-mode N=2 closure.
-/
theorem mapFinsuppModeFamily_preserves_n2_closure
    (φ : A →+* A)
    (Q R H Z : FinsuppModeFamily ι A)
    (hQR : FinsuppModeN2Closure Q R H Z) :
    FinsuppModeN2Closure
      (mapFinsuppModeFamily φ Q)
      (mapFinsuppModeFamily φ R)
      (mapFinsuppModeFamily φ H)
      (mapFinsuppModeFamily φ Z) := by
  ext i
  exact map_n2_closure φ (Q i) (R i) (H i) (Z i) (by
    simpa [FinsuppModeN2Closure] using congrFun (congrArg DFunLike.coe hQR) i)

/--
Finite-stage transport of Finsupp-mode N=2 closure.
-/
theorem iterateFinsuppModeFamily_preserves_n2_closure
    (φ : A →+* A)
    (n : ℕ)
    (Q R H Z : FinsuppModeFamily ι A)
    (hQR : FinsuppModeN2Closure Q R H Z) :
    FinsuppModeN2Closure
      (iterateFinsuppModeFamily φ n Q)
      (iterateFinsuppModeFamily φ n R)
      (iterateFinsuppModeFamily φ n H)
      (iterateFinsuppModeFamily φ n Z) := by
  exact mapFinsuppModeFamily_preserves_n2_closure (iterateEnd φ n) Q R H Z hQR

/--
Finite-stage transport of Finsupp-mode square closure.

For every mode, the transported total supercharge has square equal to the
transported structural plus central term.
-/
theorem iterateFinsuppModeFamily_preserves_n2_square_closure
    (φ : A →+* A)
    (n : ℕ)
    (Q R H Z : FinsuppModeFamily ι A)
    (hQ : FinsuppModeSquareZero Q)
    (hR : FinsuppModeSquareZero R)
    (hQR : FinsuppModeN2Closure Q R H Z) :
    ∀ i : ι,
      (iterateFinsuppModeFamily φ n (Q + R)) i *
          (iterateFinsuppModeFamily φ n (Q + R)) i =
        (iterateFinsuppModeFamily φ n H) i +
          (iterateFinsuppModeFamily φ n Z) i := by
  intro i
  exact
    iterateEnd_preserves_n2_square_closure
      φ n (Q i) (R i) (H i) (Z i) (hQ i) (hR i) (by
        simpa [FinsuppModeN2Closure] using congrFun (congrArg DFunLike.coe hQR) i)

/--
Full Finsupp direct-sum N=2 induction theorem.

This is the external-Virasoro-style finite-to-infinite step: the infinite mode
object is an actual finitely supported direct sum, transport is `mapRange`,
and the closure laws are proved by reducing each coefficient to the finite
N=2 theorem.
-/
theorem iterateFinsuppModeFamily_preserves_n2_closures
    (φ : A →+* A)
    (n : ℕ)
    (Q R H Z : FinsuppModeFamily ι A)
    (hQ : FinsuppModeSquareZero Q)
    (hR : FinsuppModeSquareZero R)
    (hQR : FinsuppModeN2Closure Q R H Z) :
    FinsuppModeN2Closure
      (iterateFinsuppModeFamily φ n Q)
      (iterateFinsuppModeFamily φ n R)
      (iterateFinsuppModeFamily φ n H)
      (iterateFinsuppModeFamily φ n Z) ∧
      (∀ i : ι,
        (iterateFinsuppModeFamily φ n (Q + R)) i *
            (iterateFinsuppModeFamily φ n (Q + R)) i =
          (iterateFinsuppModeFamily φ n H) i +
            (iterateFinsuppModeFamily φ n Z) i) := by
  exact
    ⟨iterateFinsuppModeFamily_preserves_n2_closure φ n Q R H Z hQR,
      iterateFinsuppModeFamily_preserves_n2_square_closure φ n Q R H Z hQ hR hQR⟩

end FinsuppDirectSum

end InfiniteN2ModeInduction
