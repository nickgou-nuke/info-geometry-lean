import Mathlib.Order.Filter.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import InfoGeometry.Canonical.SplitCliffordSourceCarrier

/-!
# InfoGeometry.Canonical.SplitCliffordSourceCurrent

Source-side current-mode interface over a split-Clifford carrier.

This file does not claim truncation is already proved from split completion.
It isolates the exact truncation theorem obligation.
-/

namespace InfoGeometry.Canonical.SplitCliffordSourceCurrent

open Filter
open InfoGeometry.Canonical.SplitCliffordSourceCarrier

/--
Current modes attached to a split source carrier.

`modeAction l v` is the `l`-th current mode applied to source vector `v`.
-/
structure SplitSourceCurrent
    (𝕜 V Carrier : Type*) [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup Carrier] [Module 𝕜 Carrier]
    (S : SplitSourceCarrier 𝕜 V Carrier) where
  /-- Source current mode family. -/
  modeAction : Int → V →ₗ[𝕜] Carrier

/--
Truncation obligation surface for a split source current.

This is the honest theorem target that must be proved from source stabilization
and transported normal ordering.
-/
def SplitCurrentTruncation
    {𝕜 V Carrier : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup Carrier] [Module 𝕜 Carrier]
    {S : SplitSourceCarrier 𝕜 V Carrier}
    (J : SplitSourceCurrent 𝕜 V Carrier S) : Prop :=
  ∀ v : V, ∀ᶠ l : Int in atTop, J.modeAction l v = 0

/--
A real truncation lemma.

If the source cutoff predicate is monotone in the mode index, and the current
mode vanishes whenever the source vector is past its cutoff, then the current
satisfies the `atTop` truncation obligation.
-/
theorem splitCurrentTruncation_of_stableCutoff_zero
    {𝕜 V Carrier : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup Carrier] [Module 𝕜 Carrier]
    {S : SplitSourceCarrier 𝕜 V Carrier}
    (J : SplitSourceCurrent 𝕜 V Carrier S)
    (hmono :
      ∀ {v : V} {N M : Int},
        S.stableCutoff v N → N ≤ M → S.stableCutoff v M)
    (hzero :
      ∀ (v : V) (l : Int),
        S.stableCutoff v l → J.modeAction l v = 0) :
    SplitCurrentTruncation J := by
  intro v
  rcases S.exists_stableCutoff v with ⟨N, hN⟩
  refine Filter.eventually_atTop.2 ?_
  exact ⟨N, fun l hl => hzero v l (hmono hN hl)⟩

/--
Convenience form using the carrier's built-in monotonicity field.
-/
theorem splitCurrentTruncation_of_stableCutoff
    {𝕜 V Carrier : Type*} [Field 𝕜] [CharZero 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    [AddCommGroup Carrier] [Module 𝕜 Carrier]
    {S : SplitSourceCarrier 𝕜 V Carrier}
    (J : SplitSourceCurrent 𝕜 V Carrier S)
    (hzero : ∀ {v : V} {l : Int}, S.stableCutoff v l → J.modeAction l v = 0) :
    SplitCurrentTruncation J :=
  splitCurrentTruncation_of_stableCutoff_zero J S.stableCutoff_mono
    (fun v l hv => hzero hv)

/-! ## Endomorphism-valued source-current owner surface -/

section EndLift

universe u

variable (𝕜 : Type u) [Field 𝕜] [CharZero 𝕜]
variable (V : Type u) [AddCommGroup V] [Module 𝕜 V]

/-- Endomorphism shorthand. -/
abbrev End := V →ₗ[𝕜] V

/--
Split Witt/CAR generators on the source state space.

The CAR laws are carried as theorem data and can be instantiated by concrete
`Cl(4,4)` realizations in downstream files.
-/
structure WittGenerators where
  create : Int → End 𝕜 V
  annihilate : Int → End 𝕜 V
  car_annihilate_create :
    ∀ i j : Int,
      (annihilate i).comp (create j) + (create j).comp (annihilate i) =
        if i = j then LinearMap.id else 0
  car_annihilate_annihilate :
    ∀ i j : Int,
      (annihilate i).comp (annihilate j) + (annihilate j).comp (annihilate i) = 0
  car_create_create :
    ∀ i j : Int,
      (create i).comp (create j) + (create j).comp (create i) = 0

/-- Dirac-sea polarization selector on mode labels. -/
structure DiracSeaPolarization where
  occupied : Int → Prop
  decidable_occupied : DecidablePred occupied

attribute [instance] DiracSeaPolarization.decidable_occupied

/-- Raw bilinear `a†ᵢ aⱼ`. -/
def rawBilinear
    (W : WittGenerators 𝕜 V)
    (i j : Int) : End 𝕜 V :=
  (W.create i).comp (W.annihilate j)

/-- Normal-ordered bilinear with explicit contraction term. -/
def normalOrderedBilinear
    (W : WittGenerators 𝕜 V)
    (contraction : Int → Int → 𝕜)
    (i j : Int) : End 𝕜 V :=
  rawBilinear 𝕜 V W i j - (contraction i j) • (1 : End 𝕜 V)

/--
Finite-cutoff current mode:

`J_cutoff(n) = Σ k∈cutoff :a†_k a_{k+n}:`.
-/
def cutoffCurrentMode
    (W : WittGenerators 𝕜 V)
    (contraction : Int → Int → 𝕜)
    (cutoff : Finset Int)
    (n : Int) : End 𝕜 V :=
  cutoff.sum (fun k => normalOrderedBilinear 𝕜 V W contraction k (k + n))

/-- Empty-cutoff current mode is zero. -/
@[simp] theorem cutoffCurrentMode_empty
    (W : WittGenerators 𝕜 V)
    (contraction : Int → Int → 𝕜)
    (n : Int) :
    cutoffCurrentMode 𝕜 V W contraction (∅ : Finset Int) n = 0 := by
  simp [cutoffCurrentMode]

/--
Insert-step expansion for finite-cutoff current modes.
-/
theorem cutoffCurrentMode_insert
    (W : WittGenerators 𝕜 V)
    (contraction : Int → Int → 𝕜)
    (k : Int) (cutoff : Finset Int)
    (hk : k ∉ cutoff)
    (n : Int) :
    cutoffCurrentMode 𝕜 V W contraction (insert k cutoff) n =
      normalOrderedBilinear 𝕜 V W contraction k (k + n) +
        cutoffCurrentMode 𝕜 V W contraction cutoff n := by
  simp [cutoffCurrentMode, Finset.sum_insert, hk, add_comm, add_left_comm, add_assoc]

/--
Cutoff stabilization surface: finite-cutoff current actions eventually
stabilize on each vector.
-/
def CurrentCutoffStabilizes
    (W : WittGenerators 𝕜 V)
    (contraction : Int → Int → 𝕜)
    (cutoffs : Nat → Finset Int) : Prop :=
  ∀ (n : Int) (v : V),
    ∃ N : Nat, ∀ m ≥ N,
      cutoffCurrentMode 𝕜 V W contraction (cutoffs m) n v =
        cutoffCurrentMode 𝕜 V W contraction (cutoffs N) n v

/--
Owner datum for a stabilized lifted source-current family.

This keeps the debt explicit without introducing fake closure: concrete
modules must provide `Jlift`, cutoff compatibility, and truncation.
-/
structure SplitCurrentLiftDatum where
  W : WittGenerators 𝕜 V
  contraction : Int → Int → 𝕜
  cutoffs : Nat → Finset Int
  cutoff_stabilizes : CurrentCutoffStabilizes 𝕜 V W contraction cutoffs
  Jlift : Int → End 𝕜 V
  /--
  Realization of `Jlift` by stabilized finite-cutoff formulas.
  -/
  from_cutoff :
    ∀ n : Int, ∀ v : V,
      ∃ N : Nat, ∀ m ≥ N,
        Jlift n v = cutoffCurrentMode 𝕜 V W contraction (cutoffs m) n v
  trunc : ∀ v : V, ∀ᶠ l in (atTop : Filter Int), Jlift l v = 0

/-- Readout definition for the transported lifted current family. -/
def Jlift (L : SplitCurrentLiftDatum 𝕜 V) : Int → End 𝕜 V :=
  L.Jlift

/-- Truncation predicate for endomorphism-valued lifted current families. -/
def SplitLiftTruncation (J : Int → End 𝕜 V) : Prop :=
  ∀ v : V, ∀ᶠ l in (atTop : Filter Int), J l v = 0

/-- Truncation theorem readout for the lifted current family. -/
theorem Jlift_trunc (L : SplitCurrentLiftDatum 𝕜 V) :
    SplitLiftTruncation 𝕜 V L.Jlift :=
  L.trunc

/-- Stabilized finite-cutoff realization readout for the lifted current family. -/
theorem Jlift_from_cutoff (L : SplitCurrentLiftDatum 𝕜 V) :
    ∀ n : Int, ∀ v : V,
      ∃ N : Nat, ∀ m ≥ N,
        L.Jlift n v = cutoffCurrentMode 𝕜 V L.W L.contraction (L.cutoffs m) n v :=
  L.from_cutoff

end EndLift

end InfoGeometry.Canonical.SplitCliffordSourceCurrent
