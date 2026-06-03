import InfoGeometry.OperatorAlgebra.ProperCarrierSelfDualConeExtension
import InfoGeometry.Geometry.SplitOrthogonalSpace

/-!
# InfoGeometry.OperatorAlgebra.SymmetricSplitSelfDualCartanSpaces

Concrete proper-carrier self-dual extension for symmetric split Cartan spaces.

This file keeps the owner theorem surface theorem-only. The split Cartan tower
is represented by the sigma carrier of finite split-orthogonal Cartan stages,
and the cumulative proper carriers are the initial stage segments. No socket,
certificate, witness packet, or structure field is used to hide a proof.

#### BUCKET 1: CLOSED FINITE/COLIMIT THEOREMS
[splitCartan_stageCarrier_mono,
 splitCartan_stageDetector,
 splitCartan_iUnion_stageCarrier_eq_univ,
 splitCartan_selfDualCone_extends,
 splitCartan_selfDualCone_extends_to_univ,
 splitCartan_symmetry_preserves_stageCarrier,
 splitCartan_symmetry_preserves_colimit,
 splitCartan_symmetry_colimit_mem_iff,
 splitCartan_dualPositive_cartan_invariant]

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT PREMISES
The self-dual extension theorem is conditional on a stagewise self-duality
premise for the cumulative split-Cartan carriers. The symmetry laws are
conditional on an explicit stage-preservation map, involutivity, and pairing
invariance for the supplied Cartan symmetry.

#### BUCKET 3: OPEN CLOSURE DEBT
No analytic symmetric-space theorem is claimed here. No Harish-Chandra theorem,
no Shilov boundary theorem, no modular-theory claim, and no Type III/KMS claim.
This file proves only the proper-carrier indexing geometry and its finite
Cartan-symmetry readouts.
-/

namespace InfoGeometry.OperatorAlgebra.SymmetricSplitSelfDualCartanSpaces

open InfoGeometry.Geometry.Cartan
open InfoGeometry.OperatorAlgebra.SelfDualConeColimit
open InfoGeometry.OperatorAlgebra.ProperCarrierSelfDualConeExtension

/-- The ambient carrier built from all finite split-Cartan stages. -/
abbrev SplitCartanAmbient
    (X : ∀ n : ℕ, SplitOrthogonalCartanSpace n) : Type :=
  Σ n : ℕ, (X n).carrier

/--
The cumulative proper carrier through stage `n`: all ambient points whose stage
index is at most `n`.
-/
def splitCartanStageCarrier
    (X : ∀ n : ℕ, SplitOrthogonalCartanSpace n) (n : ℕ) :
    Set (SplitCartanAmbient X) :=
  {z | z.1 ≤ n}

/-- The cumulative split-Cartan carrier family is monotone in the stage index. -/
theorem splitCartan_stageCarrier_mono
    (X : ∀ n : ℕ, SplitOrthogonalCartanSpace n) :
    Monotone (splitCartanStageCarrier X) := by
  intro i j hij z hz
  exact Nat.le_trans hz hij

/--
Every ambient point belongs to the cumulative carrier indexed by its own stage.
This is the theorem-level detector used by the colimit extension theorem.
-/
theorem splitCartan_stageDetector
    (X : ∀ n : ℕ, SplitOrthogonalCartanSpace n)
    (pairing : SplitCartanAmbient X → SplitCartanAmbient X → ℝ) :
    ∀ z, (∀ y, y ∈ Set.iUnion (splitCartanStageCarrier X) → 0 ≤ pairing z y) →
      ∃ n : ℕ, z ∈ splitCartanStageCarrier X n := by
  intro z _
  exact ⟨z.1, by
    dsimp [splitCartanStageCarrier]
    exact le_rfl⟩

/-- The cumulative finite-stage carrier union is the whole sigma carrier. -/
theorem splitCartan_iUnion_stageCarrier_eq_univ
    (X : ∀ n : ℕ, SplitOrthogonalCartanSpace n) :
    Set.iUnion (splitCartanStageCarrier X) = (Set.univ : Set (SplitCartanAmbient X)) := by
  ext z
  constructor
  · intro _
    trivial
  · intro _
    exact Set.mem_iUnion.mpr ⟨z.1, by
      dsimp [splitCartanStageCarrier]
      exact le_rfl⟩

/--
If the cumulative split-Cartan stages are self-dual cones, then the whole sigma
carrier is self-dual by proper-carrier extension.
-/
theorem splitCartan_selfDualCone_extends
    (X : ∀ n : ℕ, SplitOrthogonalCartanSpace n)
    (pairing : SplitCartanAmbient X → SplitCartanAmbient X → ℝ)
    (hself : ∀ n : ℕ, IsSelfDualCone pairing (splitCartanStageCarrier X n)) :
    IsSelfDualCone pairing (Set.iUnion (splitCartanStageCarrier X)) := by
  apply properCarrier_selfDualCone_extends_to_algebra pairing (splitCartanStageCarrier X)
  · exact splitCartan_stageCarrier_mono X
  · exact hself
  · exact splitCartan_stageDetector X pairing

/--
If the cumulative split-Cartan stages are self-dual cones, self-duality extends
to the whole ambient sigma carrier.
-/
theorem splitCartan_selfDualCone_extends_to_univ
    (X : ∀ n : ℕ, SplitOrthogonalCartanSpace n)
    (pairing : SplitCartanAmbient X → SplitCartanAmbient X → ℝ)
    (hself : ∀ n : ℕ, IsSelfDualCone pairing (splitCartanStageCarrier X n)) :
    IsSelfDualCone pairing (Set.univ : Set (SplitCartanAmbient X)) := by
  have hUnion :
      Set.iUnion (splitCartanStageCarrier X) = (Set.univ : Set (SplitCartanAmbient X)) :=
    splitCartan_iUnion_stageCarrier_eq_univ X
  simpa [hUnion] using splitCartan_selfDualCone_extends X pairing hself

/--
A Cartan symmetry that preserves the stage index preserves every cumulative
proper carrier.
-/
theorem splitCartan_symmetry_preserves_stageCarrier
    (X : ∀ n : ℕ, SplitOrthogonalCartanSpace n)
    (θ : SplitCartanAmbient X → SplitCartanAmbient X)
    (hstage : ∀ z : SplitCartanAmbient X, (θ z).1 = z.1)
    (n : ℕ) :
    Set.MapsTo θ (splitCartanStageCarrier X n) (splitCartanStageCarrier X n) := by
  intro z hz
  dsimp [splitCartanStageCarrier] at hz ⊢
  simpa [hstage z] using hz

/-- A stage-preserving Cartan symmetry preserves the algebraic colimit carrier. -/
theorem splitCartan_symmetry_preserves_colimit
    (X : ∀ n : ℕ, SplitOrthogonalCartanSpace n)
    (θ : SplitCartanAmbient X → SplitCartanAmbient X)
    (hstage : ∀ z : SplitCartanAmbient X, (θ z).1 = z.1) :
    Set.MapsTo θ
      (Set.iUnion (splitCartanStageCarrier X))
      (Set.iUnion (splitCartanStageCarrier X)) := by
  intro z hz
  rcases Set.mem_iUnion.mp hz with ⟨n, hzn⟩
  exact Set.mem_iUnion.mpr
    ⟨n, splitCartan_symmetry_preserves_stageCarrier X θ hstage n hzn⟩

/--
An involutive stage-preserving Cartan symmetry preserves and reflects membership
in the split-Cartan algebraic colimit carrier.
-/
theorem splitCartan_symmetry_colimit_mem_iff
    (X : ∀ n : ℕ, SplitOrthogonalCartanSpace n)
    (θ : SplitCartanAmbient X → SplitCartanAmbient X)
    (hstage : ∀ z : SplitCartanAmbient X, (θ z).1 = z.1)
    (hinvol : ∀ z : SplitCartanAmbient X, θ (θ z) = z)
    (z : SplitCartanAmbient X) :
    θ z ∈ Set.iUnion (splitCartanStageCarrier X) ↔
      z ∈ Set.iUnion (splitCartanStageCarrier X) := by
  constructor
  · intro hz
    have hθθz :
        θ (θ z) ∈ Set.iUnion (splitCartanStageCarrier X) :=
      splitCartan_symmetry_preserves_colimit X θ hstage hz
    simpa [hinvol z] using hθθz
  · intro hz
    exact splitCartan_symmetry_preserves_colimit X θ hstage hz

/--
Dual-positivity is invariant under an involutive stage-preserving Cartan
symmetry that preserves the pairing.
-/
theorem splitCartan_dualPositive_cartan_invariant
    (X : ∀ n : ℕ, SplitOrthogonalCartanSpace n)
    (pairing : SplitCartanAmbient X → SplitCartanAmbient X → ℝ)
    (θ : SplitCartanAmbient X → SplitCartanAmbient X)
    (hstage : ∀ z : SplitCartanAmbient X, (θ z).1 = z.1)
    (hinvol : ∀ z : SplitCartanAmbient X, θ (θ z) = z)
    (hpair : ∀ x y, pairing (θ x) (θ y) = pairing x y)
    (x : SplitCartanAmbient X) :
    (∀ y, y ∈ Set.iUnion (splitCartanStageCarrier X) → 0 ≤ pairing (θ x) y) ↔
      ∀ y, y ∈ Set.iUnion (splitCartanStageCarrier X) → 0 ≤ pairing x y := by
  constructor
  · intro hθx y hy
    have hθy :
        θ y ∈ Set.iUnion (splitCartanStageCarrier X) :=
      splitCartan_symmetry_preserves_colimit X θ hstage hy
    have h := hθx (θ y) hθy
    simpa [hpair x y] using h
  · intro hx y hy
    have hθy :
        θ y ∈ Set.iUnion (splitCartanStageCarrier X) :=
      splitCartan_symmetry_preserves_colimit X θ hstage hy
    have h := hx (θ y) hθy
    have hpair' : pairing (θ (θ x)) (θ y) = pairing (θ x) y :=
      hpair (θ x) y
    rw [← hpair']
    simpa [hinvol x] using h

end InfoGeometry.OperatorAlgebra.SymmetricSplitSelfDualCartanSpaces
