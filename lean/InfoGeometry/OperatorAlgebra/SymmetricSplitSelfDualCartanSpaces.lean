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
[selfDualCone_cartan_mem_iff,
 selfDualCone_dualPositive_cartan_invariant,
 selfDualCone_cartan_selfDual_readback,
 splitCartan_stageCarrier_mono,
 splitCartan_stage_mem_pairing_nonneg_colimit,
 splitCartan_colimit_pairing_nonneg,
 splitCartan_stageDetector,
 splitCartan_iUnion_stageCarrier_eq_univ,
 splitCartan_selfDualCone_extends,
 splitCartan_selfDualCone_extends_to_univ,
 splitCartan_symmetry_preserves_stageCarrier,
 splitCartan_symmetry_stageCarrier_mem_iff,
 splitCartan_symmetry_preserves_colimit,
 splitCartan_symmetry_colimit_mem_iff,
 splitCartan_dualPositive_cartan_invariant,
 splitCartan_stage_cartan_selfDual_readback,
 splitCartan_selfDualCone_cartan_mem_iff]

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

/-! ## General Cartan-symmetry readouts for self-dual carriers -/

/--
An involutive symmetry preserving a carrier preserves and reflects carrier
membership.
-/
theorem selfDualCone_cartan_mem_iff
    {E : Type*}
    (K : Set E)
    (θ : E → E)
    (hmap : Set.MapsTo θ K K)
    (hinvol : ∀ x : E, θ (θ x) = x)
    (x : E) :
    θ x ∈ K ↔ x ∈ K := by
  constructor
  · intro hθx
    have hθθx : θ (θ x) ∈ K := hmap hθx
    simpa [hinvol x] using hθθx
  · intro hx
    exact hmap hx

/--
Dual positivity against a carrier is invariant under an involutive
carrier-preserving Cartan symmetry that preserves the pairing.
-/
theorem selfDualCone_dualPositive_cartan_invariant
    {E : Type*}
    (pairing : E → E → ℝ)
    (K : Set E)
    (θ : E → E)
    (hmap : Set.MapsTo θ K K)
    (hinvol : ∀ x : E, θ (θ x) = x)
    (hpair : ∀ x y, pairing (θ x) (θ y) = pairing x y)
    (x : E) :
    (∀ y, y ∈ K → 0 ≤ pairing (θ x) y) ↔
      ∀ y, y ∈ K → 0 ≤ pairing x y := by
  constructor
  · intro hθx y hy
    have hθy : θ y ∈ K := hmap hy
    have h := hθx (θ y) hθy
    simpa [hpair x y] using h
  · intro hx y hy
    have hθy : θ y ∈ K := hmap hy
    have h := hx (θ y) hθy
    have hpair' : pairing (θ (θ x)) (θ y) = pairing (θ x) y :=
      hpair (θ x) y
    rw [← hpair']
    simpa [hinvol x] using h

/--
Self-dual readback under an involutive carrier-preserving Cartan symmetry:
membership of the transformed point is exactly dual positivity of the original
point.
-/
theorem selfDualCone_cartan_selfDual_readback
    {E : Type*}
    (pairing : E → E → ℝ)
    (K : Set E)
    (θ : E → E)
    (hmap : Set.MapsTo θ K K)
    (hinvol : ∀ x : E, θ (θ x) = x)
    (hpair : ∀ x y, pairing (θ x) (θ y) = pairing x y)
    (hself : IsSelfDualCone pairing K)
    (x : E) :
    θ x ∈ K ↔ ∀ y, y ∈ K → 0 ≤ pairing x y := by
  exact (hself (θ x)).trans
    (selfDualCone_dualPositive_cartan_invariant pairing K θ hmap hinvol hpair x)

/-! ## Split-Cartan proper-carrier geometry -/

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
If an ambient point already lies in a finite cumulative split-Cartan stage, then
it pairs nonnegatively with every element of the algebraic colimit carrier.
-/
theorem splitCartan_stage_mem_pairing_nonneg_colimit
    (X : ∀ n : ℕ, SplitOrthogonalCartanSpace n)
    (pairing : SplitCartanAmbient X → SplitCartanAmbient X → ℝ)
    (hself : ∀ n : ℕ, IsSelfDualCone pairing (splitCartanStageCarrier X n))
    {n : ℕ} {x : SplitCartanAmbient X}
    (hx : x ∈ splitCartanStageCarrier X n) :
    ∀ y, y ∈ Set.iUnion (splitCartanStageCarrier X) → 0 ≤ pairing x y := by
  exact selfDualCone_stage_mem_pairing_nonneg_iUnion
    pairing (splitCartanStageCarrier X) (splitCartan_stageCarrier_mono X) hself hx

/--
Any two ambient points coming from finite cumulative split-Cartan stages pair
nonnegatively once stagewise self-duality is assumed.
-/
theorem splitCartan_colimit_pairing_nonneg
    (X : ∀ n : ℕ, SplitOrthogonalCartanSpace n)
    (pairing : SplitCartanAmbient X → SplitCartanAmbient X → ℝ)
    (hself : ∀ n : ℕ, IsSelfDualCone pairing (splitCartanStageCarrier X n))
    {x y : SplitCartanAmbient X}
    (hx : x ∈ Set.iUnion (splitCartanStageCarrier X))
    (hy : y ∈ Set.iUnion (splitCartanStageCarrier X)) :
    0 ≤ pairing x y := by
  exact selfDualCone_iUnion_pairing_nonneg
    pairing (splitCartanStageCarrier X) (splitCartan_stageCarrier_mono X) hself hx hy

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

/--
An involutive stage-preserving Cartan symmetry preserves and reflects
membership in each cumulative finite stage carrier.
-/
theorem splitCartan_symmetry_stageCarrier_mem_iff
    (X : ∀ n : ℕ, SplitOrthogonalCartanSpace n)
    (θ : SplitCartanAmbient X → SplitCartanAmbient X)
    (hstage : ∀ z : SplitCartanAmbient X, (θ z).1 = z.1)
    (hinvol : ∀ z : SplitCartanAmbient X, θ (θ z) = z)
    (n : ℕ)
    (z : SplitCartanAmbient X) :
    θ z ∈ splitCartanStageCarrier X n ↔ z ∈ splitCartanStageCarrier X n := by
  constructor
  · intro hθz
    have hθθz : θ (θ z) ∈ splitCartanStageCarrier X n :=
      splitCartan_symmetry_preserves_stageCarrier X θ hstage n hθz
    simpa [hinvol z] using hθθz
  · intro hz
    exact splitCartan_symmetry_preserves_stageCarrier X θ hstage n hz

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
  exact selfDualCone_cartan_mem_iff
    (Set.iUnion (splitCartanStageCarrier X))
    θ
    (splitCartan_symmetry_preserves_colimit X θ hstage)
    hinvol
    z

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
  exact selfDualCone_dualPositive_cartan_invariant
    pairing
    (Set.iUnion (splitCartanStageCarrier X))
    θ
    (splitCartan_symmetry_preserves_colimit X θ hstage)
    hinvol
    hpair
    x

/--
Finite-stage self-dual readback under a split-Cartan symmetry: membership of
the transformed point in a finite cumulative carrier is exactly dual positivity
of the original point against that finite carrier.
-/
theorem splitCartan_stage_cartan_selfDual_readback
    (X : ∀ n : ℕ, SplitOrthogonalCartanSpace n)
    (pairing : SplitCartanAmbient X → SplitCartanAmbient X → ℝ)
    (θ : SplitCartanAmbient X → SplitCartanAmbient X)
    (hself : ∀ n : ℕ, IsSelfDualCone pairing (splitCartanStageCarrier X n))
    (hstage : ∀ z : SplitCartanAmbient X, (θ z).1 = z.1)
    (hinvol : ∀ z : SplitCartanAmbient X, θ (θ z) = z)
    (hpair : ∀ x y, pairing (θ x) (θ y) = pairing x y)
    (n : ℕ)
    (x : SplitCartanAmbient X) :
    θ x ∈ splitCartanStageCarrier X n ↔
      ∀ y, y ∈ splitCartanStageCarrier X n → 0 ≤ pairing x y := by
  exact selfDualCone_cartan_selfDual_readback
    pairing
    (splitCartanStageCarrier X n)
    θ
    (splitCartan_symmetry_preserves_stageCarrier X θ hstage n)
    hinvol
    hpair
    (hself n)
    x

/--
Self-dual cone membership is invariant under a pairing-preserving involutive
stage-preserving Cartan symmetry.
-/
theorem splitCartan_selfDualCone_cartan_mem_iff
    (X : ∀ n : ℕ, SplitOrthogonalCartanSpace n)
    (pairing : SplitCartanAmbient X → SplitCartanAmbient X → ℝ)
    (θ : SplitCartanAmbient X → SplitCartanAmbient X)
    (hstage : ∀ z : SplitCartanAmbient X, (θ z).1 = z.1)
    (hinvol : ∀ z : SplitCartanAmbient X, θ (θ z) = z)
    (hpair : ∀ x y, pairing (θ x) (θ y) = pairing x y)
    (hself : ∀ n : ℕ, IsSelfDualCone pairing (splitCartanStageCarrier X n))
    (x : SplitCartanAmbient X) :
    θ x ∈ Set.iUnion (splitCartanStageCarrier X) ↔
      x ∈ Set.iUnion (splitCartanStageCarrier X) := by
  have hcone : IsSelfDualCone pairing (Set.iUnion (splitCartanStageCarrier X)) :=
    splitCartan_selfDualCone_extends X pairing hself
  constructor
  · intro hθx
    have hpositiveθ := (hcone (θ x)).mp hθx
    have hpositivex :
        ∀ y, y ∈ Set.iUnion (splitCartanStageCarrier X) → 0 ≤ pairing x y :=
      (splitCartan_dualPositive_cartan_invariant X pairing θ hstage hinvol hpair x).mp
        hpositiveθ
    exact (hcone x).mpr hpositivex
  · intro hx
    have hpositivex := (hcone x).mp hx
    have hpositiveθ :
        ∀ y, y ∈ Set.iUnion (splitCartanStageCarrier X) → 0 ≤ pairing (θ x) y :=
      (splitCartan_dualPositive_cartan_invariant X pairing θ hstage hinvol hpair x).mpr
        hpositivex
    exact (hcone (θ x)).mpr hpositiveθ

/--
Self-dual readback under a split-Cartan symmetry: membership of the transformed
point in the colimit cone is exactly dual positivity of the original point.
-/
theorem splitCartan_cartan_selfDual_readback
    (X : ∀ n : ℕ, SplitOrthogonalCartanSpace n)
    (pairing : SplitCartanAmbient X → SplitCartanAmbient X → ℝ)
    (θ : SplitCartanAmbient X → SplitCartanAmbient X)
    (hself : ∀ n : ℕ, IsSelfDualCone pairing (splitCartanStageCarrier X n))
    (hstage : ∀ z : SplitCartanAmbient X, (θ z).1 = z.1)
    (hinvol : ∀ z : SplitCartanAmbient X, θ (θ z) = z)
    (hpair : ∀ x y, pairing (θ x) (θ y) = pairing x y)
    (x : SplitCartanAmbient X) :
    θ x ∈ Set.iUnion (splitCartanStageCarrier X) ↔
      ∀ y, y ∈ Set.iUnion (splitCartanStageCarrier X) → 0 ≤ pairing x y := by
  exact selfDualCone_cartan_selfDual_readback
    pairing
    (Set.iUnion (splitCartanStageCarrier X))
    θ
    (splitCartan_symmetry_preserves_colimit X θ hstage)
    hinvol
    hpair
    (splitCartan_selfDualCone_extends X pairing hself)
    x

end InfoGeometry.OperatorAlgebra.SymmetricSplitSelfDualCartanSpaces
