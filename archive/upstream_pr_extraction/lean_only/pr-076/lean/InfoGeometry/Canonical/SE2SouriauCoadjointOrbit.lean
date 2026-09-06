import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Instances.Real.Lemmas
import InfoGeometry.Canonical.SE2SouriauCocycle

set_option linter.unusedSectionVars false

namespace SE2Souriau

/-- 1. Elements of the Lie algebra se(2) and its dual se(2)* represented as ℝ³ -/
@[ext]
structure SE2Vector where
  j  : ℝ  -- Rotation component J
  p1 : ℝ  -- Translation component P1
  p2 : ℝ  -- Translation component P2

namespace SE2Vector

def add (u v : SE2Vector) : SE2Vector :=
  ⟨u.j + v.j, u.p1 + v.p1, u.p2 + v.p2⟩

def smul (c : ℝ) (v : SE2Vector) : SE2Vector :=
  ⟨c * v.j, c * v.p1, c * v.p2⟩

def neg (v : SE2Vector) : SE2Vector :=
  ⟨-v.j, -v.p1, -v.p2⟩

def sub (u v : SE2Vector) : SE2Vector :=
  ⟨u.j - v.j, u.p1 - v.p1, u.p2 - v.p2⟩

/-- 2. Lie bracket on se(2): [X, Y] = (0, ω w2 - Ω v2, -ω w1 + Ω v1) -/
def lieBracket (X Y : SE2Vector) : SE2Vector :=
  ⟨0,
   X.j * Y.p2 - Y.j * X.p2,
   -(X.j * Y.p1 - Y.j * X.p1)⟩

/-- Dual pairing ⟨μ, X⟩ on se(2)* × se(2) -/
def pairing (μ X : SE2Vector) : ℝ :=
  μ.j * X.j + μ.p1 * X.p1 + μ.p2 * X.p2

/-- 3. Casimir Invariant for se(2)* coadjoint orbit: C(μ) = p1² + p2² -/
def casimir (μ : SE2Vector) : ℝ :=
  μ.p1^2 + μ.p2^2

/-- 4. Souriau Symplectic 2-Cocycle on se(2): θ_m(X, Y) = m * (v1 * w2 - v2 * w1) -/
def souriauCocycle (m : ℝ) (X Y : SE2Vector) : ℝ :=
  m * (X.p1 * Y.p2 - X.p2 * Y.p1)

/-- 5. KKS Symplectic 2-form with Souriau Cocycle extension:
    ω_affine(μ)(X, Y) = ⟨μ, [X, Y]⟩ + θ_m(X, Y) -/
def affineKKSForm (m : ℝ) (μ X Y : SE2Vector) : ℝ :=
  pairing μ (lieBracket X Y) + souriauCocycle m X Y

/-- 🏆 THEOREM 1: Skew-Symmetry of the se(2) Lie Bracket -/
theorem lieBracket_skew (X Y : SE2Vector) :
    lieBracket X Y = neg (lieBracket Y X) := by
  dsimp [lieBracket, neg]
  ext <;> ring

/-- 🏆 THEOREM 2: Jacobi Identity for the se(2) Lie Bracket -/
theorem lieBracket_jacobi (X Y Z : SE2Vector) :
    add (lieBracket X (lieBracket Y Z))
        (add (lieBracket Y (lieBracket Z X))
             (lieBracket Z (lieBracket X Y))) = ⟨0, 0, 0⟩ := by
  dsimp [lieBracket, add]
  ext <;> ring

/-- 🏆 THEOREM 3: Skew-Symmetry of Souriau's Symplectic Cocycle θ_m(X, Y) = -θ_m(Y, X) -/
theorem souriauCocycle_skew (m : ℝ) (X Y : SE2Vector) :
    souriauCocycle m X Y = - souriauCocycle m Y X := by
  dsimp [souriauCocycle]
  ring

/-- 🏆 THEOREM 4: Souriau 2-Cocycle Identity (Lie Algebra Cohomology Condition)
    θ_m([X, Y], Z) + θ_m([Y, Z], X) + θ_m([Z, X], Y) = 0 -/
theorem souriauCocycle_identity (m : ℝ) (X Y Z : SE2Vector) :
    souriauCocycle m (lieBracket X Y) Z +
    souriauCocycle m (lieBracket Y Z) X +
    souriauCocycle m (lieBracket Z X) Y = 0 := by
  dsimp [souriauCocycle, lieBracket]
  ring

theorem souriauCocycle_add_left (m : ℝ) (X1 X2 Y : SE2Vector) :
    souriauCocycle m (add X1 X2) Y =
      souriauCocycle m X1 Y + souriauCocycle m X2 Y := by
  dsimp [souriauCocycle, add]
  ring

theorem souriauCocycle_smul_left (m c : ℝ) (X Y : SE2Vector) :
    souriauCocycle m (smul c X) Y = c * souriauCocycle m X Y := by
  dsimp [souriauCocycle, smul]
  ring

/-- 🏆 THEOREM 5: Skew-Symmetry of Affine KKS Symplectic Form -/
theorem affineKKSForm_skew (m : ℝ) (μ X Y : SE2Vector) :
    affineKKSForm m μ X Y = - affineKKSForm m μ Y X := by
  dsimp [affineKKSForm, pairing, lieBracket, souriauCocycle]
  ring

/-- 🏆 THEOREM 6: Linearity of Affine KKS Form in First Vector Argument -/
theorem affineKKSForm_add_left (m : ℝ) (μ X1 X2 Y : SE2Vector) :
    affineKKSForm m μ (add X1 X2) Y = affineKKSForm m μ X1 Y + affineKKSForm m μ X2 Y := by
  dsimp [affineKKSForm, pairing, lieBracket, souriauCocycle, add]
  ring

theorem affineKKSForm_add_right (m : ℝ) (μ X Y1 Y2 : SE2Vector) :
    affineKKSForm m μ X (add Y1 Y2) =
      affineKKSForm m μ X Y1 + affineKKSForm m μ X Y2 := by
  dsimp [affineKKSForm, pairing, lieBracket, souriauCocycle, add]
  ring

theorem affineKKSForm_smul_right (m c : ℝ) (μ X Y : SE2Vector) :
    affineKKSForm m μ X (smul c Y) = c * affineKKSForm m μ X Y := by
  dsimp [affineKKSForm, pairing, lieBracket, souriauCocycle, smul]
  ring

/-- 🏆 THEOREM 7: Casimir Invariance under Coadjoint Flow
    The standard KKS pairing ⟨μ, [X, Y]⟩ vanishes when evaluated with the Casimir gradient ∇C(μ) = (0, 2*p1, 2*p2). -/
theorem casimir_gradient_null (μ X : SE2Vector) :
    pairing μ (lieBracket ⟨0, 2 * μ.p1, 2 * μ.p2⟩ X) = 0 := by
  dsimp [pairing, lieBracket]
  ring

/- The affine KKS expression is polynomial in all of its coordinate inputs.
  We state continuity on the explicit coordinate space, so no auxiliary
  topology or coercion on the record `SE2Vector` is being smuggled in. -/
theorem continuous_affineKKSForm_coordinates :
    Continuous (fun q : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ =>
      affineKKSForm q.1
        ⟨q.2.1, q.2.2.1, q.2.2.2.1⟩
        ⟨q.2.2.2.2.1, q.2.2.2.2.2.1, q.2.2.2.2.2.2.1⟩
        ⟨q.2.2.2.2.2.2.2.1, q.2.2.2.2.2.2.2.2.1,
          q.2.2.2.2.2.2.2.2.2⟩) := by
  unfold affineKKSForm pairing lieBracket souriauCocycle
  fun_prop

theorem continuous_casimir_coordinates :
    Continuous (fun q : ℝ × ℝ × ℝ =>
      casimir ⟨q.1, q.2.1, q.2.2⟩) := by
  unfold casimir
  fun_prop

def casimirFiber (r : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {q | casimir ⟨q.1, q.2.1, q.2.2⟩ = r}

theorem isClosed_casimirFiber (r : ℝ) :
    IsClosed (casimirFiber r) := by
  unfold casimirFiber
  exact isClosed_singleton.preimage continuous_casimir_coordinates

/-! ## Topological rotation readout on the coadjoint momentum plane

The finite `SE(2)` matrix carrier uses the same `(c,s)` rotation block as the
coadjoint momentum coordinates.  Coordinates are used here deliberately: the
existing Casimir fiber is a subset of `ℝ × ℝ × ℝ`, so no ad hoc topology on the
record `SE2Vector` is introduced. -/

def momentumRotationCoordinates
    (c s : ℝ) (q : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (q.1, c * q.2.1 - s * q.2.2, s * q.2.1 + c * q.2.2)

theorem continuous_momentumRotationCoordinates :
    Continuous (fun q : ℝ × ℝ × (ℝ × ℝ × ℝ) =>
      momentumRotationCoordinates q.1 q.2.1 q.2.2) := by
  unfold momentumRotationCoordinates
  fun_prop

theorem casimir_momentumRotationCoordinates
    (c s : ℝ) (q : ℝ × ℝ × ℝ)
    (hrot : c ^ 2 + s ^ 2 = 1) :
    casimir ⟨(momentumRotationCoordinates c s q).1,
      (momentumRotationCoordinates c s q).2.1,
      (momentumRotationCoordinates c s q).2.2⟩ =
      casimir ⟨q.1, q.2.1, q.2.2⟩ := by
  dsimp [casimir, momentumRotationCoordinates]
  nlinarith [sq_nonneg (s * q.2.1 - c * q.2.2), hrot]

abbrev CasimirFiberCarrier (r : ℝ) :=
  {q : ℝ × ℝ × ℝ // q ∈ casimirFiber r}

theorem casimirFiber_eq_empty_of_neg {r : ℝ} (hr : r < 0) :
    casimirFiber r = ∅ := by
  ext q
  constructor
  · intro hq
    have hnonneg : 0 ≤ q.2.1 ^ 2 + q.2.2 ^ 2 :=
      add_nonneg (sq_nonneg _) (sq_nonneg _)
    change q.2.1 ^ 2 + q.2.2 ^ 2 = r at hq
    have : r = q.2.1 ^ 2 + q.2.2 ^ 2 := by
      exact hq.symm
    linarith
  · intro hq
    simp at hq

def casimirFiberZeroParam : ℝ → CasimirFiberCarrier 0 := fun j =>
  ⟨(j, (0, 0)), by
    simp [casimirFiber, casimir]
  ⟩

theorem continuous_casimirFiberZeroParam :
    Continuous casimirFiberZeroParam := by
  unfold casimirFiberZeroParam
  apply Continuous.subtype_mk
  fun_prop

theorem casimirFiberZeroParam_surjective :
    Function.Surjective casimirFiberZeroParam := by
  intro q
  have hq0 : q.1.2.1 = 0 := by
    have hsum : q.1.2.1 ^ 2 + q.1.2.2 ^ 2 = 0 := by
      exact q.2
    nlinarith [sq_nonneg q.1.2.2]
  have hq1 : q.1.2.2 = 0 := by
    have hsum : q.1.2.1 ^ 2 + q.1.2.2 ^ 2 = 0 := by
      exact q.2
    nlinarith [sq_nonneg q.1.2.1]
  refine ⟨q.1.1, ?_⟩
  apply Subtype.ext
  ext <;> simp [casimirFiberZeroParam, hq0, hq1]

instance pathConnectedSpace_casimirFiberZero :
    PathConnectedSpace (CasimirFiberCarrier 0) := by
  exact casimirFiberZeroParam_surjective.pathConnectedSpace
    continuous_casimirFiberZeroParam

theorem isClosedEmbedding_casimirFiber_subtypeVal (r : ℝ) :
    Topology.IsClosedEmbedding
      ((↑) : CasimirFiberCarrier r → (ℝ × ℝ × ℝ)) := by
  exact (isClosed_casimirFiber r).isClosedEmbedding_subtypeVal

theorem isClosedMap_casimirFiber_subtypeVal (r : ℝ) :
    IsClosedMap ((↑) : CasimirFiberCarrier r → (ℝ × ℝ × ℝ)) := by
  exact (isClosedEmbedding_casimirFiber_subtypeVal r).isClosedMap

theorem isProperMap_casimirFiber_subtypeVal (r : ℝ) :
    IsProperMap ((↑) : CasimirFiberCarrier r → (ℝ × ℝ × ℝ)) := by
  exact (isClosedEmbedding_casimirFiber_subtypeVal r).isProperMap

instance locallyCompactSpace_casimirFiberCarrier (r : ℝ) :
    LocallyCompactSpace (CasimirFiberCarrier r) := by
  exact (isClosedEmbedding_casimirFiber_subtypeVal r).locallyCompactSpace

def momentumRotationFiber
    (c s r : ℝ) (hrot : c ^ 2 + s ^ 2 = 1) :
    CasimirFiberCarrier r → CasimirFiberCarrier r := fun q =>
  ⟨momentumRotationCoordinates c s q.1,
    by
      change casimir ⟨(momentumRotationCoordinates c s q.1).1,
        (momentumRotationCoordinates c s q.1).2.1,
        (momentumRotationCoordinates c s q.1).2.2⟩ = r
      rw [casimir_momentumRotationCoordinates c s q.1 hrot]
      exact q.2⟩

theorem continuous_momentumRotationFiber
    (c s r : ℝ) (hrot : c ^ 2 + s ^ 2 = 1) :
    Continuous (momentumRotationFiber c s r hrot) := by
  apply Continuous.subtype_mk
  exact (continuous_momentumRotationCoordinates.comp
    (continuous_const.prodMk (continuous_const.prodMk continuous_subtype_val)))

/-! ## Affine KKS readout restricted to a Casimir leaf

The coadjoint coordinate `μ` may now be supplied as a point of the closed
fiber, while the Lie-algebra arguments remain explicit coordinate triples. -/

def affineKKSFiberCoordinates
    (m r : ℝ) (μ : CasimirFiberCarrier r)
    (X Y : ℝ × ℝ × ℝ) : ℝ :=
  affineKKSForm m
    ⟨μ.1.1, μ.1.2.1, μ.1.2.2⟩
    ⟨X.1, X.2.1, X.2.2⟩
    ⟨Y.1, Y.2.1, Y.2.2⟩

theorem continuous_affineKKSFiberCoordinates (m r : ℝ) :
    Continuous (fun q : CasimirFiberCarrier r ×
        (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
      affineKKSFiberCoordinates m r q.1 q.2.1 q.2.2) := by
  unfold affineKKSFiberCoordinates affineKKSForm pairing lieBracket souriauCocycle
  fun_prop

theorem continuous_affineKKSFiberCoordinates_after_rotation
    (m r c s : ℝ) (hrot : c ^ 2 + s ^ 2 = 1) :
    Continuous (fun q : CasimirFiberCarrier r ×
        (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
      affineKKSFiberCoordinates m r
        (momentumRotationFiber c s r hrot q.1) q.2.1 q.2.2) := by
  simpa only [Function.comp_apply] using
    (continuous_affineKKSFiberCoordinates m r).comp
      ((continuous_momentumRotationFiber c s r hrot |>.comp continuous_fst).prodMk
        ((continuous_fst.comp continuous_snd).prodMk
          (continuous_snd.comp continuous_snd)))

theorem affineKKSFiberCoordinates_equivariant
    (m r c s : ℝ) (hrot : c ^ 2 + s ^ 2 = 1)
    (μ : CasimirFiberCarrier r) (X Y : ℝ × ℝ × ℝ) :
    affineKKSFiberCoordinates m r
      (momentumRotationFiber c s r hrot μ)
      (momentumRotationCoordinates c s X)
      (momentumRotationCoordinates c s Y) =
      affineKKSFiberCoordinates m r μ X Y := by
  dsimp [affineKKSFiberCoordinates, affineKKSForm, pairing, lieBracket,
    souriauCocycle, momentumRotationCoordinates, momentumRotationFiber]
  ring_nf
  linear_combination
    (μ.1.2.1 * X.1 * Y.2.2 +
      (-(μ.1.2.1 * Y.1 * X.2.2) - μ.1.2.2 * X.1 * Y.2.1) +
      (μ.1.2.2 * Y.1 * X.2.1 - Y.2.1 * X.2.2 * m) +
      Y.2.2 * X.2.1 * m) * hrot

theorem momentumRotationCoordinates_comp
    (c₁ s₁ c₂ s₂ : ℝ) (q : ℝ × ℝ × ℝ) :
    momentumRotationCoordinates c₁ s₁
        (momentumRotationCoordinates c₂ s₂ q) =
      momentumRotationCoordinates
        (c₁ * c₂ - s₁ * s₂) (s₁ * c₂ + c₁ * s₂) q := by
  ext <;> dsimp [momentumRotationCoordinates] <;> ring

abbrev MatrixSE2Carrier :=
  InfoGeometry.Canonical.SE2SouriauCocycle.SE2RotationCarrier

def se2CarrierMomentumAction
    {r : ℝ} (g : MatrixSE2Carrier) (q : CasimirFiberCarrier r) :
    CasimirFiberCarrier r :=
  ⟨momentumRotationCoordinates g.1.1 g.1.2.1 q.1,
    by
      change casimir ⟨(momentumRotationCoordinates g.1.1 g.1.2.1 q.1).1,
        (momentumRotationCoordinates g.1.1 g.1.2.1 q.1).2.1,
        (momentumRotationCoordinates g.1.1 g.1.2.1 q.1).2.2⟩ = r
      rw [casimir_momentumRotationCoordinates g.1.1 g.1.2.1 q.1]
      · exact q.2
      · exact g.2⟩

theorem se2CarrierMomentumAction_one
    {r : ℝ} (q : CasimirFiberCarrier r) :
    se2CarrierMomentumAction (1 : MatrixSE2Carrier) q = q := by
  apply Subtype.ext
  change momentumRotationCoordinates 1 0 q.1 = q.1
  ext <;> dsimp [momentumRotationCoordinates] <;> ring

theorem se2CarrierMomentumAction_mul
    {r : ℝ} (g h : MatrixSE2Carrier) (q : CasimirFiberCarrier r) :
    se2CarrierMomentumAction (g * h) q =
      se2CarrierMomentumAction g (se2CarrierMomentumAction h q) := by
  apply Subtype.ext
  change momentumRotationCoordinates
      (g * h).1.1 (g * h).1.2.1 q.1 =
    momentumRotationCoordinates g.1.1 g.1.2.1
      (momentumRotationCoordinates h.1.1 h.1.2.1 q.1)
  rw [momentumRotationCoordinates_comp]
  rfl

instance {r : ℝ} : MulAction MatrixSE2Carrier (CasimirFiberCarrier r) where
  smul := se2CarrierMomentumAction
  one_smul := se2CarrierMomentumAction_one
  mul_smul := se2CarrierMomentumAction_mul

theorem continuous_se2CarrierMomentumAction
    {r : ℝ} :
    Continuous (fun p : MatrixSE2Carrier × CasimirFiberCarrier r =>
      p.1 • p.2) := by
  apply Continuous.subtype_mk
  have hmap : Continuous (fun x : MatrixSE2Carrier × CasimirFiberCarrier r =>
      (x.1.1.1, x.1.1.2.1, x.2.1)) := by
    fun_prop
  simpa only [Function.comp_apply] using
    continuous_momentumRotationCoordinates.comp hmap

def se2CarrierOrbitMap
    {r : ℝ} (q : CasimirFiberCarrier r) :
    MatrixSE2Carrier → CasimirFiberCarrier r := fun g => g • q

theorem continuous_se2CarrierOrbitMap
    {r : ℝ} (q : CasimirFiberCarrier r) :
    Continuous (se2CarrierOrbitMap q) := by
  unfold se2CarrierOrbitMap
  simpa only [Function.comp_apply] using
    continuous_se2CarrierMomentumAction.comp
      (continuous_id.prodMk continuous_const)

def se2CarrierOrbit
    {r : ℝ} (q : CasimirFiberCarrier r) :
    Set (CasimirFiberCarrier r) := Set.range (se2CarrierOrbitMap q)

theorem se2CarrierOrbitMap_mul
    {r : ℝ} (q : CasimirFiberCarrier r) (g h : MatrixSE2Carrier) :
    se2CarrierOrbitMap q (g * h) =
      se2CarrierOrbitMap (se2CarrierOrbitMap q h) g := by
  simp [se2CarrierOrbitMap, mul_smul]

theorem se2CarrierOrbitMap_mem_casimirFiber
    {r : ℝ} (q : CasimirFiberCarrier r) (g : MatrixSE2Carrier) :
    (se2CarrierOrbitMap q g).1 ∈ casimirFiber r := by
  exact (se2CarrierOrbitMap q g).2

theorem se2CarrierOrbit_nonempty
    {r : ℝ} (q : CasimirFiberCarrier r) :
    (se2CarrierOrbit q).Nonempty := by
  exact ⟨q, ⟨1, se2CarrierMomentumAction_one q⟩⟩

end SE2Vector

end SE2Souriau
