import InfoGeometry.Canonical.CliffordCARTopologicalColimit
import InfoGeometry.Canonical.CliffordCARAlgebraicTopologicalComparison

/-!
# Topological CAR generator representatives

This owner carries the finite Jordan--Wigner creation and annihilation
operators into the `TopCat` colimit.  It also proves that left multiplication
by those operators is natural for the Clifford tower embedding.  Thus the
generator relation is represented by genuine noncommutative topological
colimit points, rather than by a diagonal scalar shadow.
-/

noncomputable section

namespace InfoGeometry.Canonical.CliffordCARGeneratorTopological

open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit
open InfoGeometry.Canonical.CliffordCARTopologicalColimit
open InfoGeometry.Canonical.CliffordCARAlgebraicTopologicalComparison

abbrev TStage (n : ℕ) : Type := CliffordCARTopologicalColimit.Stage n

abbrev AlgebraicLimit : Type := InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit

/-- Creation representative in the topological colimit. -/
def creationColimitPoint (n : ℕ) (k : Fin n) : topologicalColimit :=
  topologicalInjection n (jwCreation n k)

/-- Annihilation representative in the topological colimit. -/
def annihilationColimitPoint (n : ℕ) (k : Fin n) : topologicalColimit :=
  topologicalInjection n (jwAnnihilation n k)

@[simp] theorem creationColimitPoint_castSucc (n : ℕ) (k : Fin n) :
    creationColimitPoint (n + 1) k.castSucc = creationColimitPoint n k := by
  exact creationRepresentative_transition n k

@[simp] theorem annihilationColimitPoint_castSucc (n : ℕ) (k : Fin n) :
    annihilationColimitPoint (n + 1) k.castSucc = annihilationColimitPoint n k := by
  exact annihilationRepresentative_transition n k

/-- The algebraic direct-limit representatives have the same topological
readout under the comparison map. -/
@[simp] theorem algebraic_creation_readout (n : ℕ) (k : Fin n) :
    algebraicToTopological (ofStage n (jwCreation n k)) =
      creationColimitPoint n k := by
  rfl

@[simp] theorem algebraic_annihilation_readout (n : ℕ) (k : Fin n) :
    algebraicToTopological (ofStage n (jwAnnihilation n k)) =
      annihilationColimitPoint n k := by
  rfl

/-- Left multiplication by a finite-stage creation operator, as a continuous
linear operator on the finite matrix stage. -/
def creationLeftAction (n : ℕ) (k : Fin n) :
    TStage n →L[ℝ] TStage n :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ (jwCreation n k))

/-- Left multiplication by a finite-stage annihilation operator. -/
def annihilationLeftAction (n : ℕ) (k : Fin n) :
    TStage n →L[ℝ] TStage n :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ (jwAnnihilation n k))

@[simp] theorem creationLeftAction_apply (n : ℕ) (k : Fin n) (A : TStage n) :
    creationLeftAction n k A = jwCreation n k * A := by
  exact LinearMap.mulLeft_apply ℝ _ _

@[simp] theorem annihilationLeftAction_apply (n : ℕ) (k : Fin n) (A : TStage n) :
    annihilationLeftAction n k A = jwAnnihilation n k * A := by
  exact LinearMap.mulLeft_apply ℝ _ _

theorem creationLeftAction_transition (n : ℕ) (k : Fin n) (A : TStage n) :
    bondCLM n (n + 1) (Nat.le_succ n) (creationLeftAction n k A) =
      creationLeftAction (n + 1) k.castSucc
        (bondCLM n (n + 1) (Nat.le_succ n) A) := by
  rw [bondCLM_apply, bondCLM_apply]
  change bondAlgHom n (n + 1) (Nat.le_succ n) (jwCreation n k * A) =
    jwCreation (n + 1) k.castSucc *
      bondAlgHom n (n + 1) (Nat.le_succ n) A
  rw [bondAlgHom_succ n n le_rfl]
  simp [bondAlgHom_refl, stageEmbed_apply,
    matStageEmbed_mul, matStageEmbed_jwCreation]

theorem annihilationLeftAction_transition (n : ℕ) (k : Fin n) (A : TStage n) :
    bondCLM n (n + 1) (Nat.le_succ n) (annihilationLeftAction n k A) =
      annihilationLeftAction (n + 1) k.castSucc
        (bondCLM n (n + 1) (Nat.le_succ n) A) := by
  rw [bondCLM_apply, bondCLM_apply]
  change bondAlgHom n (n + 1) (Nat.le_succ n) (jwAnnihilation n k * A) =
    jwAnnihilation (n + 1) k.castSucc *
      bondAlgHom n (n + 1) (Nat.le_succ n) A
  rw [bondAlgHom_succ n n le_rfl]
  simp [bondAlgHom_refl, stageEmbed_apply,
    matStageEmbed_mul, matStageEmbed_jwAnnihilation]

/-- Creation element represented at a finite stage of the algebraic colimit. -/
def algebraicCreationElement (n : ℕ) (k : Fin n) : AlgebraicLimit :=
  ofStage n (jwCreation n k)

/-- Annihilation element represented at a finite stage of the algebraic colimit. -/
def algebraicAnnihilationElement (n : ℕ) (k : Fin n) : AlgebraicLimit :=
  ofStage n (jwAnnihilation n k)

@[simp] theorem algebraicCreationElement_castSucc (n : ℕ) (k : Fin n) :
    algebraicCreationElement (n + 1) k.castSucc =
      algebraicCreationElement n k := by
  unfold algebraicCreationElement
  rw [← matStageEmbed_jwCreation]
  exact ofStage_apply_bond n (jwCreation n k)

@[simp] theorem algebraicAnnihilationElement_castSucc (n : ℕ) (k : Fin n) :
    algebraicAnnihilationElement (n + 1) k.castSucc =
      algebraicAnnihilationElement n k := by
  unfold algebraicAnnihilationElement
  rw [← matStageEmbed_jwAnnihilation]
  exact ofStage_apply_bond n (jwAnnihilation n k)

/-- Left multiplication by the creation element on the algebraic colimit. -/
def algebraicCreationAction (n : ℕ) (k : Fin n) :
    AlgebraicLimit →ₗ[ℝ] AlgebraicLimit :=
  LinearMap.mulLeft ℝ (algebraicCreationElement n k)

/-- Left multiplication by the annihilation element on the algebraic colimit. -/
def algebraicAnnihilationAction (n : ℕ) (k : Fin n) :
    AlgebraicLimit →ₗ[ℝ] AlgebraicLimit :=
  LinearMap.mulLeft ℝ (algebraicAnnihilationElement n k)

@[simp] theorem algebraicCreationAction_castSucc (n : ℕ) (k : Fin n) :
    algebraicCreationAction (n + 1) k.castSucc =
      algebraicCreationAction n k := by
  unfold algebraicCreationAction
  rw [algebraicCreationElement_castSucc]

@[simp] theorem algebraicAnnihilationAction_castSucc (n : ℕ) (k : Fin n) :
    algebraicAnnihilationAction (n + 1) k.castSucc =
      algebraicAnnihilationAction n k := by
  unfold algebraicAnnihilationAction
  rw [algebraicAnnihilationElement_castSucc]

@[simp] theorem algebraicCreationAction_castSucc_apply (n : ℕ) (k : Fin n)
    (x : AlgebraicLimit) :
    algebraicCreationAction (n + 1) k.castSucc x =
      algebraicCreationAction n k x := by
  rw [algebraicCreationAction_castSucc]

@[simp] theorem algebraicAnnihilationAction_castSucc_apply (n : ℕ) (k : Fin n)
    (x : AlgebraicLimit) :
    algebraicAnnihilationAction (n + 1) k.castSucc x =
      algebraicAnnihilationAction n k x := by
  rw [algebraicAnnihilationAction_castSucc]

/-- Canonical global creation action for mode `m`, represented first at stage
`m + 1`.  The cast-successor theorem makes later representatives equal. -/
def algebraicCreationActionAtMode (m : ℕ) :
    AlgebraicLimit →ₗ[ℝ] AlgebraicLimit :=
  algebraicCreationAction (m + 1) ⟨m, Nat.lt_succ_self m⟩

/-- Canonical global annihilation action for mode `m`. -/
def algebraicAnnihilationActionAtMode (m : ℕ) :
    AlgebraicLimit →ₗ[ℝ] AlgebraicLimit :=
  algebraicAnnihilationAction (m + 1) ⟨m, Nat.lt_succ_self m⟩

/-- The occurrence of mode `m` at a later stage `n`. -/
def modeIndex (m n : ℕ) (h : m + 1 ≤ n) : Fin n :=
  ⟨m, Nat.lt_of_lt_of_le (Nat.lt_succ_self m) h⟩

@[simp] theorem modeIndex_succ (m n : ℕ) (h : m + 1 ≤ n) :
    modeIndex m (n + 1) (Nat.le_trans h (Nat.le_succ n)) =
      (modeIndex m n h).castSucc := by
  apply Fin.ext
  rfl

/-- Fixed-mode creation action viewed as a family over the upper tail. -/
def algebraicCreationActionAtStage
    (m n : ℕ) (h : m + 1 ≤ n) :
    AlgebraicLimit →ₗ[ℝ] AlgebraicLimit :=
  algebraicCreationAction n (modeIndex m n h)

/-- Fixed-mode annihilation action viewed as a family over the upper tail. -/
def algebraicAnnihilationActionAtStage
    (m n : ℕ) (h : m + 1 ≤ n) :
    AlgebraicLimit →ₗ[ℝ] AlgebraicLimit :=
  algebraicAnnihilationAction n (modeIndex m n h)

theorem algebraicCreationActionAtStage_succ
    (m n : ℕ) (h : m + 1 ≤ n) :
    algebraicCreationActionAtStage m (n + 1)
        (Nat.le_trans h (Nat.le_succ n)) =
      algebraicCreationActionAtStage m n h := by
  unfold algebraicCreationActionAtStage
  rw [modeIndex_succ, algebraicCreationAction_castSucc]

theorem algebraicAnnihilationActionAtStage_succ
    (m n : ℕ) (h : m + 1 ≤ n) :
    algebraicAnnihilationActionAtStage m (n + 1)
        (Nat.le_trans h (Nat.le_succ n)) =
      algebraicAnnihilationActionAtStage m n h := by
  unfold algebraicAnnihilationActionAtStage
  rw [modeIndex_succ, algebraicAnnihilationAction_castSucc]

@[simp] theorem algebraicCreationAction_ofStage (n : ℕ) (k : Fin n)
    (A : AStage n) :
    algebraicCreationAction n k (ofStage n A) =
      ofStage n (jwCreation n k * A) := by
  change ofStage n (jwCreation n k) * ofStage n A = _
  rw [← (ofStage n).map_mul]

@[simp] theorem algebraicAnnihilationAction_ofStage (n : ℕ) (k : Fin n)
    (A : AStage n) :
    algebraicAnnihilationAction n k (ofStage n A) =
      ofStage n (jwAnnihilation n k * A) := by
  change ofStage n (jwAnnihilation n k) * ofStage n A = _
  rw [← (ofStage n).map_mul]

@[simp] theorem algebraicCreationAction_topological_readout (n : ℕ) (k : Fin n)
    (A : AStage n) :
    algebraicToTopological
        (algebraicCreationAction n k (ofStage n A)) =
      topologicalInjection n (jwCreation n k * A) := by
  rw [algebraicCreationAction_ofStage]
  rfl

@[simp] theorem algebraicAnnihilationAction_topological_readout
    (n : ℕ) (k : Fin n) (A : AStage n) :
    algebraicToTopological
        (algebraicAnnihilationAction n k (ofStage n A)) =
      topologicalInjection n (jwAnnihilation n k * A) := by
  rw [algebraicAnnihilationAction_ofStage]
  rfl

/-- Explicit owner-local cone interface for a fixed-mode action over the upper
tail.  The target is the algebraic direct-limit endomorphism space; the
topological readout remains supplied by the preceding comparison lemmas. -/
structure UpperTailLinearActionCone (m : ℕ) where
  action : ∀ (n : ℕ), m + 1 ≤ n → AlgebraicLimit →ₗ[ℝ] AlgebraicLimit
  compat : ∀ (n : ℕ) (h : m + 1 ≤ n),
    action (n + 1) (Nat.le_trans h (Nat.le_succ n)) = action n h

/-- Creation cone for the fixed mode `m`. -/
def creationUpperTailActionCone (m : ℕ) : UpperTailLinearActionCone m where
  action := algebraicCreationActionAtStage m
  compat := algebraicCreationActionAtStage_succ m

/-- Annihilation cone for the fixed mode `m`. -/
def annihilationUpperTailActionCone (m : ℕ) : UpperTailLinearActionCone m where
  action := algebraicAnnihilationActionAtStage m
  compat := algebraicAnnihilationActionAtStage_succ m

@[simp] theorem creationUpperTailActionCone_action (m n : ℕ)
    (h : m + 1 ≤ n) :
    (creationUpperTailActionCone m).action n h =
      algebraicCreationActionAtStage m n h :=
  rfl

@[simp] theorem annihilationUpperTailActionCone_action (m n : ℕ)
    (h : m + 1 ≤ n) :
    (annihilationUpperTailActionCone m).action n h =
      algebraicAnnihilationActionAtStage m n h :=
  rfl

end InfoGeometry.Canonical.CliffordCARGeneratorTopological
