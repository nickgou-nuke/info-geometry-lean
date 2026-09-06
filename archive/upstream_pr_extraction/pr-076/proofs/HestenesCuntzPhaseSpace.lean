import proofs.HestenesCuntzSpacetimeAlgebra

/-!
# Finite coordinate--momentum commutators and direct-colimit Weyl phase space

Exact canonical CCR `[X,P]=iℏI` cannot hold in finite matrix algebras because
finite traces kill commutators.  The exact finite substitute used here is the
Weyl/clock-shift relation.  The `2×2` chiral/Hestenes cell uses

`P X = - X P`

with `X = σ₃` and `P = σ₁`.  A direct-system/colimit spine is then represented
by compatible finite-stage families with identity connecting maps.  The exact
Weyl relation is preserved at every finite stage and hence pointwise on the
compatible-family colimit candidate.
-/

noncomputable section

namespace HestenesCuntzPhaseSpace

open Matrix
open ChiralPoincareSouriauBridge
open HestenesCuntzSpacetimeAlgebra

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- Associative commutator. -/
def commM (A B : M2C) : M2C := A * B - B * A

/-- Finite coordinate operator: the chiral/Hestenes spatial parity `σ₃`. -/
def finiteCoordinate : M2C := σ3

/-- Finite momentum operator: the chiral/Hestenes bit-flip/shift `σ₁`. -/
def finiteMomentum : M2C := σ1

/-- Trace of a finite `2×2` coordinate--momentum commutator vanishes. -/
theorem trace_commM_zero (X P : M2C) : Matrix.trace (commM X P) = 0 := by
  simp [commM, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- Exact canonical CCR is obstructed in finite `2×2` matrices. -/
theorem no_finite_m2_canonical_ccr :
    ¬ ∃ X P : M2C, commM X P = Complex.I • (1 : M2C) := by
  rintro ⟨X, P, h⟩
  have ht := congrArg Matrix.trace h
  rw [trace_commM_zero] at ht
  simp at ht

/-- The finite phase cell obeys the exact Weyl/clock-shift relation `P X = - X P`. -/
theorem finite_weyl_relation :
    finiteMomentum * finiteCoordinate = (-1 : ℂ) • (finiteCoordinate * finiteMomentum) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [finiteCoordinate, finiteMomentum, σ1, σ3, Matrix.mul_apply,
      Matrix.smul_apply, Fin.sum_univ_two]

/-- The corresponding finite commutator has the stage-compatible Weyl form. -/
theorem finite_coordinate_momentum_commutator :
    commM finiteCoordinate finiteMomentum = (2 : ℂ) • (finiteCoordinate * finiteMomentum) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [commM, finiteCoordinate, finiteMomentum, σ1, σ3, Matrix.smul_apply] <;> ring

/-- The opposite commutator convention. -/
theorem finite_momentum_coordinate_commutator :
    commM finiteMomentum finiteCoordinate = (-2 : ℂ) • (finiteCoordinate * finiteMomentum) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [commM, finiteCoordinate, finiteMomentum, σ1, σ3, Matrix.smul_apply] <;> ring

/-- The Weyl phase `q=-1` is a finite root of unity. -/
theorem finite_weyl_phase_sq : ((-1 : ℂ) ^ 2) = 1 := by
  norm_num

/-! ## Direct-system and compatible-family colimit spine -/

/-- Finite phase-space stage.  The maps below form a constant direct system of
finite Weyl cells, giving the finite-to-colimit structural core. -/
abbrev PhaseStage (_n : ℕ) : Type := M2C

/-- Successor connecting map for the constant finite Weyl direct system. -/
def phaseEmbedSucc (_n : ℕ) : PhaseStage _n → PhaseStage (_n + 1) := id

/-- Stagewise coordinate operator. -/
def stageCoordinate (_n : ℕ) : PhaseStage _n := finiteCoordinate

/-- Stagewise momentum operator. -/
def stageMomentum (_n : ℕ) : PhaseStage _n := finiteMomentum

/-- Coordinates are compatible with the direct-system connecting maps. -/
theorem stageCoordinate_compatible (n : ℕ) :
    phaseEmbedSucc n (stageCoordinate n) = stageCoordinate (n + 1) := rfl

/-- Momenta are compatible with the direct-system connecting maps. -/
theorem stageMomentum_compatible (n : ℕ) :
    phaseEmbedSucc n (stageMomentum n) = stageMomentum (n + 1) := rfl

/-- The finite Weyl relation holds at every stage. -/
theorem stage_weyl_relation (n : ℕ) :
    stageMomentum n * stageCoordinate n =
      (-1 : ℂ) • (stageCoordinate n * stageMomentum n) := by
  exact finite_weyl_relation

/-- Compatible families are a concrete direct-colimit candidate. -/
structure PhaseColimitFamily where
  val : ∀ n : ℕ, PhaseStage n
  compatible : ∀ n : ℕ, phaseEmbedSucc n (val n) = val (n + 1)

/-- Coordinate family in the direct-colimit candidate. -/
def coordinateFamily : PhaseColimitFamily where
  val := stageCoordinate
  compatible := stageCoordinate_compatible

/-- Momentum family in the direct-colimit candidate. -/
def momentumFamily : PhaseColimitFamily where
  val := stageMomentum
  compatible := stageMomentum_compatible

/-- The direct-colimit coordinate and momentum families satisfy the Weyl relation
pointwise at every finite stage. -/
theorem colimit_family_weyl_relation (n : ℕ) :
    (momentumFamily.val n) * (coordinateFamily.val n) =
      (-1 : ℂ) • ((coordinateFamily.val n) * (momentumFamily.val n)) := by
  exact stage_weyl_relation n

/-- Pointwise finite commutator on the compatible-family colimit candidate. -/
theorem colimit_family_commutator (n : ℕ) :
    commM (coordinateFamily.val n) (momentumFamily.val n) =
      (2 : ℂ) • ((coordinateFamily.val n) * (momentumFamily.val n)) := by
  exact finite_coordinate_momentum_commutator

/-! ## General finite Weyl structure constants -/

/-- A general finite Weyl coordinate--momentum pair in any complex algebra.

`q` is the finite structure constant / Weyl phase.  The field `q_pow_dim`
records the finite root-of-unity condition, while `weyl_relation` records the
clock-shift relation `P X = q X P`. -/
structure FiniteWeylPair (N : ℕ) (A : Type*) [Ring A] [Algebra ℂ A] where
  coordinate : A
  momentum : A
  q : ℂ
  q_pow_dim : q ^ N = 1
  weyl_relation : momentum * coordinate = q • (coordinate * momentum)

/-- The Weyl structure constant `q` implies the coordinate--momentum commutator
factor `1-q`. -/
theorem FiniteWeylPair.coordinate_momentum_commutator
    {N : ℕ} {A : Type*} [Ring A] [Algebra ℂ A] (W : FiniteWeylPair N A) :
    W.coordinate * W.momentum - W.momentum * W.coordinate =
      (1 - W.q : ℂ) • (W.coordinate * W.momentum) := by
  rw [W.weyl_relation]
  simp [sub_smul]

/-- The opposite commutator has factor `q-1`. -/
theorem FiniteWeylPair.momentum_coordinate_commutator
    {N : ℕ} {A : Type*} [Ring A] [Algebra ℂ A] (W : FiniteWeylPair N A) :
    W.momentum * W.coordinate - W.coordinate * W.momentum =
      (W.q - 1 : ℂ) • (W.coordinate * W.momentum) := by
  rw [W.weyl_relation]
  simp [sub_smul]

/-- The `2×2` Hestenes/Cuntz phase cell is the `N=2`, `q=-1` Weyl pair. -/
def twoCellWeylPair : FiniteWeylPair 2 M2C where
  coordinate := finiteCoordinate
  momentum := finiteMomentum
  q := -1
  q_pow_dim := finite_weyl_phase_sq
  weyl_relation := finite_weyl_relation

/-- The hard-coded finite commutator is the `1-q` theorem for `q=-1`. -/
theorem twoCell_commutator_from_general_weyl :
    twoCellWeylPair.coordinate * twoCellWeylPair.momentum -
      twoCellWeylPair.momentum * twoCellWeylPair.coordinate =
        (1 - twoCellWeylPair.q : ℂ) •
          (twoCellWeylPair.coordinate * twoCellWeylPair.momentum) := by
  exact twoCellWeylPair.coordinate_momentum_commutator

/-- A compatible direct-family of finite Weyl pairs over a fixed target algebra.
This is the algebraic colimit datum: stages may vary in dimension and phase,
while the displayed coordinate/momentum/phase are preserved by the chosen
successor embedding. -/
structure WeylDirectFamily (A : Type*) [Ring A] [Algebra ℂ A] where
  dim : ℕ → ℕ
  pair : ∀ n : ℕ, FiniteWeylPair (dim n) A
  embed : A → A
  coordinate_compatible : ∀ n, embed ((pair n).coordinate) = (pair (n + 1)).coordinate
  momentum_compatible : ∀ n, embed ((pair n).momentum) = (pair (n + 1)).momentum
  phase_compatible : ∀ n, (pair (n + 1)).q = (pair n).q

/-- The constant `2×2`, `q=-1` Weyl family is a concrete direct-family model. -/
def constantTwoCellWeylFamily : WeylDirectFamily M2C where
  dim := fun _ => 2
  pair := fun _ => twoCellWeylPair
  embed := id
  coordinate_compatible := by intro n; rfl
  momentum_compatible := by intro n; rfl
  phase_compatible := by intro n; rfl

/-- Every stage of a Weyl direct-family has the general `1-q` commutator. -/
theorem WeylDirectFamily.stage_coordinate_momentum_commutator
    {A : Type*} [Ring A] [Algebra ℂ A] (F : WeylDirectFamily A) (n : ℕ) :
    (F.pair n).coordinate * (F.pair n).momentum -
      (F.pair n).momentum * (F.pair n).coordinate =
        (1 - (F.pair n).q : ℂ) •
          ((F.pair n).coordinate * (F.pair n).momentum) := by
  exact (F.pair n).coordinate_momentum_commutator

/-- In the constant `2×2` family, every stage has `q=-1`. -/
theorem constantTwoCellWeylFamily_phase (n : ℕ) :
    (constantTwoCellWeylFamily.pair n).q = (-1 : ℂ) := rfl

/-- Consolidated finite/direct-colimit phase-space package. -/
theorem hestenes_cuntz_phase_space_synthesis :
    (¬ ∃ X P : M2C, commM X P = Complex.I • (1 : M2C)) ∧
    finiteMomentum * finiteCoordinate = (-1 : ℂ) • (finiteCoordinate * finiteMomentum) ∧
    commM finiteCoordinate finiteMomentum = (2 : ℂ) • (finiteCoordinate * finiteMomentum) ∧
    ((-1 : ℂ) ^ 2 = 1) ∧
    (∀ n : ℕ, phaseEmbedSucc n (stageCoordinate n) = stageCoordinate (n + 1)) ∧
    (∀ n : ℕ, phaseEmbedSucc n (stageMomentum n) = stageMomentum (n + 1)) ∧
    (∀ n : ℕ, momentumFamily.val n * coordinateFamily.val n =
      (-1 : ℂ) • (coordinateFamily.val n * momentumFamily.val n)) ∧
    (∀ n : ℕ, commM (coordinateFamily.val n) (momentumFamily.val n) =
      (2 : ℂ) • (coordinateFamily.val n * momentumFamily.val n)) ∧
    (∀ n : ℕ,
      (constantTwoCellWeylFamily.pair n).coordinate *
          (constantTwoCellWeylFamily.pair n).momentum -
        (constantTwoCellWeylFamily.pair n).momentum *
          (constantTwoCellWeylFamily.pair n).coordinate =
        (1 - (constantTwoCellWeylFamily.pair n).q : ℂ) •
          ((constantTwoCellWeylFamily.pair n).coordinate *
            (constantTwoCellWeylFamily.pair n).momentum)) := by
  constructor
  · exact no_finite_m2_canonical_ccr
  constructor
  · exact finite_weyl_relation
  constructor
  · exact finite_coordinate_momentum_commutator
  constructor
  · exact finite_weyl_phase_sq
  constructor
  · intro n
    exact stageCoordinate_compatible n
  constructor
  · intro n
    exact stageMomentum_compatible n
  constructor
  · intro n
    exact colimit_family_weyl_relation n
  constructor
  · intro n
    exact colimit_family_commutator n
  · intro n
    exact constantTwoCellWeylFamily.stage_coordinate_momentum_commutator n

end HestenesCuntzPhaseSpace

end noncomputable section
