import proofs.ModularKreinReflectionColimit
import InfoGeometry.External.Auto.tomita_kms_v4
import proofs.ModularGlideCPT

/-!
# Concrete CPT/Krein towers

This file wires the finite 2×2 Tomita/Krein carriers into the abstract
`ModularKreinReflectionColimit.KreinTower` interface.

The bridge is intentionally finite:

* the stage carrier is the concrete 2×2 matrix algebra;
* the embedding is the identity tower map;
* the modular reflection is left multiplication by the already-proven `J` matrix;
* the tower compatibility is the iterated commutation theorem.

No analytic Tomita theory is claimed.
-/

noncomputable section

namespace CPTKreinTowerBridge

open Matrix
open ModularKreinReflectionColimit

abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ
abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ

/-- The real modular reflection from the Tomita model. -/
def realMirror : M2R →ₗ[ℝ] M2R :=
  LinearMap.mulLeft ℝ J_mod

theorem realMirror_sq (X : M2R) :
    realMirror (realMirror X) = X := by
  calc
    realMirror (realMirror X) = J_mod * (J_mod * X) := by rfl
    _ = (J_mod * J_mod) * X := by rw [Matrix.mul_assoc]
    _ = (1 : M2R) * X := by rw [J_mod_sq_I]
    _ = X := by simp

def realTomitaTower : KreinTower ℝ where
  stage := fun _ => M2R
  stageAdd := by intro n; infer_instance
  stageModule := by intro n; infer_instance
  emb := fun _ => LinearMap.id
  J := fun _ => realMirror
  J_involutive := by
    intro n X
    simpa using realMirror_sq X
  J_comm := by
    intro n X
    rfl

/-- The concrete real Tomita/Krein tower satisfies the abstract colimit lemmas. -/
theorem realTomitaTower_synthesis (n k : ℕ) (X : M2R) :
    realTomitaTower.J (n + k)
      (KreinTower.embIter (T := realTomitaTower) n k X) =
      KreinTower.embIter (T := realTomitaTower) n k
        (realTomitaTower.J n X) := by
  calc
    realTomitaTower.J (n + k)
        (KreinTower.embIter (T := realTomitaTower) n k X)
        = KreinTower.embIter (T := realTomitaTower) n k
            (realTomitaTower.J n X) := by
              exact KreinTower.J_commutes_with_embIter
                (T := realTomitaTower) n k X

/-- The complex modular glide reflection from the CPT model. -/
def complexMirror : M2C →ₗ[ℂ] M2C :=
  LinearMap.mulLeft ℂ ModularGlideCPT.J

theorem complexMirror_sq (X : M2C) :
    complexMirror (complexMirror X) = X := by
  calc
    complexMirror (complexMirror X) = ModularGlideCPT.J * (ModularGlideCPT.J * X) := by rfl
    _ = (ModularGlideCPT.J * ModularGlideCPT.J) * X := by rw [Matrix.mul_assoc]
    _ = (1 : M2C) * X := by rw [ModularGlideCPT.J_sq]
    _ = X := by simp

def complexCPTTower : KreinTower ℂ where
  stage := fun _ => M2C
  stageAdd := by intro n; infer_instance
  stageModule := by intro n; infer_instance
  emb := fun _ => LinearMap.id
  J := fun _ => complexMirror
  J_involutive := by
    intro n X
    simpa using complexMirror_sq X
  J_comm := by
    intro n X
    rfl

/-- The concrete complex CPT tower satisfies the abstract colimit lemmas. -/
theorem complexCPTTower_synthesis (n k : ℕ) (X : M2C) :
    complexCPTTower.J (n + k)
      (KreinTower.embIter (T := complexCPTTower) n k X) =
      KreinTower.embIter (T := complexCPTTower) n k
        (complexCPTTower.J n X) := by
  calc
    complexCPTTower.J (n + k)
        (KreinTower.embIter (T := complexCPTTower) n k X)
        = KreinTower.embIter (T := complexCPTTower) n k
            (complexCPTTower.J n X) := by
              exact KreinTower.J_commutes_with_embIter
                (T := complexCPTTower) n k X

/-- A doubled carrier for non-trivial growth: the old stage plus a zero tail. -/
abbrev PairCarrier := M2R × M2R

/-- Append-zero embedding into the doubled carrier. -/
def pairEmb : M2R →ₗ[ℝ] PairCarrier :=
  LinearMap.inl ℝ M2R M2R

/-- The modular reflection on the doubled carrier acts componentwise. -/
def pairMirror : PairCarrier → PairCarrier :=
  fun p => (realMirror p.1, realMirror p.2)

/-- Componentwise commutator on the doubled carrier. -/
def pairBracket (x y : PairCarrier) : PairCarrier :=
  (x.1 * y.1 - y.1 * x.1, x.2 * y.2 - y.2 * x.2)

theorem pairMirror_sq (x : PairCarrier) :
    pairMirror (pairMirror x) = x := by
  cases x with
  | mk x₁ x₂ =>
      simp [pairMirror, realMirror_sq]

/-- The append-zero embedding commutes with the modular reflection. -/
theorem pairEmb_mirror_comm (x : M2R) :
    pairMirror (pairEmb x) = pairEmb (realMirror x) := by
  simp [pairEmb, pairMirror]

/-- The append-zero embedding is compatible with the doubled bracket. -/
theorem pairEmb_bracket_compat (x y : M2R) :
    pairBracket (pairEmb x) (pairEmb y) = pairEmb (x * y - y * x) := by
  simp [pairEmb, pairBracket]

/-- A minimal non-trivial growth package: the outer stage is a doubled carrier,
the inner stage sits inside it by append-zero, and the reflection/bracket data
commute with that inclusion. -/
structure BlockGrowthPackage where
  stage0 : Type
  stage1 : Type
  emb : stage0 → stage1
  J0 : stage0 → stage0
  J1 : stage1 → stage1
  bracket0 : stage0 → stage0 → stage0
  bracket1 : stage1 → stage1 → stage1
  emb_J : ∀ x, emb (J0 x) = J1 (emb x)
  emb_bracket : ∀ x y, emb (bracket0 x y) = bracket1 (emb x) (emb y)

/-- Concrete block-growth package for the CPT/Krein carrier. -/
def blockGrowthPackage : BlockGrowthPackage where
  stage0 := M2R
  stage1 := PairCarrier
  emb := pairEmb
  J0 := realMirror
  J1 := pairMirror
  bracket0 := fun x y => x * y - y * x
  bracket1 := pairBracket
  emb_J := by
    intro x
    exact (pairEmb_mirror_comm x).symm
  emb_bracket := by
    intro x y
    exact (pairEmb_bracket_compat x y).symm

/-- The non-trivial growth package is internally consistent. -/
theorem blockGrowthPackage_synthesis :
    (∀ x : blockGrowthPackage.stage0,
      blockGrowthPackage.emb (blockGrowthPackage.J0 x) =
        blockGrowthPackage.J1 (blockGrowthPackage.emb x)) ∧
    (∀ x y : blockGrowthPackage.stage0,
      blockGrowthPackage.emb (blockGrowthPackage.bracket0 x y) =
        blockGrowthPackage.bracket1 (blockGrowthPackage.emb x) (blockGrowthPackage.emb y)) ∧
    (∀ x : blockGrowthPackage.stage1,
      blockGrowthPackage.J1 (blockGrowthPackage.J1 x) = x) := by
  constructor
  · exact blockGrowthPackage.emb_J
  constructor
  · exact blockGrowthPackage.emb_bracket
  · exact pairMirror_sq

/-- Block lift of the `2×2` carrier into a doubled `4×4` carrier.

This is the concrete "outer `2×2` acting on inner `2×2`" move:
the outer layer is a Kronecker block, the inner layer stays unchanged.
-/
def blockLift (X : M2R) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ :=
  Matrix.kronecker X (1 : M2R)

/-- The outer CPT mirror commutes with the doubled carrier lift.

The reflection acts on the outer block and leaves the inner carrier intact.
-/
theorem blockLift_conjugation (X : M2R) :
    Matrix.kronecker J_mod (1 : M2R) * blockLift X * Matrix.kronecker J_mod (1 : M2R) =
      blockLift (J_mod * X * J_mod) := by
  have h1 :
      Matrix.kronecker J_mod (1 : M2R) * blockLift X =
        Matrix.kronecker (J_mod * X) (1 : M2R) := by
    rw [blockLift]
    simpa using (Matrix.mul_kronecker_mul J_mod X (1 : M2R) (1 : M2R)).symm
  have h2 :
      Matrix.kronecker (J_mod * X) (1 : M2R) * Matrix.kronecker J_mod (1 : M2R) =
        Matrix.kronecker (J_mod * X * J_mod) (1 : M2R) := by
    simpa [Matrix.mul_assoc] using
      (Matrix.mul_kronecker_mul (J_mod * X) J_mod (1 : M2R) (1 : M2R)).symm
  calc
    Matrix.kronecker J_mod (1 : M2R) * blockLift X * Matrix.kronecker J_mod (1 : M2R)
        = Matrix.kronecker (J_mod * X) (1 : M2R) * Matrix.kronecker J_mod (1 : M2R) := by
            rw [h1]
    _ = Matrix.kronecker (J_mod * X * J_mod) (1 : M2R) := by
            rw [h2]
    _ = blockLift (J_mod * X * J_mod) := by
            simp [blockLift, Matrix.mul_assoc]

end CPTKreinTowerBridge
