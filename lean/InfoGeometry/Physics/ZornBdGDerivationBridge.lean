import Mathlib.Data.Matrix.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

/-!
# Split-Octonion Zorn Algebra, Pauli Soldering, and BdG Derivation Orbits

This module formalizes the three-level architecture:
  Split-Octonion Zorn Algebra ⟶ Pauli Soldering ⟶ Associative BdG Readout

All lemmas and theorems are proven natively in Mathlib with zero `sorry`s.
-/

open Matrix

/-!
=============================================================================
PART 1: Pauli Soldering, Dot Products, and Cross Products
=============================================================================
-/

namespace InfoGeometry.Physics.PauliSolderedCrossProductBridge

/-- Standard 3D dot product for vector coordinates -/
def dot3 (u v : Fin 3 → ℂ) : ℂ :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- Standard 3D cross product for vector coordinates -/
def cross3 (u v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

/-- 
  The Pauli Soldering Map:
  Σ(u) = u₀ σ₁ + u₁ σ₂ + u₂ σ₃ = [[u₂, u₀ - i u₁], [u₀ + i u₁, -u₂]]
-/
def sigmaVec (u : Fin 3 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![u 2, u 0 - Complex.I * u 1],
    ![u 0 + Complex.I * u 1, -u 2]]

/--
  THEOREM 1: The Fundamental Pauli Product Identity
  Σ(u) Σ(v) = (u · v) I₂ + i Σ(u × v)
-/
theorem sigmaVec_mul (u v : Fin 3 → ℂ) :
    sigmaVec u * sigmaVec v =
      (dot3 u v) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        Complex.I • sigmaVec (cross3 u v) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [mul_apply, Fin.sum_univ_two, sigmaVec, smul_apply, add_apply, dot3, cross3]
    linear_combination -(u 1 * v 1 * Complex.I_mul_I)
  · simp [mul_apply, Fin.sum_univ_two, sigmaVec, smul_apply, add_apply, dot3, cross3]
    linear_combination (u 2 * v 0 - u 0 * v 2) * Complex.I_mul_I
  · simp [mul_apply, Fin.sum_univ_two, sigmaVec, smul_apply, add_apply, dot3, cross3]
    linear_combination -(u 2 * v 0 - u 0 * v 2) * Complex.I_mul_I
  · simp [mul_apply, Fin.sum_univ_two, sigmaVec, smul_apply, add_apply, dot3, cross3]
    linear_combination -(u 1 * v 1 * Complex.I_mul_I)

/-- Linearity of Pauli soldering with respect to vector negation -/
lemma sigmaVec_neg (w : Fin 3 → ℂ) : sigmaVec (-w) = - sigmaVec w := by
  ext i j
  fin_cases i <;> fin_cases j
  · change -w 2 = -w 2; rfl
  · change -w 0 - Complex.I * (-w 1) = -(w 0 - Complex.I * w 1); ring
  · change -w 0 + Complex.I * (-w 1) = -(w 0 + Complex.I * w 1); ring
  · change -(-w 2) = -(-w 2); rfl

/--
  THEOREM 2: The Anticommutator selects the Dot Product (Scalar Channel)
  {Σ(u), Σ(v)} = 2 (u · v) I₂
-/
theorem sigmaVec_anticomm (u v : Fin 3 → ℂ) :
    sigmaVec u * sigmaVec v + sigmaVec v * sigmaVec u =
      (2 * dot3 u v) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h1 := sigmaVec_mul u v
  have h2 := sigmaVec_mul v u
  have h_cross : cross3 v u = - cross3 u v := by
    ext i; fin_cases i <;> { dsimp [cross3]; ring }
  have h_dot : dot3 v u = dot3 u v := by
    dsimp [dot3]; ring
  rw [h1, h2, h_dot, h_cross, sigmaVec_neg]
  ext i j
  simp only [add_apply, smul_apply, smul_eq_mul, neg_apply, smul_neg]
  ring

/--
  THEOREM 3: The Commutator selects the Cross Product (Oriented Bivector Channel)
  [Σ(u), Σ(v)] = 2i Σ(u × v)
-/
theorem sigmaVec_comm (u v : Fin 3 → ℂ) :
    sigmaVec u * sigmaVec v - sigmaVec v * sigmaVec u =
      (2 * Complex.I) • sigmaVec (cross3 u v) := by
  have h1 := sigmaVec_mul u v
  have h2 := sigmaVec_mul v u
  have h_cross : cross3 v u = - cross3 u v := by
    ext i; fin_cases i <;> { dsimp [cross3]; ring }
  have h_dot : dot3 v u = dot3 u v := by
    dsimp [dot3]; ring
  rw [h1, h2, h_dot, h_cross, sigmaVec_neg]
  ext i j
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, neg_apply, smul_neg]
  ring

end InfoGeometry.Physics.PauliSolderedCrossProductBridge

/-!
=============================================================================
PART 2: The Split-Octonion Zorn Matrix Algebra
=============================================================================
-/

namespace InfoGeometry.Physics.ZornVectorMatrixAlgebra

open InfoGeometry.Physics.PauliSolderedCrossProductBridge

/-- A Split Octonion in Zorn vector-matrix presentation: [[a, u], [v, b]] -/
@[ext]
structure Zorn (R : Type*) where
  a : R
  u : Fin 3 → R
  v : Fin 3 → R
  b : R

variable {R : Type*} [CommRing R]

lemma eq_zero_of_self_eq_add_self {x : R} (h : x = x + x) : x = 0 := by
  have h1 : x + x = x + 0 := by rw [add_zero, ← h]
  exact add_left_cancel h1

/-- The Dot Product on R³ -/
def dotR (u v : Fin 3 → R) : R :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- The Cross Product on R³ -/
def crossR (u v : Fin 3 → R) : Fin 3 → R :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

/-- The non-associative Zorn multiplication law -/
def zornMul (X Y : Zorn R) : Zorn R where
  a := X.a * Y.a + dotR X.u Y.v
  u := fun i => X.a * Y.u i + Y.b * X.u i - crossR X.v Y.v i
  v := fun i => Y.a * X.v i + X.b * Y.v i + crossR X.u Y.u i
  b := X.b * Y.b + dotR X.v Y.u

instance : Mul (Zorn R) := ⟨zornMul⟩

/-- The Unit element of the Zorn algebra: 1_𝕆s = [[1, 0], [0, 1]] -/
def zornOne : Zorn R where
  a := 1
  u := fun _ => 0
  v := fun _ => 0
  b := 1

instance : One (Zorn R) := ⟨zornOne⟩

/-- The Zero element of the Zorn algebra: 0_𝕆s = [[0, 0], [0, 0]] -/
def zornZero : Zorn R where
  a := 0
  u := fun _ => 0
  v := fun _ => 0
  b := 0

instance : Zero (Zorn R) := ⟨zornZero⟩

/-- Addition of Zorn matrices -/
def zornAdd (X Y : Zorn R) : Zorn R where
  a := X.a + Y.a
  u := fun i => X.u i + Y.u i
  v := fun i => X.v i + Y.v i
  b := X.b + Y.b

instance : Add (Zorn R) := ⟨zornAdd⟩

/-- Scalar multiplication of Zorn matrices -/
def zornSMul (c : R) (X : Zorn R) : Zorn R where
  a := c * X.a
  u := fun i => c * X.u i
  v := fun i => c * X.v i
  b := c * X.b

instance : SMul R (Zorn R) := ⟨zornSMul⟩

@[simp] theorem zorn_zero_a : (0 : Zorn R).a = 0 := rfl
@[simp] theorem zorn_zero_u (i : Fin 3) : (0 : Zorn R).u i = 0 := rfl
@[simp] theorem zorn_zero_v (i : Fin 3) : (0 : Zorn R).v i = 0 := rfl
@[simp] theorem zorn_zero_b : (0 : Zorn R).b = 0 := rfl

@[simp] theorem zorn_one_a : (1 : Zorn R).a = 1 := rfl
@[simp] theorem zorn_one_u (i : Fin 3) : (1 : Zorn R).u i = 0 := rfl
@[simp] theorem zorn_one_v (i : Fin 3) : (1 : Zorn R).v i = 0 := rfl
@[simp] theorem zorn_one_b : (1 : Zorn R).b = 1 := rfl

@[simp] theorem zorn_add_a (X Y : Zorn R) : (X + Y).a = X.a + Y.a := rfl
@[simp] theorem zorn_add_u (X Y : Zorn R) (i : Fin 3) : (X + Y).u i = X.u i + Y.u i := rfl
@[simp] theorem zorn_add_v (X Y : Zorn R) (i : Fin 3) : (X + Y).v i = X.v i + Y.v i := rfl
@[simp] theorem zorn_add_b (X Y : Zorn R) : (X + Y).b = X.b + Y.b := rfl

@[simp] theorem zorn_smul_a (c : R) (X : Zorn R) : (c • X).a = c * X.a := rfl
@[simp] theorem zorn_smul_u (c : R) (X : Zorn R) (i : Fin 3) : (c • X).u i = c * X.u i := rfl
@[simp] theorem zorn_smul_v (c : R) (X : Zorn R) (i : Fin 3) : (c • X).v i = c * X.v i := rfl
@[simp] theorem zorn_smul_b (c : R) (X : Zorn R) : (c • X).b = c * X.b := rfl

/-- THEOREM: Left multiplication by 1 is the identity -/
@[simp]
theorem zorn_one_mul (X : Zorn R) : (1 : Zorn R) * X = X := by
  ext
  · change (1 : R) * X.a + (0 * X.v 0 + 0 * X.v 1 + 0 * X.v 2) = X.a
    ring
  · rename_i i
    fin_cases i <;> {
      change (1 : R) * X.u _ + X.b * 0 - (0 * X.v _ - 0 * X.v _) = X.u _
      ring
    }
  · rename_i i
    fin_cases i <;> {
      change X.a * (0 : R) + (1 : R) * X.v _ + (0 * X.u _ - 0 * X.u _) = X.v _
      ring
    }
  · change (1 : R) * X.b + (0 * X.u 0 + 0 * X.u 1 + 0 * X.u 2) = X.b
    ring

/-- THEOREM: Right multiplication by 1 is the identity -/
@[simp]
theorem zorn_mul_one (X : Zorn R) : X * (1 : Zorn R) = X := by
  ext
  · change X.a * (1 : R) + (X.u 0 * 0 + X.u 1 * 0 + X.u 2 * 0) = X.a
    ring
  · rename_i i
    fin_cases i <;> {
      change X.a * (0 : R) + (1 : R) * X.u _ - (X.v _ * 0 - X.v _ * 0) = X.u _
      ring
    }
  · rename_i i
    fin_cases i <;> {
      change (1 : R) * X.v _ + X.b * (0 : R) + (X.u _ * 0 - X.u _ * 0) = X.v _
      ring
    }
  · change X.b * (1 : R) + (X.v 0 * 0 + X.v 1 * 0 + X.v 2 * 0) = X.b
    ring

@[simp]
theorem zorn_one_sq : (1 : Zorn R) * (1 : Zorn R) = (1 : Zorn R) :=
  zorn_one_mul 1

/-- The split (4,4) composition norm: N(Z) = a b - u · v -/
def zornNorm (X : Zorn R) : R :=
  X.a * X.b - dotR X.u X.v

/-- Predicate stating that D is a derivation on the Zorn algebra -/
def IsZornDerivation (D : Zorn R → Zorn R) : Prop :=
  (∀ X Y, D (X + Y) = D X + D Y) ∧
  (∀ (c : R) X, D (c • X) = c • D X) ∧
  (∀ X Y, D (X * Y) = (D X) * Y + X * (D Y))

/-- THEOREM: Every Zorn derivation strictly annihilates the identity element 1_𝕆s -/
theorem derivation_annihilates_one (D : Zorn R → Zorn R) (hD : IsZornDerivation D) :
    D 1 = 0 := by
  have h_mul := hD.2.2 1 1
  rw [zorn_one_sq, zorn_mul_one, zorn_one_mul] at h_mul
  have ha : (D 1).a = 0 := by
    have h := congrArg (fun z : Zorn R => z.a) h_mul
    dsimp at h
    exact eq_zero_of_self_eq_add_self h
  have hb : (D 1).b = 0 := by
    have h := congrArg (fun z : Zorn R => z.b) h_mul
    dsimp at h
    exact eq_zero_of_self_eq_add_self h
  have hu : ∀ i, (D 1).u i = 0 := by
    intro i
    have h := congrArg (fun z : Zorn R => z.u i) h_mul
    dsimp at h
    exact eq_zero_of_self_eq_add_self h
  have hv : ∀ i, (D 1).v i = 0 := by
    intro i
    have h := congrArg (fun z : Zorn R => z.v i) h_mul
    dsimp at h
    exact eq_zero_of_self_eq_add_self h
  ext
  · exact ha
  · rename_i i; exact hu i
  · rename_i i; exact hv i
  · exact hb

/-- THEOREM: Every central scalar seed (c • 1) is strictly annihilated by all derivations -/
theorem derivation_annihilates_scalar_seed (D : Zorn R → Zorn R) (hD : IsZornDerivation D) (c : R) :
    D (c • (1 : Zorn R)) = 0 := by
  rw [hD.2.1 c 1, derivation_annihilates_one D hD]
  ext <;> simp

end InfoGeometry.Physics.ZornVectorMatrixAlgebra

/-!
=============================================================================
PART 3: Associative 2×2 Block BdG Soldering Readout
=============================================================================
-/

namespace InfoGeometry.Physics.ZornBdGSolderingReadout

open InfoGeometry.Physics.PauliSolderedCrossProductBridge
open InfoGeometry.Physics.ZornVectorMatrixAlgebra

/--
  The Associative BdG Readout Map Π : Zorn ℂ → Matrix (Fin 4) (Fin 4) ℂ
  Embedding the Zorn 3-vectors into 2×2 Pauli blocks:
  Π(Z) = [[ a I₂,  Σ(u) ],
          [ Σ(v),  b I₂ ]]
-/
def bdgReadout (Z : Zorn ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  ![![Z.a, 0, Z.u 2, Z.u 0 - Complex.I * Z.u 1],
    ![0, Z.a, Z.u 0 + Complex.I * Z.u 1, -Z.u 2],
    ![Z.v 2, Z.v 0 - Complex.I * Z.v 1, Z.b, 0],
    ![Z.v 0 + Complex.I * Z.v 1, -Z.v 2, 0, Z.b]]

/-- Upper-Left block extraction (Normal Particle Sector) -/
def block11 (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![M 0 0, M 0 1],
    ![M 1 0, M 1 1]]

/-- Upper-Right block extraction (Superconducting Pairing Sector Δ) -/
def block12 (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![M 0 2, M 0 3],
    ![M 1 2, M 1 3]]

/-- Lower-Left block extraction (Conjugate Pairing Sector Δ†) -/
def block21 (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![M 2 0, M 2 1],
    ![M 3 0, M 3 1]]

/-- Lower-Right block extraction (Hole Sector) -/
def block22 (M : Matrix (Fin 4) (Fin 4) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![M 2 2, M 2 3],
    ![M 3 2, M 3 3]]

/-- THEOREM: Upper-right block of the readout is IDENTICALLY the soldered Pauli pairing Σ(u) -/
@[simp]
theorem bdgReadout_block12_eq_sigmaVec (Z : Zorn ℂ) :
    block12 (bdgReadout Z) = sigmaVec Z.u := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- THEOREM: Lower-left block of the readout is IDENTICALLY the soldered Pauli pairing Σ(v) -/
@[simp]
theorem bdgReadout_block21_eq_sigmaVec (Z : Zorn ℂ) :
    block21 (bdgReadout Z) = sigmaVec Z.v := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- THEOREM: Diagonal blocks are pure scalar multiples of the identity matrix -/
@[simp]
theorem bdgReadout_diagonal_blocks (Z : Zorn ℂ) :
    block11 (bdgReadout Z) = Z.a • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    block22 (bdgReadout Z) = Z.b • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [block11, block22, bdgReadout, smul_apply]

end InfoGeometry.Physics.ZornBdGSolderingReadout

/-!
=============================================================================
PART 4: G₂(2) Derivation Orbits and Pairing Generation
=============================================================================
-/

namespace InfoGeometry.Physics.G2BdGOrbit

open InfoGeometry.Physics.ZornVectorMatrixAlgebra
open InfoGeometry.Physics.ZornBdGSolderingReadout
open InfoGeometry.Physics.PauliSolderedCrossProductBridge

/-- A diagonal normal-state seed: [[a, 0], [0, b]] -/
def normalSeed (a b : ℂ) : Zorn ℂ where
  a := a
  u := fun _ => 0
  v := fun _ => 0
  b := b

/-- First-order Taylor flow under a derivation D: Z(t) = Z₀ + t • D(Z₀) -/
def firstOrderFlow (D : Zorn ℂ → Zorn ℂ) (Z₀ : Zorn ℂ) (t : ℂ) : Zorn ℂ :=
  Z₀ + (t • D Z₀)

/--
  THEOREM 1: Central Normal Seed produces NO Pairing.
  If a = b, the seed is central (a • 1), hence D(Z₀) = 0 and pairing remains zero for all t.
-/
theorem central_seed_generates_no_pairing
    (D : Zorn ℂ → Zorn ℂ) (hD : IsZornDerivation D) (a : ℂ) (t : ℂ) :
    block12 (bdgReadout (firstOrderFlow D (normalSeed a a) t)) = 0 := by
  have h_seed : normalSeed a a = a • (1 : Zorn ℂ) := by
    ext <;> simp [normalSeed]
  dsimp [firstOrderFlow]
  rw [h_seed, derivation_annihilates_scalar_seed D hD a]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [block12, bdgReadout]

/--
  THEOREM 2: First-Order Generated Pairing from a Cartan Seed.
  For a generic non-central seed (a ≠ b), the upper-right BdG pairing block 
  at first order is precisely t • Σ(pr_u D(Z₀)).
-/
theorem cartan_seed_generates_pairing
    (D : Zorn ℂ → Zorn ℂ) (a b t : ℂ) :
    block12 (bdgReadout (firstOrderFlow D (normalSeed a b) t)) =
      t • sigmaVec (D (normalSeed a b)).u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [firstOrderFlow, normalSeed, block12, bdgReadout, sigmaVec, smul_apply] <;>
    ring

end InfoGeometry.Physics.G2BdGOrbit
