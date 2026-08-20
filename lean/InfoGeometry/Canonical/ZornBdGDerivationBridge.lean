import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.ZornBdGDerivationBridge

Proves the structural bridge between the split-octonionic Zorn algebra
and Bogoliubov-de Gennes (BdG) Hamiltonians.

KEY THEOREMS:
1. `sigmaVec_mul`: Fundamental Pauli product theorem:
     Σ(u) Σ(v) = (u · v) I₂ + i Σ(u × v)
2. `sigmaVec_anticomm`: Anticommutator extracts dot product {Σ(u), Σ(v)} = 2(u·v)I₂
3. `sigmaVec_comm`: Commutator extracts cross product [Σ(u), Σ(v)] = 2i Σ(u × v)
4. `derivation_annihilates_one`: Every derivation D on Zorn strictly annihilates 1_𝕆s
5. `derivation_annihilates_scalar_seed`: Every derivation D strictly annihilates central seed λ • 1
6. `central_seed_generates_no_pairing`: Normal central seed has zero BdG pairing
7. `cartan_seed_generates_pairing`: Off-diagonal Cartan seed generates superconducting pairing
-/

noncomputable section

namespace InfoGeometry.Canonical.ZornBdGDerivationBridge

open Matrix

/-!
=============================================================================
PART 1: Pauli Matrix Soldering & Cross-Product Embedding
=============================================================================
-/

namespace PauliSolderedCrossProductBridge

/-- Dot product on ℂ³ -/
def dot3 (u v : Fin 3 → ℂ) : ℂ :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- Cross product on ℂ³ -/
def cross3 (u v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

/-- Pauli Soldering Map Σ : ℂ³ → Mat(2×2, ℂ), Σ(u) = u₁ σ₁ + u₂ σ₂ + u₃ σ₃ -/
def sigmaVec (u : Fin 3 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![u 2, u 0 - Complex.I * u 1],
    ![u 0 + Complex.I * u 1, -u 2]]

theorem sigmaVec_add (u v : Fin 3 → ℂ) :
    sigmaVec (u + v) = sigmaVec u + sigmaVec v := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaVec, Pi.add_apply, mul_add]
    <;> ring

theorem sigmaVec_smul (c : ℂ) (u : Fin 3 → ℂ) :
    sigmaVec (c • u) = c • sigmaVec u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sigmaVec, Pi.smul_apply, smul_eq_mul]
    <;> ring

/-- The Pauli soldering is a bundled complex-linear map. -/
def sigmaVecLinear :
    (Fin 3 → ℂ) →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun := sigmaVec
  map_add' := sigmaVec_add
  map_smul' := sigmaVec_smul

@[simp]
theorem sigmaVecLinear_apply (u : Fin 3 → ℂ) :
    sigmaVecLinear u = sigmaVec u := rfl

theorem sigmaVec_zero : sigmaVec (fun _ => 0) = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> { simp [sigmaVec] }

theorem sigmaVec_eq_zero_iff (u : Fin 3 → ℂ) :
    sigmaVec u = 0 ↔ ∀ i, u i = 0 := by
  constructor
  · intro h i
    fin_cases i
    · have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
      have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) h
      simp [sigmaVec] at h01 h10
      change u 0 = 0
      linear_combination (1 / 2 : ℂ) * (h01 + h10)
    · have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
      have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 0) h
      simp [sigmaVec] at h01 h10
      change u 1 = 0
      have hprod : Complex.I * u 1 = 0 := by
        linear_combination (1 / 2 : ℂ) * (h10 - h01)
      exact (mul_eq_zero.mp hprod).resolve_left Complex.I_ne_zero
    · have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) h
      simp only [sigmaVec, Matrix.zero_apply] at h00
      change u 2 = 0 at h00
      exact h00
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sigmaVec, h]

theorem sigmaVec_sub (u v : Fin 3 → ℂ) :
    sigmaVec (u - v) = sigmaVec u - sigmaVec v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaVec, sub_eq_add_neg] <;> ring

theorem sigmaVec_injective : Function.Injective sigmaVec := by
  intro u v h
  have hz : sigmaVec (u - v) = 0 := by
    rw [sigmaVec_sub, h, sub_self]
  have hzero := (sigmaVec_eq_zero_iff (u - v)).mp hz
  ext i
  have hi : (u - v) i = 0 := hzero i
  change u i - v i = 0 at hi
  exact sub_eq_zero.mp hi

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
  · simp [sigmaVec, dot3, cross3, mul_apply, Fin.sum_univ_two, smul_apply, add_apply]
    linear_combination -Complex.I_sq * (u 1 * v 1)
  · simp [sigmaVec, dot3, cross3, mul_apply, Fin.sum_univ_two, smul_apply, add_apply]
    linear_combination Complex.I_sq * (u 2 * v 0 - u 0 * v 2)
  · simp [sigmaVec, dot3, cross3, mul_apply, Fin.sum_univ_two, smul_apply, add_apply]
    linear_combination Complex.I_sq * (u 0 * v 2 - u 2 * v 0)
  · simp [sigmaVec, dot3, cross3, mul_apply, Fin.sum_univ_two, smul_apply, add_apply]
    linear_combination -Complex.I_sq * (u 1 * v 1)

/--
  THEOREM 2: The Anticommutator selects the Dot Product (Scalar Channel)
  {Σ(u), Σ(v)} = 2 (u · v) I₂
-/
theorem sigmaVec_anticomm (u v : Fin 3 → ℂ) :
    sigmaVec u * sigmaVec v + sigmaVec v * sigmaVec u =
      (2 * dot3 u v) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h1 := sigmaVec_mul u v
  have h2 := sigmaVec_mul v u
  have h_cross : cross3 u v = - cross3 v u := by
    ext i; fin_cases i <;> simp [cross3] <;> ring
  have h_dot : dot3 v u = dot3 u v := by
    simp [dot3]; ring
  rw [h1, h2, h_dot, h_cross]
  ext i j
  fin_cases i <;> fin_cases j <;>
    { simp [sigmaVec, dot3, cross3, smul_apply, add_apply]; ring }

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
    ext i; fin_cases i <;> simp [cross3] <;> ring
  have h_dot : dot3 v u = dot3 u v := by
    simp [dot3]; ring
  rw [h1, h2, h_dot, h_cross]
  ext i j
  fin_cases i <;> fin_cases j <;>
    { simp [sigmaVec, dot3, cross3, smul_apply, sub_apply]; ring }

end PauliSolderedCrossProductBridge

/-!
=============================================================================
PART 2: The Split-Octonion Zorn Matrix Algebra
=============================================================================
-/

namespace ZornVectorMatrixAlgebra

open PauliSolderedCrossProductBridge

/-- A Split Octonion in Zorn vector-matrix presentation: [[a, u], [v, b]] -/
@[ext]
structure Zorn (R : Type*) where
  a : R
  u : Fin 3 → R
  v : Fin 3 → R
  b : R

variable {R : Type*} [CommRing R]

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

instance zornMulInstance : Mul (Zorn R) := ⟨zornMul⟩

/-- The Unit element of the Zorn algebra: 1_𝕆s = [[1, 0], [0, 1]] -/
def zornOne : Zorn R where
  a := 1
  u := fun _ => 0
  v := fun _ => 0
  b := 1

instance : One (Zorn R) := ⟨zornOne⟩

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

@[simp] theorem zornMul_a (X Y : Zorn R) :
    (X * Y).a = X.a * Y.a + dotR X.u Y.v := rfl

@[simp] theorem zornMul_u (X Y : Zorn R) :
    (X * Y).u = fun i =>
      X.a * Y.u i + Y.b * X.u i - crossR X.v Y.v i := rfl

@[simp] theorem zornMul_v (X Y : Zorn R) :
    (X * Y).v = fun i =>
      Y.a * X.v i + X.b * Y.v i + crossR X.u Y.u i := rfl

@[simp] theorem zornMul_b (X Y : Zorn R) :
    (X * Y).b = X.b * Y.b + dotR X.v Y.u := rfl

/-- THEOREM: Left multiplication by 1 is the identity -/
@[simp]
theorem zorn_one_mul (X : Zorn R) : (1 : Zorn R) * X = X := by
  have hu : (fun i => (1 : R) * X.u i + X.b * 0 - (![(0 : R) * X.v 2 - 0 * X.v 1,
      0 * X.v 0 - 0 * X.v 2, 0 * X.v 1 - 0 * X.v 0] i)) = X.u := by
    ext i; fin_cases i <;> simp
  have hv : (fun i => X.a * (0 : R) + 1 * X.v i + (![(0 : R) * X.u 2 - 0 * X.u 1,
      0 * X.u 0 - 0 * X.u 2, 0 * X.u 1 - 0 * X.u 0] i)) = X.v := by
    ext i; fin_cases i <;> simp
  ext
  · change 1 * X.a + dotR (fun _ => 0) X.v = X.a
    simp [dotR]
  · rename_i i
    change (fun i => (1 : R) * X.u i + X.b * 0 - (![(0 : R) * X.v 2 - 0 * X.v 1,
      0 * X.v 0 - 0 * X.v 2, 0 * X.v 1 - 0 * X.v 0] i)) i = X.u i
    rw [hu]
  · rename_i i
    change (fun i => X.a * (0 : R) + 1 * X.v i + (![(0 : R) * X.u 2 - 0 * X.u 1,
      0 * X.u 0 - 0 * X.u 2, 0 * X.u 1 - 0 * X.u 0] i)) i = X.v i
    rw [hv]
  · change 1 * X.b + dotR (fun _ => 0) X.u = X.b
    simp [dotR]

/-- THEOREM: Right multiplication by 1 is the identity -/
@[simp]
theorem zorn_mul_one (X : Zorn R) : X * (1 : Zorn R) = X := by
  have hu : (fun i => X.a * (0 : R) + 1 * X.u i - (![X.v 1 * (0 : R) - X.v 2 * 0,
      X.v 2 * 0 - X.v 0 * 0, X.v 0 * 0 - X.v 1 * 0] i)) = X.u := by
    ext i; fin_cases i <;> simp
  have hv : (fun i => (1 : R) * X.v i + X.b * (0 : R) + (![X.u 1 * (0 : R) - X.u 2 * 0,
      X.u 2 * 0 - X.u 0 * 0, X.u 0 * 0 - X.u 1 * 0] i)) = X.v := by
    ext i; fin_cases i <;> simp
  ext
  · change X.a * 1 + dotR X.u (fun _ => 0) = X.a
    simp [dotR]
  · rename_i i
    change (fun i => X.a * (0 : R) + 1 * X.u i - (![X.v 1 * (0 : R) - X.v 2 * 0,
      X.v 2 * 0 - X.v 0 * 0, X.v 0 * 0 - X.v 1 * 0] i)) i = X.u i
    rw [hu]
  · rename_i i
    change (fun i => (1 : R) * X.v i + X.b * (0 : R) + (![X.u 1 * (0 : R) - X.u 2 * 0,
      X.u 2 * 0 - X.u 0 * 0, X.u 0 * 0 - X.u 1 * 0] i)) i = X.v i
    rw [hv]
  · change X.b * 1 + dotR X.v (fun _ => 0) = X.b
    simp [dotR]

/-- The split (4,4) composition norm: N(Z) = a b - u · v -/
def zornNorm (X : Zorn R) : R :=
  X.a * X.b - dotR X.u X.v

@[simp]
theorem zornNorm_one : zornNorm (1 : Zorn R) = 1 := by
  change (1 : R) * 1 - (0 * 0 + 0 * 0 + 0 * 0) = 1
  ring

theorem zornNorm_scalar_one (c : R) :
    zornNorm (c • (1 : Zorn R)) = c * c := by
  change (c * 1) * (c * 1) - (c * 0 * (c * 0) + c * 0 * (c * 0) + c * 0 * (c * 0)) = c * c
  ring

/-- The reduced Zorn norm is multiplicative, hence is a composition norm. -/
theorem zornNorm_mul (X Y : Zorn R) :
    zornNorm (X * Y) = zornNorm X * zornNorm Y := by
  dsimp [zornNorm, dotR, crossR]
  change (X.a * Y.a + (X.u 0 * Y.v 0 + X.u 1 * Y.v 1 + X.u 2 * Y.v 2)) *
         (X.b * Y.b + (X.v 0 * Y.u 0 + X.v 1 * Y.u 1 + X.v 2 * Y.u 2)) -
         ((X.a * Y.u 0 + Y.b * X.u 0 - (X.v 1 * Y.v 2 - X.v 2 * Y.v 1)) *
          (Y.a * X.v 0 + X.b * Y.v 0 + (X.u 1 * Y.u 2 - X.u 2 * Y.u 1)) +
          (X.a * Y.u 1 + Y.b * X.u 1 - (X.v 2 * Y.v 0 - X.v 0 * Y.v 2)) *
          (Y.a * X.v 1 + X.b * Y.v 1 + (X.u 2 * Y.u 0 - X.u 0 * Y.u 2)) +
          (X.a * Y.u 2 + Y.b * X.u 2 - (X.v 0 * Y.v 1 - X.v 1 * Y.v 0)) *
          (Y.a * X.v 2 + X.b * Y.v 2 + (X.u 0 * Y.u 1 - X.u 1 * Y.u 0))) =
         (X.a * X.b - (X.u 0 * X.v 0 + X.u 1 * X.v 1 + X.u 2 * X.v 2)) *
         (Y.a * Y.b - (Y.u 0 * Y.v 0 + Y.u 1 * Y.v 1 + Y.u 2 * Y.v 2))
  ring

/-- Predicate stating that D is a derivation on the Zorn algebra -/
def IsZornDerivation (D : Zorn R → Zorn R) : Prop :=
  (∀ X Y, D (X + Y) = D X + D Y) ∧
  (∀ (c : R) X, D (c • X) = c • D X) ∧
  (∀ X Y, D (X * Y) = (D X) * Y + X * (D Y))

/-- THEOREM: Every Zorn derivation strictly annihilates the identity element 1_𝕆s -/
theorem derivation_annihilates_one (D : Zorn R → Zorn R) (hD : IsZornDerivation D) :
    D 1 = ⟨0, fun _ => 0, fun _ => 0, 0⟩ := by
  have h_add : D 1 = D 1 + D 1 := by
    calc D 1 = D (1 * 1) := by rw [zorn_mul_one 1]
    _ = D 1 * 1 + 1 * D 1 := hD.2.2 1 1
    _ = D 1 + D 1 := by rw [zorn_mul_one (D 1), zorn_one_mul (D 1)]
  have h_zero : ∀ (x : R), x = x + x → x = 0 := by
    intro x h
    calc x = (x + x) - x := by ring
    _ = x - x := by rw [← h]
    _ = 0 := by ring
  ext
  · exact h_zero (D 1).a (congr_arg Zorn.a h_add)
  · rename_i i
    exact h_zero ((D 1).u i) (congr_fun (congr_arg Zorn.u h_add) i)
  · rename_i i
    exact h_zero ((D 1).v i) (congr_fun (congr_arg Zorn.v h_add) i)
  · exact h_zero (D 1).b (congr_arg Zorn.b h_add)

/-- THEOREM: Every central scalar seed (c • 1) is strictly annihilated by all derivations -/
theorem derivation_annihilates_scalar_seed (D : Zorn R → Zorn R) (hD : IsZornDerivation D) (c : R) :
    D (c • (1 : Zorn R)) = ⟨0, fun _ => 0, fun _ => 0, 0⟩ := by
  rw [hD.2.1 c 1, derivation_annihilates_one D hD]
  ext
  · change c * 0 = 0; ring
  · rename_i i; change c * 0 = 0; ring
  · rename_i i; change c * 0 = 0; ring
  · change c * 0 = 0; ring

end ZornVectorMatrixAlgebra

/-!
=============================================================================
PART 3: Associative 2×2 Block BdG Soldering Readout
=============================================================================
-/

namespace ZornBdGSolderingReadout

open PauliSolderedCrossProductBridge
open ZornVectorMatrixAlgebra

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
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> simp [block11, bdgReadout, smul_apply]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [block22, bdgReadout, smul_apply]

end ZornBdGSolderingReadout

/-!
=============================================================================
PART 4: G₂(2) Derivation Orbits and Pairing Generation
=============================================================================
-/

namespace G2BdGOrbit

open ZornVectorMatrixAlgebra
open ZornBdGSolderingReadout
open PauliSolderedCrossProductBridge

/-- A diagonal normal-state seed: [[a, 0], [0, b]] -/
def normalSeed (a b : ℂ) : Zorn ℂ where
  a := a
  u := fun _ => 0
  v := fun _ => 0
  b := b

theorem normalSeed_eq_scalar_iff (a b : ℂ) :
    normalSeed a b = a • (1 : Zorn ℂ) ↔ a = b := by
  constructor
  · intro h
    have hb := congrArg Zorn.b h
    simp only [normalSeed] at hb
    change b = a * 1 at hb
    simpa using hb.symm
  · intro hab
    subst b
    ext
    · change a = a * 1
      ring
    · rename_i i
      change (0 : ℂ) = a * 0
      ring
    · rename_i i
      change (0 : ℂ) = a * 0
      ring
    · change a = a * 1
      ring

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
    ext
    · change a = a * 1; ring
    · rename_i i; change (0 : ℂ) = a * 0; ring
    · rename_i i; change (0 : ℂ) = a * 0; ring
    · change a = a * 1; ring
  have hD_seed : D (normalSeed a a) = ⟨0, fun _ => 0, fun _ => 0, 0⟩ := by
    rw [h_seed, derivation_annihilates_scalar_seed D hD a]
  rw [bdgReadout_block12_eq_sigmaVec]
  have hu : (firstOrderFlow D (normalSeed a a) t).u = fun _ => 0 := by
    change (fun i => (normalSeed a a).u i + t * (D (normalSeed a a)).u i) = fun _ => 0
    rw [hD_seed]
    ext i
    change (0 : ℂ) + t * 0 = 0
    ring
  rw [hu, sigmaVec_zero]

/--
  THEOREM 2: First-Order Generated Pairing from a Cartan Seed.
  For a generic non-central seed (a ≠ b), the upper-right BdG pairing block 
  at first order is precisely t • Σ(pr_u D(Z₀)).
-/
theorem cartan_seed_generates_pairing
    (D : Zorn ℂ → Zorn ℂ) (a b t : ℂ) :
    block12 (bdgReadout (firstOrderFlow D (normalSeed a b) t)) =
      t • sigmaVec (D (normalSeed a b)).u := by
  rw [bdgReadout_block12_eq_sigmaVec]
  have hu : (firstOrderFlow D (normalSeed a b) t).u = fun i => t * (D (normalSeed a b)).u i := by
    change (fun i => (normalSeed a b).u i + t * (D (normalSeed a b)).u i) = fun i => t * (D (normalSeed a b)).u i
    ext i
    change (0 : ℂ) + t * (D (normalSeed a b)).u i = t * (D (normalSeed a b)).u i
    ring
  rw [hu]
  ext i j
  fin_cases i <;> fin_cases j
  · change t * (D (normalSeed a b)).u 2 = t * (D (normalSeed a b)).u 2
    rfl
  · change t * (D (normalSeed a b)).u 0 - Complex.I * (t * (D (normalSeed a b)).u 1) =
      t * ((D (normalSeed a b)).u 0 - Complex.I * (D (normalSeed a b)).u 1)
    ring
  · change t * (D (normalSeed a b)).u 0 + Complex.I * (t * (D (normalSeed a b)).u 1) =
      t * ((D (normalSeed a b)).u 0 + Complex.I * (D (normalSeed a b)).u 1)
    ring
  · change -(t * (D (normalSeed a b)).u 2) = t * (-(D (normalSeed a b)).u 2)
    ring

/- The lower-left BdG channel is transported by the second Zorn vector
component.  It is proved separately because no relation between the two
off-diagonal components is assumed. -/
theorem cartan_seed_generates_conjugate_pairing
    (D : Zorn ℂ → Zorn ℂ) (a b t : ℂ) :
    block21 (bdgReadout (firstOrderFlow D (normalSeed a b) t)) =
      t • sigmaVec (D (normalSeed a b)).v := by
  rw [bdgReadout_block21_eq_sigmaVec]
  have hv : (firstOrderFlow D (normalSeed a b) t).v =
      fun i => t * (D (normalSeed a b)).v i := by
    change (fun i => (normalSeed a b).v i + t * (D (normalSeed a b)).v i) =
      fun i => t * (D (normalSeed a b)).v i
    ext i
    change (0 : ℂ) + t * (D (normalSeed a b)).v i =
      t * (D (normalSeed a b)).v i
    ring
  rw [hv]
  ext i j
  fin_cases i <;> fin_cases j
  · change t * (D (normalSeed a b)).v 2 = t * (D (normalSeed a b)).v 2
    rfl
  · change t * (D (normalSeed a b)).v 0 -
      Complex.I * (t * (D (normalSeed a b)).v 1) =
      t * ((D (normalSeed a b)).v 0 -
        Complex.I * (D (normalSeed a b)).v 1)
    ring
  · change t * (D (normalSeed a b)).v 0 +
      Complex.I * (t * (D (normalSeed a b)).v 1) =
      t * ((D (normalSeed a b)).v 0 +
        Complex.I * (D (normalSeed a b)).v 1)
    ring
  · change -(t * (D (normalSeed a b)).v 2) =
      t * (-(D (normalSeed a b)).v 2)
    ring

end G2BdGOrbit

/-!
=============================================================================
PART 4: Star Compatibility and BdG Orbit Preservation
=============================================================================
-/

namespace BdGStarOrbitPreservation

open ZornVectorMatrixAlgebra
open ZornBdGSolderingReadout
open PauliSolderedCrossProductBridge

/-- Canonical conjugation on the scalar Zorn carrier over `ℂ`.
    This is the involution compatible with the particle-hole BdG readout. -/
def zornStar (Z : Zorn ℂ) : Zorn ℂ where
  a := Z.b
  u := fun i => - Z.u i
  v := fun i => - Z.v i
  b := Z.a

theorem bdgReadout_star (Z : Zorn ℂ) :
    block11 (bdgReadout (zornStar Z)) = Z.b • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    block22 (bdgReadout (zornStar Z)) = Z.a • (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
    block12 (bdgReadout (zornStar Z)) = -sigmaVec Z.u ∧
    block21 (bdgReadout (zornStar Z)) = -sigmaVec Z.v := by
  have hσu : sigmaVec (fun i => -Z.u i) = -sigmaVec Z.u := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sigmaVec] <;> ring
  have hσv : sigmaVec (fun i => -Z.v i) = -sigmaVec Z.v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sigmaVec] <;> ring
  have hd := bdgReadout_diagonal_blocks (zornStar Z)
  have hu := bdgReadout_block12_eq_sigmaVec (zornStar Z)
  have hv := bdgReadout_block21_eq_sigmaVec (zornStar Z)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [zornStar] using hd.1
  · simpa [zornStar] using hd.2
  · simpa [zornStar, hσu] using hu
  · simpa [zornStar, hσv] using hv

/-- The star involution is an involution on the scalar Zorn carrier. -/
@[simp]
theorem zornStar_involutive (Z : Zorn ℂ) :
    zornStar (zornStar Z) = Z := by
  ext <;> simp [zornStar]

/-- THEOREM: A self-adjoint normal seed remains self-adjoint along the first-order orbit.
    If `Z₀ = zornStar Z₀`, then `G2BdGOrbit.firstOrderFlow D Z₀ t = zornStar (G2BdGOrbit.firstOrderFlow D Z₀ t)`. -/
theorem bdgOrbit_selfAdjoint
    (D : Zorn ℂ → Zorn ℂ)
    (_hD : ZornVectorMatrixAlgebra.IsZornDerivation D)
    (hstar : ∀ Z : Zorn ℂ, D (zornStar Z) = zornStar (D Z))
    (Z₀ : Zorn ℂ)
    (hZ₀ : zornStar Z₀ = Z₀)
    (t : ℂ) :
    zornStar (G2BdGOrbit.firstOrderFlow D Z₀ t) =
      G2BdGOrbit.firstOrderFlow D Z₀ t := by
  have hD₀ : D Z₀ = zornStar (D Z₀) := by
    rw [← hstar Z₀, hZ₀]
  apply congrArg zornStar at hD₀
  rw [zornStar_involutive] at hD₀
  have hZₐ : Z₀.b = Z₀.a := by
    exact congrArg Zorn.a hZ₀
  have hZᵤ (i : Fin 3) : -Z₀.u i = Z₀.u i := by
    exact congrArg (fun Z : Zorn ℂ => Z.u i) hZ₀
  have hZᵥ (i : Fin 3) : -Z₀.v i = Z₀.v i := by
    exact congrArg (fun Z : Zorn ℂ => Z.v i) hZ₀
  have hDₐ : (D Z₀).b = (D Z₀).a := by
    exact congrArg Zorn.a hD₀
  have hDᵤ (i : Fin 3) : -(D Z₀).u i = (D Z₀).u i := by
    exact congrArg (fun Z : Zorn ℂ => Z.u i) hD₀
  have hDᵥ (i : Fin 3) : -(D Z₀).v i = (D Z₀).v i := by
    exact congrArg (fun Z : Zorn ℂ => Z.v i) hD₀
  have hstar_add (X Y : Zorn ℂ) :
      zornStar (X + Y) = zornStar X + zornStar Y := by
    cases X with
    | mk Xa Xu Xv Xb =>
      cases Y with
      | mk Ya Yu Yv Yb =>
        ext i
        · rfl
        · change -(Xu i + Yu i) = -Xu i + -Yu i
          ring
        · change -(Xv i + Yv i) = -Xv i + -Yv i
          ring
        · rfl
  have hstar_smul (c : ℂ) (X : Zorn ℂ) :
      zornStar (c • X) = c • zornStar X := by
    cases X with
    | mk Xa Xu Xv Xb =>
      ext i
      · rfl
      · change -(c * Xu i) = c * (-Xu i)
        ring
      · change -(c * Xv i) = c * (-Xv i)
        ring
      · rfl
  dsimp [G2BdGOrbit.firstOrderFlow]
  rw [hstar_add, hstar_smul, hZ₀, hD₀]

/-- THEOREM: A particle-hole-compatible seed stays particle-hole-compatible along the orbit.
    If `Z₀` satisfies `zornStar Z₀ = Z₀`, then the first-order flow preserves that relation. -/
theorem bdgOrbit_particleHole
    (D : Zorn ℂ → Zorn ℂ)
    (hD : ZornVectorMatrixAlgebra.IsZornDerivation D)
    (hstar : ∀ Z : Zorn ℂ, D (zornStar Z) = zornStar (D Z))
    (Z₀ : Zorn ℂ)
    (hZ₀ : zornStar Z₀ = Z₀)
    (t : ℂ) :
    zornStar (G2BdGOrbit.firstOrderFlow D Z₀ t) =
      G2BdGOrbit.firstOrderFlow D Z₀ t :=
  bdgOrbit_selfAdjoint D hD hstar Z₀ hZ₀ t

theorem bdgCompatible_preserved_of_derivation_commutes_star
    (D : Zorn ℂ → Zorn ℂ)
    (hD : ZornVectorMatrixAlgebra.IsZornDerivation D)
    (hstar : ∀ Z : Zorn ℂ, D (zornStar Z) = zornStar (D Z))
    (Z₀ : Zorn ℂ)
    (hZ₀ : zornStar Z₀ = Z₀)
    (t : ℂ) :
    zornStar (G2BdGOrbit.firstOrderFlow D Z₀ t) =
      G2BdGOrbit.firstOrderFlow D Z₀ t :=
  bdgOrbit_particleHole D hD hstar Z₀ hZ₀ t

theorem bdgOrbit_preserves_reducedNorm
    (D : Zorn ℂ → Zorn ℂ)
    (_hD : ZornVectorMatrixAlgebra.IsZornDerivation D)
    (Z₀ : Zorn ℂ)
    (hD₀ : D Z₀ = ⟨0, fun _ => 0, fun _ => 0, 0⟩)
    (t : ℂ) :
    zornNorm (G2BdGOrbit.firstOrderFlow D Z₀ t) = zornNorm Z₀ := by
  dsimp [G2BdGOrbit.firstOrderFlow]
  rw [hD₀]
  change zornNorm (Z₀ + t • ⟨0, fun _ => 0, fun _ => 0, 0⟩) = zornNorm Z₀
  cases Z₀ with
  | mk a u v b =>
    change
      (a + t * 0) * (b + t * 0) -
          ((u 0 + t * 0) * (v 0 + t * 0) +
            (u 1 + t * 0) * (v 1 + t * 0) +
            (u 2 + t * 0) * (v 2 + t * 0)) =
        a * b - (u 0 * v 0 + u 1 * v 1 + u 2 * v 2)
    ring

end BdGStarOrbitPreservation

end InfoGeometry.Canonical.ZornBdGDerivationBridge
