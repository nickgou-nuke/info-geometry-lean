import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Matrix

/-!
# Split-Octonion Zorn Algebra, Pauli Soldering, and BdG Derivation Orbits

This module formalizes the three-level architecture:
  Split-Octonion Zorn Algebra ⟶ Pauli Soldering ⟶ Associative BdG Readout

All lemmas and theorems are proven natively in Mathlib with zero `sorry`s and zero custom axioms.
-/

/-!
=============================================================================
PART 1: Pauli Soldering, Dot Products, and Cross Products
=============================================================================
-/

namespace PauliSolderedCrossProductBridge

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
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  ext i j
  fin_cases i <;> fin_cases j
  · simp [mul_apply, Fin.sum_univ_two, sigmaVec, dot3, cross3, smul_apply, add_apply]
    linear_combination -hI * (u 1 * v 1)
  · simp [mul_apply, Fin.sum_univ_two, sigmaVec, dot3, cross3, smul_apply, add_apply]
    linear_combination -hI * (u 0 * v 2 - u 2 * v 0)
  · simp [mul_apply, Fin.sum_univ_two, sigmaVec, dot3, cross3, smul_apply, add_apply]
    linear_combination -hI * (u 2 * v 0 - u 0 * v 2)
  · simp [mul_apply, Fin.sum_univ_two, sigmaVec, dot3, cross3, smul_apply, add_apply]
    linear_combination -hI * (u 1 * v 1)

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
    simp [sigmaVec, dot3, cross3, smul_apply, add_apply] <;> ring

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
    simp [sigmaVec, dot3, cross3, smul_apply, sub_apply] <;> ring

end PauliSolderedCrossProductBridge

/-!
=============================================================================
PART 2: The Split-Octonion Zorn Matrix Algebra
=============================================================================
-/

namespace ZornVectorMatrixAlgebra

open PauliSolderedCrossProductBridge

/-- A Split Octonion in Zorn vector-matrix presentation: [[a, u], [v, b]] -/
structure Zorn (R : Type*) where
  a : R
  u : Fin 3 → R
  v : Fin 3 → R
  b : R

variable {R : Type*} [CommRing R]

theorem zorn_ext (X Y : Zorn R)
    (ha : X.a = Y.a)
    (hu : ∀ i, X.u i = Y.u i)
    (hv : ∀ i, X.v i = Y.v i)
    (hb : X.b = Y.b) : X = Y := by
  cases X; cases Y; congr
  · exact funext hu
  · exact funext hv

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

/-- THEOREM: Left multiplication by 1 is the identity -/
@[simp]
theorem zorn_one_mul (X : Zorn R) : (1 : Zorn R) * X = X := by
  rcases X with ⟨Xa, Xu, Xv, Xb⟩
  apply zorn_ext
  · show (1 : R) * Xa + dotR (fun _ => (0 : R)) Xv = Xa
    dsimp [dotR]; ring
  · intro i
    fin_cases i
    · show (1 : R) * Xu 0 + Xb * (0 : R) - crossR (fun _ => (0 : R)) Xv 0 = Xu 0
      dsimp [crossR]; ring
    · show (1 : R) * Xu 1 + Xb * (0 : R) - crossR (fun _ => (0 : R)) Xv 1 = Xu 1
      dsimp [crossR]; ring
    · show (1 : R) * Xu 2 + Xb * (0 : R) - crossR (fun _ => (0 : R)) Xv 2 = Xu 2
      dsimp [crossR]; ring
  · intro i
    fin_cases i
    · show Xa * (0 : R) + (1 : R) * Xv 0 + crossR (fun _ => (0 : R)) Xu 0 = Xv 0
      dsimp [crossR]; ring
    · show Xa * (0 : R) + (1 : R) * Xv 1 + crossR (fun _ => (0 : R)) Xu 1 = Xv 1
      dsimp [crossR]; ring
    · show Xa * (0 : R) + (1 : R) * Xv 2 + crossR (fun _ => (0 : R)) Xu 2 = Xv 2
      dsimp [crossR]; ring
  · show (1 : R) * Xb + dotR (fun _ => (0 : R)) Xu = Xb
    dsimp [dotR]; ring

/-- THEOREM: Right multiplication by 1 is the identity -/
@[simp]
theorem zorn_mul_one (X : Zorn R) : X * (1 : Zorn R) = X := by
  rcases X with ⟨Xa, Xu, Xv, Xb⟩
  apply zorn_ext
  · show Xa * (1 : R) + dotR Xu (fun _ => (0 : R)) = Xa
    dsimp [dotR]; ring
  · intro i
    fin_cases i
    · show Xa * (0 : R) + (1 : R) * Xu 0 - crossR Xv (fun _ => (0 : R)) 0 = Xu 0
      dsimp [crossR]; ring
    · show Xa * (0 : R) + (1 : R) * Xu 1 - crossR Xv (fun _ => (0 : R)) 1 = Xu 1
      dsimp [crossR]; ring
    · show Xa * (0 : R) + (1 : R) * Xu 2 - crossR Xv (fun _ => (0 : R)) 2 = Xu 2
      dsimp [crossR]; ring
  · intro i
    fin_cases i
    · show (1 : R) * Xv 0 + Xb * (0 : R) + crossR Xu (fun _ => (0 : R)) 0 = Xv 0
      dsimp [crossR]; ring
    · show (1 : R) * Xv 1 + Xb * (0 : R) + crossR Xu (fun _ => (0 : R)) 1 = Xv 1
      dsimp [crossR]; ring
    · show (1 : R) * Xv 2 + Xb * (0 : R) + crossR Xu (fun _ => (0 : R)) 2 = Xv 2
      dsimp [crossR]; ring
  · show Xb * (1 : R) + dotR Xv (fun _ => (0 : R)) = Xb
    dsimp [dotR]; ring

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
    D 1 = ⟨0, fun _ => 0, fun _ => 0, 0⟩ := by
  have h := hD.2.2 1 1
  have h1 : (1 : Zorn R) * 1 = 1 := zorn_mul_one 1
  rw [h1, zorn_mul_one, zorn_one_mul] at h
  have h_cancel : ∀ x : R, x = x + x → x = 0 := by
    intro x hx
    have h2 : x + x = x + 0 := by rw [add_zero, ← hx]
    exact add_left_cancel h2
  apply zorn_ext
  · have ha : (D 1).a = (D 1).a + (D 1).a := congrArg Zorn.a h
    exact h_cancel _ ha
  · intro i
    have hu : (D 1).u i = (D 1).u i + (D 1).u i := congrArg (fun Z : Zorn R => Z.u i) h
    exact h_cancel _ hu
  · intro i
    have hv : (D 1).v i = (D 1).v i + (D 1).v i := congrArg (fun Z : Zorn R => Z.v i) h
    exact h_cancel _ hv
  · have hb : (D 1).b = (D 1).b + (D 1).b := congrArg Zorn.b h
    exact h_cancel _ hb

/-- THEOREM: Every central scalar seed (c • 1) is strictly annihilated by all derivations -/
theorem derivation_annihilates_scalar_seed (D : Zorn R → Zorn R) (hD : IsZornDerivation D) (c : R) :
    D (c • (1 : Zorn R)) = ⟨0, fun _ => 0, fun _ => 0, 0⟩ := by
  rw [hD.2.1 c 1, derivation_annihilates_one D hD]
  apply zorn_ext
  · show c * (0 : R) = 0; ring
  · intro i; show c * (0 : R) = 0; ring
  · intro i; show c * (0 : R) = 0; ring
  · show c * (0 : R) = 0; ring

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
theorem bdgReadout_block11 (Z : Zorn ℂ) :
    block11 (bdgReadout Z) = Z.a • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [block11, bdgReadout]

@[simp]
theorem bdgReadout_block22 (Z : Zorn ℂ) :
    block22 (bdgReadout Z) = Z.b • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [block22, bdgReadout]

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
    apply zorn_ext
    · show a = a * 1; ring
    · intro i; show (0 : ℂ) = a * 0; ring
    · intro i; show (0 : ℂ) = a * 0; ring
    · show a = a * 1; ring
  have h_flow : firstOrderFlow D (normalSeed a a) t = normalSeed a a := by
    dsimp [firstOrderFlow]
    rw [h_seed, derivation_annihilates_scalar_seed D hD a]
    apply zorn_ext
    · show (a • (1 : Zorn ℂ)).a + t * (0 : ℂ) = (a • (1 : Zorn ℂ)).a; ring
    · intro i; show (a • (1 : Zorn ℂ)).u i + t * (0 : ℂ) = (a • (1 : Zorn ℂ)).u i; ring
    · intro i; show (a • (1 : Zorn ℂ)).v i + t * (0 : ℂ) = (a • (1 : Zorn ℂ)).v i; ring
    · show (a • (1 : Zorn ℂ)).b + t * (0 : ℂ) = (a • (1 : Zorn ℂ)).b; ring
  rw [h_flow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [block12, bdgReadout, normalSeed]

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
  fin_cases i <;> fin_cases j
  · show (0 : ℂ) + t * (D (normalSeed a b)).u 2 = t * (D (normalSeed a b)).u 2
    ring
  · show (0 : ℂ) + t * (D (normalSeed a b)).u 0 - Complex.I * ((0 : ℂ) + t * (D (normalSeed a b)).u 1) =
      t * ((D (normalSeed a b)).u 0 - Complex.I * (D (normalSeed a b)).u 1)
    ring
  · show (0 : ℂ) + t * (D (normalSeed a b)).u 0 + Complex.I * ((0 : ℂ) + t * (D (normalSeed a b)).u 1) =
      t * ((D (normalSeed a b)).u 0 + Complex.I * (D (normalSeed a b)).u 1)
    ring
  · show -((0 : ℂ) + t * (D (normalSeed a b)).u 2) = t * (- (D (normalSeed a b)).u 2)
    ring

end G2BdGOrbit
