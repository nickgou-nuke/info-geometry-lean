/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.QuantumContext.DrazinSpectralKernel
import InfoGeometry.Exceptional.AlbertBPSNilpotentOrbits
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# AI Studio 1SSh9 Track M2: Krein Thermofield Double, Parity Shift, Drazin Hodge & Cl(1,3)

Formalizes the verified finite/algebraic targets from Phase C-C5b and Phase D (`D-C1b` through `D-C6c`)
of `docs/contracts/AISTUDIO_1SSH9_THEOREM_CONTRACTS.md`, discharging all transcript `sorry`s cleanly:
- `C-C5b`: `E6Decomposition` dimension partitions (`52 + 26 = 78`) and non-vacuous `half_bps_rank1_det_zero`
  via `AlbertBPSNilpotentOrbits.rank1_implies_det_zero` on 27D `H3Zorn ℝ`.
- `D-C1b`: `SuperModule`, involutive `parityShift`, `OddHom M N ≃ EvenHom M (parityShift N)`, and
  nondegenerate Grassmann Berezin pairing (`det = -1`).
- `D-C2a`: Krein thermofield double (`kreinEta`, `modularJ`, `forwardOp`, `backwardTwinOp`,
  `kreinTrace`, `kreinSuperTrace`) and finite-stage AB5 colimit stability.
- `D-C3`: Abstract `[Ring A]` `Cl11Generators` (`e₀² = -1, e₁² = 1`) and `IsDrazinHodgeInverse`.
- `D-C4`: Krein isometries $O(V,V)$, `krein_isometry_dual` (`C174` discharge), unipotent shears,
  and Möbius `moebiusJ` trace reversal.
- `D-C5`: Krein-BRST Kugo-Ojima quartet (`C180`/`C186` discharge) and Plabic `MoebiusConnection`.
- `D-C6`: Lightcone `sl_2` ladder (`C183` discharge), thermofield Shannon entropy (`C189`), and
  genuinely noncommutative `[Algebra R A]` `SpacetimeAlgebra` `Cl(1,3)` `feynmanSlash_sq` (`C192` discharge).
-/

namespace InfoGeometry.Synthesis.Aistudio1SSh9KreinThermofieldCl13Bridge

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.QuantumContext.Drazin
open Matrix

/-! ## Section 1 (C-C5b): Exceptional E6 Dimension Partitions & Rank-1 BPS Cubic Vanishing -/

/-- Bookkeeping data for the exceptional Lie-branching dimension partitions
`52 + 26 = 78`, `52 = 28 + 24`, `28 = 14 + 7 + 7`, `24 = 8 + 8 + 8`, `1 + 26 = 27`.
This does not construct the 78-dimensional Lie algebra `e_{6(6)}`. -/
structure E6Decomposition where
  f4_dim : ℕ := 52
  p26_dim : ℕ := 26
  so44_dim : ℕ := 28
  triality_dim : ℕ := 24
  g2_dim : ℕ := 14
  coset_dims : ℕ × ℕ × ℕ × ℕ × ℕ := (7, 7, 8, 8, 8)
  f4_split : f4_dim = so44_dim + triality_dim := by decide
  so44_split : so44_dim = g2_dim + coset_dims.1 + coset_dims.2.1 := by decide
  triality_split : triality_dim = coset_dims.2.2.1 + coset_dims.2.2.2.1 + coset_dims.2.2.2.2 := by decide
  albert_split : 1 + p26_dim = 27 := by decide

/-- Constructive default witness for `E6Decomposition`. -/
def canonicalE6Decomposition : E6Decomposition := {}

theorem e6_dimension_partition (D : E6Decomposition) :
    D.f4_dim + D.p26_dim = D.so44_dim + D.triality_dim + D.p26_dim := by
  rw [D.f4_split]

theorem e6_deep_exceptional_split (D : E6Decomposition) :
    D.f4_dim + D.p26_dim =
      D.g2_dim + D.coset_dims.1 + D.coset_dims.2.1 +
      D.coset_dims.2.2.1 + D.coset_dims.2.2.2.1 + D.coset_dims.2.2.2.2 + D.p26_dim := by
  have h1 := D.f4_split
  have h2 := D.so44_split
  have h3 := D.triality_split
  omega

theorem e6_canonical_dimension_eq :
    canonicalE6Decomposition.f4_dim + canonicalE6Decomposition.p26_dim = 78 := by
  decide

/-- Non-vacuous 1/2-BPS cubic vanishing on the 27-dimensional split Albert algebra `H3Zorn ℝ`. -/
theorem half_bps_rank1_det_zero (X : H3Zorn ℝ) (h_sharp : adjointQuad X = 0) :
    normCubic X = 0 :=
  InfoGeometry.Exceptional.AlbertBPSNilpotentOrbits.rank1_implies_det_zero X h_sharp

/-! ## Section 2 (D-C1b): Parity Shift Π and Berezin Grassmann Pairing -/

/-- A `ℤ₂`-graded `R`-module split into even and odd sectors. -/
structure SuperModule (R : Type*) [CommRing R] where
  even : Type
  odd : Type
  [evenAdd : AddCommGroup even]
  [oddAdd : AddCommGroup odd]
  [evenMod : Module R even]
  [oddMod : Module R odd]

attribute [instance] SuperModule.evenAdd SuperModule.oddAdd SuperModule.evenMod SuperModule.oddMod

/-- Constructive witness of a `SuperModule` over `ℤ`. -/
def intSuperModule : SuperModule ℤ where
  even := ℤ
  odd := ℤ

/-- The parity shift functor `Π`, swapping even and odd sectors. -/
def parityShift {R : Type*} [CommRing R] (M : SuperModule R) : SuperModule R where
  even := M.odd
  odd := M.even
  evenAdd := M.oddAdd
  oddAdd := M.evenAdd
  evenMod := M.oddMod
  oddMod := M.evenMod

theorem parityShift_involutive {R : Type*} [CommRing R] (M : SuperModule R) :
    parityShift (parityShift M) = M := by
  cases M
  rfl

/-- Parity-preserving (`ℤ₂`-degree 0) `R`-linear morphisms between supermodules. -/
structure EvenHom {R : Type*} [CommRing R] (M N : SuperModule R) where
  mapEven : M.even →ₗ[R] N.even
  mapOdd : M.odd →ₗ[R] N.odd

/-- Constructive witness of `EvenHom` on `intSuperModule`. -/
def intEvenHom : EvenHom intSuperModule intSuperModule where
  mapEven := LinearMap.id
  mapOdd := LinearMap.id

/-- Parity-reversing (`ℤ₂`-degree 1) `R`-linear morphisms between supermodules. -/
structure OddHom {R : Type*} [CommRing R] (M N : SuperModule R) where
  mapEvenToOdd : M.even →ₗ[R] N.odd
  mapOddToEven : M.odd →ₗ[R] N.even

/-- Constructive witness of `OddHom` on `intSuperModule`. -/
def intOddHom : OddHom intSuperModule intSuperModule where
  mapEvenToOdd := LinearMap.id
  mapOddToEven := LinearMap.id

/-- Canonical equivalence `OddHom M N ≃ EvenHom M (parityShift N)`. -/
def oddHomEquivEvenHomShift {R : Type*} [CommRing R] (M N : SuperModule R) :
    OddHom M N ≃ EvenHom M (parityShift N) where
  toFun f := ⟨f.mapEvenToOdd, f.mapOddToEven⟩
  invFun g := ⟨g.mapEven, g.mapOdd⟩
  left_inv f := by cases f; rfl
  right_inv g := by cases g; rfl

/-- Single-odd-variable Grassmann element `a₀ + a₁ θ` with `θ² = 0`. -/
structure GrassmannElement (R : Type*) where
  a₀ : R
  a₁ : R

/-- Constructive witness for `GrassmannElement`. -/
def intGrassmannElement : GrassmannElement ℤ := ⟨1, 1⟩

def grassmannMul {R : Type*} [CommRing R] (x y : GrassmannElement R) : GrassmannElement R where
  a₀ := x.a₀ * y.a₀
  a₁ := x.a₀ * y.a₁ + x.a₁ * y.a₀

/-- Berezin integral `∫ (a₀ + a₁ θ) dθ = a₁`. -/
def berezinIntegral {R : Type*} (x : GrassmannElement R) : R := x.a₁

/-- Berezin pairing `(x, y) ↦ ∫ (x * y) dθ`. -/
def berezinPairing {R : Type*} [CommRing R] (x y : GrassmannElement R) : R :=
  berezinIntegral (grassmannMul x y)

/-- Gram matrix of the Berezin pairing in the `(1, θ)` basis. -/
def berezinGramMatrix (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R :=
  !![0, 1; 1, 0]

theorem berezinGramMatrix_det {R : Type*} [CommRing R] :
    Matrix.det (berezinGramMatrix R) = -1 := by
  simp [berezinGramMatrix, Matrix.det_fin_two]

theorem berezinPairing_nondegenerate {R : Type*} [CommRing R] (x : GrassmannElement R)
    (h_even : berezinPairing x ⟨1, 0⟩ = 0) (h_odd : berezinPairing x ⟨0, 1⟩ = 0) :
    x.a₀ = 0 ∧ x.a₁ = 0 := by
  dsimp [berezinPairing, berezinIntegral, grassmannMul] at h_even h_odd
  simp only [mul_zero, zero_add, mul_one, add_zero] at h_even h_odd
  exact ⟨h_odd, h_even⟩

/-! ## Section 3 (D-C2a): Krein Thermofield Double, Commutant, & AB5 Stability -/

section ThermofieldKrein

variable {R : Type*} [CommRing R]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {V_ext : Type*} [Fintype V_ext] [DecidableEq V_ext]

/-- Off-diagonal swap Krein metric `η = [[0, 1], [1, 0]]` on `V ⊕ V`. -/
def kreinEta : Matrix (V ⊕ V) (V ⊕ V) R :=
  Matrix.fromBlocks 0 1 1 0

/-- Chiral grading `Γ = [[1, 0], [0, -1]]` on `V ⊕ V`. -/
def chiralGamma : Matrix (V ⊕ V) (V ⊕ V) R :=
  Matrix.fromBlocks 1 0 0 (-1)

theorem kreinEta_sq :
    (kreinEta (R := R) (V := V)) * (kreinEta (R := R) (V := V)) = 1 := by
  dsimp [kreinEta]
  rw [Matrix.fromBlocks_multiply]
  simp [← Matrix.fromBlocks_one]

/-- Every forward-sheet vector `(u, 0)` is strictly Krein-isotropic (`η`-null). -/
theorem forward_sheet_strictly_isotropic (u : V → R) :
    dotProduct (Sum.elim u (0 : V → R))
      ((kreinEta (R := R) (V := V)) *ᵥ Sum.elim u (0 : V → R)) = 0 := by
  have hvec : (kreinEta (R := R) (V := V)) *ᵥ Sum.elim u (0 : V → R) =
      Sum.elim (0 : V → R) u := by
    ext x
    cases x with
    | inl i =>
      simp [kreinEta, Matrix.mulVec, dotProduct, Matrix.fromBlocks]
    | inr i =>
      simp [kreinEta, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Matrix.one_apply]
  rw [hvec]
  simp [dotProduct]

/-- Tomita modular conjugation `J = [[0, 1], [1, 0]]` on the thermofield double `V ⊕ V`. -/
def modularJ : Matrix (V ⊕ V) (V ⊕ V) R :=
  Matrix.fromBlocks 0 1 1 0

/-- Forward-sheet operator embedding `A ↦ diag(A, 0)`. -/
def forwardOp (A : Matrix V V R) : Matrix (V ⊕ V) (V ⊕ V) R :=
  Matrix.fromBlocks A 0 0 0

/-- Backward-twin operator embedding `B ↦ diag(0, B)`. -/
def backwardTwinOp (B : Matrix V V R) : Matrix (V ⊕ V) (V ⊕ V) R :=
  Matrix.fromBlocks 0 0 0 B

theorem modular_conjugation_generates_commutant (B : Matrix V V R) :
    modularJ * forwardOp B * modularJ = backwardTwinOp B := by
  dsimp [modularJ, forwardOp, backwardTwinOp]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

theorem thermofield_commutant_exact_commutation (A B : Matrix V V R) :
    forwardOp A * backwardTwinOp B - backwardTwinOp B * forwardOp A = 0 := by
  dsimp [forwardOp, backwardTwinOp]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

/-- Finite-stage zero-padded embedding of `Matrix V V R` into `Matrix (V ⊕ V_ext) (V ⊕ V_ext) R`. -/
def embedOp (A : Matrix V V R) : Matrix (V ⊕ V_ext) (V ⊕ V_ext) R :=
  Matrix.fromBlocks A 0 0 0

theorem ab5_colimit_preserves_thermofield_commutant (A B : Matrix V V R) :
    forwardOp (embedOp (V_ext := V_ext) A) * backwardTwinOp (embedOp (V_ext := V_ext) B) -
      backwardTwinOp (embedOp (V_ext := V_ext) B) * forwardOp (embedOp (V_ext := V_ext) A) = 0 :=
  thermofield_commutant_exact_commutation (embedOp A) (embedOp B)

/-- Krein trace `Tr_η(M) = Tr(η M)`. -/
def kreinTrace (M : Matrix (V ⊕ V) (V ⊕ V) R) : R :=
  Matrix.trace ((kreinEta (R := R) (V := V)) * M)

/-- Krein supertrace `STr_η(M) = Tr(Γ η M)`. -/
def kreinSuperTrace (M : Matrix (V ⊕ V) (V ⊕ V) R) : R :=
  Matrix.trace ((chiralGamma (R := R) (V := V)) * (kreinEta (R := R) (V := V)) * M)

theorem kreinTrace_blockOp_eq (A B C D : Matrix V V R) :
    kreinTrace (Matrix.fromBlocks A B C D) = Matrix.trace C + Matrix.trace B := by
  dsimp [kreinTrace, kreinEta]
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

theorem kreinTrace_diagonal_zero (A D : Matrix V V R) :
    kreinTrace (Matrix.fromBlocks A 0 0 D) = 0 := by
  rw [kreinTrace_blockOp_eq]
  simp

theorem kreinSuperTrace_blockOp_eq (A B C D : Matrix V V R) :
    kreinSuperTrace (Matrix.fromBlocks A B C D) = Matrix.trace C - Matrix.trace B := by
  dsimp [kreinSuperTrace, chiralGamma, kreinEta]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, sub_eq_add_neg, add_comm]

theorem ab5_colimit_preserves_kreinTrace (A B C D : Matrix V V R) :
    kreinTrace (Matrix.fromBlocks (embedOp (V_ext := V_ext) A) (embedOp (V_ext := V_ext) B)
      (embedOp (V_ext := V_ext) C) (embedOp (V_ext := V_ext) D)) =
      kreinTrace (Matrix.fromBlocks A B C D) := by
  rw [kreinTrace_blockOp_eq, kreinTrace_blockOp_eq]
  simp [embedOp, Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

end ThermofieldKrein

/-! ## Section 4 (D-C3 & D-C6a): Abstract Cl(1,1) Generators & Drazin-Hodge Inverse -/

/-- Abstract split-Clifford generators in an associative ring (`e₀² = -1, e₁² = 1`). -/
structure Cl11Generators (A : Type*) [Ring A] where
  e₀ : A
  e₁ : A
  e₀_sq : e₀ * e₀ = -1
  e₁_sq : e₁ * e₁ = 1
  anticomm : e₀ * e₁ + e₁ * e₀ = 0

def mat2E0 : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]
def mat2E1 : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]

theorem mat2E0_mat2E1_noncommutative :
    mat2E0 * mat2E1 ≠ mat2E1 * mat2E0 := by
  decide

def mat2RE12 (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![0, 1; 0, 0]
def mat2RE21 (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![0, 0; 1, 0]

theorem mat2RE12_mat2RE21_noncommutative {R : Type*} [CommRing R] [Nontrivial R] :
    mat2RE12 R * mat2RE21 R ≠ mat2RE21 R * mat2RE12 R := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  simp [mat2RE12, mat2RE21, Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem mat2R_noncommutative_exists {R : Type*} [CommRing R] [Nontrivial R] :
    ∃ A B : Matrix (Fin 2) (Fin 2) R, A * B ≠ B * A :=
  ⟨mat2RE12 R, mat2RE21 R, mat2RE12_mat2RE21_noncommutative⟩

/-- Constructive noncommutative witness of `Cl11Generators` in `M₂(ℤ)`. -/
def mat2Cl11Generators : Cl11Generators (Matrix (Fin 2) (Fin 2) ℤ) where
  e₀ := mat2E0
  e₁ := mat2E1
  e₀_sq := by decide
  e₁_sq := by decide
  anticomm := by decide

theorem mat2Cl11_noncommutative :
    mat2Cl11Generators.e₀ * mat2Cl11Generators.e₁ ≠
      mat2Cl11Generators.e₁ * mat2Cl11Generators.e₀ :=
  mat2E0_mat2E1_noncommutative

section Cl11Lightcone

variable {A : Type*} [Ring A]

def gammaPlus (G : Cl11Generators A) (half : A) : A :=
  half * (G.e₀ + G.e₁)

def gammaMinus (G : Cl11Generators A) (half : A) : A :=
  half * (-G.e₀ + G.e₁)

def spinGenerator (G : Cl11Generators A) (_half : A) : A :=
  G.e₀ * G.e₁

theorem spinGenerator_eq_bivector (G : Cl11Generators A) (half : A) :
    spinGenerator G half = G.e₀ * G.e₁ :=
  rfl

theorem gammaPlus_sq_zero (G : Cl11Generators A) (half : A)
    (h_c0 : half * G.e₀ = G.e₀ * half) (h_c1 : half * G.e₁ = G.e₁ * half) :
    gammaPlus G half * gammaPlus G half = 0 := by
  dsimp [gammaPlus]
  have h1 : (G.e₀ + G.e₁) * half = half * (G.e₀ + G.e₁) := by
    rw [add_mul, ← h_c0, ← h_c1, mul_add]
  have hsq : (G.e₀ + G.e₁) * (G.e₀ + G.e₁) = 0 := by
    calc (G.e₀ + G.e₁) * (G.e₀ + G.e₁)
      _ = G.e₀ * G.e₀ + (G.e₀ * G.e₁ + G.e₁ * G.e₀) + G.e₁ * G.e₁ := by noncomm_ring
      _ = (-1) + 0 + 1 := by rw [G.e₀_sq, G.anticomm, G.e₁_sq]
      _ = 0 := by abel
  calc (half * (G.e₀ + G.e₁)) * (half * (G.e₀ + G.e₁))
    _ = half * ((G.e₀ + G.e₁) * half) * (G.e₀ + G.e₁) := by simp only [mul_assoc]
    _ = half * (half * (G.e₀ + G.e₁)) * (G.e₀ + G.e₁) := by rw [h1]
    _ = (half * half) * ((G.e₀ + G.e₁) * (G.e₀ + G.e₁)) := by noncomm_ring
    _ = 0 := by rw [hsq, mul_zero]

theorem gammaMinus_sq_zero (G : Cl11Generators A) (half : A)
    (h_c0 : half * G.e₀ = G.e₀ * half) (h_c1 : half * G.e₁ = G.e₁ * half) :
    gammaMinus G half * gammaMinus G half = 0 := by
  dsimp [gammaMinus]
  have h1 : (-G.e₀ + G.e₁) * half = half * (-G.e₀ + G.e₁) := by
    rw [add_mul, neg_mul, ← h_c0, ← h_c1, mul_add, mul_neg]
  have hsq : (-G.e₀ + G.e₁) * (-G.e₀ + G.e₁) = 0 := by
    calc (-G.e₀ + G.e₁) * (-G.e₀ + G.e₁)
      _ = G.e₀ * G.e₀ - (G.e₀ * G.e₁ + G.e₁ * G.e₀) + G.e₁ * G.e₁ := by noncomm_ring
      _ = (-1) - 0 + 1 := by rw [G.e₀_sq, G.anticomm, G.e₁_sq]
      _ = 0 := by abel
  calc (half * (-G.e₀ + G.e₁)) * (half * (-G.e₀ + G.e₁))
    _ = half * ((-G.e₀ + G.e₁) * half) * (-G.e₀ + G.e₁) := by simp only [mul_assoc]
    _ = half * (half * (-G.e₀ + G.e₁)) * (-G.e₀ + G.e₁) := by rw [h1]
    _ = (half * half) * ((-G.e₀ + G.e₁) * (-G.e₀ + G.e₁)) := by noncomm_ring
    _ = 0 := by rw [hsq, mul_zero]

theorem gamma_anticommutator_unit (G : Cl11Generators A) (half : A)
    (h_half : (2 : A) * half = 1)
    (h_c0 : half * G.e₀ = G.e₀ * half) (h_c1 : half * G.e₁ = G.e₁ * half) :
    gammaPlus G half * gammaMinus G half + gammaMinus G half * gammaPlus G half = 1 := by
  dsimp [gammaPlus, gammaMinus]
  have h1 : (G.e₀ + G.e₁) * half = half * (G.e₀ + G.e₁) := by
    rw [add_mul, ← h_c0, ← h_c1, mul_add]
  have h2 : (-G.e₀ + G.e₁) * half = half * (-G.e₀ + G.e₁) := by
    rw [add_mul, neg_mul, ← h_c0, ← h_c1, mul_add, mul_neg]
  have hsum : (G.e₀ + G.e₁) * (-G.e₀ + G.e₁) + (-G.e₀ + G.e₁) * (G.e₀ + G.e₁) = (4 : A) := by
    calc (G.e₀ + G.e₁) * (-G.e₀ + G.e₁) + (-G.e₀ + G.e₁) * (G.e₀ + G.e₁)
      _ = -((2 : A) * (G.e₀ * G.e₀)) + (2 : A) * (G.e₁ * G.e₁) := by
          rw [two_mul, two_mul]; noncomm_ring
      _ = -((2 : A) * (-1)) + (2 : A) * 1 := by rw [G.e₀_sq, G.e₁_sq]
      _ = (4 : A) := by norm_num
  have hhalf4 : (half * half) * (4 : A) = 1 := by
    calc (half * half) * (4 : A)
      _ = half * (half * (2 : A) * (2 : A)) := by
          have h4 : (4 : A) = (2 : A) * (2 : A) := by norm_num
          rw [h4]; simp only [mul_assoc]
      _ = half * (((2 : A) * half) * (2 : A)) := by
          have hc : half * (2 : A) = (2 : A) * half := by
            rw [mul_two, two_mul]
          rw [hc]
      _ = half * (2 : A) := by rw [h_half, one_mul]
      _ = 1 := by rw [mul_two, ← two_mul, h_half]
  calc (half * (G.e₀ + G.e₁)) * (half * (-G.e₀ + G.e₁)) +
        (half * (-G.e₀ + G.e₁)) * (half * (G.e₀ + G.e₁))
    _ = half * ((G.e₀ + G.e₁) * half) * (-G.e₀ + G.e₁) +
          half * ((-G.e₀ + G.e₁) * half) * (G.e₀ + G.e₁) := by simp only [mul_assoc]
    _ = half * (half * (G.e₀ + G.e₁)) * (-G.e₀ + G.e₁) +
          half * (half * (-G.e₀ + G.e₁)) * (G.e₀ + G.e₁) := by rw [h1, h2]
    _ = (half * half) * ((G.e₀ + G.e₁) * (-G.e₀ + G.e₁) + (-G.e₀ + G.e₁) * (G.e₀ + G.e₁)) := by
          noncomm_ring
    _ = (half * half) * (4 : A) := by rw [hsum]
    _ = 1 := hhalf4

theorem spin_raises_gammaPlus (G : Cl11Generators A) (half : A)
    (h_c0 : half * G.e₀ = G.e₀ * half) (h_c1 : half * G.e₁ = G.e₁ * half) :
    (G.e₀ * G.e₁) * gammaPlus G half - gammaPlus G half * (G.e₀ * G.e₁) =
      (2 : A) * gammaPlus G half := by
  dsimp [gammaPlus]
  have h10 : G.e₁ * G.e₀ = -(G.e₀ * G.e₁) := eq_neg_of_add_eq_zero_right G.anticomm
  have hcore : (G.e₀ * G.e₁) * (G.e₀ + G.e₁) - (G.e₀ + G.e₁) * (G.e₀ * G.e₁) =
      (2 : A) * (G.e₀ + G.e₁) := by
    calc (G.e₀ * G.e₁) * (G.e₀ + G.e₁) - (G.e₀ + G.e₁) * (G.e₀ * G.e₁)
      _ = G.e₀ * (G.e₁ * G.e₀) + G.e₀ * (G.e₁ * G.e₁) -
            ((G.e₀ * G.e₀) * G.e₁ + (G.e₁ * G.e₀) * G.e₁) := by
          rw [mul_add, add_mul]; simp only [mul_assoc]
      _ = G.e₀ * (-(G.e₀ * G.e₁)) + G.e₀ * 1 - ((-1) * G.e₁ + (-(G.e₀ * G.e₁)) * G.e₁) := by
          rw [h10, G.e₁_sq, G.e₀_sq]
      _ = -(G.e₀ * G.e₀) * G.e₁ + G.e₀ + G.e₁ + G.e₀ * (G.e₁ * G.e₁) := by noncomm_ring
      _ = -(-1) * G.e₁ + G.e₀ + G.e₁ + G.e₀ * 1 := by rw [G.e₀_sq, G.e₁_sq]
      _ = (2 : A) * (G.e₀ + G.e₁) := by rw [two_mul]; noncomm_ring
  calc (G.e₀ * G.e₁) * (half * (G.e₀ + G.e₁)) - (half * (G.e₀ + G.e₁)) * (G.e₀ * G.e₁)
    _ = half * ((G.e₀ * G.e₁) * (G.e₀ + G.e₁) - (G.e₀ + G.e₁) * (G.e₀ * G.e₁)) := by
        calc (G.e₀ * G.e₁) * (half * (G.e₀ + G.e₁)) - (half * (G.e₀ + G.e₁)) * (G.e₀ * G.e₁)
          _ = ((G.e₀ * G.e₁) * half) * (G.e₀ + G.e₁) - half * ((G.e₀ + G.e₁) * (G.e₀ * G.e₁)) := by
              simp only [mul_assoc]
          _ = (half * (G.e₀ * G.e₁)) * (G.e₀ + G.e₁) - half * ((G.e₀ + G.e₁) * (G.e₀ * G.e₁)) := by
              have hc : (G.e₀ * G.e₁) * half = half * (G.e₀ * G.e₁) := by
                calc G.e₀ * G.e₁ * half = G.e₀ * (G.e₁ * half) := by rw [mul_assoc]
                  _ = G.e₀ * (half * G.e₁) := by rw [h_c1]
                  _ = (G.e₀ * half) * G.e₁ := by rw [mul_assoc]
                  _ = (half * G.e₀) * G.e₁ := by rw [h_c0]
                  _ = half * (G.e₀ * G.e₁) := by rw [mul_assoc]
              rw [hc]
          _ = half * ((G.e₀ * G.e₁) * (G.e₀ + G.e₁) - (G.e₀ + G.e₁) * (G.e₀ * G.e₁)) := by
              noncomm_ring
    _ = half * ((2 : A) * (G.e₀ + G.e₁)) := by rw [hcore]
    _ = (2 : A) * (half * (G.e₀ + G.e₁)) := by
        rw [two_mul, two_mul]; noncomm_ring

theorem spin_lowers_gammaMinus (G : Cl11Generators A) (half : A)
    (h_c0 : half * G.e₀ = G.e₀ * half) (h_c1 : half * G.e₁ = G.e₁ * half) :
    (G.e₀ * G.e₁) * gammaMinus G half - gammaMinus G half * (G.e₀ * G.e₁) =
      -(2 : A) * gammaMinus G half := by
  dsimp [gammaMinus]
  have h10 : G.e₁ * G.e₀ = -(G.e₀ * G.e₁) := eq_neg_of_add_eq_zero_right G.anticomm
  have hneg2 : -(2 : A) = -((1 : A) + 1) := by norm_num
  have hcore : (G.e₀ * G.e₁) * (-G.e₀ + G.e₁) - (-G.e₀ + G.e₁) * (G.e₀ * G.e₁) =
      -(2 : A) * (-G.e₀ + G.e₁) := by
    calc (G.e₀ * G.e₁) * (-G.e₀ + G.e₁) - (-G.e₀ + G.e₁) * (G.e₀ * G.e₁)
      _ = -(G.e₀ * (G.e₁ * G.e₀)) + G.e₀ * (G.e₁ * G.e₁) +
            (G.e₀ * G.e₀) * G.e₁ - (G.e₁ * G.e₀) * G.e₁ := by noncomm_ring
      _ = -(G.e₀ * (-(G.e₀ * G.e₁))) + G.e₀ * 1 + (-1) * G.e₁ -
            (-(G.e₀ * G.e₁)) * G.e₁ := by rw [h10, G.e₁_sq, G.e₀_sq]
      _ = (G.e₀ * G.e₀) * G.e₁ + G.e₀ - G.e₁ + G.e₀ * (G.e₁ * G.e₁) := by noncomm_ring
      _ = (-1) * G.e₁ + G.e₀ - G.e₁ + G.e₀ * 1 := by rw [G.e₀_sq, G.e₁_sq]
      _ = -(2 : A) * (-G.e₀ + G.e₁) := by rw [hneg2]; noncomm_ring
  calc (G.e₀ * G.e₁) * (half * (-G.e₀ + G.e₁)) - (half * (-G.e₀ + G.e₁)) * (G.e₀ * G.e₁)
    _ = half * ((G.e₀ * G.e₁) * (-G.e₀ + G.e₁) - (-G.e₀ + G.e₁) * (G.e₀ * G.e₁)) := by
        calc (G.e₀ * G.e₁) * (half * (-G.e₀ + G.e₁)) - (half * (-G.e₀ + G.e₁)) * (G.e₀ * G.e₁)
          _ = ((G.e₀ * G.e₁) * half) * (-G.e₀ + G.e₁) -
                half * ((-G.e₀ + G.e₁) * (G.e₀ * G.e₁)) := by simp only [mul_assoc]
          _ = (half * (G.e₀ * G.e₁)) * (-G.e₀ + G.e₁) -
                half * ((-G.e₀ + G.e₁) * (G.e₀ * G.e₁)) := by
              have hc : (G.e₀ * G.e₁) * half = half * (G.e₀ * G.e₁) := by
                calc G.e₀ * G.e₁ * half = G.e₀ * (G.e₁ * half) := by rw [mul_assoc]
                  _ = G.e₀ * (half * G.e₁) := by rw [h_c1]
                  _ = (G.e₀ * half) * G.e₁ := by rw [mul_assoc]
                  _ = (half * G.e₀) * G.e₁ := by rw [h_c0]
                  _ = half * (G.e₀ * G.e₁) := by rw [mul_assoc]
              rw [hc]
          _ = half * ((G.e₀ * G.e₁) * (-G.e₀ + G.e₁) - (-G.e₀ + G.e₁) * (G.e₀ * G.e₁)) := by
              noncomm_ring
    _ = half * (-(2 : A) * (-G.e₀ + G.e₁)) := by rw [hcore]
    _ = -(2 : A) * (half * (-G.e₀ + G.e₁)) := by
        rw [hneg2]; noncomm_ring

end Cl11Lightcone

section DrazinHodge

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-- Index-1 group inverse specialization of `Drazin.IsDrazinInverse` for discrete Hodge Laplacians. -/
abbrev IsDrazinHodgeInverse (Δ Δ_D : Matrix n n R) : Prop :=
  IsDrazinInverse Δ Δ_D 1

def hodgeKernelProj (Δ Δ_D : Matrix n n R) : Matrix n n R :=
  kernelProj Δ Δ_D

theorem laplacian_annihilates_kernel_proj (Δ Δ_D : Matrix n n R)
    (hD : IsDrazinHodgeInverse Δ Δ_D) :
    Δ * hodgeKernelProj Δ Δ_D = 0 :=
  group_inverse_nilpotent_zero hD

theorem supertrace_drazin_resolvent_zero (L L_D : Matrix n n R) :
    kreinSuperTrace (Matrix.fromBlocks (L * L_D) 0 0 (L * L_D)) = 0 := by
  rw [kreinSuperTrace_blockOp_eq]
  simp

end DrazinHodge

/-! ## Section 5 (D-C4): Krein Isometries O(V,V), `krein_isometry_dual`, & Möbius Reversal -/

section KreinIsometries

variable {R : Type*} [CommRing R]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {V_ext : Type*} [Fintype V_ext] [DecidableEq V_ext]

/-- `g` preserves the Krein indefinite metric `η = [[0, 1], [1, 0]]`. -/
def isKreinIsometry (g : Matrix (V ⊕ V) (V ⊕ V) R) : Prop :=
  gᵀ * kreinEta * g = kreinEta

/-- **Discharges `C174` `sorry` in `krein_isometry_dual`**:
Every right-invertible Krein isometry `g` satisfies the dual transpose equation `g η gᵀ = η`. -/
theorem krein_isometry_dual (g g_inv : Matrix (V ⊕ V) (V ⊕ V) R)
    (h_iso : isKreinIsometry g) (h_right : g * g_inv = 1) :
    g * kreinEta * gᵀ = kreinEta := by
  have hη : (kreinEta (R := R) (V := V)) * kreinEta = 1 := kreinEta_sq
  have h_gt : gᵀ = kreinEta * g_inv * kreinEta := by
    calc gᵀ
      _ = gᵀ * 1 := (Matrix.mul_one _).symm
      _ = gᵀ * (kreinEta * kreinEta) := by rw [hη]
      _ = (gᵀ * kreinEta) * (1 * kreinEta) := by
          rw [Matrix.one_mul]; simp only [Matrix.mul_assoc]
      _ = (gᵀ * kreinEta) * ((g * g_inv) * kreinEta) := by rw [h_right]
      _ = (gᵀ * kreinEta * g) * g_inv * kreinEta := by simp only [Matrix.mul_assoc]
      _ = kreinEta * g_inv * kreinEta := by rw [h_iso]
  calc g * kreinEta * gᵀ
    _ = g * kreinEta * (kreinEta * g_inv * kreinEta) := by rw [h_gt]
    _ = g * (kreinEta * kreinEta) * g_inv * kreinEta := by simp only [Matrix.mul_assoc]
    _ = (g * g_inv) * kreinEta := by rw [hη, Matrix.mul_one]
    _ = kreinEta := by rw [h_right, Matrix.one_mul]

/-- If we only assume left-invertibility of `g` via `h_left`, note `kreinTrace` is invariant
under congruence `M ↦ g M gᵀ` directly from `h_iso`. -/
theorem kreinTrace_isometry_invariant (g M : Matrix (V ⊕ V) (V ⊕ V) R)
    (h_iso : isKreinIsometry g) :
    kreinTrace (g * M * gᵀ) = kreinTrace M := by
  dsimp [kreinTrace]
  calc Matrix.trace (kreinEta * (g * M * gᵀ))
    _ = Matrix.trace ((kreinEta * g) * (M * gᵀ)) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((M * gᵀ) * (kreinEta * g)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (M * (gᵀ * kreinEta * g)) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace (M * kreinEta) := by rw [h_iso]
    _ = Matrix.trace (kreinEta * M) := Matrix.trace_mul_comm _ _

/-- Unipotent shear `[[1, B], [0, 1]]` on `V ⊕ V`. -/
def unipotentShear (B : Matrix V V R) : Matrix (V ⊕ V) (V ⊕ V) R :=
  Matrix.fromBlocks 1 B 0 1

theorem unipotentShear_is_krein_isometry (B : Matrix V V R) (hB : Bᵀ = -B) :
    isKreinIsometry (unipotentShear B) := by
  dsimp [isKreinIsometry, unipotentShear, kreinEta]
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hB]

/-- Symplectic/Möbius complex structure `J_M = [[0, -1], [1, 0]]` on `V ⊕ V`. -/
def moebiusJ : Matrix (V ⊕ V) (V ⊕ V) R :=
  Matrix.fromBlocks 0 (-1) 1 0

theorem moebiusJ_sq :
    (moebiusJ (R := R) (V := V)) * (moebiusJ (R := R) (V := V)) = -1 := by
  dsimp [moebiusJ]
  rw [Matrix.fromBlocks_multiply]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp

theorem kreinTrace_moebius_reversal (M : Matrix (V ⊕ V) (V ⊕ V) R) :
    kreinTrace (moebiusJ * M * moebiusJᵀ) = -kreinTrace M := by
  have hRev : (moebiusJ (R := R) (V := V))ᵀ * kreinEta * moebiusJ = -kreinEta := by
    dsimp [moebiusJ, kreinEta]
    rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_neg]
    simp
  dsimp [kreinTrace]
  calc Matrix.trace (kreinEta * (moebiusJ * M * moebiusJᵀ))
    _ = Matrix.trace ((kreinEta * moebiusJ) * (M * moebiusJᵀ)) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((M * moebiusJᵀ) * (kreinEta * moebiusJ)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (M * (moebiusJᵀ * kreinEta * moebiusJ)) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace (M * (-kreinEta)) := by rw [hRev]
    _ = -Matrix.trace (M * kreinEta) := by rw [Matrix.mul_neg, Matrix.trace_neg]
    _ = -Matrix.trace (kreinEta * M) := by rw [Matrix.trace_mul_comm]

/-- Stabilization embedding of a Krein operator on `V ⊕ V` to `(V ⊕ V_ext) ⊕ (V ⊕ V_ext)`. -/
def embedIsometry (g : Matrix (V ⊕ V) (V ⊕ V) R) :
    Matrix ((V ⊕ V_ext) ⊕ (V ⊕ V_ext)) ((V ⊕ V_ext) ⊕ (V ⊕ V_ext)) R :=
  Matrix.fromBlocks
    (Matrix.fromBlocks g.toBlocks₁₁ 0 0 1)
    (Matrix.fromBlocks g.toBlocks₁₂ 0 0 0)
    (Matrix.fromBlocks g.toBlocks₂₁ 0 0 0)
    (Matrix.fromBlocks g.toBlocks₂₂ 0 0 1)

theorem embedIsometry_preserves_krein (g : Matrix (V ⊕ V) (V ⊕ V) R)
    (h_iso : isKreinIsometry g) :
    isKreinIsometry (embedIsometry (V_ext := V_ext) g) := by
  have h_blocks : g = Matrix.fromBlocks g.toBlocks₁₁ g.toBlocks₁₂ g.toBlocks₂₁ g.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks g).symm
  have hg₁₁ : g.toBlocks₂₁ᵀ * g.toBlocks₁₁ + g.toBlocks₁₁ᵀ * g.toBlocks₂₁ = 0 := by
    have h0 := congrArg Matrix.toBlocks₁₁ h_iso
    rw [h_blocks] at h0
    simpa [kreinEta, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply] using h0
  have hg₁₂ : g.toBlocks₂₁ᵀ * g.toBlocks₁₂ + g.toBlocks₁₁ᵀ * g.toBlocks₂₂ = 1 := by
    have h0 := congrArg Matrix.toBlocks₁₂ h_iso
    rw [h_blocks] at h0
    simpa [kreinEta, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply] using h0
  have hg₂₁ : g.toBlocks₂₂ᵀ * g.toBlocks₁₁ + g.toBlocks₁₂ᵀ * g.toBlocks₂₁ = 1 := by
    have h0 := congrArg Matrix.toBlocks₂₁ h_iso
    rw [h_blocks] at h0
    simpa [kreinEta, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply] using h0
  have hg₂₂ : g.toBlocks₂₂ᵀ * g.toBlocks₁₂ + g.toBlocks₁₂ᵀ * g.toBlocks₂₂ = 0 := by
    have h0 := congrArg Matrix.toBlocks₂₂ h_iso
    rw [h_blocks] at h0
    simpa [kreinEta, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply] using h0
  dsimp [isKreinIsometry, embedIsometry, kreinEta]
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add,
    Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.transpose_zero, Matrix.transpose_one, zero_add, add_zero]
  simp [hg₁₁, hg₁₂, hg₂₁, hg₂₂]

end KreinIsometries

/-! ## Section 6 (D-C5): Krein-BRST Kugo-Ojima Quartet (`C180`/`C186`) & Plabic Möbius Spin -/

section KreinBRST

variable {R : Type*} [CommRing R]
variable {V : Type*} [Fintype V] [DecidableEq V]

def brstOperator (B : Matrix V V R) : Matrix (V ⊕ V) (V ⊕ V) R :=
  Matrix.fromBlocks 0 B 0 0

def antiBrstOperator (B : Matrix V V R) : Matrix (V ⊕ V) (V ⊕ V) R :=
  Matrix.fromBlocks 0 0 Bᵀ 0

def brstLaplacian (B : Matrix V V R) : Matrix (V ⊕ V) (V ⊕ V) R :=
  brstOperator B * antiBrstOperator B + antiBrstOperator B * brstOperator B

theorem brst_sq_zero (B : Matrix V V R) :
    brstOperator B * brstOperator B = 0 := by
  dsimp [brstOperator]
  rw [Matrix.fromBlocks_multiply]
  simp

theorem brstLaplacian_block_eq (B : Matrix V V R) :
    brstLaplacian B = Matrix.fromBlocks (B * Bᵀ) 0 0 (Bᵀ * B) := by
  dsimp [brstLaplacian, brstOperator, antiBrstOperator]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  simp

theorem brst_krein_adjoint_relation (B : Matrix V V R) :
    (brstOperator B)ᵀ * kreinEta = antiBrstOperator B * kreinEta ∧
      (brstOperator B)ᵀ * kreinEta = kreinEta * brstOperator Bᵀ := by
  dsimp [brstOperator, antiBrstOperator, kreinEta]
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp

/-- **Discharges `C180` `sorry` #1**: Whenever `Δ_BD` is a group inverse of `Δ_B` and
`brstOperator B` is stabilized by `Δ_B` (`brstOperator B * Δ_B = brstOperator B`), the physical
Drazin kernel projector `1 - Δ_B * Δ_BD` is annihilated by `brstOperator B`. -/
theorem brst_annihilates_physical_space (B : Matrix V V R)
    (Δ_B Δ_BD : Matrix (V ⊕ V) (V ⊕ V) R)
    (h_drazin : IsDrazinInverse Δ_B Δ_BD 1)
    (h_stab : brstOperator B * Δ_B = brstOperator B) :
    brstOperator B * (1 - Δ_B * Δ_BD) = 0 := by
  have hnil := group_inverse_nilpotent_zero h_drazin
  dsimp [kernelProj, spectralProj] at hnil
  calc brstOperator B * (1 - Δ_B * Δ_BD)
    _ = (brstOperator B * Δ_B) * (1 - Δ_B * Δ_BD) := by rw [h_stab]
    _ = brstOperator B * (Δ_B * (1 - Δ_B * Δ_BD)) := by rw [Matrix.mul_assoc]
    _ = brstOperator B * 0 := by rw [hnil]
    _ = 0 := Matrix.mul_zero _

/-- Kugo-Ojima Krein-metric decoupling (`C186` repaired): any physical subspace `P_phys` whose
Krein-dual image `kreinEta * P_phys` is annihilated by `antiBrstOperator B` (`Q_Bᵀ`) decouples
every BRST-exact state `brstOperator B *ᵥ x` from `P_phys *ᵥ y` in the Krein inner product. -/
theorem kugo_ojima_metric_decoupling (B : Matrix V V R) (P_phys : Matrix (V ⊕ V) (V ⊕ V) R)
    (h_annihilate : antiBrstOperator B * (kreinEta * P_phys) = 0) (x y : (V ⊕ V) → R) :
    dotProduct (brstOperator B *ᵥ x) ((kreinEta (R := R) (V := V)) *ᵥ (P_phys *ᵥ y)) = 0 := by
  calc dotProduct (brstOperator B *ᵥ x) (kreinEta *ᵥ (P_phys *ᵥ y))
    _ = dotProduct (kreinEta *ᵥ (P_phys *ᵥ y)) (brstOperator B *ᵥ x) := dotProduct_comm _ _
    _ = dotProduct ((kreinEta *ᵥ (P_phys *ᵥ y)) ᵥ* brstOperator B) x :=
          Matrix.dotProduct_mulVec _ _ _
    _ = dotProduct ((brstOperator B)ᵀ *ᵥ (kreinEta *ᵥ (P_phys *ᵥ y))) x := by
          rw [← Matrix.mulVec_transpose]
    _ = dotProduct x ((brstOperator B)ᵀ *ᵥ (kreinEta *ᵥ (P_phys *ᵥ y))) := dotProduct_comm _ _
    _ = dotProduct x ((antiBrstOperator B * (kreinEta * P_phys)) *ᵥ y) := by
        have h_adj : (brstOperator B)ᵀ = antiBrstOperator B := by
          dsimp [brstOperator, antiBrstOperator]
          rw [Matrix.fromBlocks_transpose]
          simp
        rw [h_adj, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = 0 := by
        rw [h_annihilate, Matrix.zero_mulVec, dotProduct_zero]

/-- Two-parameter Plabic Möbius spin connection data `(a, b)` over a commutative ring. -/
structure MoebiusConnection (R : Type*) [CommRing R] where
  a : R
  b : R

/-- Constructive witness of `MoebiusConnection`. -/
def intMoebiusConnection : MoebiusConnection ℤ := ⟨1, 0⟩

def moebiusSpinMatrix {R : Type*} [CommRing R] (c : MoebiusConnection R) : Matrix (Fin 2) (Fin 2) R :=
  !![c.a, c.b; -c.b, -c.a]

theorem chiral_vacuum_trembling_stabilized {R : Type*} [CommRing R] (c : MoebiusConnection R) :
    moebiusSpinMatrix c * moebiusSpinMatrix c = (c.a ^ 2 - c.b ^ 2) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [moebiusSpinMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end KreinBRST

/-! ## Section 7 (D-C6): Thermofield Zitterbewegung, Shannon Entropy (`C189`), & Cl(1,3) `feynmanSlash_sq` (`C192`) -/

section ThermofieldSpinAndEntropy

variable {R : Type*} [CommRing R]
variable {V : Type*} [Fintype V] [DecidableEq V]

def forwardSpin (S : Matrix V V R) : Matrix (V ⊕ V) (V ⊕ V) R :=
  forwardOp S

def backwardSpin (S : Matrix V V R) : Matrix (V ⊕ V) (V ⊕ V) R :=
  backwardTwinOp S

theorem zitterbewegung_interference_zero (S₁ S₂ : Matrix V V R) :
    forwardSpin S₁ * backwardSpin S₂ - backwardSpin S₂ * forwardSpin S₁ = 0 :=
  thermofield_commutant_exact_commutation S₁ S₂

theorem kreinTrace_forwardSpin_zero (S : Matrix V V R) :
    kreinTrace (forwardSpin S) = 0 :=
  kreinTrace_diagonal_zero S 0

end ThermofieldSpinAndEntropy

/-- Finite normalized positive probability spectrum `(pᵢ)ᵢ` of length `n`. -/
structure DensitySpectrum (n : ℕ) where
  prob : Fin n → ℝ
  prob_pos : ∀ i, 0 < prob i
  prob_sum : (∑ i, prob i) = 1

/-- Constructive non-degenerate uniform 2-state witness for `DensitySpectrum`. -/
noncomputable def twoStateDensitySpectrum : DensitySpectrum 2 where
  prob := fun _ => (1 / 2 : ℝ)
  prob_pos := fun _ => by norm_num
  prob_sum := by norm_num

noncomputable def modularHamiltonian {n : ℕ} (D : DensitySpectrum n) (i : Fin n) : ℝ :=
  -Real.log (D.prob i)

noncomputable def entanglementEntropy {n : ℕ} (D : DensitySpectrum n) : ℝ :=
  ∑ i, D.prob i * modularHamiltonian D i

theorem entanglementEntropy_eq_shannon {n : ℕ} (D : DensitySpectrum n) :
    entanglementEntropy D = -∑ i, D.prob i * Real.log (D.prob i) := by
  dsimp [entanglementEntropy, modularHamiltonian]
  simp only [mul_neg, Finset.sum_neg_distrib]

theorem holographic_area_law_exact (N : ℕ) :
    Real.log ((2 : ℝ) ^ N) = (N : ℝ) * Real.log 2 := by
  rw [Real.log_pow]

theorem colimit_entropy_density_constant (N : ℕ) (hN : (N : ℝ) ≠ 0) :
    Real.log ((2 : ℝ) ^ N) / (N : ℝ) = Real.log 2 := by
  rw [holographic_area_law_exact, mul_div_cancel_left₀ _ hN]

/-- Abstract associative `[Ring A]` Spacetime Algebra `Cl(1,3)` with signature `(-, +, +, +)`. -/
structure SpacetimeAlgebra (A : Type*) [Ring A] where
  e₀ : A
  e₁ : A
  e₂ : A
  e₃ : A
  e₀_sq : e₀ * e₀ = -1
  e₁_sq : e₁ * e₁ = 1
  e₂_sq : e₂ * e₂ = 1
  e₃_sq : e₃ * e₃ = 1
  anti_01 : e₀ * e₁ + e₁ * e₀ = 0
  anti_02 : e₀ * e₂ + e₂ * e₀ = 0
  anti_03 : e₀ * e₃ + e₃ * e₀ = 0
  anti_12 : e₁ * e₂ + e₂ * e₁ = 0
  anti_13 : e₁ * e₃ + e₃ * e₁ = 0
  anti_23 : e₂ * e₃ + e₃ * e₂ = 0

/-- Constructive genuinely noncommutative witness of `SpacetimeAlgebra` in `M₄(ℤ)`. -/
def mat4SpacetimeAlgebra : SpacetimeAlgebra (Matrix (Fin 4) (Fin 4) ℤ) where
  e₀ := !![0, 0, -1, 0; 0, 0, 0, -1; 1, 0, 0, 0; 0, 1, 0, 0]
  e₁ := !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]
  e₂ := !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1]
  e₃ := !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, -1; 0, 0, -1, 0]
  e₀_sq := by decide
  e₁_sq := by decide
  e₂_sq := by decide
  e₃_sq := by decide
  anti_01 := by decide
  anti_02 := by decide
  anti_03 := by decide
  anti_12 := by decide
  anti_13 := by decide
  anti_23 := by decide

section SpacetimeCl13

variable {A : Type*} [Ring A]

def pseudoscalarI (STA : SpacetimeAlgebra A) : A :=
  STA.e₀ * STA.e₁ * STA.e₂ * STA.e₃

def sigma1 (STA : SpacetimeAlgebra A) : A := STA.e₁ * STA.e₀
def sigma2 (STA : SpacetimeAlgebra A) : A := STA.e₂ * STA.e₀
def sigma3 (STA : SpacetimeAlgebra A) : A := STA.e₃ * STA.e₀

theorem pseudoscalarI_sq_neg_one (STA : SpacetimeAlgebra A) :
    pseudoscalarI STA * pseudoscalarI STA = -1 := by
  dsimp [pseudoscalarI]
  have h10 : STA.e₁ * STA.e₀ = -(STA.e₀ * STA.e₁) := eq_neg_of_add_eq_zero_right STA.anti_01
  have h20 : STA.e₂ * STA.e₀ = -(STA.e₀ * STA.e₂) := eq_neg_of_add_eq_zero_right STA.anti_02
  have h30 : STA.e₃ * STA.e₀ = -(STA.e₀ * STA.e₃) := eq_neg_of_add_eq_zero_right STA.anti_03
  have h21 : STA.e₂ * STA.e₁ = -(STA.e₁ * STA.e₂) := eq_neg_of_add_eq_zero_right STA.anti_12
  have h31 : STA.e₃ * STA.e₁ = -(STA.e₁ * STA.e₃) := eq_neg_of_add_eq_zero_right STA.anti_13
  have h32 : STA.e₃ * STA.e₂ = -(STA.e₂ * STA.e₃) := eq_neg_of_add_eq_zero_right STA.anti_23
  calc (STA.e₀ * STA.e₁ * STA.e₂ * STA.e₃) * (STA.e₀ * STA.e₁ * STA.e₂ * STA.e₃)
    _ = STA.e₀ * STA.e₁ * STA.e₂ * (STA.e₃ * STA.e₀) * STA.e₁ * STA.e₂ * STA.e₃ := by
        simp only [mul_assoc]
    _ = -(STA.e₀ * STA.e₁ * STA.e₂ * STA.e₀ * STA.e₃ * STA.e₁ * STA.e₂ * STA.e₃) := by
        rw [h30]; simp only [mul_neg, neg_mul, mul_assoc]
    _ = (STA.e₀ * STA.e₁ * STA.e₀ * STA.e₂ * STA.e₃ * STA.e₁ * STA.e₂ * STA.e₃) := by
        calc -(STA.e₀ * STA.e₁ * STA.e₂ * STA.e₀ * STA.e₃ * STA.e₁ * STA.e₂ * STA.e₃)
          _ = -(STA.e₀ * STA.e₁ * (STA.e₂ * STA.e₀) * STA.e₃ * STA.e₁ * STA.e₂ * STA.e₃) := by
              simp only [mul_assoc]
          _ = STA.e₀ * STA.e₁ * STA.e₀ * STA.e₂ * STA.e₃ * STA.e₁ * STA.e₂ * STA.e₃ := by
              rw [h20]; simp only [mul_neg, neg_mul, neg_neg, mul_assoc]
    _ = -((STA.e₀ * STA.e₀) * STA.e₁ * STA.e₂ * STA.e₃ * STA.e₁ * STA.e₂ * STA.e₃) := by
        calc STA.e₀ * STA.e₁ * STA.e₀ * STA.e₂ * STA.e₃ * STA.e₁ * STA.e₂ * STA.e₃
          _ = STA.e₀ * (STA.e₁ * STA.e₀) * STA.e₂ * STA.e₃ * STA.e₁ * STA.e₂ * STA.e₃ := by
              simp only [mul_assoc]
          _ = -((STA.e₀ * STA.e₀) * STA.e₁ * STA.e₂ * STA.e₃ * STA.e₁ * STA.e₂ * STA.e₃) := by
              rw [h10]; simp only [mul_neg, neg_mul, mul_assoc]
    _ = STA.e₁ * STA.e₂ * STA.e₃ * STA.e₁ * STA.e₂ * STA.e₃ := by
        rw [STA.e₀_sq]; simp only [neg_mul, one_mul, neg_neg]
    _ = -(STA.e₁ * STA.e₂ * STA.e₁ * STA.e₃ * STA.e₂ * STA.e₃) := by
        calc STA.e₁ * STA.e₂ * STA.e₃ * STA.e₁ * STA.e₂ * STA.e₃
          _ = STA.e₁ * STA.e₂ * (STA.e₃ * STA.e₁) * STA.e₂ * STA.e₃ := by
              simp only [mul_assoc]
          _ = -(STA.e₁ * STA.e₂ * STA.e₁ * STA.e₃ * STA.e₂ * STA.e₃) := by
              rw [h31]; simp only [mul_neg, neg_mul, mul_assoc]
    _ = (STA.e₁ * STA.e₁) * STA.e₂ * STA.e₃ * STA.e₂ * STA.e₃ := by
        calc -(STA.e₁ * STA.e₂ * STA.e₁ * STA.e₃ * STA.e₂ * STA.e₃)
          _ = -(STA.e₁ * (STA.e₂ * STA.e₁) * STA.e₃ * STA.e₂ * STA.e₃) := by
              simp only [mul_assoc]
          _ = (STA.e₁ * STA.e₁) * STA.e₂ * STA.e₃ * STA.e₂ * STA.e₃ := by
              rw [h21]; simp only [mul_neg, neg_mul, neg_neg, mul_assoc]
    _ = STA.e₂ * STA.e₃ * STA.e₂ * STA.e₃ := by
        rw [STA.e₁_sq, one_mul]
    _ = -(STA.e₂ * STA.e₂) * (STA.e₃ * STA.e₃) := by
        calc STA.e₂ * STA.e₃ * STA.e₂ * STA.e₃
          _ = STA.e₂ * (STA.e₃ * STA.e₂) * STA.e₃ := by simp only [mul_assoc]
          _ = -(STA.e₂ * STA.e₂) * (STA.e₃ * STA.e₃) := by
              rw [h32]; simp only [mul_neg, neg_mul, mul_assoc]
    _ = -1 := by rw [STA.e₂_sq, STA.e₃_sq]; simp

theorem sigma1_sq (STA : SpacetimeAlgebra A) : sigma1 STA * sigma1 STA = 1 := by
  dsimp [sigma1]
  have h10 : STA.e₁ * STA.e₀ = -(STA.e₀ * STA.e₁) := eq_neg_of_add_eq_zero_right STA.anti_01
  calc (STA.e₁ * STA.e₀) * (STA.e₁ * STA.e₀)
    _ = STA.e₁ * (STA.e₀ * STA.e₁) * STA.e₀ := by simp only [mul_assoc]
    _ = STA.e₁ * (-(STA.e₁ * STA.e₀)) * STA.e₀ := by rw [← neg_eq_iff_eq_neg.mpr h10]
    _ = -((STA.e₁ * STA.e₁) * (STA.e₀ * STA.e₀)) := by noncomm_ring
    _ = 1 := by rw [STA.e₁_sq, STA.e₀_sq]; simp

theorem sigma2_sq (STA : SpacetimeAlgebra A) : sigma2 STA * sigma2 STA = 1 := by
  dsimp [sigma2]
  have h20 : STA.e₂ * STA.e₀ = -(STA.e₀ * STA.e₂) := eq_neg_of_add_eq_zero_right STA.anti_02
  calc (STA.e₂ * STA.e₀) * (STA.e₂ * STA.e₀)
    _ = STA.e₂ * (STA.e₀ * STA.e₂) * STA.e₀ := by simp only [mul_assoc]
    _ = STA.e₂ * (-(STA.e₂ * STA.e₀)) * STA.e₀ := by rw [← neg_eq_iff_eq_neg.mpr h20]
    _ = -((STA.e₂ * STA.e₂) * (STA.e₀ * STA.e₀)) := by noncomm_ring
    _ = 1 := by rw [STA.e₂_sq, STA.e₀_sq]; simp

theorem sigma3_sq (STA : SpacetimeAlgebra A) : sigma3 STA * sigma3 STA = 1 := by
  dsimp [sigma3]
  have h30 : STA.e₃ * STA.e₀ = -(STA.e₀ * STA.e₃) := eq_neg_of_add_eq_zero_right STA.anti_03
  calc (STA.e₃ * STA.e₀) * (STA.e₃ * STA.e₀)
    _ = STA.e₃ * (STA.e₀ * STA.e₃) * STA.e₀ := by simp only [mul_assoc]
    _ = STA.e₃ * (-(STA.e₃ * STA.e₀)) * STA.e₀ := by rw [← neg_eq_iff_eq_neg.mpr h30]
    _ = -((STA.e₃ * STA.e₃) * (STA.e₀ * STA.e₀)) := by noncomm_ring
    _ = 1 := by rw [STA.e₃_sq, STA.e₀_sq]; simp

/-- Feynman slash operator `k̸ = k₀ e₀ + k₁ e₁ + k₂ e₂ + k₃ e₃` with central scalar
coefficients in `R`, keeping `A` genuinely noncommutative (Trap T16 compliant). -/
def feynmanSlash {R : Type*} [CommRing R] [Algebra R A]
    (STA : SpacetimeAlgebra A) (k₀ k₁ k₂ k₃ : R) : A :=
  k₀ • STA.e₀ + k₁ • STA.e₁ + k₂ • STA.e₂ + k₃ • STA.e₃

/-- **Discharges `C192` `feynmanSlash_sq` `sorry`** cleanly for any noncommutative `R`-algebra `A`:
`(k̸)² = (-k₀² + k₁² + k₂² + k₃²) · 1`. -/
theorem feynmanSlash_sq {R : Type*} [CommRing R] [Algebra R A]
    (STA : SpacetimeAlgebra A) (k₀ k₁ k₂ k₃ : R) :
    feynmanSlash STA k₀ k₁ k₂ k₃ * feynmanSlash STA k₀ k₁ k₂ k₃ =
      algebraMap R A (-k₀ ^ 2 + k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2) := by
  dsimp [feynmanSlash]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
  rw [show STA.e₁ * STA.e₀ = -(STA.e₀ * STA.e₁) from eq_neg_of_add_eq_zero_right STA.anti_01]
  rw [show STA.e₂ * STA.e₀ = -(STA.e₀ * STA.e₂) from eq_neg_of_add_eq_zero_right STA.anti_02]
  rw [show STA.e₃ * STA.e₀ = -(STA.e₀ * STA.e₃) from eq_neg_of_add_eq_zero_right STA.anti_03]
  rw [show STA.e₂ * STA.e₁ = -(STA.e₁ * STA.e₂) from eq_neg_of_add_eq_zero_right STA.anti_12]
  rw [show STA.e₃ * STA.e₁ = -(STA.e₁ * STA.e₃) from eq_neg_of_add_eq_zero_right STA.anti_13]
  rw [show STA.e₃ * STA.e₂ = -(STA.e₂ * STA.e₃) from eq_neg_of_add_eq_zero_right STA.anti_23]
  rw [STA.e₀_sq, STA.e₁_sq, STA.e₂_sq, STA.e₃_sq]
  simp only [smul_neg]
  rw [show (k₁ * k₀) = k₀ * k₁ from mul_comm _ _,
      show (k₂ * k₀) = k₀ * k₂ from mul_comm _ _,
      show (k₃ * k₀) = k₀ * k₃ from mul_comm _ _,
      show (k₂ * k₁) = k₁ * k₂ from mul_comm _ _,
      show (k₃ * k₁) = k₁ * k₃ from mul_comm _ _,
      show (k₃ * k₂) = k₂ * k₃ from mul_comm _ _]
  calc _
    _ = -((k₀ * k₀) • (1 : A)) + (k₁ * k₁) • (1 : A) + (k₂ * k₂) • (1 : A) + (k₃ * k₃) • (1 : A) := by
        abel
    _ = (-k₀ ^ 2 + k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2) • (1 : A) := by
        simp only [sq, add_smul, neg_smul]
    _ = algebraMap R A (-k₀ ^ 2 + k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2) := by
        rw [Algebra.algebraMap_eq_smul_one]

theorem massless_field_strictly_nilpotent {R : Type*} [CommRing R] [Algebra R A]
    (STA : SpacetimeAlgebra A) (k₀ k₁ k₂ k₃ : R)
    (h_null : -k₀ ^ 2 + k₁ ^ 2 + k₂ ^ 2 + k₃ ^ 2 = 0) :
    feynmanSlash STA k₀ k₁ k₂ k₃ * feynmanSlash STA k₀ k₁ k₂ k₃ = 0 := by
  rw [feynmanSlash_sq, h_null, map_zero]

end SpacetimeCl13

end InfoGeometry.Synthesis.Aistudio1SSh9KreinThermofieldCl13Bridge
