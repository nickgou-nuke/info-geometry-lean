/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Canonical.RoadToGravityFromSpinning
import InfoGeometry.Canonical.GeometroMagnetoGravityCrankingDirac
import InfoGeometry.Canonical.DiracSpinCasimirNambuModulesBridge
import InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge
import InfoGeometry.Canonical.DoubledMinkowskiRotatingSpinInstability
import InfoGeometry.OperatorAlgebra.PeirceSpine.AlternatingCornerTriple
import InfoGeometry.Clifford.LochakRodichevFierzKrein
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Real Dirac–Palatini Variational Field Equations & Graded Cartan–Bianchi Identities

Extends `RoadToGravityFromSpinning` and `GeometroMagnetoGravityCrankingDirac` purely over `ℝ`
(`0` complex `i`) inside `Cl(3,1) ≅ M₄(ℝ)` to first-order variational field equations and graded
Cartan–Bianchi identities:

1. **Graded Cartan–Bianchi Split (`graded_cartan_bianchi_jacobi_split`, `graded_cartan_bianchi_covariant_split`)**:
   Splits the total Jacobi and covariant exterior differential identities `D_𝒜 ℱ = 0` under `Γ`-parity
   into the `Γ`-even second Cartan–Bianchi identity `D_ω R = 0`, the cosmological area–torsion balance
   `D_ω E + [e, T]_cyc = 0`, and the `Γ`-odd first Cartan–Bianchi identity `D_ω T = [R, e]_cyc`.
2. **First-Order MacDowell–Mansouri / Palatini `δe` Variation (`palatini_delta_e_variation_and_lambda_eq`)**:
   Computes the exact directional derivative (`HasDerivAt`) of the `γ₅`-weighted Palatini + cosmological
   action `2 Tr(γ₅ R [e₁, e₂]) + Λ Tr(γ₅ E₀ [e₁, e₂])` with respect to the soldering tetrad `e₁`,
   proves stationary vanishing on the constant-curvature Einstein–de Sitter locus `2 R + Λ E₀ = 0`,
   and extracts the explicit `(2,3)` Hodge-dual readout `-(2 r₀₁ + Λ)` on `solderVec 0..3`.
3. **First-Order Einstein–Cartan `δω` & `δT` Variation (`einstein_cartan_delta_omega_and_torsion_spin_lock`)**:
   Computes the exact directional derivative (`HasDerivAt`) of `Tr(γ₅ (dω + [ω₁, ω₂]) E)` with respect
   to `ω₁` (vanishing when `E` is `γ₅`-even and covariantly parallel `[ω₂, E] = 0`), and proves that
   varying the Einstein–Cartan axial torsion–spin functional `(1/2) η(T,T) - κ_EC η(T,J₅)` vanishes
   for all `δT` iff `T = κ_EC J₅` (and `T = 0` in vacuum), evaluating on shell to
   `(1/2) κ_EC² (Ω₁² + Ω₂²)`.

## Three-Bucket Audit Map

#### BUCKET 1: CLOSED FINITE & VARIATIONAL THEOREMS
* `exists_noncomm_mat2x2_palatini_var`
* `palatini_delta_e_variation_and_lambda_eq`
* `einstein_cartan_delta_omega_and_torsion_spin_lock`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
* `graded_cartan_bianchi_jacobi_split` (under explicit `Γ`-even `ω`, `Γ`-odd `e` hypotheses)
* `graded_cartan_bianchi_covariant_split` (under explicit covariant Leibniz / closedness laws)

#### BUCKET 3: OPEN CLOSURE DEBT
* Smooth 4D spacetime differential-form integration and coupled Einstein–Dirac PDE solutions remain
  outside this finite pointwise Clifford-algebra variational bridge.
-/

set_option autoImplicit false

noncomputable section

open scoped Kronecker
open Matrix

namespace InfoGeometry.Canonical.RealDiracPalatiniVariationBridge

open InfoGeometry.Canonical.DoubledMinkowskiBdGColimitBridge
open InfoGeometry.Canonical.DoubledMinkowskiRotatingSpinInstability
open InfoGeometry.Canonical.DiracSpinCasimirNambuModulesBridge
open InfoGeometry.Canonical.RoadToGravityFromSpinning
open InfoGeometry.Canonical.GeometroMagnetoGravityCrankingDirac
open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.PeirceSpine

/-- Explicit non-commutativity witness on the real `M₄(ℝ)` Palatini operator carrier. -/
theorem exists_noncomm_mat2x2_palatini_var :
    ∃ A B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ, A * B ≠ B * A := by
  refine ⟨diracGamma0, diracGamma3, fun h => ?_⟩
  have h03 := diracGamma_clifford_relations.2.2.2.2.2.2.1
  rw [h, ← two_smul ℝ (diracGamma3 * diracGamma0)] at h03
  have h01 := congrArg (fun M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ => M (0, 0) (1, 0)) h03
  simp [diracGamma3, diracGamma0, zCut2, eps2,
    Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two] at h01

/-! ### Part 1: Graded Cartan–Bianchi Identities (`Γ`-Even Second & `Γ`-Odd First Bianchi) -/

/-- Cyclic three-argument sum `f x y z + f y z x + f z x y` in any ring. -/
def cyclicSum {B : Type*} [Ring B] (f : B → B → B → B) (x y z : B) : B :=
  f x y z + f y z x + f z x y

private lemma gamma_comm_even_even {B : Type*} [Ring B] {Γ x y : B}
    (hx : Γ * x = x * Γ) (hy : Γ * y = y * Γ) :
    Γ * PeirceSpine.comm x y = PeirceSpine.comm x y * Γ := by
  unfold PeirceSpine.comm
  calc
    Γ * (x * y - y * x) = (Γ * x) * y - (Γ * y) * x := by noncomm_ring
    _ = (x * Γ) * y - (y * Γ) * x := by rw [hx, hy]
    _ = x * (Γ * y) - y * (Γ * x) := by noncomm_ring
    _ = x * (y * Γ) - y * (x * Γ) := by rw [hy, hx]
    _ = (x * y - y * x) * Γ := by noncomm_ring

private lemma gamma_comm_odd_odd {B : Type*} [Ring B] {Γ x y : B}
    (hx : Γ * x = -(x * Γ)) (hy : Γ * y = -(y * Γ)) :
    Γ * PeirceSpine.comm x y = PeirceSpine.comm x y * Γ := by
  unfold PeirceSpine.comm
  calc
    Γ * (x * y - y * x) = (Γ * x) * y - (Γ * y) * x := by noncomm_ring
    _ = (-(x * Γ)) * y - (-(y * Γ)) * x := by rw [hx, hy]
    _ = -(x * (Γ * y)) + y * (Γ * x) := by noncomm_ring
    _ = -(x * (-(y * Γ))) + y * (-(x * Γ)) := by rw [hy, hx]
    _ = (x * y - y * x) * Γ := by noncomm_ring

private lemma gamma_comm_even_odd {B : Type*} [Ring B] {Γ x y : B}
    (hx : Γ * x = x * Γ) (hy : Γ * y = -(y * Γ)) :
    Γ * PeirceSpine.comm x y = -(PeirceSpine.comm x y * Γ) := by
  unfold PeirceSpine.comm
  calc
    Γ * (x * y - y * x) = (Γ * x) * y - (Γ * y) * x := by noncomm_ring
    _ = (x * Γ) * y - (-(y * Γ)) * x := by rw [hx, hy]
    _ = x * (Γ * y) + y * (Γ * x) := by noncomm_ring
    _ = x * (-(y * Γ)) + y * (x * Γ) := by rw [hy, hx]
    _ = -((x * y - y * x) * Γ) := by noncomm_ring

private lemma gamma_comm_odd_even {B : Type*} [Ring B] {Γ x y : B}
    (hx : Γ * x = -(x * Γ)) (hy : Γ * y = y * Γ) :
    Γ * PeirceSpine.comm x y = -(PeirceSpine.comm x y * Γ) := by
  unfold PeirceSpine.comm
  calc
    Γ * (x * y - y * x) = (Γ * x) * y - (Γ * y) * x := by noncomm_ring
    _ = (-(x * Γ)) * y - (y * Γ) * x := by rw [hx, hy]
    _ = -(x * (Γ * y)) - y * (Γ * x) := by noncomm_ring
    _ = -(x * (y * Γ)) - y * (-(x * Γ)) := by rw [hy, hx]
    _ = -((x * y - y * x) * Γ) := by noncomm_ring

private lemma gamma_even_add_even {B : Type*} [Ring B] {Γ a b : B}
    (ha : Γ * a = a * Γ) (hb : Γ * b = b * Γ) :
    Γ * (a + b) = (a + b) * Γ := by
  rw [mul_add, add_mul, ha, hb]

private lemma gamma_even_sub_even {B : Type*} [Ring B] {Γ a b : B}
    (ha : Γ * a = a * Γ) (hb : Γ * b = b * Γ) :
    Γ * (a - b) = (a - b) * Γ := by
  rw [mul_sub, sub_mul, ha, hb]

private lemma gamma_odd_add_odd {B : Type*} [Ring B] {Γ a b : B}
    (ha : Γ * a = -(a * Γ)) (hb : Γ * b = -(b * Γ)) :
    Γ * (a + b) = -((a + b) * Γ) := by
  rw [mul_add, add_mul, ha, hb]; abel

private lemma gamma_odd_sub_odd {B : Type*} [Ring B] {Γ a b : B}
    (ha : Γ * a = -(a * Γ)) (hb : Γ * b = -(b * Γ)) :
    Γ * (a - b) = -((a - b) * Γ) := by
  rw [mul_sub, sub_mul, ha, hb]; abel

/-- **Theorem 1A (Graded Jacobi / Algebraic Cartan–Bianchi Parity Split)**:
For any `Γ`-even spin connections `ω₁, ω₂, ω₃` and `Γ`-odd soldering tetrads `e₁, e₂, e₃` with
`𝒜_i = ω_i + e_i`:
1. The total Jacobi cyclic sum vanishes and splits identically into `Γ`-even and `Γ`-odd parts.
2. Pure-spin Jacobi, pure-soldering Jacobi, the mixed `Γ`-even cosmological–torsion Jacobi, and the
   mixed `Γ`-odd first-Bianchi commutator sum each vanish identically. -/
theorem graded_cartan_bianchi_jacobi_split {B : Type*} [Ring B]
    (Γ ω₁ ω₂ ω₃ e₁ e₂ e₃ : B)
    (hω1 : Γ * ω₁ = ω₁ * Γ) (hω2 : Γ * ω₂ = ω₂ * Γ) (hω3 : Γ * ω₃ = ω₃ * Γ)
    (he1 : Γ * e₁ = -(e₁ * Γ)) (he2 : Γ * e₂ = -(e₂ * Γ)) (he3 : Γ * e₃ = -(e₃ * Γ)) :
    let A₁ := ω₁ + e₁
    let A₂ := ω₂ + e₂
    let A₃ := ω₃ + e₃
    let pureSpin := PeirceSpine.comm ω₁ (PeirceSpine.comm ω₂ ω₃) +
      PeirceSpine.comm ω₂ (PeirceSpine.comm ω₃ ω₁) +
      PeirceSpine.comm ω₃ (PeirceSpine.comm ω₁ ω₂)
    let pureSolder := PeirceSpine.comm e₁ (PeirceSpine.comm e₂ e₃) +
      PeirceSpine.comm e₂ (PeirceSpine.comm e₃ e₁) +
      PeirceSpine.comm e₃ (PeirceSpine.comm e₁ e₂)
    let mixedEven := (PeirceSpine.comm ω₁ (PeirceSpine.comm e₂ e₃) +
        PeirceSpine.comm ω₂ (PeirceSpine.comm e₃ e₁) +
        PeirceSpine.comm ω₃ (PeirceSpine.comm e₁ e₂)) +
      (PeirceSpine.comm e₁ (PeirceSpine.comm ω₂ e₃ - PeirceSpine.comm ω₃ e₂) +
        PeirceSpine.comm e₂ (PeirceSpine.comm ω₃ e₁ - PeirceSpine.comm ω₁ e₃) +
        PeirceSpine.comm e₃ (PeirceSpine.comm ω₁ e₂ - PeirceSpine.comm ω₂ e₁))
    let mixedOdd := (PeirceSpine.comm e₁ (PeirceSpine.comm ω₂ ω₃) +
        PeirceSpine.comm e₂ (PeirceSpine.comm ω₃ ω₁) +
        PeirceSpine.comm e₃ (PeirceSpine.comm ω₁ ω₂)) +
      (PeirceSpine.comm ω₁ (PeirceSpine.comm ω₂ e₃ - PeirceSpine.comm ω₃ e₂) +
        PeirceSpine.comm ω₂ (PeirceSpine.comm ω₃ e₁ - PeirceSpine.comm ω₁ e₃) +
        PeirceSpine.comm ω₃ (PeirceSpine.comm ω₁ e₂ - PeirceSpine.comm ω₂ e₁))
    (PeirceSpine.comm A₁ (PeirceSpine.comm A₂ A₃) +
      PeirceSpine.comm A₂ (PeirceSpine.comm A₃ A₁) +
      PeirceSpine.comm A₃ (PeirceSpine.comm A₁ A₂) =
        (pureSpin + mixedEven) + (mixedOdd + pureSolder)) ∧
    (Γ * (pureSpin + mixedEven) = (pureSpin + mixedEven) * Γ) ∧
    (Γ * (mixedOdd + pureSolder) = -((mixedOdd + pureSolder) * Γ)) ∧
    (pureSpin = 0) ∧
    (pureSolder = 0) ∧
    (mixedEven = 0) ∧
    (mixedOdd = 0) := by
  have hw23 : Γ * PeirceSpine.comm ω₂ ω₃ = PeirceSpine.comm ω₂ ω₃ * Γ :=
    gamma_comm_even_even hω2 hω3
  have hw31 : Γ * PeirceSpine.comm ω₃ ω₁ = PeirceSpine.comm ω₃ ω₁ * Γ :=
    gamma_comm_even_even hω3 hω1
  have hw12 : Γ * PeirceSpine.comm ω₁ ω₂ = PeirceSpine.comm ω₁ ω₂ * Γ :=
    gamma_comm_even_even hω1 hω2
  have he23 : Γ * PeirceSpine.comm e₂ e₃ = PeirceSpine.comm e₂ e₃ * Γ :=
    gamma_comm_odd_odd he2 he3
  have he31 : Γ * PeirceSpine.comm e₃ e₁ = PeirceSpine.comm e₃ e₁ * Γ :=
    gamma_comm_odd_odd he3 he1
  have he12 : Γ * PeirceSpine.comm e₁ e₂ = PeirceSpine.comm e₁ e₂ * Γ :=
    gamma_comm_odd_odd he1 he2
  have ht23 : Γ * (PeirceSpine.comm ω₂ e₃ - PeirceSpine.comm ω₃ e₂) =
      -((PeirceSpine.comm ω₂ e₃ - PeirceSpine.comm ω₃ e₂) * Γ) :=
    gamma_odd_sub_odd (gamma_comm_even_odd hω2 he3) (gamma_comm_even_odd hω3 he2)
  have ht31 : Γ * (PeirceSpine.comm ω₃ e₁ - PeirceSpine.comm ω₁ e₃) =
      -((PeirceSpine.comm ω₃ e₁ - PeirceSpine.comm ω₁ e₃) * Γ) :=
    gamma_odd_sub_odd (gamma_comm_even_odd hω3 he1) (gamma_comm_even_odd hω1 he3)
  have ht12 : Γ * (PeirceSpine.comm ω₁ e₂ - PeirceSpine.comm ω₂ e₁) =
      -((PeirceSpine.comm ω₁ e₂ - PeirceSpine.comm ω₂ e₁) * Γ) :=
    gamma_odd_sub_odd (gamma_comm_even_odd hω1 he2) (gamma_comm_even_odd hω2 he1)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [PeirceSpine.comm]; noncomm_ring
  · apply gamma_even_add_even
    · exact gamma_even_add_even (gamma_even_add_even (gamma_comm_even_even hω1 hw23)
        (gamma_comm_even_even hω2 hw31)) (gamma_comm_even_even hω3 hw12)
    · exact gamma_even_add_even
        (gamma_even_add_even (gamma_even_add_even (gamma_comm_even_even hω1 he23)
          (gamma_comm_even_even hω2 he31)) (gamma_comm_even_even hω3 he12))
        (gamma_even_add_even (gamma_even_add_even (gamma_comm_odd_odd he1 ht23)
          (gamma_comm_odd_odd he2 ht31)) (gamma_comm_odd_odd he3 ht12))
  · apply gamma_odd_add_odd
    · exact gamma_odd_add_odd
        (gamma_odd_add_odd (gamma_odd_add_odd (gamma_comm_odd_even he1 hw23)
          (gamma_comm_odd_even he2 hw31)) (gamma_comm_odd_even he3 hw12))
        (gamma_odd_add_odd (gamma_odd_add_odd (gamma_comm_even_odd hω1 ht23)
          (gamma_comm_even_odd hω2 ht31)) (gamma_comm_even_odd hω3 ht12))
    · exact gamma_odd_add_odd (gamma_odd_add_odd (gamma_comm_odd_even he1 he23)
        (gamma_comm_odd_even he2 he31)) (gamma_comm_odd_even he3 he12)
  · dsimp [PeirceSpine.comm]; noncomm_ring
  · dsimp [PeirceSpine.comm]; noncomm_ring
  · dsimp [PeirceSpine.comm]; noncomm_ring
  · dsimp [PeirceSpine.comm]; noncomm_ring

/-- **Theorem 1B (Covariant First & Second Cartan–Bianchi Identities from `D_𝒜 ℱ = 0`)**:
For curvature `R_ij = dω_ij + [ω_i, ω_j]`, area bivector `E_ij = [e_i, e_j]`, and torsion
`T_ij = de_ij + [ω_i, e_j] - [ω_j, e_i]` satisfying the graded Leibniz differential laws (`d(dω)=0`,
`d(de)=0`):
1. **Second Cartan–Bianchi (`Γ`-even)**: `dR + ∑_cyc [ω, R] = 0`.
2. **Cosmological Area–Torsion Bianchi Balance (`Γ`-even)**: `dE + ∑_cyc [ω, E] + ∑_cyc [e, T] = 0`.
3. **First Cartan–Bianchi (`Γ`-odd)**: `dT + ∑_cyc [ω, T] = ∑_cyc [R, e]`.
4. **Total Cartan–Bianchi**: `dF + ∑_cyc [ω + e, R + E + T] = 0`. -/
theorem graded_cartan_bianchi_covariant_split {B : Type*} [Ring B]
    (Γ ω₁ ω₂ ω₃ e₁ e₂ e₃ dω₁₂ dω₂₃ dω₃₁ de₁₂ de₂₃ de₃₁ : B)
    (hω1 : Γ * ω₁ = ω₁ * Γ) (hω2 : Γ * ω₂ = ω₂ * Γ) (hω3 : Γ * ω₃ = ω₃ * Γ)
    (he1 : Γ * e₁ = -(e₁ * Γ)) (he2 : Γ * e₂ = -(e₂ * Γ)) (he3 : Γ * e₃ = -(e₃ * Γ))
    (hdw12 : Γ * dω₁₂ = dω₁₂ * Γ) (hdw23 : Γ * dω₂₃ = dω₂₃ * Γ) (hdw31 : Γ * dω₃₁ = dω₃₁ * Γ)
    (hde12 : Γ * de₁₂ = -(de₁₂ * Γ)) (hde23 : Γ * de₂₃ = -(de₂₃ * Γ))
    (hde31 : Γ * de₃₁ = -(de₃₁ * Γ)) :
    let R₁₂ := dω₁₂ + PeirceSpine.comm ω₁ ω₂
    let R₂₃ := dω₂₃ + PeirceSpine.comm ω₂ ω₃
    let R₃₁ := dω₃₁ + PeirceSpine.comm ω₃ ω₁
    let E₁₂ := PeirceSpine.comm e₁ e₂
    let E₂₃ := PeirceSpine.comm e₂ e₃
    let E₃₁ := PeirceSpine.comm e₃ e₁
    let T₁₂ := de₁₂ + PeirceSpine.comm ω₁ e₂ - PeirceSpine.comm ω₂ e₁
    let T₂₃ := de₂₃ + PeirceSpine.comm ω₂ e₃ - PeirceSpine.comm ω₃ e₂
    let T₃₁ := de₃₁ + PeirceSpine.comm ω₃ e₁ - PeirceSpine.comm ω₁ e₃
    let dR := -(PeirceSpine.comm ω₁ dω₂₃ + PeirceSpine.comm ω₂ dω₃₁ + PeirceSpine.comm ω₃ dω₁₂)
    let dE := -(PeirceSpine.comm e₁ de₂₃ + PeirceSpine.comm e₂ de₃₁ + PeirceSpine.comm e₃ de₁₂)
    let dT := (PeirceSpine.comm dω₁₂ e₃ + PeirceSpine.comm dω₂₃ e₁ + PeirceSpine.comm dω₃₁ e₂) -
      (PeirceSpine.comm ω₁ de₂₃ + PeirceSpine.comm ω₂ de₃₁ + PeirceSpine.comm ω₃ de₁₂)
    let DωR := dR + (PeirceSpine.comm ω₁ R₂₃ + PeirceSpine.comm ω₂ R₃₁ + PeirceSpine.comm ω₃ R₁₂)
    let DωE_eT := dE + (PeirceSpine.comm ω₁ E₂₃ + PeirceSpine.comm ω₂ E₃₁ + PeirceSpine.comm ω₃ E₁₂) +
      (PeirceSpine.comm e₁ T₂₃ + PeirceSpine.comm e₂ T₃₁ + PeirceSpine.comm e₃ T₁₂)
    let DωT := dT + (PeirceSpine.comm ω₁ T₂₃ + PeirceSpine.comm ω₂ T₃₁ + PeirceSpine.comm ω₃ T₁₂)
    let Re_cyc := PeirceSpine.comm R₁₂ e₃ + PeirceSpine.comm R₂₃ e₁ + PeirceSpine.comm R₃₁ e₂
    (DωR = 0) ∧
    (DωE_eT = 0) ∧
    (DωT = Re_cyc) ∧
    (Γ * DωR = DωR * Γ) ∧
    (Γ * DωT = -(DωT * Γ)) ∧
    (Γ * T₁₂ = -(T₁₂ * Γ) ∧ Γ * T₂₃ = -(T₂₃ * Γ) ∧ Γ * T₃₁ = -(T₃₁ * Γ)) ∧
    ((dR + dE + dT) +
      (PeirceSpine.comm (ω₁ + e₁) (R₂₃ + E₂₃ + T₂₃) +
       PeirceSpine.comm (ω₂ + e₂) (R₃₁ + E₃₁ + T₃₁) +
       PeirceSpine.comm (ω₃ + e₃) (R₁₂ + E₁₂ + T₁₂)) = 0) := by
  have hT12 : Γ * (de₁₂ + PeirceSpine.comm ω₁ e₂ - PeirceSpine.comm ω₂ e₁) =
      -((de₁₂ + PeirceSpine.comm ω₁ e₂ - PeirceSpine.comm ω₂ e₁) * Γ) :=
    gamma_odd_sub_odd (gamma_odd_add_odd hde12 (gamma_comm_even_odd hω1 he2))
      (gamma_comm_even_odd hω2 he1)
  have hT23 : Γ * (de₂₃ + PeirceSpine.comm ω₂ e₃ - PeirceSpine.comm ω₃ e₂) =
      -((de₂₃ + PeirceSpine.comm ω₂ e₃ - PeirceSpine.comm ω₃ e₂) * Γ) :=
    gamma_odd_sub_odd (gamma_odd_add_odd hde23 (gamma_comm_even_odd hω2 he3))
      (gamma_comm_even_odd hω3 he2)
  have hT31 : Γ * (de₃₁ + PeirceSpine.comm ω₃ e₁ - PeirceSpine.comm ω₁ e₃) =
      -((de₃₁ + PeirceSpine.comm ω₃ e₁ - PeirceSpine.comm ω₁ e₃) * Γ) :=
    gamma_odd_sub_odd (gamma_odd_add_odd hde31 (gamma_comm_even_odd hω3 he1))
      (gamma_comm_even_odd hω1 he3)
  have hR12 : Γ * (dω₁₂ + PeirceSpine.comm ω₁ ω₂) = (dω₁₂ + PeirceSpine.comm ω₁ ω₂) * Γ :=
    gamma_even_add_even hdw12 (gamma_comm_even_even hω1 hω2)
  have hR23 : Γ * (dω₂₃ + PeirceSpine.comm ω₂ ω₃) = (dω₂₃ + PeirceSpine.comm ω₂ ω₃) * Γ :=
    gamma_even_add_even hdw23 (gamma_comm_even_even hω2 hω3)
  have hR31 : Γ * (dω₃₁ + PeirceSpine.comm ω₃ ω₁) = (dω₃₁ + PeirceSpine.comm ω₃ ω₁) * Γ :=
    gamma_even_add_even hdw31 (gamma_comm_even_even hω3 hω1)
  have hRe_cyc : Γ * (PeirceSpine.comm (dω₁₂ + PeirceSpine.comm ω₁ ω₂) e₃ +
        PeirceSpine.comm (dω₂₃ + PeirceSpine.comm ω₂ ω₃) e₁ +
        PeirceSpine.comm (dω₃₁ + PeirceSpine.comm ω₃ ω₁) e₂) =
      -((PeirceSpine.comm (dω₁₂ + PeirceSpine.comm ω₁ ω₂) e₃ +
        PeirceSpine.comm (dω₂₃ + PeirceSpine.comm ω₂ ω₃) e₁ +
        PeirceSpine.comm (dω₃₁ + PeirceSpine.comm ω₃ ω₁) e₂) * Γ) :=
    gamma_odd_add_odd
      (gamma_odd_add_odd (gamma_comm_even_odd hR12 he3) (gamma_comm_even_odd hR23 he1))
      (gamma_comm_even_odd hR31 he2)
  have hDωR0 : -(PeirceSpine.comm ω₁ dω₂₃ + PeirceSpine.comm ω₂ dω₃₁ + PeirceSpine.comm ω₃ dω₁₂) +
      (PeirceSpine.comm ω₁ (dω₂₃ + PeirceSpine.comm ω₂ ω₃) +
       PeirceSpine.comm ω₂ (dω₃₁ + PeirceSpine.comm ω₃ ω₁) +
       PeirceSpine.comm ω₃ (dω₁₂ + PeirceSpine.comm ω₁ ω₂)) = 0 := by
    dsimp [PeirceSpine.comm]; noncomm_ring
  have hDωT_eq : (PeirceSpine.comm dω₁₂ e₃ + PeirceSpine.comm dω₂₃ e₁ + PeirceSpine.comm dω₃₁ e₂) -
      (PeirceSpine.comm ω₁ de₂₃ + PeirceSpine.comm ω₂ de₃₁ + PeirceSpine.comm ω₃ de₁₂) +
      (PeirceSpine.comm ω₁ (de₂₃ + PeirceSpine.comm ω₂ e₃ - PeirceSpine.comm ω₃ e₂) +
       PeirceSpine.comm ω₂ (de₃₁ + PeirceSpine.comm ω₃ e₁ - PeirceSpine.comm ω₁ e₃) +
       PeirceSpine.comm ω₃ (de₁₂ + PeirceSpine.comm ω₁ e₂ - PeirceSpine.comm ω₂ e₁)) =
      PeirceSpine.comm (dω₁₂ + PeirceSpine.comm ω₁ ω₂) e₃ +
      PeirceSpine.comm (dω₂₃ + PeirceSpine.comm ω₂ ω₃) e₁ +
      PeirceSpine.comm (dω₃₁ + PeirceSpine.comm ω₃ ω₁) e₂ := by
    dsimp [PeirceSpine.comm]; noncomm_ring
  refine ⟨hDωR0, ?_, hDωT_eq, ?_, ?_, ⟨hT12, hT23, hT31⟩, ?_⟩
  · dsimp [PeirceSpine.comm]; noncomm_ring
  · rw [hDωR0, mul_zero, zero_mul]
  · rw [hDωT_eq]; exact hRe_cyc
  · dsimp [PeirceSpine.comm]; noncomm_ring

/-! ### Part 2: First-Order MacDowell–Mansouri / Palatini `δe` Variation -/

/-- Real `M₄(ℝ)` chiral-trace Palatini + cosmological action on curvature `R`, reference area
bivector `E₀`, cosmological constant `Λ`, and soldering frame generators `e₁, e₂`. -/
def mmPalatiniAction
    (R E₀ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) (Λ : ℝ)
    (e₁ e₂ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) : ℝ :=
  2 * Matrix.trace (diracOmega4 * R * PeirceSpine.comm e₁ e₂) +
    Λ * Matrix.trace (diracOmega4 * E₀ * PeirceSpine.comm e₁ e₂)

private lemma mmPalatiniAction_affine
    (R E₀ e₁ δe e₂ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) (Λ ε : ℝ) :
    mmPalatiniAction R E₀ Λ (e₁ + ε • δe) e₂ =
      mmPalatiniAction R E₀ Λ e₁ e₂ +
        ε * Matrix.trace (δe * PeirceSpine.comm e₂ (diracOmega4 * ((2 : ℝ) • R + Λ • E₀))) := by
  set M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ := diracOmega4 * ((2 : ℝ) • R + Λ • E₀)
  have hAct : ∀ X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ,
      mmPalatiniAction R E₀ Λ X e₂ = Matrix.trace (M * PeirceSpine.comm X e₂) := by
    intro X
    unfold mmPalatiniAction
    dsimp [M]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul,
      Matrix.trace_smul, smul_eq_mul, smul_eq_mul, Matrix.mul_assoc, Matrix.mul_assoc]
  have hComm : PeirceSpine.comm (e₁ + ε • δe) e₂ =
      PeirceSpine.comm e₁ e₂ + ε • PeirceSpine.comm δe e₂ := by
    unfold PeirceSpine.comm
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
    abel
  have hCyc : Matrix.trace (M * PeirceSpine.comm δe e₂) =
      Matrix.trace (δe * PeirceSpine.comm e₂ M) := by
    unfold PeirceSpine.comm
    have h1 : Matrix.trace (M * (δe * e₂)) = Matrix.trace (δe * (e₂ * M)) := by
      rw [Matrix.trace_mul_comm M (δe * e₂), Matrix.mul_assoc δe e₂ M]
    have h2 : Matrix.trace (M * (e₂ * δe)) = Matrix.trace (δe * (M * e₂)) := by
      rw [← Matrix.mul_assoc M e₂ δe, Matrix.trace_mul_comm (M * e₂) δe]
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub, h1, h2]
  rw [hAct (e₁ + ε • δe), hComm, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add,
    Matrix.trace_smul, smul_eq_mul, ← hAct e₁, hCyc]

private lemma spinBiv_cross_trace_zero_02_23 :
    Matrix.trace (diracOmega4 * spinBiv 0 2 * PeirceSpine.comm (solderVec 2) (solderVec 3)) = 0 := by
  rw [palatini_trace_eq_neg_leviCivita4 0 2 2 3]
  have hlc : InfoGeometry.Clifford.LochakRodichevFierzKrein.leviCivita4 0 2 2 3 = 0 := by decide
  rw [hlc]
  norm_num

private lemma spinBiv_cross_trace_zero_03_23 :
    Matrix.trace (diracOmega4 * spinBiv 0 3 * PeirceSpine.comm (solderVec 2) (solderVec 3)) = 0 := by
  rw [palatini_trace_eq_neg_leviCivita4 0 3 2 3]
  have hlc : InfoGeometry.Clifford.LochakRodichevFierzKrein.leviCivita4 0 3 2 3 = 0 := by decide
  rw [hlc]
  norm_num

private lemma scalar_palatini_readout (r01 r02 r03 Λ : ℝ) :
    2 * (r01 * -1 + r02 * 0 + r03 * 0) + Λ * -1 = -(2 * r01 + Λ) := by
  ring

/-- **Theorem 2 (First-Order MacDowell–Mansouri / Palatini `δe` Variation & Λ Readout)**:
1. Exact `HasDerivAt` at `ε = 0` of `mmPalatiniAction R E₀ Λ (e₁ + ε • δe) e₂`.
2. Stationarity at the Einstein–de Sitter locus `2 R + Λ E₀ = 0` for all variations `δe`.
3. Evaluating at `(solderVec 2, solderVec 3)` on `R = r₀₁ Σ₀₁ + r₀₂ Σ₀₂ + r₀₃ Σ₀₃`, `E₀ = Σ₀₁`
   extracts `-(2 * r₀₁ + Λ)`. -/
theorem palatini_delta_e_variation_and_lambda_eq
    (R E₀ e₁ δe e₂ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) (Λ : ℝ) :
    HasDerivAt (fun ε : ℝ => mmPalatiniAction R E₀ Λ (e₁ + ε • δe) e₂)
      (Matrix.trace (δe * PeirceSpine.comm e₂ (diracOmega4 * ((2 : ℝ) • R + Λ • E₀)))) 0 ∧
    ((2 : ℝ) • R + Λ • E₀ = 0 →
      ∀ δX : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ,
        Matrix.trace (δX * PeirceSpine.comm e₂ (diracOmega4 * ((2 : ℝ) • R + Λ • E₀))) = 0) ∧
    (∀ r01 r02 r03 : ℝ,
      mmPalatiniAction (r01 • spinBiv 0 1 + r02 • spinBiv 0 2 + r03 • spinBiv 0 3)
        (spinBiv 0 1) Λ (solderVec 2) (solderVec 3) = -(2 * r01 + Λ)) := by
  refine ⟨?_, ?_, ?_⟩
  · have hEq : (fun ε : ℝ => mmPalatiniAction R E₀ Λ (e₁ + ε • δe) e₂) =
        fun ε : ℝ => mmPalatiniAction R E₀ Λ e₁ e₂ +
          ε * Matrix.trace (δe * PeirceSpine.comm e₂ (diracOmega4 * ((2 : ℝ) • R + Λ • E₀))) := by
      ext ε
      exact mmPalatiniAction_affine R E₀ e₁ δe e₂ Λ ε
    rw [hEq]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const
      (Matrix.trace (δe * PeirceSpine.comm e₂ (diracOmega4 * ((2 : ℝ) • R + Λ • E₀))))).const_add
      (mmPalatiniAction R E₀ Λ e₁ e₂)
  · intro hVac δX
    rw [hVac, Matrix.mul_zero]
    unfold PeirceSpine.comm
    rw [Matrix.mul_zero, Matrix.zero_mul, sub_zero, Matrix.mul_zero, Matrix.trace_zero]
  · intro r01 r02 r03
    have h01 := (soldering_commutators_generate_spin_and_palatini_gravity 0 0 0).2.2.2.1
    have h02 := spinBiv_cross_trace_zero_02_23
    have h03 := spinBiv_cross_trace_zero_03_23
    unfold mmPalatiniAction
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul,
      Matrix.trace_add, Matrix.trace_add,
      Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, h01, h02, h03]
    exact scalar_palatini_readout r01 r02 r03 Λ

/-! ### Part 3: First-Order Einstein–Cartan `δω` & `δT` Variation (Torsion–Axial-Spin Lock) -/

/-- Real `M₄(ℝ)` spin-connection Palatini functional `Tr(γ₅ (dω + [ω₁, ω₂]) E)`. -/
def palatiniSpinAction
    (dω ω₁ ω₂ E : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) : ℝ :=
  Matrix.trace (diracOmega4 * (dω + PeirceSpine.comm ω₁ ω₂) * E)

private lemma palatiniSpinAction_affine
    (dω ω₁ δω ω₂ E : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ) (ε : ℝ) :
    palatiniSpinAction dω (ω₁ + ε • δω) ω₂ E =
      palatiniSpinAction dω ω₁ ω₂ E +
        ε * Matrix.trace (δω * PeirceSpine.comm ω₂ (E * diracOmega4)) := by
  have hComm : PeirceSpine.comm (ω₁ + ε • δω) ω₂ =
      PeirceSpine.comm ω₁ ω₂ + ε • PeirceSpine.comm δω ω₂ := by
    unfold PeirceSpine.comm
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
    abel
  have hCyc : Matrix.trace (diracOmega4 * PeirceSpine.comm δω ω₂ * E) =
      Matrix.trace (δω * PeirceSpine.comm ω₂ (E * diracOmega4)) := by
    unfold PeirceSpine.comm
    have h1 : Matrix.trace (diracOmega4 * (δω * ω₂) * E) =
        Matrix.trace (δω * (ω₂ * (E * diracOmega4))) := by
      rw [Matrix.trace_mul_comm (diracOmega4 * (δω * ω₂)) E,
        ← Matrix.mul_assoc E diracOmega4 (δω * ω₂),
        Matrix.trace_mul_comm (E * diracOmega4) (δω * ω₂),
        Matrix.mul_assoc δω ω₂ (E * diracOmega4)]
    have h2 : Matrix.trace (diracOmega4 * (ω₂ * δω) * E) =
        Matrix.trace (δω * ((E * diracOmega4) * ω₂)) := by
      rw [Matrix.trace_mul_comm (diracOmega4 * (ω₂ * δω)) E,
        ← Matrix.mul_assoc E diracOmega4 (ω₂ * δω),
        ← Matrix.mul_assoc (E * diracOmega4) ω₂ δω,
        Matrix.trace_mul_comm ((E * diracOmega4) * ω₂) δω]
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, h1, h2, Matrix.mul_sub, Matrix.trace_sub]
  unfold palatiniSpinAction
  rw [hComm, ← add_assoc, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.trace_add, Matrix.trace_smul, smul_eq_mul, hCyc]

/-- Algebraic Einstein–Cartan axial torsion–spin Lagrangian
`L_EC(T, J₅) = ½ η(T, T) - κ_EC η(T, J₅)`. -/
def ecTorsionSpinLagrangian (κ_EC : ℝ) (T J₅ : Fin 4 → ℝ) : ℝ :=
  (1 / 2 : ℝ) * minkPair T T - κ_EC * minkPair T J₅

private lemma ecTorsionSpinLagrangian_expand (κ_EC : ℝ) (T δT J₅ : Fin 4 → ℝ) (ε : ℝ) :
    ecTorsionSpinLagrangian κ_EC (fun μ => T μ + ε * δT μ) J₅ =
      ecTorsionSpinLagrangian κ_EC T J₅ +
        ε * minkPair δT (fun μ => T μ - κ_EC * J₅ μ) +
        ε ^ 2 * ((1 / 2 : ℝ) * minkPair δT δT) := by
  simp only [ecTorsionSpinLagrangian, minkPair]
  ring

private lemma scalar_deriv_quad (c₀ c₁ c₂ : ℝ) :
    HasDerivAt (fun ε : ℝ => c₀ + ε * c₁ + ε ^ 2 * c₂) c₁ 0 := by
  have h1 : HasDerivAt (fun ε : ℝ => c₀ + ε * c₁) c₁ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c₁).const_add c₀
  have h2 : HasDerivAt (fun ε : ℝ => ε ^ 2 * c₂) 0 0 := by
    simpa using (hasDerivAt_pow 2 (0 : ℝ)).mul_const c₂
  simpa using h1.fun_add h2

private lemma minkPair_perp_iff (v : Fin 4 → ℝ) :
    (∀ δT : Fin 4 → ℝ, minkPair δT v = 0) ↔ ∀ μ : Fin 4, v μ = 0 := by
  constructor
  · intro h μ
    fin_cases μ
    · have h0 := h ![1, 0, 0, 0]
      simp [minkPair] at h0
      exact h0
    · have h1 := h ![0, 1, 0, 0]
      simp [minkPair] at h1
      exact h1
    · have h2 := h ![0, 0, 1, 0]
      simp [minkPair] at h2
      exact h2
    · have h3 := h ![0, 0, 0, 1]
      simp [minkPair] at h3
      exact h3
  · intro hv δT
    simp [minkPair, hv 0, hv 1, hv 2, hv 3]

private lemma scalar_ec_fkr_eval
    (a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ κ_EC : ℝ) :
    let j5 := diracAxialCurrent a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂
    let Ω₁ := diracScalarOmega1 a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂
    let Ω₂ := diracPseudoscalarOmega2 a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂
    ecTorsionSpinLagrangian κ_EC (fun μ => κ_EC * j5 μ) j5 =
      (1 / 2 : ℝ) * κ_EC ^ 2 * (Ω₁ ^ 2 + Ω₂ ^ 2) := by
  dsimp
  have hFKR := fierz_kofink_rodichev_chiral_null_current_identities a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ κ_EC
  dsimp at hFKR
  have hJ5 := hFKR.2.2.1
  have hSJ5 := hFKR.2.2.2.2
  have hM1 : minkPair (fun μ => κ_EC * diracAxialCurrent a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ μ)
      (fun μ => κ_EC * diracAxialCurrent a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ μ) =
      -(κ_EC ^ 2 * ((diracScalarOmega1 a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂) ^ 2 +
        (diracPseudoscalarOmega2 a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂) ^ 2)) := by
    have hScale : minkPair (fun μ => κ_EC * diracAxialCurrent a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ μ)
        (fun μ => κ_EC * diracAxialCurrent a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ μ) =
        κ_EC ^ 2 * minkPair (diracAxialCurrent a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂)
          (diracAxialCurrent a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂) := by
      simp only [minkPair]; ring
    rw [hScale, hJ5]
    ring
  have hM2 : minkPair (fun μ => κ_EC * diracAxialCurrent a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ μ)
      (diracAxialCurrent a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂) =
      -(κ_EC * ((diracScalarOmega1 a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂) ^ 2 +
        (diracPseudoscalarOmega2 a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂) ^ 2)) := by
    linarith [hSJ5]
  unfold ecTorsionSpinLagrangian
  rw [hM1, hM2]
  ring

/-- **Theorem 3 (First-Order Einstein–Cartan `δω` & `δT` Variations and Torsion–Spin Lock)**:
1. `HasDerivAt` of `palatiniSpinAction dω (ω₁ + ε • δω) ω₂ E` at `ε = 0` equals
   `Tr(δω * [ω₂, E * γ₅])`, vanishing for all `δω` whenever `ω₂` is `γ₅`-even and `[ω₂, E] = 0`.
2. `HasDerivAt` of `ecTorsionSpinLagrangian κ_EC (T + ε δT) J₅` at `ε = 0` equals
   `η(δT, T - κ_EC J₅)`.
3. Stationarity holds for all `δT` **iff** `T = κ_EC J₅` (collapsing to `T = 0` in vacuum `J₅ = 0`).
4. On shell along `J₅ = diracAxialCurrent ...`, the Fierz–Kofink–Rodichev identity evaluates the
   Lagrangian to `(1 / 2) * κ_EC² * (Ω₁² + Ω₂²)`. -/
theorem einstein_cartan_delta_omega_and_torsion_spin_lock
    (dω ω₁ δω ω₂ E : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ)
    (κ_EC : ℝ) (T δT J₅ : Fin 4 → ℝ) :
    (HasDerivAt (fun ε : ℝ => palatiniSpinAction dω (ω₁ + ε • δω) ω₂ E)
      (Matrix.trace (δω * PeirceSpine.comm ω₂ (E * diracOmega4))) 0) ∧
    (diracOmega4 * ω₂ = ω₂ * diracOmega4 →
      PeirceSpine.comm ω₂ E = 0 →
      ∀ δX : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℝ,
        Matrix.trace (δX * PeirceSpine.comm ω₂ (E * diracOmega4)) = 0) ∧
    (HasDerivAt (fun ε : ℝ => ecTorsionSpinLagrangian κ_EC (fun μ => T μ + ε * δT μ) J₅)
      (minkPair δT (fun μ => T μ - κ_EC * J₅ μ)) 0) ∧
    ((∀ dT : Fin 4 → ℝ, minkPair dT (fun μ => T μ - κ_EC * J₅ μ) = 0) ↔
      (∀ μ : Fin 4, T μ = κ_EC * J₅ μ)) ∧
    ((∀ dT : Fin 4 → ℝ, minkPair dT T = 0) ↔ (∀ μ : Fin 4, T μ = 0)) ∧
    (∀ a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ : ℝ,
      let j5 := diracAxialCurrent a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂
      let Ω₁ := diracScalarOmega1 a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂
      let Ω₂ := diracPseudoscalarOmega2 a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂
      ecTorsionSpinLagrangian κ_EC (fun μ => κ_EC * j5 μ) j5 =
        (1 / 2 : ℝ) * κ_EC ^ 2 * (Ω₁ ^ 2 + Ω₂ ^ 2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hEq : (fun ε : ℝ => palatiniSpinAction dω (ω₁ + ε • δω) ω₂ E) =
        fun ε : ℝ => palatiniSpinAction dω ω₁ ω₂ E +
          ε * Matrix.trace (δω * PeirceSpine.comm ω₂ (E * diracOmega4)) := by
      ext ε
      exact palatiniSpinAction_affine dω ω₁ δω ω₂ E ε
    rw [hEq]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const
      (Matrix.trace (δω * PeirceSpine.comm ω₂ (E * diracOmega4)))).const_add
      (palatiniSpinAction dω ω₁ ω₂ E)
  · intro hW hWE δX
    have hZero : PeirceSpine.comm ω₂ (E * diracOmega4) = 0 := by
      unfold PeirceSpine.comm at hWE ⊢
      have hWE' : ω₂ * E = E * ω₂ := sub_eq_zero.mp hWE
      calc
        ω₂ * (E * diracOmega4) - (E * diracOmega4) * ω₂
            = (ω₂ * E) * diracOmega4 - E * (diracOmega4 * ω₂) := by noncomm_ring
        _ = (E * ω₂) * diracOmega4 - E * (ω₂ * diracOmega4) := by rw [hWE', hW]
        _ = 0 := by noncomm_ring
    rw [hZero, Matrix.mul_zero, Matrix.trace_zero]
  · have hEq : (fun ε : ℝ => ecTorsionSpinLagrangian κ_EC (fun μ => T μ + ε * δT μ) J₅) =
        fun ε : ℝ => ecTorsionSpinLagrangian κ_EC T J₅ +
          ε * minkPair δT (fun μ => T μ - κ_EC * J₅ μ) +
          ε ^ 2 * ((1 / 2 : ℝ) * minkPair δT δT) := by
      ext ε
      exact ecTorsionSpinLagrangian_expand κ_EC T δT J₅ ε
    rw [hEq]
    exact scalar_deriv_quad _ _ _
  · rw [minkPair_perp_iff]
    exact ⟨fun h μ => sub_eq_zero.mp (h μ), fun h μ => sub_eq_zero.mpr (h μ)⟩
  · exact minkPair_perp_iff T
  · intro a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂
    exact scalar_ec_fkr_eval a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ κ_EC

end InfoGeometry.Canonical.RealDiracPalatiniVariationBridge
