/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Clifford.SpinorRep
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# The two commuting bivectors in the native `Cl(3,3)` owner

This file uses the repository's recursive split Clifford carrier and its
native real spinor representation. It proves the hyperbolic and elliptic
square laws and commutation for the chosen orthogonal coordinate bivectors,
then transports those identities to the full `8 × 8` real spinor matrices.
It does not identify the `4 × 4` matrix toy with `Cl(3,3)`, nor claim a
twistor/projective action or a Tomita/RoPE interpretation.
-/

noncomputable section

namespace InfoGeometry.Clifford.Cl33BivectorLoxodromicBridge

open InfoGeometry.Clifford.SpinorRep
open InfoGeometry.CliffordTower

abbrev Carrier := InfoGeometry.CliffordTower.SplitSpace 3
abbrev Algebra := Cl_split 3
abbrev Q33 := InfoGeometry.CliffordTower.Qsplit 3
abbrev SpinorMatrix := Matrix (Fin 8) (Fin 8) ℝ

/-- The first positive coordinate vector in the recursive split carrier. -/
def e₁ : Carrier := ((1, 0), 0)

/-- The first negative coordinate vector in the recursive split carrier. -/
def f₁ : Carrier := ((0, 1), 0)

/-- The second positive coordinate vector in the recursive split carrier. -/
def e₂ : Carrier := ((0, 0), ((1, 0), 0))

/-- The third positive coordinate vector in the recursive split carrier. -/
def e₃ : Carrier := ((0, 0), ((0, 0), ((1, 0), 0)))

/-- Clifford vector represented by a carrier vector. -/
def γ (v : Carrier) : Algebra := CliffordAlgebra.ι (Q33) v

/-- The mixed positive-negative bivector. -/
def boostBivector : Algebra := γ e₁ * γ f₁

/-- The positive-positive transverse bivector. -/
def rotationBivector : Algebra := γ e₂ * γ e₃

/-- The unnormalised first null vector in the positive Witt sheet. -/
def wittU₁ : Algebra := γ e₁ + γ f₁

/-- The unnormalised first null vector in the negative Witt sheet. -/
def wittV₁ : Algebra := γ e₁ - γ f₁

private theorem e₁_f₁_ortho : (Q33).IsOrtho e₁ f₁ := by
  rw [QuadraticMap.isOrtho_def]
  norm_num [e₁, f₁, Q33, InfoGeometry.CliffordTower.Qsplit,
    InfoGeometry.CliffordTower.Q11_apply, QuadraticMap.prod]

private theorem e₂_e₃_ortho : Q33.IsOrtho e₂ e₃ := by
  rw [QuadraticMap.isOrtho_def]
  norm_num [e₂, e₃, Q33, InfoGeometry.CliffordTower.Qsplit,
    InfoGeometry.CliffordTower.Q11_apply, QuadraticMap.prod]

private theorem e₁_e₂_ortho : Q33.IsOrtho e₁ e₂ := by
  rw [QuadraticMap.isOrtho_def]
  norm_num [e₁, e₂, Q33, InfoGeometry.CliffordTower.Qsplit,
    InfoGeometry.CliffordTower.Q11_apply, QuadraticMap.prod]

private theorem e₁_e₃_ortho : Q33.IsOrtho e₁ e₃ := by
  rw [QuadraticMap.isOrtho_def]
  norm_num [e₁, e₃, Q33, InfoGeometry.CliffordTower.Qsplit,
    InfoGeometry.CliffordTower.Q11_apply, QuadraticMap.prod]

private theorem f₁_e₂_ortho : Q33.IsOrtho f₁ e₂ := by
  rw [QuadraticMap.isOrtho_def]
  norm_num [f₁, e₂, Q33, InfoGeometry.CliffordTower.Qsplit,
    InfoGeometry.CliffordTower.Q11_apply, QuadraticMap.prod]

private theorem f₁_e₃_ortho : Q33.IsOrtho f₁ e₃ := by
  rw [QuadraticMap.isOrtho_def]
  norm_num [f₁, e₃, Q33, InfoGeometry.CliffordTower.Qsplit,
    InfoGeometry.CliffordTower.Q11_apply, QuadraticMap.prod]

private theorem e₁_sq : Q33 e₁ = 1 := by
  norm_num [e₁, Q33, InfoGeometry.CliffordTower.Qsplit,
    InfoGeometry.CliffordTower.Q11_apply, QuadraticMap.prod]

private theorem f₁_sq : Q33 f₁ = -1 := by
  norm_num [f₁, Q33, InfoGeometry.CliffordTower.Qsplit,
    InfoGeometry.CliffordTower.Q11_apply, QuadraticMap.prod]

private theorem gamma_e₁_sq : γ e₁ * γ e₁ = 1 := by
  unfold γ
  rw [CliffordAlgebra.ι_sq_scalar, e₁_sq]
  simp

private theorem gamma_f₁_sq : γ f₁ * γ f₁ = -1 := by
  unfold γ
  rw [CliffordAlgebra.ι_sq_scalar, f₁_sq]
  simp

private theorem gamma_e₁_f₁_anticommute :
    γ e₁ * γ f₁ = -(γ f₁ * γ e₁) :=
  CliffordAlgebra.ι_mul_ι_comm_of_isOrtho e₁_f₁_ortho

private theorem gamma_f₁_e₁_anticommute :
    γ f₁ * γ e₁ = -(γ e₁ * γ f₁) := by
  calc
    γ f₁ * γ e₁ = -(-(γ f₁ * γ e₁)) := by simp
    _ = -(γ e₁ * γ f₁) := by rw [← gamma_e₁_f₁_anticommute]

/-- The first Witt generator is null in the Clifford algebra. -/
theorem wittU₁_sq_zero : wittU₁ * wittU₁ = 0 := by
  unfold wittU₁
  rw [add_mul, mul_add, mul_add, gamma_e₁_sq, gamma_f₁_sq,
    gamma_e₁_f₁_anticommute, gamma_f₁_e₁_anticommute]
  abel

/-- The paired first Witt generator is null in the Clifford algebra. -/
theorem wittV₁_sq_zero : wittV₁ * wittV₁ = 0 := by
  unfold wittV₁
  rw [sub_mul, mul_sub, mul_sub, gamma_e₁_sq, gamma_f₁_sq,
    gamma_e₁_f₁_anticommute, gamma_f₁_e₁_anticommute]
  abel

/-- Left multiplication by the boost bivector has eigenvalue `-1` on the
positive null vector `e₁ + f₁`. This fixes the sign of the Witt action for
the repository's convention `ι(v) * ι(v) = Q(v)`. -/
theorem boostBivector_wittU₁ : boostBivector * wittU₁ = -wittU₁ := by
  unfold boostBivector wittU₁
  rw [mul_add]
  have h₁ : (γ e₁ * γ f₁) * γ e₁ = -γ f₁ := by
    calc
      (γ e₁ * γ f₁) * γ e₁ = γ e₁ * (γ f₁ * γ e₁) := by noncomm_ring
      _ = γ e₁ * (-(γ e₁ * γ f₁)) := by rw [gamma_f₁_e₁_anticommute]
      _ = -γ f₁ := by rw [mul_neg, ← mul_assoc, gamma_e₁_sq, one_mul]
  have h₂ : (γ e₁ * γ f₁) * γ f₁ = -γ e₁ := by
    rw [mul_assoc, gamma_f₁_sq]
    simp
  rw [h₁, h₂]
  abel

/-- Left multiplication by the boost bivector has eigenvalue `+1` on the
negative null vector `e₁ - f₁`. -/
theorem boostBivector_wittV₁ : boostBivector * wittV₁ = wittV₁ := by
  unfold boostBivector wittV₁
  rw [mul_sub]
  have h₁ : (γ e₁ * γ f₁) * γ e₁ = -γ f₁ := by
    calc
      (γ e₁ * γ f₁) * γ e₁ = γ e₁ * (γ f₁ * γ e₁) := by noncomm_ring
      _ = γ e₁ * (-(γ e₁ * γ f₁)) := by rw [gamma_f₁_e₁_anticommute]
      _ = -γ f₁ := by rw [mul_neg, ← mul_assoc, gamma_e₁_sq, one_mul]
  have h₂ : (γ e₁ * γ f₁) * γ f₁ = -γ e₁ := by
    rw [mul_assoc, gamma_f₁_sq]
    simp
  rw [h₁, h₂]
  abel

private theorem e₂_sq : Q33 e₂ = 1 := by
  norm_num [e₂, Q33, InfoGeometry.CliffordTower.Qsplit,
    InfoGeometry.CliffordTower.Q11_apply, QuadraticMap.prod]

private theorem e₃_sq : Q33 e₃ = 1 := by
  norm_num [e₃, Q33, InfoGeometry.CliffordTower.Qsplit,
    InfoGeometry.CliffordTower.Q11_apply, QuadraticMap.prod]

/-- The mixed bivector has square `+1` in the full split Clifford algebra. -/
theorem boostBivector_sq : boostBivector * boostBivector = 1 := by
  unfold boostBivector γ
  let x := CliffordAlgebra.ι Q33 e₁
  let y := CliffordAlgebra.ι Q33 f₁
  have hxy : x * y = -(y * x) :=
    CliffordAlgebra.ι_mul_ι_comm_of_isOrtho e₁_f₁_ortho
  have hswap : y * x = -(x * y) := by
    calc
      y * x = -(-(y * x)) := by simp
      _ = -(x * y) := by rw [← hxy]
  have hx : x * x = algebraMap ℝ Algebra (Q33 e₁) := by
    dsimp [x]
    exact CliffordAlgebra.ι_sq_scalar Q33 e₁
  have hy : y * y = algebraMap ℝ Algebra (Q33 f₁) := by
    dsimp [y]
    exact CliffordAlgebra.ι_sq_scalar Q33 f₁
  change (x * y) * (x * y) = 1
  calc
    (x * y) * (x * y) = x * (y * x) * y := by noncomm_ring
    _ = x * (-(x * y)) * y := by rw [hswap]
    _ = -(x * x) * (y * y) := by noncomm_ring
    _ = 1 := by
      rw [hx, hy, e₁_sq, f₁_sq]
      simp

/-- The positive transverse bivector has square `-1` in the full split Clifford algebra. -/
theorem rotationBivector_sq : rotationBivector * rotationBivector = -1 := by
  unfold rotationBivector γ
  let x := CliffordAlgebra.ι Q33 e₂
  let y := CliffordAlgebra.ι Q33 e₃
  have hxy : x * y = -(y * x) :=
    CliffordAlgebra.ι_mul_ι_comm_of_isOrtho e₂_e₃_ortho
  have hswap : y * x = -(x * y) := by
    calc
      y * x = -(-(y * x)) := by simp
      _ = -(x * y) := by rw [← hxy]
  have hx : x * x = algebraMap ℝ Algebra (Q33 e₂) := by
    dsimp [x]
    exact CliffordAlgebra.ι_sq_scalar Q33 e₂
  have hy : y * y = algebraMap ℝ Algebra (Q33 e₃) := by
    dsimp [y]
    exact CliffordAlgebra.ι_sq_scalar Q33 e₃
  change (x * y) * (x * y) = -1
  calc
    (x * y) * (x * y) = x * (y * x) * y := by noncomm_ring
    _ = x * (-(x * y)) * y := by rw [hswap]
    _ = -(x * x) * (y * y) := by noncomm_ring
    _ = -1 := by
      rw [hx, hy, e₂_sq, e₃_sq]
      simp

/-- The two disjoint bivectors commute in the full split Clifford algebra. -/
theorem boost_rotation_commute :
    boostBivector * rotationBivector = rotationBivector * boostBivector := by
  unfold boostBivector rotationBivector γ
  let a := CliffordAlgebra.ι Q33 e₁
  let b := CliffordAlgebra.ι Q33 f₁
  let c := CliffordAlgebra.ι Q33 e₂
  let d := CliffordAlgebra.ι Q33 e₃
  have h_ac : a * c = -(c * a) := by
    exact CliffordAlgebra.ι_mul_ι_comm_of_isOrtho e₁_e₂_ortho
  have h_ad : a * d = -(d * a) := by
    exact CliffordAlgebra.ι_mul_ι_comm_of_isOrtho e₁_e₃_ortho
  have h_bc : b * c = -(c * b) := by
    exact CliffordAlgebra.ι_mul_ι_comm_of_isOrtho f₁_e₂_ortho
  have h_bd : b * d = -(d * b) := by
    exact CliffordAlgebra.ι_mul_ι_comm_of_isOrtho f₁_e₃_ortho
  calc
    (a * b) * (c * d) = a * (b * c) * d := by noncomm_ring
    _ = a * (-(c * b)) * d := by rw [h_bc]
    _ = -(a * c) * (b * d) := by noncomm_ring
    _ = -(-(c * a)) * (b * d) := by rw [h_ac]
    _ = c * a * (b * d) := by noncomm_ring
    _ = -(c * a * d) * b := by rw [h_bd]; noncomm_ring
    _ = -(c * (-(d * a))) * b := by
      calc
        -(c * a * d) * b = -(c * (a * d)) * b := by noncomm_ring
        _ = -(c * (-(d * a))) * b := by rw [h_ad]
    _ = (c * d) * (a * b) := by noncomm_ring

/-- The Clifford vector generators for two orthogonal positive directions do
not commute. This rules out treating the split Clifford action as a commutative
or diagonal proxy. -/
theorem positive_generators_noncommute : γ e₁ * γ e₂ ≠ γ e₂ * γ e₁ := by
  let x := γ e₁
  let y := γ e₂
  have hxy : x * y = -(y * x) := by
    simpa [x, y, γ] using
      (CliffordAlgebra.ι_mul_ι_comm_of_isOrtho e₁_e₂_ortho)
  have hx : x * x = 1 := by
    dsimp [x, γ]
    rw [CliffordAlgebra.ι_sq_scalar, e₁_sq]
    simp
  have hy : y * y = 1 := by
    dsimp [y, γ]
    rw [CliffordAlgebra.ι_sq_scalar, e₂_sq]
    simp
  have hswap : y * x = -(x * y) := by
    calc
      y * x = -(-(y * x)) := by simp
      _ = -(x * y) := by rw [← hxy]
  intro hcomm
  have hsq_pos : (x * y) * (x * y) = 1 := by
    have hcomm' : x * y = y * x := by simpa [x, y, γ] using hcomm
    calc
      (x * y) * (x * y) = x * y * x * y := by noncomm_ring
      _ = x * (y * x) * y := by noncomm_ring
      _ = x * (x * y) * y := by rw [hcomm']
      _ = x * x * (y * y) := by noncomm_ring
      _ = 1 := by rw [hx, hy]; simp
  have hsq_neg : (x * y) * (x * y) = -1 := by
    calc
      (x * y) * (x * y) = x * y * x * y := by noncomm_ring
      _ = x * (y * x) * y := by noncomm_ring
      _ = x * (-(x * y)) * y := by rw [hswap]
      _ = -(x * x) * (y * y) := by noncomm_ring
      _ = -1 := by rw [hx, hy]; simp
  have hone : (1 : Algebra) = -1 := hsq_pos.symm.trans hsq_neg
  have hone_map : algebraMap ℝ Algebra (1 : ℝ) = algebraMap ℝ Algebra (-1 : ℝ) := by
    simpa using hone
  have honeR : (1 : ℝ) = -1 := FaithfulSMul.algebraMap_injective ℝ Algebra hone_map
  norm_num at honeR

/-- The canonical full `8 × 8` real spinor matrix readout of the boost bivector. -/
def boostMatrix : SpinorMatrix := spinorRepresentation 3 boostBivector

/-- The canonical full `8 × 8` real spinor matrix readout of the rotation bivector. -/
def rotationMatrix : SpinorMatrix := spinorRepresentation 3 rotationBivector

/-- The full-spinor matrix readout of the first positive Clifford generator. -/
def positiveGeneratorMatrix₁ : SpinorMatrix := spinorRepresentation 3 (γ e₁)

/-- The full-spinor matrix readout of the second positive Clifford generator. -/
def positiveGeneratorMatrix₂ : SpinorMatrix := spinorRepresentation 3 (γ e₂)

/-- The represented boost matrix squares to identity. -/
theorem boostMatrix_sq : boostMatrix * boostMatrix = 1 := by
  change spinorRepresentation 3 boostBivector * spinorRepresentation 3 boostBivector = 1
  rw [← map_mul]
  rw [boostBivector_sq]
  simp

/-- The represented rotation matrix squares to minus identity. -/
theorem rotationMatrix_sq : rotationMatrix * rotationMatrix = -1 := by
  change spinorRepresentation 3 rotationBivector * spinorRepresentation 3 rotationBivector = -1
  rw [← map_mul, rotationBivector_sq]
  simp

/-- The represented boost and rotation commute as full `8 × 8` matrices. -/
theorem boostMatrix_rotationMatrix_commute :
    boostMatrix * rotationMatrix = rotationMatrix * boostMatrix := by
  change spinorRepresentation 3 boostBivector * spinorRepresentation 3 rotationBivector =
    spinorRepresentation 3 rotationBivector * spinorRepresentation 3 boostBivector
  rw [← map_mul, ← map_mul, boost_rotation_commute]

/-- The two positive Clifford generators remain noncommuting in the actual
`8 × 8` spinor matrix readout. -/
theorem positive_spinor_generators_noncommute :
    positiveGeneratorMatrix₁ * positiveGeneratorMatrix₂ ≠
      positiveGeneratorMatrix₂ * positiveGeneratorMatrix₁ := by
  have h₁cl : γ e₁ * γ e₁ = 1 := by
    dsimp [γ]
    rw [CliffordAlgebra.ι_sq_scalar, e₁_sq]
    simp
  have h₂cl : γ e₂ * γ e₂ = 1 := by
    dsimp [γ]
    rw [CliffordAlgebra.ι_sq_scalar, e₂_sq]
    simp
  have h₁ : positiveGeneratorMatrix₁ * positiveGeneratorMatrix₁ = 1 := by
    have := congrArg (spinorRepresentation 3) h₁cl
    simpa [positiveGeneratorMatrix₁] using this
  have h₂ : positiveGeneratorMatrix₂ * positiveGeneratorMatrix₂ = 1 := by
    have := congrArg (spinorRepresentation 3) h₂cl
    simpa [positiveGeneratorMatrix₂] using this
  have hantiCl : γ e₁ * γ e₂ = -(γ e₂ * γ e₁) := by
    simpa [γ] using
      (CliffordAlgebra.ι_mul_ι_comm_of_isOrtho e₁_e₂_ortho)
  have hanti : positiveGeneratorMatrix₁ * positiveGeneratorMatrix₂ =
      -(positiveGeneratorMatrix₂ * positiveGeneratorMatrix₁) := by
    have := congrArg (spinorRepresentation 3) hantiCl
    simpa [positiveGeneratorMatrix₁, positiveGeneratorMatrix₂] using this
  intro hcomm
  have hswap : positiveGeneratorMatrix₂ * positiveGeneratorMatrix₁ =
      -(positiveGeneratorMatrix₁ * positiveGeneratorMatrix₂) := by
    calc
      positiveGeneratorMatrix₂ * positiveGeneratorMatrix₁ =
          -(-(positiveGeneratorMatrix₂ * positiveGeneratorMatrix₁)) := by simp
      _ = -(positiveGeneratorMatrix₁ * positiveGeneratorMatrix₂) := by rw [← hanti]
  have hsq₁ : (positiveGeneratorMatrix₁ * positiveGeneratorMatrix₂) *
      (positiveGeneratorMatrix₁ * positiveGeneratorMatrix₂) = 1 := by
    calc
      _ = positiveGeneratorMatrix₁ * positiveGeneratorMatrix₂ *
          positiveGeneratorMatrix₁ * positiveGeneratorMatrix₂ := by noncomm_ring
      _ = positiveGeneratorMatrix₁ *
          (positiveGeneratorMatrix₂ * positiveGeneratorMatrix₁) *
          positiveGeneratorMatrix₂ := by noncomm_ring
      _ = positiveGeneratorMatrix₁ *
          (positiveGeneratorMatrix₁ * positiveGeneratorMatrix₂) *
          positiveGeneratorMatrix₂ := by rw [hcomm]
      _ = positiveGeneratorMatrix₁ * positiveGeneratorMatrix₁ *
          (positiveGeneratorMatrix₂ * positiveGeneratorMatrix₂) := by noncomm_ring
      _ = 1 := by rw [h₁, h₂]; simp
  have hsq₂ : (positiveGeneratorMatrix₁ * positiveGeneratorMatrix₂) *
      (positiveGeneratorMatrix₁ * positiveGeneratorMatrix₂) = -1 := by
    calc
      _ = positiveGeneratorMatrix₁ *
          (positiveGeneratorMatrix₂ * positiveGeneratorMatrix₁) *
          positiveGeneratorMatrix₂ := by noncomm_ring
      _ = positiveGeneratorMatrix₁ *
          (-(positiveGeneratorMatrix₁ * positiveGeneratorMatrix₂)) *
          positiveGeneratorMatrix₂ := by rw [hswap]
      _ = -(positiveGeneratorMatrix₁ * positiveGeneratorMatrix₁) *
          (positiveGeneratorMatrix₂ * positiveGeneratorMatrix₂) := by noncomm_ring
      _ = -1 := by rw [h₁, h₂]; simp
  have hone : (1 : SpinorMatrix) = -1 := hsq₁.symm.trans hsq₂
  have honeEntry : (1 : ℝ) = -1 := by
    have h := congrArg (fun M : SpinorMatrix => M 0 0) hone
    simpa using h
  norm_num at honeEntry

/-- The sum of the commuting hyperbolic and elliptic spinor generators. -/
def loxodromicGenerator (b ω : ℝ) : SpinorMatrix :=
  b • boostMatrix + ω • rotationMatrix

/-- Exponential of the combined finite spinor generator factors into the two
commuting exponentials. This is an algebraic matrix identity; it asserts no
analytic continuation or physical modular-flow interpretation. -/
theorem exp_loxodromicGenerator (b ω τ : ℝ) :
    NormedSpace.exp (τ • loxodromicGenerator b ω) =
      NormedSpace.exp (τ • b • boostMatrix) * NormedSpace.exp (τ • ω • rotationMatrix) := by
  have hcomm : Commute (τ • b • boostMatrix) (τ • ω • rotationMatrix) := by
    have hmul : (τ • b • boostMatrix) * (τ • ω • rotationMatrix) =
        (τ • ω • rotationMatrix) * (τ • b • boostMatrix) := by
      rw [smul_smul, smul_smul, smul_mul_smul_comm, smul_mul_smul_comm,
        boostMatrix_rotationMatrix_commute]
      congr 1
      ring
    simpa [Commute, SemiconjBy] using hmul
  have hsplit : τ • loxodromicGenerator b ω =
      (τ • b • boostMatrix) + (τ • ω • rotationMatrix) := by
    simp [loxodromicGenerator, smul_add, smul_smul, mul_comm]
  rw [hsplit]
  exact Matrix.exp_add_of_commute _ _ hcomm

end InfoGeometry.Clifford.Cl33BivectorLoxodromicBridge
