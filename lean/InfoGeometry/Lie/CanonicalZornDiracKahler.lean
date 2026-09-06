import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Lie.CanonicalZornClifford

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornDiracKahler

open InfoGeometry.Lie.CanonicalZornCircularHodgeTransport
open InfoGeometry.Lie.CanonicalZornClifford

abbrev CZ := InfoGeometry.Canonical.ZornMatrix ℝ
abbrev EndCZ := Module.End ℝ CZ

/-! ### 1. Clifford Elements and Module Action Bridge -/

/-- Clifford basis vector e₀ = ι(1, 0), generating the Hodge star. -/
def e0 : CliffordAlgebra Q11 := CliffordAlgebra.ι Q11 (1, 0)

/-- Clifford basis vector e₁ = ι(0, 1), generating the complex structure. -/
def e1 : CliffordAlgebra Q11 := CliffordAlgebra.ι Q11 (0, 1)

/-- Clifford volume pseudoscalar ω = e₀ e₁, generating graded chirality. -/
def omega : CliffordAlgebra Q11 := e0 * e1

@[simp] theorem cl11Rep_e0 : cl11Rep e0 = circularHodgeStar :=
  cl11Rep_ι_star

@[simp] theorem cl11Rep_omega : cl11Rep omega = circularGradedChirality := by
  rw [omega, e0, e1, cl11Rep_pseudoscalar]

@[simp] theorem e0_smul (x : CZ) : e0 • x = circularHodgeStar x := by
  change cl11Rep e0 x = circularHodgeStar x
  rw [cl11Rep_e0]

@[simp] theorem omega_smul (x : CZ) : omega • x = circularGradedChirality x := by
  change cl11Rep omega x = circularGradedChirality x
  rw [cl11Rep_omega]

/-- The Clifford generator e₀ acts as an involution on the carrier. -/
@[simp] theorem e0_smul_e0_smul (x : CZ) : e0 • (e0 • x) = x := by
  rw [e0_smul, e0_smul]
  exact LinearMap.congr_fun circularHodgeStar_sq x

theorem cl11Rep_e0_sq : cl11Rep e0 * cl11Rep e0 = 1 := by
  rw [cl11Rep_e0, circularHodgeStar_sq]

theorem cl11Rep_omega_sq : cl11Rep omega * cl11Rep omega = 1 := by
  rw [cl11Rep_omega, circularGradedChirality_sq]

theorem cl11Rep_e0_anticommute_omega :
    cl11Rep e0 * cl11Rep omega = -(cl11Rep omega * cl11Rep e0) := by
  rw [cl11Rep_e0, cl11Rep_omega, circularHodgeStar_gradedChirality_anticommutes]

@[simp] theorem cl11Rep_e1 : cl11Rep e1 = circularHodgeStar * circularGradedChirality :=
  cl11Rep_ι_complex

theorem cl11Rep_e1_anticommute_omega :
    cl11Rep e1 * cl11Rep omega = -(cl11Rep omega * cl11Rep e1) := by
  rw [cl11Rep_e1, cl11Rep_omega]
  have h1 : (circularHodgeStar * circularGradedChirality) * circularGradedChirality =
      circularHodgeStar := by
    rw [mul_assoc, circularGradedChirality_sq, mul_one]
  have h_anti : circularGradedChirality * circularHodgeStar =
      -(circularHodgeStar * circularGradedChirality) := by
    rw [← neg_neg (circularGradedChirality * circularHodgeStar),
        ← circularHodgeStar_gradedChirality_anticommutes]
  have h2 : circularGradedChirality * (circularHodgeStar * circularGradedChirality) =
      -circularHodgeStar := by
    rw [← mul_assoc, h_anti, neg_mul, mul_assoc, circularGradedChirality_sq, mul_one]
  rw [h1, h2, neg_neg]

/-! ### 2. The Discrete Codifferential and Dirac-Kähler Operator -/

/-- The discrete codifferential δ = -⋆d⋆ expressed via e₀ conjugation. -/
def codiff (d : EndCZ) : EndCZ :=
  -(cl11Rep e0 * d * cl11Rep e0)

/-- Pointwise evaluation of the codifferential via the Cl(1,1) module action:
    δ(x) = -(e₀ • d(e₀ • x)). -/
theorem codiff_apply (d : EndCZ) (x : CZ) :
    codiff d x = -(e0 • d (e0 • x)) := by
  simp only [codiff, LinearMap.neg_apply, Module.End.mul_apply]
  rfl

/-- The discrete Dirac-Kähler operator D = d - δ = d + ⋆d⋆. -/
def diracKahler (d : EndCZ) : EndCZ :=
  d - codiff d

/-- Pointwise evaluation of the Dirac-Kähler operator:
    D(x) = d(x) + e₀ • d(e₀ • x). -/
theorem diracKahler_apply (d : EndCZ) (x : CZ) :
    diracKahler d x = d x + e0 • d (e0 • x) := by
  simp only [diracKahler, codiff_apply, sub_neg_eq_add, LinearMap.sub_apply]

/-! ### 3. Fundamental Structural Theorems -/

/-- **Nilpotency of the Codifferential**:
    If d² = 0, then δ² = 0, proved purely by e₀ involution cancelation. -/
theorem codiff_sq (d : EndCZ) (hd : d * d = 0) :
    codiff d * codiff d = 0 := by
  dsimp [codiff]
  rw [neg_mul_neg]
  have h_assoc :
      (cl11Rep e0 * d * cl11Rep e0) * (cl11Rep e0 * d * cl11Rep e0) =
        cl11Rep e0 * d * (cl11Rep e0 * cl11Rep e0) * d * cl11Rep e0 := by
    simp only [mul_assoc]
  rw [h_assoc, cl11Rep_e0_sq, mul_one, mul_assoc (cl11Rep e0) d d, hd,
      mul_zero, zero_mul]

/-- **Hodge Invariance of the Dirac-Kähler Operator**:
    D is self-dual under Clifford e₀ conjugation: e₀ D e₀ = D. -/
theorem diracKahler_hodge_conjugate (d : EndCZ) :
    cl11Rep e0 * diracKahler d * cl11Rep e0 = diracKahler d := by
  dsimp [diracKahler, codiff]
  simp only [sub_neg_eq_add, mul_add, add_mul]
  have h_inner :
      cl11Rep e0 * (cl11Rep e0 * d * cl11Rep e0) * cl11Rep e0 = d := by
    simp only [mul_assoc]
    rw [← mul_assoc (cl11Rep e0), cl11Rep_e0_sq, one_mul, mul_one]
  rw [h_inner, add_comm]

/-- Pointwise version: e₀ • D(e₀ • x) = D(x). -/
theorem diracKahler_hodge_conjugate_apply (d : EndCZ) (x : CZ) :
    e0 • (diracKahler d (e0 • x)) = diracKahler d x := by
  have h := LinearMap.congr_fun (diracKahler_hodge_conjugate d) x
  simpa only [Module.End.mul_apply] using h

/-! ### 4. Chirality Anticommutation and the Hodge Laplacian -/

/-- If the differential d is an odd operator ({d, ω} = 0), then the codifferential δ
    is also odd ({δ, ω} = 0). -/
theorem codiff_anticommute_omega (d : EndCZ)
    (h_odd : d * cl11Rep omega = -(cl11Rep omega * d)) :
    codiff d * cl11Rep omega = -(cl11Rep omega * codiff d) := by
  have h_comm := cl11Rep_e0_anticommute_omega
  have h_calc :
      cl11Rep e0 * d * cl11Rep e0 * cl11Rep omega =
        -(cl11Rep omega * (cl11Rep e0 * d * cl11Rep e0)) := by
    calc
      cl11Rep e0 * d * cl11Rep e0 * cl11Rep omega
        = cl11Rep e0 * d * (cl11Rep e0 * cl11Rep omega) := by simp only [mul_assoc]
      _ = cl11Rep e0 * d * -(cl11Rep omega * cl11Rep e0) := by rw [h_comm]
      _ = -(cl11Rep e0 * (d * cl11Rep omega) * cl11Rep e0) := by
        simp only [mul_assoc, mul_neg]
      _ = -(cl11Rep e0 * -(cl11Rep omega * d) * cl11Rep e0) := by rw [h_odd]
      _ = (cl11Rep e0 * cl11Rep omega) * d * cl11Rep e0 := by
        simp only [mul_assoc, mul_neg, neg_mul, neg_neg]
      _ = -(cl11Rep omega * cl11Rep e0) * d * cl11Rep e0 := by rw [h_comm]
      _ = -(cl11Rep omega * (cl11Rep e0 * d * cl11Rep e0)) := by
        simp only [mul_assoc, neg_mul]
  dsimp [codiff]
  rw [neg_mul, h_calc, neg_neg, mul_neg, neg_neg]

/-- The Dirac-Kähler operator anticommutes with graded chirality: {D, ω} = 0. -/
theorem diracKahler_anticommute_omega (d : EndCZ)
    (h_odd : d * cl11Rep omega = -(cl11Rep omega * d)) :
    diracKahler d * cl11Rep omega = -(cl11Rep omega * diracKahler d) := by
  dsimp [diracKahler]
  rw [sub_mul, mul_sub, h_odd, codiff_anticommute_omega d h_odd]
  rw [sub_neg_eq_add, add_comm, ← sub_eq_add_neg, neg_sub]

/-- The discrete Hodge-de Rham Laplacian Δ = -(dδ + δd). -/
def hodgeLaplacian (d : EndCZ) : EndCZ :=
  -(d * codiff d + codiff d * d)

/-- **Dirac-Kähler Square Identity**:
    When d² = 0, D² = Δ (the discrete Hodge-de Rham Laplacian). -/
theorem diracKahler_sq (d : EndCZ) (hd : d * d = 0) :
    diracKahler d * diracKahler d = hodgeLaplacian d := by
  dsimp [diracKahler, hodgeLaplacian]
  rw [sub_mul, mul_sub, mul_sub]
  rw [hd, codiff_sq d hd, zero_sub, sub_zero, sub_eq_add_neg, ← neg_add]

end InfoGeometry.Lie.CanonicalZornDiracKahler
