import InfoGeometry.Clifford.Hestenes
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.Tactic.NoncommRing

namespace InfoGeometry.Canonical.HestenesCliffordKrein

open InfoGeometry.Clifford
open InfoGeometry.Clifford.Hestenes

abbrev Cl11 := CliffordAlgebra splitQ11

noncomputable def beta : Cl11 := Pseudoscalar

noncomputable def gamma0 : Cl11 :=
  CliffordAlgebra.ι splitQ11 ((1 : ℝ), 0)

theorem gamma0_sq : gamma0 * gamma0 = 1 := by
  simp [gamma0, splitQ11_apply]

theorem reverse_gamma0 : CliffordAlgebra.reverse gamma0 = gamma0 := by
  simp [gamma0]

noncomputable def reverseKrein (x : Cl11) : Cl11 :=
  beta * CliffordAlgebra.reverse x * beta

theorem beta_sq : beta * beta = (1 : Cl11) := by
  exact pseudoscalar_sq

theorem reverse_beta : CliffordAlgebra.reverse beta = -beta := by
  unfold beta Pseudoscalar
  let e₁ : Cl11 := CliffordAlgebra.ι splitQ11 ((1 : ℝ), 0)
  let e₂ : Cl11 := CliffordAlgebra.ι splitQ11 ((0 : ℝ), 1)
  have hswap : e₂ * e₁ = -(e₁ * e₂) := by
    simpa [e₁, e₂] using
      (CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
        (Q := splitQ11) (a := ((0 : ℝ), 1)) (b := ((1 : ℝ), 0)) (by
          unfold QuadraticMap.IsOrtho
          simp [splitQ11_apply]))
  change CliffordAlgebra.reverse (e₁ * e₂) = -(e₁ * e₂)
  rw [CliffordAlgebra.reverse.map_mul]
  have he₁ : CliffordAlgebra.reverse e₁ = e₁ := by
    simp [e₁]
  have he₂ : CliffordAlgebra.reverse e₂ = e₂ := by
    simp [e₂]
  rw [he₂, he₁]
  exact hswap

@[simp] theorem reverseKrein_one : reverseKrein (1 : Cl11) = 1 := by
  simp [reverseKrein, beta_sq]

@[simp] theorem reverseKrein_zero : reverseKrein (0 : Cl11) = 0 := by
  simp [reverseKrein]

theorem reverseKrein_add (x y : Cl11) :
    reverseKrein (x + y) = reverseKrein x + reverseKrein y := by
  simp only [reverseKrein, map_add, add_mul, mul_add]

theorem reverseKrein_smul (r : ℝ) (x : Cl11) :
    reverseKrein (r • x) = r • reverseKrein x := by
  simp only [reverseKrein, LinearMap.map_smul, smul_mul_assoc, mul_smul_comm]

theorem reverseKrein_mul (x y : Cl11) :
    reverseKrein (x * y) = reverseKrein y * reverseKrein x := by
  simp only [reverseKrein, CliffordAlgebra.reverse.map_mul]
  calc
    beta * (CliffordAlgebra.reverse y * CliffordAlgebra.reverse x) * beta =
        beta * CliffordAlgebra.reverse y * (beta * beta) *
          CliffordAlgebra.reverse x * beta := by
            rw [beta_sq]
            simp [mul_assoc]
    _ = (beta * CliffordAlgebra.reverse y * beta) *
          (beta * CliffordAlgebra.reverse x * beta) := by
            noncomm_ring

theorem reverseKrein_involutive (x : Cl11) :
    reverseKrein (reverseKrein x) = x := by
  simp only [reverseKrein, CliffordAlgebra.reverse.map_mul,
    CliffordAlgebra.reverse_reverse]
  rw [reverse_beta]
  calc
    beta * (-beta * (x * -beta)) * beta =
        ((-beta * beta) * x) * ((-beta) * beta) := by
          noncomm_ring
    _ = x := by simp [beta_sq]

theorem reverseKrein_beta : reverseKrein beta = -beta := by
  simp only [reverseKrein, reverse_beta]
  calc
    beta * -beta * beta = -(beta * beta) * beta := by noncomm_ring
    _ = -beta := by simp [beta_sq]

/-- The Hestenes involution corresponding to conjugate transpose. -/
noncomputable def hestenesAdjoint (x : Cl11) : Cl11 :=
  gamma0 * CliffordAlgebra.reverse x * gamma0

theorem hestenesAdjoint_one : hestenesAdjoint (1 : Cl11) = 1 := by
  simp [hestenesAdjoint, gamma0_sq]

@[simp] theorem hestenesAdjoint_zero : hestenesAdjoint (0 : Cl11) = 0 := by
  simp [hestenesAdjoint]

theorem hestenesAdjoint_add (x y : Cl11) :
    hestenesAdjoint (x + y) = hestenesAdjoint x + hestenesAdjoint y := by
  simp [hestenesAdjoint, add_mul, mul_add]

theorem hestenesAdjoint_smul (r : ℝ) (x : Cl11) :
    hestenesAdjoint (r • x) = r • hestenesAdjoint x := by
  simp [hestenesAdjoint]

theorem hestenesAdjoint_mul (x y : Cl11) :
    hestenesAdjoint (x * y) = hestenesAdjoint y * hestenesAdjoint x := by
  simp only [hestenesAdjoint, CliffordAlgebra.reverse.map_mul]
  calc
    gamma0 * (CliffordAlgebra.reverse y * CliffordAlgebra.reverse x) * gamma0 =
        gamma0 * CliffordAlgebra.reverse y * (gamma0 * gamma0) *
          CliffordAlgebra.reverse x * gamma0 := by
            rw [gamma0_sq]
            simp [mul_assoc]
    _ = (gamma0 * CliffordAlgebra.reverse y * gamma0) *
          (gamma0 * CliffordAlgebra.reverse x * gamma0) := by
            noncomm_ring

theorem hestenesAdjoint_involutive (x : Cl11) :
    hestenesAdjoint (hestenesAdjoint x) = x := by
  simp only [hestenesAdjoint, CliffordAlgebra.reverse.map_mul,
    CliffordAlgebra.reverse_reverse]
  rw [reverse_gamma0]
  calc
    gamma0 * (gamma0 * (x * gamma0)) * gamma0 =
        ((gamma0 * gamma0) * x) * (gamma0 * gamma0) := by
          noncomm_ring
    _ = x := by simp [gamma0_sq]

theorem gamma0_beta_anticommute : gamma0 * beta = -(beta * gamma0) := by
  let e1 : Cl11 := CliffordAlgebra.ι splitQ11 ((1 : ℝ), 0)
  let e2 : Cl11 := CliffordAlgebra.ι splitQ11 ((0 : ℝ), 1)
  have hswap : e2 * e1 = -(e1 * e2) := by
    simpa [e1, e2] using
      (CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
        (Q := splitQ11) (a := ((0 : ℝ), 1)) (b := ((1 : ℝ), 0)) (by
          unfold QuadraticMap.IsOrtho
          simp [splitQ11_apply]))
  have he1sq : e1 * e1 = (1 : Cl11) := by
    simp [e1, splitQ11_apply]
  have h : e1 * (e1 * e2) = -(e1 * e2) * e1 := by
    calc
      e1 * (e1 * e2) = (e1 * e1) * e2 := by
        simp [mul_assoc]
      _ = e2 := by rw [he1sq]; simp
      _ = -(e1 * e2) * e1 := by
        rw [← hswap]
        simp [mul_assoc, he1sq]
  simpa [gamma0, beta, Pseudoscalar, e1, e2] using h

theorem reverseKrein_gamma0 : reverseKrein gamma0 = -gamma0 := by
  simp only [reverseKrein, reverse_gamma0]
  have hswap : beta * gamma0 = -(gamma0 * beta) := by
    rw [gamma0_beta_anticommute]
    simp
  calc
    beta * gamma0 * beta = -(gamma0 * beta) * beta := by rw [hswap]
    _ = -(gamma0 * (beta * beta)) := by noncomm_ring
    _ = -gamma0 := by rw [beta_sq]; simp

theorem hestenesAdjoint_beta : hestenesAdjoint beta = beta := by
  simp only [hestenesAdjoint, reverse_beta, mul_neg, neg_mul]
  rw [gamma0_beta_anticommute]
  simp [mul_assoc, gamma0_sq]

theorem hestenesAdjoint_gamma0 : hestenesAdjoint gamma0 = gamma0 := by
  simp [hestenesAdjoint, reverse_gamma0, gamma0_sq]

/-- The native Hestenes-Krein adjoint built from the Hermitian Clifford adjoint. -/
noncomputable def hestenesKreinAdjoint (x : Cl11) : Cl11 :=
  beta * hestenesAdjoint x * beta

theorem hestenesKreinAdjoint_eq (x : Cl11) :
    hestenesKreinAdjoint x =
      beta * gamma0 * CliffordAlgebra.reverse x * gamma0 * beta := by
  unfold hestenesKreinAdjoint hestenesAdjoint
  simp only [mul_assoc]

theorem hestenesKreinAdjoint_one :
    hestenesKreinAdjoint (1 : Cl11) = 1 := by
  simp [hestenesKreinAdjoint, hestenesAdjoint_one, beta_sq]

@[simp] theorem hestenesKreinAdjoint_zero :
    hestenesKreinAdjoint (0 : Cl11) = 0 := by
  simp [hestenesKreinAdjoint]

theorem hestenesKreinAdjoint_add (x y : Cl11) :
    hestenesKreinAdjoint (x + y) =
      hestenesKreinAdjoint x + hestenesKreinAdjoint y := by
  simp [hestenesKreinAdjoint, hestenesAdjoint_add, add_mul, mul_add]

theorem hestenesKreinAdjoint_smul (r : ℝ) (x : Cl11) :
    hestenesKreinAdjoint (r • x) = r • hestenesKreinAdjoint x := by
  simp [hestenesKreinAdjoint, hestenesAdjoint_smul]

theorem hestenesKreinAdjoint_mul (x y : Cl11) :
    hestenesKreinAdjoint (x * y) =
      hestenesKreinAdjoint y * hestenesKreinAdjoint x := by
  simp only [hestenesKreinAdjoint, hestenesAdjoint_mul]
  calc
    beta * (hestenesAdjoint y * hestenesAdjoint x) * beta =
        beta * hestenesAdjoint y * (beta * beta) *
          hestenesAdjoint x * beta := by
            rw [beta_sq]
            simp [mul_assoc]
    _ = (beta * hestenesAdjoint y * beta) *
          (beta * hestenesAdjoint x * beta) := by
            noncomm_ring

theorem hestenesKreinAdjoint_involutive (x : Cl11) :
    hestenesKreinAdjoint (hestenesKreinAdjoint x) = x := by
  simp only [hestenesKreinAdjoint, hestenesAdjoint_mul,
    hestenesAdjoint_involutive, hestenesAdjoint_beta]
  calc
    beta * (beta * (x * beta)) * beta =
        ((beta * beta) * x) * (beta * beta) := by
          noncomm_ring
    _ = x := by simp [beta_sq]

theorem hestenesKreinAdjoint_beta :
    hestenesKreinAdjoint beta = beta := by
  simp [hestenesKreinAdjoint, hestenesAdjoint_beta, beta_sq]

theorem hestenesKreinAdjoint_gamma0 :
    hestenesKreinAdjoint gamma0 = -gamma0 := by
  simp only [hestenesKreinAdjoint, hestenesAdjoint_gamma0]
  have hswap : beta * gamma0 = -(gamma0 * beta) := by
    rw [gamma0_beta_anticommute]
    simp
  calc
    beta * gamma0 * beta = -(gamma0 * beta) * beta := by rw [hswap]
    _ = -(gamma0 * (beta * beta)) := by noncomm_ring
    _ = -gamma0 := by rw [beta_sq]; simp

section Representation

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem cl11Rep_commutator (K X : Cl11) :
    _root_.cl11Rep (E := E) (cl11_commutator K X) =
      _root_.cl11Rep (E := E) K * _root_.cl11Rep (E := E) X -
        _root_.cl11Rep (E := E) X * _root_.cl11Rep (E := E) K := by
  simp [cl11_commutator]

omit [CompleteSpace E] in
theorem cl11Rep_commutator_apply
    (K X : Cl11) (v : InfoGeometry.Krein.DoubledSpace E) :
    _root_.cl11Rep (E := E) (cl11_commutator K X) v =
      _root_.cl11Rep (E := E) K (_root_.cl11Rep (E := E) X v) -
        _root_.cl11Rep (E := E) X (_root_.cl11Rep (E := E) K v) := by
  rw [cl11Rep_commutator]
  rfl

omit [CompleteSpace E] in
theorem cl11Rep_commutator_derivation (K X Y : Cl11) :
    _root_.cl11Rep (E := E) (cl11_commutator K (X * Y)) =
      _root_.cl11Rep (E := E) (cl11_commutator K X) *
          _root_.cl11Rep (E := E) Y +
        _root_.cl11Rep (E := E) X *
          _root_.cl11Rep (E := E) (cl11_commutator K Y) := by
  rw [cl11_commutator_is_derivation]
  simp only [map_add, map_mul]

end Representation

end InfoGeometry.Canonical.HestenesCliffordKrein
