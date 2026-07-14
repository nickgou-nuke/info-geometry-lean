import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
import Mathlib.Tactic

/-!
# Three-dimensional geometric Clifford Hurwitz readout

This file formalizes the paper's basic 3D Clifford-algebra readout:

* a diagonal 3D quadratic form on `ℝ × (ℝ × ℝ)`;
* the three Clifford generators and their pairwise orthogonality;
* the bivector squares `(e_i e_j)^2 = - Q(e_i) Q(e_j)`;
* the pseudoscalar square `(e_0 e_1 e_2)^2 = - Q(e_0) Q(e_1) Q(e_2)`.

These are the algebraic identities behind the paper's table of complex,
split-complex, quaternionic, split-quaternionic, and octonionic readouts.
The actual identification with a concrete Hurwitz carrier is not claimed here;
that is a later equivalence theorem.
-/

noncomputable section

namespace ThreeDHurwitz

open scoped Matrix

abbrev Space3 := ℝ × (ℝ × ℝ)

/--
Diagonal quadratic form on 3D product coordinates.

The coefficients `s0`, `s1`, `s2` are the signature signs.
-/
noncomputable def Qdiag3 (s0 s1 s2 : ℝ) : QuadraticForm ℝ Space3 :=
  QuadraticMap.ofPolar
    (fun v => s0 * v.1 ^ 2 + s1 * v.2.1 ^ 2 + s2 * v.2.2 ^ 2)
    (by
      intro a v
      dsimp
      ring)
    (by
      intro x x' y
      dsimp [QuadraticMap.polar]
      ring)
    (by
      intro a x y
      dsimp [QuadraticMap.polar]
      ring)

@[simp] theorem Qdiag3_apply (s0 s1 s2 : ℝ) (v : Space3) :
    Qdiag3 s0 s1 s2 v = s0 * v.1 ^ 2 + s1 * v.2.1 ^ 2 + s2 * v.2.2 ^ 2 := by
  rfl

/-- The first standard basis vector. -/
def e0 : Space3 := (1, (0, 0))

/-- The second standard basis vector. -/
def e1 : Space3 := (0, (1, 0))

/-- The third standard basis vector. -/
def e2 : Space3 := (0, (0, 1))

@[simp] theorem Qdiag3_e0 (s0 s1 s2 : ℝ) :
    Qdiag3 s0 s1 s2 e0 = s0 := by
  simp [Qdiag3, e0]

@[simp] theorem Qdiag3_e1 (s0 s1 s2 : ℝ) :
    Qdiag3 s0 s1 s2 e1 = s1 := by
  simp [Qdiag3, e1]

@[simp] theorem Qdiag3_e2 (s0 s1 s2 : ℝ) :
    Qdiag3 s0 s1 s2 e2 = s2 := by
  simp [Qdiag3, e2]

@[simp] theorem Qdiag3_e0_e1_orthogonal (s0 s1 s2 : ℝ) :
    QuadraticMap.IsOrtho (Qdiag3 s0 s1 s2) e0 e1 := by
  unfold QuadraticMap.IsOrtho
  simp [Qdiag3, e0, e1]

@[simp] theorem Qdiag3_e0_e2_orthogonal (s0 s1 s2 : ℝ) :
    QuadraticMap.IsOrtho (Qdiag3 s0 s1 s2) e0 e2 := by
  unfold QuadraticMap.IsOrtho
  simp [Qdiag3, e0, e2]

@[simp] theorem Qdiag3_e1_e2_orthogonal (s0 s1 s2 : ℝ) :
    QuadraticMap.IsOrtho (Qdiag3 s0 s1 s2) e1 e2 := by
  unfold QuadraticMap.IsOrtho
  simp [Qdiag3, e1, e2]

/-- The Clifford algebra of the diagonal 3D signature. -/
abbrev Cl3 (s0 s1 s2 : ℝ) :=
  CliffordAlgebra (Qdiag3 s0 s1 s2)

/-- The three lifted Clifford generators. -/
def g0 (s0 s1 s2 : ℝ) : Cl3 s0 s1 s2 :=
  CliffordAlgebra.ι (Qdiag3 s0 s1 s2) e0

def g1 (s0 s1 s2 : ℝ) : Cl3 s0 s1 s2 :=
  CliffordAlgebra.ι (Qdiag3 s0 s1 s2) e1

def g2 (s0 s1 s2 : ℝ) : Cl3 s0 s1 s2 :=
  CliffordAlgebra.ι (Qdiag3 s0 s1 s2) e2

@[simp] theorem g0_sq (s0 s1 s2 : ℝ) :
    g0 s0 s1 s2 * g0 s0 s1 s2 = algebraMap ℝ (Cl3 s0 s1 s2) s0 := by
  rw [g0]
  have h := (CliffordAlgebra.ι_sq_scalar (Q := Qdiag3 s0 s1 s2) e0)
  rw [Qdiag3_e0] at h
  exact h

@[simp] theorem g1_sq (s0 s1 s2 : ℝ) :
    g1 s0 s1 s2 * g1 s0 s1 s2 = algebraMap ℝ (Cl3 s0 s1 s2) s1 := by
  rw [g1]
  have h := (CliffordAlgebra.ι_sq_scalar (Q := Qdiag3 s0 s1 s2) e1)
  rw [Qdiag3_e1] at h
  exact h

@[simp] theorem g2_sq (s0 s1 s2 : ℝ) :
    g2 s0 s1 s2 * g2 s0 s1 s2 = algebraMap ℝ (Cl3 s0 s1 s2) s2 := by
  rw [g2]
  have h := (CliffordAlgebra.ι_sq_scalar (Q := Qdiag3 s0 s1 s2) e2)
  rw [Qdiag3_e2] at h
  exact h

@[simp] theorem g0_g1_anti (s0 s1 s2 : ℝ) :
    g0 s0 s1 s2 * g1 s0 s1 s2 = - (g1 s0 s1 s2 * g0 s0 s1 s2) := by
  rw [g0, g1]
  simpa using
    (CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
      (Q := Qdiag3 s0 s1 s2) (a := e0) (b := e1) (Qdiag3_e0_e1_orthogonal s0 s1 s2))

@[simp] theorem g0_g2_anti (s0 s1 s2 : ℝ) :
    g0 s0 s1 s2 * g2 s0 s1 s2 = - (g2 s0 s1 s2 * g0 s0 s1 s2) := by
  rw [g0, g2]
  simpa using
    (CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
      (Q := Qdiag3 s0 s1 s2) (a := e0) (b := e2) (Qdiag3_e0_e2_orthogonal s0 s1 s2))

@[simp] theorem g1_g2_anti (s0 s1 s2 : ℝ) :
    g1 s0 s1 s2 * g2 s0 s1 s2 = - (g2 s0 s1 s2 * g1 s0 s1 s2) := by
  rw [g1, g2]
  simpa using
    (CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
      (Q := Qdiag3 s0 s1 s2) (a := e1) (b := e2) (Qdiag3_e1_e2_orthogonal s0 s1 s2))

/-- The bivector `g0 g1` squares to `-s0*s1`. -/
theorem bivector01_sq (s0 s1 s2 : ℝ) :
    (g0 s0 s1 s2 * g1 s0 s1 s2) * (g0 s0 s1 s2 * g1 s0 s1 s2)
      = algebraMap ℝ (Cl3 s0 s1 s2) (-(s0 * s1)) := by
  have hswap : g1 s0 s1 s2 * g0 s0 s1 s2 = - (g0 s0 s1 s2 * g1 s0 s1 s2) := by
    simpa using congrArg Neg.neg (g0_g1_anti (s0 := s0) (s1 := s1) (s2 := s2))
  have htri :
      g0 s0 s1 s2 * g1 s0 s1 s2 * g0 s0 s1 s2 =
        -((algebraMap ℝ (Cl3 s0 s1 s2) s0) * g1 s0 s1 s2) := by
    calc
      g0 s0 s1 s2 * g1 s0 s1 s2 * g0 s0 s1 s2 = g0 s0 s1 s2 * (g1 s0 s1 s2 * g0 s0 s1 s2) := by
        rw [mul_assoc]
      _ = g0 s0 s1 s2 * (-(g0 s0 s1 s2 * g1 s0 s1 s2)) := by
        rw [hswap]
      _ = -(g0 s0 s1 s2 * (g0 s0 s1 s2 * g1 s0 s1 s2)) := by
        rw [mul_neg]
      _ = -((g0 s0 s1 s2 * g0 s0 s1 s2) * g1 s0 s1 s2) := by
        rw [mul_assoc]
      _ = -((algebraMap ℝ (Cl3 s0 s1 s2) s0) * g1 s0 s1 s2) := by
        rw [g0_sq]
  have hstart :
      (g0 s0 s1 s2 * g1 s0 s1 s2) * (g0 s0 s1 s2 * g1 s0 s1 s2)
        = (g0 s0 s1 s2 * g1 s0 s1 s2 * g0 s0 s1 s2) * g1 s0 s1 s2 := by
    repeat rw [mul_assoc]
  calc
    (g0 s0 s1 s2 * g1 s0 s1 s2) * (g0 s0 s1 s2 * g1 s0 s1 s2) = _ := hstart
    _ = -((algebraMap ℝ (Cl3 s0 s1 s2) s0) * g1 s0 s1 s2) * g1 s0 s1 s2 := by
      rw [htri]
    _ = -((algebraMap ℝ (Cl3 s0 s1 s2) s0) * (g1 s0 s1 s2 * g1 s0 s1 s2)) := by
      rw [neg_mul, mul_assoc]
    _ = algebraMap ℝ (Cl3 s0 s1 s2) (-(s0 * s1)) := by
      rw [g1_sq]
      simp

/-- The bivector `g1 g2` squares to `-s1*s2`. -/
theorem bivector12_sq (s0 s1 s2 : ℝ) :
    (g1 s0 s1 s2 * g2 s0 s1 s2) * (g1 s0 s1 s2 * g2 s0 s1 s2)
      = algebraMap ℝ (Cl3 s0 s1 s2) (-(s1 * s2)) := by
  have hswap : g2 s0 s1 s2 * g1 s0 s1 s2 = - (g1 s0 s1 s2 * g2 s0 s1 s2) := by
    simpa using congrArg Neg.neg (g1_g2_anti (s0 := s0) (s1 := s1) (s2 := s2))
  have htri :
      g1 s0 s1 s2 * g2 s0 s1 s2 * g1 s0 s1 s2 =
        -((algebraMap ℝ (Cl3 s0 s1 s2) s1) * g2 s0 s1 s2) := by
    calc
      g1 s0 s1 s2 * g2 s0 s1 s2 * g1 s0 s1 s2 = g1 s0 s1 s2 * (g2 s0 s1 s2 * g1 s0 s1 s2) := by
        rw [mul_assoc]
      _ = g1 s0 s1 s2 * (-(g1 s0 s1 s2 * g2 s0 s1 s2)) := by
        rw [hswap]
      _ = -(g1 s0 s1 s2 * (g1 s0 s1 s2 * g2 s0 s1 s2)) := by
        rw [mul_neg]
      _ = -((g1 s0 s1 s2 * g1 s0 s1 s2) * g2 s0 s1 s2) := by
        rw [mul_assoc]
      _ = -((algebraMap ℝ (Cl3 s0 s1 s2) s1) * g2 s0 s1 s2) := by
        rw [g1_sq]
  have hstart :
      (g1 s0 s1 s2 * g2 s0 s1 s2) * (g1 s0 s1 s2 * g2 s0 s1 s2)
        = (g1 s0 s1 s2 * g2 s0 s1 s2 * g1 s0 s1 s2) * g2 s0 s1 s2 := by
    repeat rw [mul_assoc]
  calc
    (g1 s0 s1 s2 * g2 s0 s1 s2) * (g1 s0 s1 s2 * g2 s0 s1 s2) = _ := hstart
    _ = -((algebraMap ℝ (Cl3 s0 s1 s2) s1) * g2 s0 s1 s2) * g2 s0 s1 s2 := by
      rw [htri]
    _ = -((algebraMap ℝ (Cl3 s0 s1 s2) s1) * (g2 s0 s1 s2 * g2 s0 s1 s2)) := by
      rw [neg_mul, mul_assoc]
    _ = algebraMap ℝ (Cl3 s0 s1 s2) (-(s1 * s2)) := by
      rw [g2_sq]
      simp

/-- The bivector `g0 g2` squares to `-s0*s2`. -/
theorem bivector02_sq (s0 s1 s2 : ℝ) :
    (g0 s0 s1 s2 * g2 s0 s1 s2) * (g0 s0 s1 s2 * g2 s0 s1 s2)
      = algebraMap ℝ (Cl3 s0 s1 s2) (-(s0 * s2)) := by
  have hswap : g2 s0 s1 s2 * g0 s0 s1 s2 = - (g0 s0 s1 s2 * g2 s0 s1 s2) := by
    simpa using congrArg Neg.neg (g0_g2_anti (s0 := s0) (s1 := s1) (s2 := s2))
  have htri :
      g0 s0 s1 s2 * g2 s0 s1 s2 * g0 s0 s1 s2 =
        -((algebraMap ℝ (Cl3 s0 s1 s2) s0) * g2 s0 s1 s2) := by
    calc
      g0 s0 s1 s2 * g2 s0 s1 s2 * g0 s0 s1 s2 = g0 s0 s1 s2 * (g2 s0 s1 s2 * g0 s0 s1 s2) := by
        rw [mul_assoc]
      _ = g0 s0 s1 s2 * (-(g0 s0 s1 s2 * g2 s0 s1 s2)) := by
        rw [hswap]
      _ = -(g0 s0 s1 s2 * (g0 s0 s1 s2 * g2 s0 s1 s2)) := by
        rw [mul_neg]
      _ = -((g0 s0 s1 s2 * g0 s0 s1 s2) * g2 s0 s1 s2) := by
        rw [mul_assoc]
      _ = -((algebraMap ℝ (Cl3 s0 s1 s2) s0) * g2 s0 s1 s2) := by
        rw [g0_sq]
  have hstart :
      (g0 s0 s1 s2 * g2 s0 s1 s2) * (g0 s0 s1 s2 * g2 s0 s1 s2)
        = (g0 s0 s1 s2 * g2 s0 s1 s2 * g0 s0 s1 s2) * g2 s0 s1 s2 := by
    repeat rw [mul_assoc]
  calc
    (g0 s0 s1 s2 * g2 s0 s1 s2) * (g0 s0 s1 s2 * g2 s0 s1 s2) = _ := hstart
    _ = -((algebraMap ℝ (Cl3 s0 s1 s2) s0) * g2 s0 s1 s2) * g2 s0 s1 s2 := by
      rw [htri]
    _ = -((algebraMap ℝ (Cl3 s0 s1 s2) s0) * (g2 s0 s1 s2 * g2 s0 s1 s2)) := by
      rw [neg_mul, mul_assoc]
    _ = algebraMap ℝ (Cl3 s0 s1 s2) (-(s0 * s2)) := by
      rw [g2_sq]
      simp

/-- The pseudoscalar `g0 g1 g2` squares to `-s0*s1*s2`. -/
theorem pseudoscalar_sq (s0 s1 s2 : ℝ) :
    ((g0 s0 s1 s2 * g1 s0 s1 s2) * g2 s0 s1 s2)
      * ((g0 s0 s1 s2 * g1 s0 s1 s2) * g2 s0 s1 s2)
      = algebraMap ℝ (Cl3 s0 s1 s2) (-(s0 * s1 * s2)) := by
  have h20 : g2 s0 s1 s2 * g0 s0 s1 s2 = -(g0 s0 s1 s2 * g2 s0 s1 s2) := by
    simpa using congrArg Neg.neg (g0_g2_anti (s0 := s0) (s1 := s1) (s2 := s2))
  have h21 : g2 s0 s1 s2 * g1 s0 s1 s2 = -(g1 s0 s1 s2 * g2 s0 s1 s2) := by
    simpa using congrArg Neg.neg (g1_g2_anti (s0 := s0) (s1 := s1) (s2 := s2))
  have hcomm :
      g2 s0 s1 s2 * (g0 s0 s1 s2 * g1 s0 s1 s2) =
        (g0 s0 s1 s2 * g1 s0 s1 s2) * g2 s0 s1 s2 := by
    calc
      g2 s0 s1 s2 * (g0 s0 s1 s2 * g1 s0 s1 s2)
          = (g2 s0 s1 s2 * g0 s0 s1 s2) * g1 s0 s1 s2 := by rw [mul_assoc]
      _ = (-(g0 s0 s1 s2 * g2 s0 s1 s2)) * g1 s0 s1 s2 := by rw [h20]
      _ = -((g0 s0 s1 s2 * g2 s0 s1 s2) * g1 s0 s1 s2) := by rw [neg_mul]
      _ = -(g0 s0 s1 s2 * (g2 s0 s1 s2 * g1 s0 s1 s2)) := by rw [mul_assoc]
      _ = -(g0 s0 s1 s2 * (-(g1 s0 s1 s2 * g2 s0 s1 s2))) := by rw [h21]
      _ = g0 s0 s1 s2 * (g1 s0 s1 s2 * g2 s0 s1 s2) := by simp
      _ = (g0 s0 s1 s2 * g1 s0 s1 s2) * g2 s0 s1 s2 := by rw [mul_assoc]
  calc
    ((g0 s0 s1 s2 * g1 s0 s1 s2) * g2 s0 s1 s2)
        * ((g0 s0 s1 s2 * g1 s0 s1 s2) * g2 s0 s1 s2)
        = (g0 s0 s1 s2 * g1 s0 s1 s2)
            * (g2 s0 s1 s2 * (g0 s0 s1 s2 * g1 s0 s1 s2))
            * g2 s0 s1 s2 := by
              repeat rw [mul_assoc]
    _ = (g0 s0 s1 s2 * g1 s0 s1 s2)
          * ((g0 s0 s1 s2 * g1 s0 s1 s2) * g2 s0 s1 s2)
          * g2 s0 s1 s2 := by rw [hcomm]
    _ = ((g0 s0 s1 s2 * g1 s0 s1 s2) * (g0 s0 s1 s2 * g1 s0 s1 s2))
          * (g2 s0 s1 s2 * g2 s0 s1 s2) := by
            repeat rw [mul_assoc]
    _ = (algebraMap ℝ (Cl3 s0 s1 s2) (-(s0 * s1)))
          * (algebraMap ℝ (Cl3 s0 s1 s2) s2) := by
            rw [bivector01_sq, g2_sq]
    _ = algebraMap ℝ (Cl3 s0 s1 s2) (-(s0 * s1 * s2)) := by
            simp [mul_assoc]

end ThreeDHurwitz
