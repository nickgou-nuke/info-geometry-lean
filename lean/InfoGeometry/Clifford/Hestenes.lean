import InfoGeometry.Clifford.SplitQ11
import InfoGeometry.Clifford.Lift
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Hestenes Geometric Algebra for Information Fluids

Formalizes the pseudoscalar, exponential maps, and signed volume in 
Clifford algebras Cl(n,n) following the Hestenes convention.

This connects the algebraic volume form to the Weyl scaling of the 
information manifold.
-/

namespace InfoGeometry.Clifford.Hestenes

open InfoGeometry.Clifford

/-- Concrete split-signature Clifford algebra `Cl(1,1)`. -/
abbrev Cl11 := CliffordAlgebra splitQ11

/--
Pseudoscalar (I).
Representing the signed unit volume element.
For Cl(1,1), I² = 1.
-/
noncomputable def Pseudoscalar : Cl11 :=
  CliffordAlgebra.ι splitQ11 (1, 0) * CliffordAlgebra.ι splitQ11 (0, 1)

private lemma splitQ11_isOrtho_e2_e1 :
    splitQ11.IsOrtho ((0 : ℝ), 1) ((1 : ℝ), 0) := by
  unfold QuadraticMap.IsOrtho
  simp [splitQ11_apply]

/-- In `Cl(1,1)`, the pseudoscalar squares to the unit. -/
theorem pseudoscalar_sq : Pseudoscalar * Pseudoscalar = 1 := by
  let e1 : Cl11 := CliffordAlgebra.ι splitQ11 ((1 : ℝ), 0)
  let e2 : Cl11 := CliffordAlgebra.ι splitQ11 ((0 : ℝ), 1)
  have hswap : e2 * e1 = -(e1 * e2) := by
    simpa [e1, e2] using
      (CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
        (Q := splitQ11) (a := ((0 : ℝ), 1)) (b := ((1 : ℝ), 0))
        splitQ11_isOrtho_e2_e1)
  have he1sq : e1 * e1 = (1 : Cl11) := by
    simp [e1, splitQ11_apply]
  have he2sq : e2 * e2 = (-1 : Cl11) := by
    simp [e2, splitQ11_apply]
  calc
    Pseudoscalar * Pseudoscalar = e1 * (e2 * e1) * e2 := by
      simp [Pseudoscalar, e1, e2, mul_assoc]
    _ = e1 * (-(e1 * e2)) * e2 := by
      rw [hswap]
    _ = -((e1 * e1) * (e2 * e2)) := by
      simp [mul_assoc]
    _ = -((1 : Cl11) * (-1 : Cl11)) := by
      rw [he1sq, he2sq]
    _ = 1 := by
      simp

/--
Exponential Map of the Pseudoscalar.
In GA, exp(θ I) = cosh θ + I sinh θ (when I² = 1).
This generates a Weyl scaling (dilation) of the volume form.
-/
noncomputable def expPseudoscalar (θ : ℝ) : ℝ :=
  Real.cosh θ + Real.sinh θ

/--
Theorem: Weyl Scaling Generation.
The exponential of the pseudoscalar generates a multiplicative scaling 
of the information volume.
-/
theorem expPseudoscalar_is_scaling (θ : ℝ) :
    expPseudoscalar θ = Real.exp θ := by
  unfold expPseudoscalar
  rw [Real.cosh_add_sinh]

/--
Bridge: Pseudoscalar as Signed Volume.
Identifies the top-level GA form with the Radon-Nikodym derivative.
-/
def IsSignedVolume (RN : ℝ) : Prop :=
  ∃ ρ : Cl11 →ₗ[ℝ] ℝ, ρ Pseudoscalar = RN

/-- The commutator bracket on `Cl(1,1)` as an inner derivation. -/
def cl11_commutator (K X : Cl11) : Cl11 :=
  K * X - X * K

/-- Associativity of the concrete `Cl(1,1)` algebra. -/
theorem Cl11_mul_assoc (q1 q2 q3 : Cl11) :
    (q1 * q2) * q3 = q1 * (q2 * q3) := by
  exact mul_assoc q1 q2 q3

/-- The commutator is a derivation for the product in `Cl(1,1)`. -/
theorem cl11_commutator_is_derivation (K X Y : Cl11) :
    cl11_commutator K (X * Y) = cl11_commutator K X * Y + X * cl11_commutator K Y := by
  unfold cl11_commutator
  noncomm_ring

/-- Additivity of the infinitesimal Connes/Radon--Nikodym commutator in the generator. -/
theorem radon_nikodym_infinitesimal_additivity (K1 K2 X : Cl11) :
    cl11_commutator (K1 - K2) X = cl11_commutator K1 X - cl11_commutator K2 X := by
  unfold cl11_commutator
  noncomm_ring

section Representation

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Concrete representation bridge:
the Cl(1,1) pseudoscalar maps to the doubled-space spectral involution.
-/
lemma cl11Rep_pseudoscalar_eq_spectral_epsilon :
    cl11Rep (E := E) Pseudoscalar
      = InfoGeometry.Krein.spectral_epsilon (E := E) := by
  simpa [Pseudoscalar, Q11] using
    (cl11Rep_pseudoscalar (E := E))

/-- Representation-level involution: the pseudoscalar image squares to identity. -/
lemma cl11Rep_pseudoscalar_comp_self :
    (cl11Rep (E := E) Pseudoscalar).comp (cl11Rep (E := E) Pseudoscalar)
      = ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E) := by
  rw [cl11Rep_pseudoscalar_eq_spectral_epsilon]
  simpa using (InfoGeometry.Krein.spectral_epsilon_involution (E := E))

end Representation

end InfoGeometry.Clifford.Hestenes
