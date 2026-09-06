import Mathlib.Tactic

/-!
# Repaired MD 014: finite `Z₃` projector and extension algebra

Source: `github-nick:nickgou-nuke/MD`, file `014.md`.

Chapter 14 discusses a proposed `TriSpin(1,3)` central extension, `Z₃`
projectors, conformal groups, and speculative generation/CP interpretations.
The source itself flags inconsistencies in the topology/covering discussion.
This owner formalizes only the finite algebraic socket:

* a finite `Z₃`-sector projector triple on `ℂ³`;
* orthogonal idempotent, completeness, trace, and two-sided sector-eigenvalue readouts;
* a finite central-extension product on `G × ZMod 3`, with associativity stated
  under the explicit product-level cocycle associativity equation.

No theorem here asserts existence/uniqueness of a nontrivial Lie-group central
extension of `Spin(1,3)`, a triple cover of `SL(2,ℂ)`, conformal embedding in
`SL(4,ℂ)`, representation classification, three fermion generations, CP
violation, or Yukawa/mixing-matrix physics.
-/

noncomputable section

namespace InfoGeometry.Physics.MD014TriSpinZ3Projectors

set_option linter.unusedSimpArgs false

open Matrix

/-- Concrete three-sector complex carrier. -/
abbrev Sector3Carrier := Matrix (Fin 3) (Fin 3) ℂ

/-- Trace on the concrete three-sector carrier. -/
def trace3 (A : Sector3Carrier) : ℂ := ∑ i : Fin 3, A i i

/-- Sector-0 diagonal projector. -/
def sectorProjector0 : Sector3Carrier :=
  fun i j => if i = 0 ∧ j = 0 then 1 else 0

/-- Sector-1 diagonal projector. -/
def sectorProjector1 : Sector3Carrier :=
  fun i j => if i = 1 ∧ j = 1 then 1 else 0

/-- Sector-2 diagonal projector. -/
def sectorProjector2 : Sector3Carrier :=
  fun i j => if i = 2 ∧ j = 2 then 1 else 0

/-- Sector-0 projector is idempotent. -/
theorem sectorProjector0_idempotent :
    sectorProjector0 * sectorProjector0 = sectorProjector0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sectorProjector0, Matrix.mul_apply]

/-- Sector-1 projector is idempotent. -/
theorem sectorProjector1_idempotent :
    sectorProjector1 * sectorProjector1 = sectorProjector1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sectorProjector1, Matrix.mul_apply]

/-- Sector-2 projector is idempotent. -/
theorem sectorProjector2_idempotent :
    sectorProjector2 * sectorProjector2 = sectorProjector2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sectorProjector2, Matrix.mul_apply]

/-- Distinct sector projectors are orthogonal: `P₀P₁=0`. -/
theorem sectorProjector0_mul_sectorProjector1 :
    sectorProjector0 * sectorProjector1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sectorProjector0, sectorProjector1, Matrix.mul_apply]

/-- Distinct sector projectors are orthogonal: `P₁P₂=0`. -/
theorem sectorProjector1_mul_sectorProjector2 :
    sectorProjector1 * sectorProjector2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sectorProjector1, sectorProjector2, Matrix.mul_apply]

/-- Distinct sector projectors are orthogonal: `P₂P₀=0`. -/
theorem sectorProjector2_mul_sectorProjector0 :
    sectorProjector2 * sectorProjector0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sectorProjector2, sectorProjector0, Matrix.mul_apply]

/-- Distinct sector projectors are orthogonal: `P₁P₀=0`. -/
theorem sectorProjector1_mul_sectorProjector0 :
    sectorProjector1 * sectorProjector0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sectorProjector0, sectorProjector1, Matrix.mul_apply]

/-- Distinct sector projectors are orthogonal: `P₂P₁=0`. -/
theorem sectorProjector2_mul_sectorProjector1 :
    sectorProjector2 * sectorProjector1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sectorProjector1, sectorProjector2, Matrix.mul_apply]

/-- Distinct sector projectors are orthogonal: `P₀P₂=0`. -/
theorem sectorProjector0_mul_sectorProjector2 :
    sectorProjector0 * sectorProjector2 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sectorProjector0, sectorProjector2, Matrix.mul_apply]

/-- Complete pairwise orthogonality of the three sector projectors. -/
theorem sectorProjector_pairwise_orthogonal_packet :
    sectorProjector0 * sectorProjector1 = 0 ∧ sectorProjector1 * sectorProjector0 = 0 ∧
    sectorProjector1 * sectorProjector2 = 0 ∧ sectorProjector2 * sectorProjector1 = 0 ∧
    sectorProjector2 * sectorProjector0 = 0 ∧ sectorProjector0 * sectorProjector2 = 0 := by
  exact ⟨sectorProjector0_mul_sectorProjector1, sectorProjector1_mul_sectorProjector0,
    sectorProjector1_mul_sectorProjector2, sectorProjector2_mul_sectorProjector1,
    sectorProjector2_mul_sectorProjector0, sectorProjector0_mul_sectorProjector2⟩

/-- The three finite sector projectors sum to the identity. -/
theorem sectorProjector_sum_identity :
    sectorProjector0 + sectorProjector1 + sectorProjector2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sectorProjector0, sectorProjector1, sectorProjector2]

/-- Diagonal finite `Z₃` phase operator with formal phase `ω`. -/
def sectorPhase (omega : ℂ) : Sector3Carrier :=
  sectorProjector0 + omega • sectorProjector1 + (omega ^ 2) • sectorProjector2

/-- Sector 0 has phase eigenvalue `1`. -/
theorem sectorPhase_mul_projector0 (omega : ℂ) :
    sectorPhase omega * sectorProjector0 = sectorProjector0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectorPhase, sectorProjector0, sectorProjector1, sectorProjector2, Matrix.mul_apply]

/-- Sector 1 has phase eigenvalue `ω`. -/
theorem sectorPhase_mul_projector1 (omega : ℂ) :
    sectorPhase omega * sectorProjector1 = omega • sectorProjector1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectorPhase, sectorProjector0, sectorProjector1, sectorProjector2, Matrix.mul_apply]

/-- Sector 2 has phase eigenvalue `ω²`. -/
theorem sectorPhase_mul_projector2 (omega : ℂ) :
    sectorPhase omega * sectorProjector2 = (omega ^ 2) • sectorProjector2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectorPhase, sectorProjector0, sectorProjector1, sectorProjector2, Matrix.mul_apply]

/-- Sector 0 has the same phase readout on the right. -/
theorem sectorProjector0_mul_sectorPhase (omega : ℂ) :
    sectorProjector0 * sectorPhase omega = sectorProjector0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectorPhase, sectorProjector0, sectorProjector1, sectorProjector2, Matrix.mul_apply]

/-- Sector 1 has the same phase readout on the right. -/
theorem sectorProjector1_mul_sectorPhase (omega : ℂ) :
    sectorProjector1 * sectorPhase omega = omega • sectorProjector1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectorPhase, sectorProjector0, sectorProjector1, sectorProjector2, Matrix.mul_apply]

/-- Sector 2 has the same phase readout on the right. -/
theorem sectorProjector2_mul_sectorPhase (omega : ℂ) :
    sectorProjector2 * sectorPhase omega = (omega ^ 2) • sectorProjector2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectorPhase, sectorProjector0, sectorProjector1, sectorProjector2, Matrix.mul_apply]

/-- Each diagonal sector projector has trace one. -/
theorem trace3_sectorProjector0 : trace3 sectorProjector0 = 1 := by
  norm_num [trace3, sectorProjector0, Fin.sum_univ_three]

/-- Each diagonal sector projector has trace one. -/
theorem trace3_sectorProjector1 : trace3 sectorProjector1 = 1 := by
  norm_num [trace3, sectorProjector1, Fin.sum_univ_three]

/-- Each diagonal sector projector has trace one. -/
theorem trace3_sectorProjector2 : trace3 sectorProjector2 = 1 := by
  norm_num [trace3, sectorProjector2, Fin.sum_univ_three]

/-- The phase trace is the finite character sum `1 + ω + ω²`. -/
theorem trace3_sectorPhase (omega : ℂ) : trace3 (sectorPhase omega) = 1 + omega + omega ^ 2 := by
  simp [trace3, sectorPhase, sectorProjector0, sectorProjector1, sectorProjector2, Fin.sum_univ_three]

/-- If `ω³=1`, the finite sector phase cubes to identity. -/
theorem sectorPhase_cube_identity (omega : ℂ) (homega : omega ^ 3 = 1) :
    sectorPhase omega * sectorPhase omega * sectorPhase omega = 1 := by
  have h1 : omega * omega * omega = 1 := by
    calc
      omega * omega * omega = omega ^ 3 := by ring
      _ = 1 := homega
  have h2 : omega ^ 2 * omega ^ 2 * omega ^ 2 = 1 := by
    calc
      omega ^ 2 * omega ^ 2 * omega ^ 2 = (omega ^ 3) ^ 2 := by ring
      _ = 1 := by rw [homega]; norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sectorPhase, sectorProjector0, sectorProjector1, sectorProjector2,
      Matrix.mul_apply, h1, h2]

/-- Finite central-extension product on `G × ZMod 3` using an explicit cocycle table. -/
def finiteCentralExtensionMul {G : Type} [Mul G] (tau : G → G → ZMod 3) :
    (G × ZMod 3) → (G × ZMod 3) → (G × ZMod 3)
  | (g, a), (h, b) => (g * h, a + b + tau g h)

/-- Product-level cocycle associativity equation for the finite central-extension law. -/
def ProductCocycleAssociative {G : Type} [Mul G] (tau : G → G → ZMod 3) : Prop :=
  ∀ g h k a b c,
    a + b + tau g h + c + tau (g * h) k =
      a + (b + c + tau h k) + tau g (h * k)

/-- Under explicit cocycle associativity, the finite extension product is associative. -/
theorem finiteCentralExtensionMul_assoc {G : Type} [Semigroup G]
    (tau : G → G → ZMod 3) (hassoc : ProductCocycleAssociative tau)
    (x y z : G × ZMod 3) :
    finiteCentralExtensionMul tau (finiteCentralExtensionMul tau x y) z =
      finiteCentralExtensionMul tau x (finiteCentralExtensionMul tau y z) := by
  rcases x with ⟨g, a⟩
  rcases y with ⟨h, b⟩
  rcases z with ⟨k, c⟩
  unfold finiteCentralExtensionMul
  ext
  · simp [mul_assoc]
  · exact hassoc g h k a b c

/-- Projection from the finite extension to the base multiplication component. -/
theorem finiteCentralExtensionMul_fst {G : Type} [Mul G]
    (tau : G → G → ZMod 3) (g h : G) (a b : ZMod 3) :
    (finiteCentralExtensionMul tau (g, a) (h, b)).1 = g * h := by
  rfl

/-- Central `ZMod 3` kernel addition in the trivial base component. -/
theorem finiteCentralExtension_kernel_add {G : Type} [Mul G] [One G]
    (tau : G → G → ZMod 3) (a b : ZMod 3) :
    (finiteCentralExtensionMul tau (1, a) (1, b)).2 = a + b + tau 1 1 := by
  rfl

/-- Repaired theorem-safe Chapter 14 finite `Z₃` packet. -/
theorem repaired_MD014_z3_projector_packet {G : Type} [Semigroup G]
    (tau : G → G → ZMod 3) (hassoc : ProductCocycleAssociative tau)
    (omega : ℂ) (homega : omega ^ 3 = 1) (x y z : G × ZMod 3) :
    sectorProjector0 * sectorProjector0 = sectorProjector0 ∧
    sectorProjector1 * sectorProjector1 = sectorProjector1 ∧
    sectorProjector2 * sectorProjector2 = sectorProjector2 ∧
    sectorProjector0 * sectorProjector1 = 0 ∧
    sectorProjector1 * sectorProjector0 = 0 ∧
    sectorProjector0 + sectorProjector1 + sectorProjector2 = 1 ∧
    trace3 sectorProjector0 = 1 ∧
    trace3 sectorProjector1 = 1 ∧
    trace3 sectorProjector2 = 1 ∧
    trace3 (sectorPhase omega) = 1 + omega + omega ^ 2 ∧
    sectorPhase omega * sectorProjector1 = omega • sectorProjector1 ∧
    sectorProjector1 * sectorPhase omega = omega • sectorProjector1 ∧
    sectorPhase omega * sectorPhase omega * sectorPhase omega = 1 ∧
    finiteCentralExtensionMul tau (finiteCentralExtensionMul tau x y) z =
      finiteCentralExtensionMul tau x (finiteCentralExtensionMul tau y z) := by
  exact ⟨sectorProjector0_idempotent, sectorProjector1_idempotent,
    sectorProjector2_idempotent, sectorProjector0_mul_sectorProjector1,
    sectorProjector1_mul_sectorProjector0, sectorProjector_sum_identity,
    trace3_sectorProjector0, trace3_sectorProjector1, trace3_sectorProjector2,
    trace3_sectorPhase omega, sectorPhase_mul_projector1 omega,
    sectorProjector1_mul_sectorPhase omega, sectorPhase_cube_identity omega homega,
    finiteCentralExtensionMul_assoc tau hassoc x y z⟩

end InfoGeometry.Physics.MD014TriSpinZ3Projectors

end noncomputable section
