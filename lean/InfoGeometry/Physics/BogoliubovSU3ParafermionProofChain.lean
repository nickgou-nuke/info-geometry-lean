import InfoGeometry.Physics.BogoliubovSU3ParafermionWeld

/-!
# Bogoliubov--SU(3)--parafermion proof chain

This file contains explicit finite algebraic lemma chains:

* a four-component color spinor is a color triplet plus one singlet component;
* the SU(3) Lie algebra acts by matrix multiplication on the triplet and kills
  the singlet infinitesimally;
* this action genuinely represents commutators;
* Bogoliubov q-clock braiding is scalar multiplication on the four-component
  spinor, with the chemical-potential shift proved from the log-clock lemma;
* concrete Gell-Mann commutators are transported to genuine color-action
  commutator identities.
-/

noncomputable section

namespace BogoliubovSU3ParafermionProofChain

open InfoGeometry.Physics.BogoliubovWeylChemicalPotential
open InfoGeometry.Physics.BogoliubovSU3ParafermionWeld
open InfoGeometry.Physics.SupergradedCuntzBdG
open InfoGeometry.Physics.GellMannSU3
open InfoGeometry.Topology.AlgebraicCuntzQuotient

abbrev M3C := Matrix (Fin 3) (Fin 3) ℂ
abbrev ParafermionStage4 := CuntzAlg ℂ (Fin 4)

/-- A four-component color/BdG spinor: three color components plus one color
singlet component. -/
abbrev ColorSpinor4 (V : Type*) := (Fin 3 → V) × V

/-- Infinitesimal SU(3) color action on a four-component spinor: fundamental
matrix action on the triplet and zero action on the singlet. -/
def colorLieAction4 {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : M3C) (ψ : ColorSpinor4 V) : ColorSpinor4 V :=
  (fun i => ∑ j : Fin 3, A i j • ψ.1 j, 0)

/-- Matrix multiplication is represented by composition of color actions. -/
theorem colorLieAction4_mul {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : M3C) (ψ : ColorSpinor4 V) :
    colorLieAction4 (A * B) ψ = colorLieAction4 A (colorLieAction4 B ψ) := by
  ext i <;> simp [colorLieAction4, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  simp [smul_smul]

/-- The infinitesimal color action is linear in the Lie-algebra matrix. -/
theorem colorLieAction4_sub {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : M3C) (ψ : ColorSpinor4 V) :
    colorLieAction4 (A - B) ψ = colorLieAction4 A ψ - colorLieAction4 B ψ := by
  ext i <;> simp [colorLieAction4, Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]

/-- Genuine representation lemma: the action of a matrix commutator is the
commutator of the actions. -/
theorem colorLieAction4_commutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : M3C) (ψ : ColorSpinor4 V) :
    colorLieAction4 (A * B - B * A) ψ =
      colorLieAction4 A (colorLieAction4 B ψ) -
        colorLieAction4 B (colorLieAction4 A ψ) := by
  rw [colorLieAction4_sub, colorLieAction4_mul, colorLieAction4_mul]

/-- Scalar q-braiding on the four-component spinor. -/
def qBraid4 {V : Type*} [SMul ℂ V] (q : ℂ) (ψ : ColorSpinor4 V) : ColorSpinor4 V :=
  q • ψ

/-- Braiding phases compose multiplicatively. -/
theorem qBraid4_comp {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (q r : ℂ) (ψ : ColorSpinor4 V) :
    qBraid4 q (qBraid4 r ψ) = qBraid4 (q * r) ψ := by
  simp [qBraid4, smul_smul]

/-- The Bogoliubov frame braiding is scalar multiplication by the frame q-clock. -/
def frameBraid4 {V : Type*} [SMul ℂ V]
    (F : BogoliubovInertialFrame) (ψ : ColorSpinor4 V) : ColorSpinor4 V :=
  qBraid4 (frameBraidingPhase F) ψ

/-- Chemical-potential shifts act on braiding by multiplying the phase by
`exp(β δμ Q)`. -/
theorem frameBraid4_mu_shift {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (F : BogoliubovInertialFrame) (δμ : ℝ) (ψ : ColorSpinor4 V) :
    frameBraid4 { F with μ := F.μ + δμ } ψ =
      qBraid4 (qRapidity (F.β * δμ * F.Q)) (frameBraid4 F ψ) := by
  unfold frameBraid4
  rw [frameBraidingPhase_mu_shift F δμ]
  rw [qBraid4_comp]

/-- A concrete four-component BdG/Majorana spinor: three color components plus a
singlet fourth component. -/
def bdgMajoranaPlusColorSpinor4 : ColorSpinor4 ParafermionStage4 :=
  (fun i : Fin 3 =>
    bdgParafermionPlus4 ⟨i.1, Nat.lt_trans i.2 (by decide : 3 < 4)⟩,
    bdgParafermionPlus4 3)

/-- The triplet entries of the concrete BdG spinor square to Hamiltonian atoms. -/
theorem bdgMajoranaPlusColorSpinor4_color_sq (i : Fin 3) :
    bdgMajoranaPlusColorSpinor4.1 i * bdgMajoranaPlusColorSpinor4.1 i =
      hamiltonianAtom (⟨i.1, Nat.lt_trans i.2 (by decide : 3 < 4)⟩ : Fin 4) := by
  simp [bdgMajoranaPlusColorSpinor4, bdgParafermionPlus4_sq]

/-- The singlet entry of the concrete BdG spinor squares to its Hamiltonian atom. -/
theorem bdgMajoranaPlusColorSpinor4_singlet_sq :
    bdgMajoranaPlusColorSpinor4.2 * bdgMajoranaPlusColorSpinor4.2 =
      hamiltonianAtom (3 : Fin 4) := by
  simp [bdgMajoranaPlusColorSpinor4, bdgParafermionPlus4_sq]

/-- Concrete SU(3) proof-chain identity: `[λ₁,λ₂]=2iλ₃` represented on every
four-component color/BdG spinor. -/
theorem colorAction_gl1_gl2_commutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ψ : ColorSpinor4 V) :
    colorLieAction4 ((2 * Complex.I) • gl3) ψ =
      colorLieAction4 gl1 (colorLieAction4 gl2 ψ) -
        colorLieAction4 gl2 (colorLieAction4 gl1 ψ) := by
  rw [← colorLieAction4_commutator gl1 gl2 ψ]
  rw [gl1_comm_gl2]

/-- Concrete SU(3) proof-chain identity: `[λ₁,λ₃]=-2iλ₂` represented on every
four-component color/BdG spinor. -/
theorem colorAction_gl1_gl3_commutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ψ : ColorSpinor4 V) :
    colorLieAction4 ((-2 * Complex.I) • gl2) ψ =
      colorLieAction4 gl1 (colorLieAction4 gl3 ψ) -
        colorLieAction4 gl3 (colorLieAction4 gl1 ψ) := by
  rw [← colorLieAction4_commutator gl1 gl3 ψ]
  rw [gl1_comm_gl3]

/-- Concrete SU(3) proof-chain identity: `[λ₂,λ₃]=2iλ₁` represented on every
four-component color/BdG spinor. -/
theorem colorAction_gl2_gl3_commutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ψ : ColorSpinor4 V) :
    colorLieAction4 ((2 * Complex.I) • gl1) ψ =
      colorLieAction4 gl2 (colorLieAction4 gl3 ψ) -
        colorLieAction4 gl3 (colorLieAction4 gl2 ψ) := by
  rw [← colorLieAction4_commutator gl2 gl3 ψ]
  rw [gl2_comm_gl3]

/-- Concrete SU(3): `[λ₁,λ₆]=iλ₅`. -/
theorem colorAction_gl1_gl6_commutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ψ : ColorSpinor4 V) :
    colorLieAction4 (Complex.I • gl5) ψ =
      colorLieAction4 gl1 (colorLieAction4 gl6 ψ) -
        colorLieAction4 gl6 (colorLieAction4 gl1 ψ) := by
  rw [← colorLieAction4_commutator gl1 gl6 ψ]
  rw [gl1_comm_gl6]

/-- Concrete SU(3): `[λ₁,λ₇]=-iλ₄`. -/
theorem colorAction_gl1_gl7_commutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ψ : ColorSpinor4 V) :
    colorLieAction4 ((-Complex.I) • gl4) ψ =
      colorLieAction4 gl1 (colorLieAction4 gl7 ψ) -
        colorLieAction4 gl7 (colorLieAction4 gl1 ψ) := by
  rw [← colorLieAction4_commutator gl1 gl7 ψ]
  rw [gl1_comm_gl7]

/-- Concrete SU(3): `[λ₂,λ₆]=-iλ₄`. -/
theorem colorAction_gl2_gl6_commutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ψ : ColorSpinor4 V) :
    colorLieAction4 ((-Complex.I) • gl4) ψ =
      colorLieAction4 gl2 (colorLieAction4 gl6 ψ) -
        colorLieAction4 gl6 (colorLieAction4 gl2 ψ) := by
  rw [← colorLieAction4_commutator gl2 gl6 ψ]
  rw [gl2_comm_gl6]

/-- Concrete SU(3): `[λ₂,λ₇]=-iλ₅`. -/
theorem colorAction_gl2_gl7_commutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ψ : ColorSpinor4 V) :
    colorLieAction4 ((-Complex.I) • gl5) ψ =
      colorLieAction4 gl2 (colorLieAction4 gl7 ψ) -
        colorLieAction4 gl7 (colorLieAction4 gl2 ψ) := by
  rw [← colorLieAction4_commutator gl2 gl7 ψ]
  rw [gl2_comm_gl7]

/-- Concrete SU(3): `[λ₃,λ₄]=iλ₅`. -/
theorem colorAction_gl3_gl4_commutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ψ : ColorSpinor4 V) :
    colorLieAction4 (Complex.I • gl5) ψ =
      colorLieAction4 gl3 (colorLieAction4 gl4 ψ) -
        colorLieAction4 gl4 (colorLieAction4 gl3 ψ) := by
  rw [← colorLieAction4_commutator gl3 gl4 ψ]
  rw [gl3_comm_gl4]

/-- Concrete SU(3): `[λ₃,λ₅]=-iλ₄`. -/
theorem colorAction_gl3_gl5_commutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ψ : ColorSpinor4 V) :
    colorLieAction4 ((-Complex.I) • gl4) ψ =
      colorLieAction4 gl3 (colorLieAction4 gl5 ψ) -
        colorLieAction4 gl5 (colorLieAction4 gl3 ψ) := by
  rw [← colorLieAction4_commutator gl3 gl5 ψ]
  rw [gl3_comm_gl5]

/-- Concrete SU(3): `[λ₄,λ₆]=iλ₂`. -/
theorem colorAction_gl4_gl6_commutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ψ : ColorSpinor4 V) :
    colorLieAction4 (Complex.I • gl2) ψ =
      colorLieAction4 gl4 (colorLieAction4 gl6 ψ) -
        colorLieAction4 gl6 (colorLieAction4 gl4 ψ) := by
  rw [← colorLieAction4_commutator gl4 gl6 ψ]
  rw [gl4_comm_gl6]

/-- Concrete SU(3): `[λ₄,λ₇]=iλ₁`. -/
theorem colorAction_gl4_gl7_commutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ψ : ColorSpinor4 V) :
    colorLieAction4 (Complex.I • gl1) ψ =
      colorLieAction4 gl4 (colorLieAction4 gl7 ψ) -
        colorLieAction4 gl7 (colorLieAction4 gl4 ψ) := by
  rw [← colorLieAction4_commutator gl4 gl7 ψ]
  rw [gl4_comm_gl7]

/-- Concrete SU(3): `[λ₅,λ₆]=-iλ₁`. -/
theorem colorAction_gl5_gl6_commutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ψ : ColorSpinor4 V) :
    colorLieAction4 ((-Complex.I) • gl1) ψ =
      colorLieAction4 gl5 (colorLieAction4 gl6 ψ) -
        colorLieAction4 gl6 (colorLieAction4 gl5 ψ) := by
  rw [← colorLieAction4_commutator gl5 gl6 ψ]
  rw [gl5_comm_gl6]

/-- Concrete SU(3): `[λ₅,λ₇]=iλ₂`. -/
theorem colorAction_gl5_gl7_commutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ψ : ColorSpinor4 V) :
    colorLieAction4 (Complex.I • gl2) ψ =
      colorLieAction4 gl5 (colorLieAction4 gl7 ψ) -
        colorLieAction4 gl7 (colorLieAction4 gl5 ψ) := by
  rw [← colorLieAction4_commutator gl5 gl7 ψ]
  rw [gl5_comm_gl7]

/-- Concrete SU(3): Cartan subalgebra `[λ₃,λ₈]=0`. The gauge actions commute. -/
theorem colorAction_gl3_gl8_commute {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ψ : ColorSpinor4 V) :
    colorLieAction4 gl3 (colorLieAction4 gl8 ψ) =
      colorLieAction4 gl8 (colorLieAction4 gl3 ψ) := by
  have h := colorLieAction4_commutator gl3 gl8 ψ
  have hzero : gl3 * gl8 - gl8 * gl3 = (0 : M3C) := by
    rw [gl3_comm_gl8, sub_self]
  rw [hzero] at h
  have h0 : colorLieAction4 (0 : M3C) ψ = 0 := by
    ext i <;> simp [colorLieAction4]
  rw [h0] at h
  exact sub_eq_zero.mp h.symm

/-- Concrete SU(3): `[λ₄,λ₈]=-3iλ₅`. Cartan action on the (4,5) root. -/
theorem colorAction_gl4_gl8_commutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ψ : ColorSpinor4 V) :
    colorLieAction4 ((-3 * Complex.I) • gl5) ψ =
      colorLieAction4 gl4 (colorLieAction4 gl8 ψ) -
        colorLieAction4 gl8 (colorLieAction4 gl4 ψ) := by
  rw [← colorLieAction4_commutator gl4 gl8 ψ]
  rw [gl4_comm_gl8]

/-- Concrete SU(3): `[λ₅,λ₈]=3iλ₄`. Cartan action on the (5,4) root. -/
theorem colorAction_gl5_gl8_commutator {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ψ : ColorSpinor4 V) :
    colorLieAction4 ((3 * Complex.I) • gl4) ψ =
      colorLieAction4 gl5 (colorLieAction4 gl8 ψ) -
        colorLieAction4 gl8 (colorLieAction4 gl5 ψ) := by
  rw [← colorLieAction4_commutator gl5 gl8 ψ]
  rw [gl5_comm_gl8]

/-- All 16 SU(3) Gell-Mann commutators transported to the color Lie action
on four-component color/BdG spinors.  Includes the two Cartan diagonal
generators λ₃,λ₈ which commute, and 14 off-diagonal commutators. -/
theorem su3_color_action_all_commutators
    {V : Type*} [AddCommGroup V] [Module ℂ V] (ψ : ColorSpinor4 V) :
    colorLieAction4 ((2 * Complex.I) • gl3) ψ =
      colorLieAction4 gl1 (colorLieAction4 gl2 ψ) -
        colorLieAction4 gl2 (colorLieAction4 gl1 ψ) ∧
    colorLieAction4 ((-2 * Complex.I) • gl2) ψ =
      colorLieAction4 gl1 (colorLieAction4 gl3 ψ) -
        colorLieAction4 gl3 (colorLieAction4 gl1 ψ) ∧
    colorLieAction4 ((2 * Complex.I) • gl1) ψ =
      colorLieAction4 gl2 (colorLieAction4 gl3 ψ) -
        colorLieAction4 gl3 (colorLieAction4 gl2 ψ) ∧
    colorLieAction4 (Complex.I • gl5) ψ =
      colorLieAction4 gl1 (colorLieAction4 gl6 ψ) -
        colorLieAction4 gl6 (colorLieAction4 gl1 ψ) ∧
    colorLieAction4 ((-Complex.I) • gl4) ψ =
      colorLieAction4 gl1 (colorLieAction4 gl7 ψ) -
        colorLieAction4 gl7 (colorLieAction4 gl1 ψ) ∧
    colorLieAction4 ((-Complex.I) • gl4) ψ =
      colorLieAction4 gl2 (colorLieAction4 gl6 ψ) -
        colorLieAction4 gl6 (colorLieAction4 gl2 ψ) ∧
    colorLieAction4 ((-Complex.I) • gl5) ψ =
      colorLieAction4 gl2 (colorLieAction4 gl7 ψ) -
        colorLieAction4 gl7 (colorLieAction4 gl2 ψ) ∧
    colorLieAction4 (Complex.I • gl5) ψ =
      colorLieAction4 gl3 (colorLieAction4 gl4 ψ) -
        colorLieAction4 gl4 (colorLieAction4 gl3 ψ) ∧
    colorLieAction4 ((-Complex.I) • gl4) ψ =
      colorLieAction4 gl3 (colorLieAction4 gl5 ψ) -
        colorLieAction4 gl5 (colorLieAction4 gl3 ψ) ∧
    colorLieAction4 (Complex.I • gl2) ψ =
      colorLieAction4 gl4 (colorLieAction4 gl6 ψ) -
        colorLieAction4 gl6 (colorLieAction4 gl4 ψ) ∧
    colorLieAction4 (Complex.I • gl1) ψ =
      colorLieAction4 gl4 (colorLieAction4 gl7 ψ) -
        colorLieAction4 gl7 (colorLieAction4 gl4 ψ) ∧
    colorLieAction4 ((-Complex.I) • gl1) ψ =
      colorLieAction4 gl5 (colorLieAction4 gl6 ψ) -
        colorLieAction4 gl6 (colorLieAction4 gl5 ψ) ∧
    colorLieAction4 (Complex.I • gl2) ψ =
      colorLieAction4 gl5 (colorLieAction4 gl7 ψ) -
        colorLieAction4 gl7 (colorLieAction4 gl5 ψ) ∧
    colorLieAction4 gl3 (colorLieAction4 gl8 ψ) =
      colorLieAction4 gl8 (colorLieAction4 gl3 ψ) ∧
    colorLieAction4 ((-3 * Complex.I) • gl5) ψ =
      colorLieAction4 gl4 (colorLieAction4 gl8 ψ) -
        colorLieAction4 gl8 (colorLieAction4 gl4 ψ) ∧
    colorLieAction4 ((3 * Complex.I) • gl4) ψ =
      colorLieAction4 gl5 (colorLieAction4 gl8 ψ) -
        colorLieAction4 gl8 (colorLieAction4 gl5 ψ) := by
  constructor
  · exact colorAction_gl1_gl2_commutator ψ
  constructor
  · exact colorAction_gl1_gl3_commutator ψ
  constructor
  · exact colorAction_gl2_gl3_commutator ψ
  constructor
  · exact colorAction_gl1_gl6_commutator ψ
  constructor
  · exact colorAction_gl1_gl7_commutator ψ
  constructor
  · exact colorAction_gl2_gl6_commutator ψ
  constructor
  · exact colorAction_gl2_gl7_commutator ψ
  constructor
  · exact colorAction_gl3_gl4_commutator ψ
  constructor
  · exact colorAction_gl3_gl5_commutator ψ
  constructor
  · exact colorAction_gl4_gl6_commutator ψ
  constructor
  · exact colorAction_gl4_gl7_commutator ψ
  constructor
  · exact colorAction_gl5_gl6_commutator ψ
  constructor
  · exact colorAction_gl5_gl7_commutator ψ
  constructor
  · exact colorAction_gl3_gl8_commute ψ
  constructor
  · exact colorAction_gl4_gl8_commutator ψ
  · exact colorAction_gl5_gl8_commutator ψ

/-- The Bogoliubov-deformed even-even bracket recovers the SU(3) action
commutator on the four-component spinor. -/
theorem frame_colorAction_gl1_gl2
    (F : BogoliubovInertialFrame) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ψ : ColorSpinor4 V) :
    colorLieAction4
        (affineSuperBracket (frameWeylQ F) Z2Parity.even Z2Parity.even gl1 gl2) ψ =
      colorLieAction4 gl1 (colorLieAction4 gl2 ψ) -
        colorLieAction4 gl2 (colorLieAction4 gl1 ψ) := by
  rw [frame_affine_gl1_gl2]
  exact colorAction_gl1_gl2_commutator ψ

/-- Closed synthesis for the proved finite chain.

All 16 SU(3) Gell-Mann commutators are proved for the color Lie action
on four-component spinors over any ℂ-module with additive inverses.
The braiding phase, Majorana square laws, and Bogoliubov frame compatibility
are bundled. -/
theorem bogoliubov_su3_parafermion_proof_chain
    (F : BogoliubovInertialFrame) (δμ : ℝ)
    {V : Type*} [AddCommGroup V] [Module ℂ V] (ψ : ColorSpinor4 V) :
    frameBraid4 { F with μ := F.μ + δμ } bdgMajoranaPlusColorSpinor4 =
      qBraid4 (qRapidity (F.β * δμ * F.Q))
        (frameBraid4 F bdgMajoranaPlusColorSpinor4) ∧
    (∀ i : Fin 3,
      bdgMajoranaPlusColorSpinor4.1 i * bdgMajoranaPlusColorSpinor4.1 i =
        hamiltonianAtom (⟨i.1, Nat.lt_trans i.2 (by decide : 3 < 4)⟩ : Fin 4)) ∧
    bdgMajoranaPlusColorSpinor4.2 * bdgMajoranaPlusColorSpinor4.2 =
      hamiltonianAtom (3 : Fin 4) ∧
    (colorLieAction4 ((2 * Complex.I) • gl3) ψ =
      colorLieAction4 gl1 (colorLieAction4 gl2 ψ) -
        colorLieAction4 gl2 (colorLieAction4 gl1 ψ) ∧
     colorLieAction4 ((-2 * Complex.I) • gl2) ψ =
      colorLieAction4 gl1 (colorLieAction4 gl3 ψ) -
        colorLieAction4 gl3 (colorLieAction4 gl1 ψ) ∧
     colorLieAction4 ((2 * Complex.I) • gl1) ψ =
      colorLieAction4 gl2 (colorLieAction4 gl3 ψ) -
        colorLieAction4 gl3 (colorLieAction4 gl2 ψ) ∧
     colorLieAction4 (Complex.I • gl5) ψ =
      colorLieAction4 gl1 (colorLieAction4 gl6 ψ) -
        colorLieAction4 gl6 (colorLieAction4 gl1 ψ) ∧
     colorLieAction4 ((-Complex.I) • gl4) ψ =
      colorLieAction4 gl1 (colorLieAction4 gl7 ψ) -
        colorLieAction4 gl7 (colorLieAction4 gl1 ψ) ∧
     colorLieAction4 ((-Complex.I) • gl4) ψ =
      colorLieAction4 gl2 (colorLieAction4 gl6 ψ) -
        colorLieAction4 gl6 (colorLieAction4 gl2 ψ) ∧
     colorLieAction4 ((-Complex.I) • gl5) ψ =
      colorLieAction4 gl2 (colorLieAction4 gl7 ψ) -
        colorLieAction4 gl7 (colorLieAction4 gl2 ψ) ∧
     colorLieAction4 (Complex.I • gl5) ψ =
      colorLieAction4 gl3 (colorLieAction4 gl4 ψ) -
        colorLieAction4 gl4 (colorLieAction4 gl3 ψ) ∧
     colorLieAction4 ((-Complex.I) • gl4) ψ =
      colorLieAction4 gl3 (colorLieAction4 gl5 ψ) -
        colorLieAction4 gl5 (colorLieAction4 gl3 ψ) ∧
     colorLieAction4 (Complex.I • gl2) ψ =
      colorLieAction4 gl4 (colorLieAction4 gl6 ψ) -
        colorLieAction4 gl6 (colorLieAction4 gl4 ψ) ∧
     colorLieAction4 (Complex.I • gl1) ψ =
      colorLieAction4 gl4 (colorLieAction4 gl7 ψ) -
        colorLieAction4 gl7 (colorLieAction4 gl4 ψ) ∧
     colorLieAction4 ((-Complex.I) • gl1) ψ =
      colorLieAction4 gl5 (colorLieAction4 gl6 ψ) -
        colorLieAction4 gl6 (colorLieAction4 gl5 ψ) ∧
     colorLieAction4 (Complex.I • gl2) ψ =
      colorLieAction4 gl5 (colorLieAction4 gl7 ψ) -
        colorLieAction4 gl7 (colorLieAction4 gl5 ψ) ∧
     colorLieAction4 gl3 (colorLieAction4 gl8 ψ) =
      colorLieAction4 gl8 (colorLieAction4 gl3 ψ) ∧
     colorLieAction4 ((-3 * Complex.I) • gl5) ψ =
      colorLieAction4 gl4 (colorLieAction4 gl8 ψ) -
        colorLieAction4 gl8 (colorLieAction4 gl4 ψ) ∧
     colorLieAction4 ((3 * Complex.I) • gl4) ψ =
      colorLieAction4 gl5 (colorLieAction4 gl8 ψ) -
        colorLieAction4 gl8 (colorLieAction4 gl5 ψ)) := by
  constructor
  · exact frameBraid4_mu_shift F δμ bdgMajoranaPlusColorSpinor4
  constructor
  · exact bdgMajoranaPlusColorSpinor4_color_sq
  constructor
  · exact bdgMajoranaPlusColorSpinor4_singlet_sq
  · exact su3_color_action_all_commutators ψ



end BogoliubovSU3ParafermionProofChain

end noncomputable section
