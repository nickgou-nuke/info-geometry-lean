/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Modular.SchrodingerGKSLFlowBridge
import InfoGeometry.Core.JordanAssociatorRing
import InfoGeometry.Thermodynamics.FiniteEntropyLeaves
import InfoGeometry.Lie.ContinuousDerivationExponential
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef

/-!
# Conserved commutant readouts for finite-matrix GKSL flows

The Schrödinger GKSL generator has an exact trace-dual invariant for every
observable commuting with the Hamiltonian and with each jump and adjoint.
Consequently a flow orbit cannot converge to a proposed state whose readout
differs from the initial readout. This is an operator-valued commutant
obstruction; it does not assume that the semigroup converges or is primitive.
-/

noncomputable section

namespace InfoGeometry.Modular.CommutantInvariantGKSLFlow

open Matrix
open Filter Topology
open scoped Matrix.Norms.L2Operator ComplexOrder
open InfoGeometry.Modular.SchrodingerGKSL
open InfoGeometry.Modular.SchrodingerGKSLFlowBridge

variable {n : Type*} [Fintype n] [DecidableEq n]
local notation "Mat" => Matrix n n ℂ

/-- A matrix observable's real trace readout on a Schrödinger state/operator. -/
def observableReadoutCLM (Q : Mat) : Mat →L[ℝ] ℝ :=
  realTraceCLM.comp ((leftMul Q).restrictScalars ℝ)

@[simp] theorem observableReadoutCLM_apply (Q X : Mat) :
    observableReadoutCLM Q X = (Matrix.trace (Q * X)).re := rfl

omit [DecidableEq n] in
private theorem trace_hamiltonian_commutant_zero
    (Q H ρ : Mat) (hQH : Q * H = H * Q) :
    Matrix.trace (Q * hamiltonianTerm H ρ) = 0 := by
  simp only [hamiltonianTerm, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.mul_sub, Matrix.trace_sub]
  have hcyc : Matrix.trace (Q * (H * ρ)) =
      Matrix.trace (Q * (ρ * H)) := by
    calc
      Matrix.trace (Q * (H * ρ)) = Matrix.trace ((Q * H) * ρ) := by simp [mul_assoc]
      _ = Matrix.trace ((H * Q) * ρ) := by rw [hQH]
      _ = Matrix.trace (H * (Q * ρ)) := by simp [mul_assoc]
      _ = Matrix.trace ((Q * ρ) * H) := Matrix.trace_mul_comm H (Q * ρ)
      _ = Matrix.trace (Q * (ρ * H)) := by simp [mul_assoc]
  rw [hcyc, sub_self, smul_zero]

omit [DecidableEq n] in
private theorem trace_dissipator_commutant_zero
    (Q V ρ : Mat) (hQV : Q * V = V * Q)
    (hQstarV : Q * star V = star V * Q) :
    Matrix.trace (Q * schrodingerDissipatorTerm V ρ) = 0 := by
  simp only [schrodingerDissipatorTerm, Matrix.mul_sub, Matrix.trace_sub,
    Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.trace_add,
    smul_eq_mul]
  have hprod_comm : Q * (star V * V) = (star V * V) * Q := by
    calc
      Q * (star V * V) = (Q * star V) * V := by simp [mul_assoc]
      _ = (star V * Q) * V := by rw [hQstarV]
      _ = star V * (Q * V) := by simp [mul_assoc]
      _ = star V * (V * Q) := by rw [hQV]
      _ = (star V * V) * Q := by simp [mul_assoc]
  have hjump :
      Matrix.trace (Q * (V * ρ * star V)) =
        Matrix.trace (star V * V * Q * ρ) := by
    calc
      Matrix.trace (Q * (V * ρ * star V)) =
          Matrix.trace ((Q * V * ρ) * star V) := by simp [mul_assoc]
      _ = Matrix.trace (star V * (Q * V * ρ)) :=
          Matrix.trace_mul_comm (Q * V * ρ) (star V)
      _ = Matrix.trace (star V * (V * Q * ρ)) := by rw [hQV]
      _ = Matrix.trace (star V * V * Q * ρ) := by simp [mul_assoc]
  have hleft :
      Matrix.trace (Q * (star V * V * ρ)) =
        Matrix.trace (star V * V * Q * ρ) := by
    calc
      Matrix.trace (Q * (star V * V * ρ)) =
          Matrix.trace ((Q * (star V * V)) * ρ) := by simp [mul_assoc]
      _ = Matrix.trace (((star V * V) * Q) * ρ) := by rw [hprod_comm]
      _ = Matrix.trace (star V * V * Q * ρ) := by simp [mul_assoc]
  have hright :
      Matrix.trace (Q * (ρ * star V * V)) =
        Matrix.trace (star V * V * Q * ρ) := by
    calc
      Matrix.trace (Q * (ρ * star V * V)) =
          Matrix.trace ((Q * ρ) * (star V * V)) := by simp [mul_assoc]
      _ = Matrix.trace ((star V * V) * (Q * ρ)) :=
          Matrix.trace_mul_comm (Q * ρ) (star V * V)
      _ = Matrix.trace (star V * V * Q * ρ) := by simp [mul_assoc]
  rw [hjump, hleft, hright]
  ring

/-- The Schrödinger GKSL generator annihilates the trace pairing with any
observable in the joint commutant of the Hamiltonian and all jump operators
and their adjoints. -/
theorem observableReadout_generator_eq_zero
    (H Q X : Mat) {ι : Type*} [Fintype ι] (V : ι → Mat)
    (hQH : Q * H = H * Q)
    (hQV : ∀ i, Q * V i = V i * Q)
    (hQstarV : ∀ i, Q * star (V i) = star (V i) * Q) :
    observableReadoutCLM Q (generatorEnd H V X) = 0 := by
  change (Matrix.trace (Q * generatorCLM H V X)).re = 0
  rw [generatorCLM_apply]
  unfold schrodingerLindbladian schrodingerDissipator
  rw [Matrix.mul_add, Matrix.trace_add, Matrix.mul_sum, Matrix.trace_sum]
  have hham := trace_hamiltonian_commutant_zero Q H X hQH
  have hterms : ∀ i ∈ (Finset.univ : Finset ι),
      Matrix.trace (Q * schrodingerDissipatorTerm (V i) X) = 0 := by
    intro i _
    exact trace_dissipator_commutant_zero Q (V i) X (hQV i) (hQstarV i)
  have hsum : ∑ i : ι, Matrix.trace (Q * schrodingerDissipatorTerm (V i) X) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact hterms i (Finset.mem_univ i)
  rw [hham, hsum]
  simp

/-- The commutant readout is conserved along the full exponential GKSL flow.
The statement applies to arbitrary matrices, without positivity, diagonal
form, or a convergence assumption. -/
theorem observableReadout_gkslFlow_invariant
    (H Q X : Mat) {ι : Type*} [Fintype ι] (V : ι → Mat)
    (hQH : Q * H = H * Q)
    (hQV : ∀ i, Q * V i = V i * Q)
    (hQstarV : ∀ i, Q * star (V i) = star (V i) * Q) (t : ℝ) :
    (Matrix.trace (Q * gkslFlow H V t X)).re = (Matrix.trace (Q * X)).re := by
  apply InfoGeometry.Modular.SchrodingerFlow.trace_flow_preservation (generatorEnd H V)
    (observableReadoutCLM Q) ?_ X t
  intro Y
  exact observableReadout_generator_eq_zero H Q Y V hQH hQV hQstarV

/-- The affine level set of a joint-commutant observable readout through an
initial operator. This is a finite-matrix invariant leaf in the precise sense
of `FiniteEntropyLeaves.entropyLeaf`; no symplectic structure is asserted. -/
def commutantReadoutLeaf (Q X : Mat) : Set Mat :=
  InfoGeometry.Thermodynamics.FiniteEntropyLeaves.entropyLeaf
    (observableReadoutCLM Q) (observableReadoutCLM Q X)

/-- A Schrödinger GKSL orbit remains in the readout leaf selected by its
initial operator whenever the observable lies in the joint commutant of the
Hamiltonian and all jumps and adjoints. -/
theorem gkslFlow_maps_commutantReadoutLeaf
    (H Q X : Mat) {ι : Type*} [Fintype ι] (V : ι → Mat)
    (hQH : Q * H = H * Q)
    (hQV : ∀ i, Q * V i = V i * Q)
    (hQstarV : ∀ i, Q * star (V i) = star (V i) * Q) (t : ℝ) :
    gkslFlow H V t X ∈ commutantReadoutLeaf Q X := by
  change observableReadoutCLM Q (gkslFlow H V t X) =
    observableReadoutCLM Q X
  exact observableReadout_gkslFlow_invariant H Q X V hQH hQV hQstarV t

/-- The joint readout profile of a family of observables. Each coordinate is
the real trace pairing with the full matrix operator; the family may encode
several independent conserved charges. -/
def commutantReadoutProfile {ι : Type*} (Q : ι → Mat) (X : Mat) : ι → ℝ :=
  fun i => observableReadoutCLM (Q i) X

/-- The simultaneous invariant leaf cut out by a family of commutant
readouts. -/
def jointCommutantReadoutLeaf {ι : Type*} (Q : ι → Mat) (X : Mat) : Set Mat :=
  {Y | commutantReadoutProfile Q Y = commutantReadoutProfile Q X}

/-- A joint readout leaf is precisely the intersection of its individual
commutant readout leaves. -/
theorem jointCommutantReadoutLeaf_eq_iInter {ι : Type*}
    (Q : ι → Mat) (X : Mat) :
    jointCommutantReadoutLeaf Q X = ⋂ i, commutantReadoutLeaf (Q i) X := by
  ext Y
  simp only [jointCommutantReadoutLeaf, Set.mem_ofPred_eq, Set.mem_iInter,
    commutantReadoutLeaf,
    InfoGeometry.Thermodynamics.FiniteEntropyLeaves.entropyLeaf,
    commutantReadoutProfile, funext_iff]

/-- The full operator-valued GKSL orbit remains on every simultaneous leaf
defined by a family of joint-commutant observables. -/
theorem gkslFlow_maps_jointCommutantReadoutLeaf
    (H X : Mat) {ι κ : Type*} [Fintype κ] (V : κ → Mat)
    (Q : ι → Mat)
    (hQH : ∀ i, Q i * H = H * Q i)
    (hQV : ∀ i j, Q i * V j = V j * Q i)
    (hQstarV : ∀ i j, Q i * star (V j) = star (V j) * Q i)
    (t : ℝ) :
    gkslFlow H V t X ∈ jointCommutantReadoutLeaf Q X := by
  change commutantReadoutProfile Q (gkslFlow H V t X) =
    commutantReadoutProfile Q X
  funext i
  exact observableReadout_gkslFlow_invariant H (Q i) X V
    (hQH i) (hQV i) (hQstarV i) t

/-- Every norm limit of an orbit lies on the same joint commutant-readout
leaf as its initial operator. This constrains any NESS limit without assuming
that such a limit exists or is unique. -/
theorem tendsto_limit_mem_jointCommutantReadoutLeaf
    (H X rhoLimit : Mat) {ι κ : Type*} [Fintype κ] (V : κ → Mat)
    (Q : ι → Mat)
    (hQH : ∀ i, Q i * H = H * Q i)
    (hQV : ∀ i j, Q i * V j = V j * Q i)
    (hQstarV : ∀ i j, Q i * star (V j) = star (V j) * Q i)
    (hlim : Tendsto (fun t : ℝ => gkslFlow H V t X) atTop (𝓝 rhoLimit)) :
    rhoLimit ∈ jointCommutantReadoutLeaf Q X := by
  change commutantReadoutProfile Q rhoLimit = commutantReadoutProfile Q X
  funext i
  have hreadout :=
    ((observableReadoutCLM (Q i)).continuous.tendsto rhoLimit).comp hlim
  have hconst_eq :
      (fun t : ℝ => observableReadoutCLM (Q i) (gkslFlow H V t X)) =
        fun _ : ℝ => observableReadoutCLM (Q i) X := by
    funext t
    exact observableReadout_gkslFlow_invariant H (Q i) X V
      (hQH i) (hQV i) (hQstarV i) t
  have hconst : Tendsto
      (fun t : ℝ => observableReadoutCLM (Q i) (gkslFlow H V t X))
      atTop (𝓝 (observableReadoutCLM (Q i) X)) := by
    rw [hconst_eq]
    exact tendsto_const_nhds
  exact (tendsto_nhds_unique hconst hreadout).symm

/-- If the initial and proposed limiting operators have different joint-
commutant readouts, the GKSL orbit cannot converge to that proposed limit.
This is a direct consequence of the conserved full-matrix readout above. -/
theorem not_tendsto_gkslFlow_of_readout_ne
    (H Q X rhoLimit : Mat) {ι : Type*} [Fintype ι] (V : ι → Mat)
    (hQH : Q * H = H * Q)
    (hQV : ∀ i, Q * V i = V i * Q)
    (hQstarV : ∀ i, Q * star (V i) = star (V i) * Q)
    (hne : (Matrix.trace (Q * X)).re ≠ (Matrix.trace (Q * rhoLimit)).re) :
    ¬ Tendsto (fun t : ℝ => gkslFlow H V t X) atTop (𝓝 rhoLimit) := by
  intro hlim
  have hreadout :=
    ((observableReadoutCLM Q).continuous.tendsto rhoLimit).comp hlim
  have hconst : Tendsto (fun t : ℝ =>
      observableReadoutCLM Q (gkslFlow H V t X)) atTop
      (𝓝 ((Matrix.trace (Q * X)).re)) := by
    simpa only [observableReadout_gkslFlow_invariant H Q X V hQH hQV hQstarV,
      observableReadoutCLM_apply] using tendsto_const_nhds
  have hreadout_eq :
      (Matrix.trace (Q * X)).re = (Matrix.trace (Q * rhoLimit)).re :=
    tendsto_nhds_unique hconst hreadout
  exact hne hreadout_eq

/-- For a self-adjoint matrix projection used as a single Lindblad jump, its
range projection and its complementary projection are positive stationary
operators of the full Schrödinger generator. This gives an explicit
operator-valued memory pair for a reducible jump algebra; no diagonal form or
commutative matrix model is imposed. -/
theorem projection_jump_stationary_positive_pair
    [Nonempty n] (P : Mat) (hP : P * P = P) (hPs : star P = P) :
    P.PosSemidef ∧ (1 - P).PosSemidef ∧
      schrodingerLindbladian 0 (fun _ : Unit => P) P = 0 ∧
      schrodingerLindbladian 0 (fun _ : Unit => P) (1 - P) = 0 ∧
      P ≠ 1 - P := by
  have hQ : (1 - P) * (1 - P) = 1 - P := by
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP]; noncomm_ring
  have hQs : star (1 - P) = 1 - P := by simp [hPs]
  have hpFactor : P = star P * P := by rw [hPs, hP]
  have hqFactor : 1 - P = star (1 - P) * (1 - P) := by rw [hQs, hQ]
  refine ⟨hpFactor ▸ Matrix.posSemidef_conjTranspose_mul_self P,
    hqFactor ▸ Matrix.posSemidef_conjTranspose_mul_self (1 - P), ?_, ?_, ?_⟩
  · simp [schrodingerLindbladian, hamiltonianTerm, schrodingerDissipator,
      schrodingerDissipatorTerm, hPs, hP]; module
  · have hPQ : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hP, sub_self]
    have hQP : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
    simp [schrodingerLindbladian, hamiltonianTerm, schrodingerDissipator,
      schrodingerDissipatorTerm, hPs, hP, hPQ, hQP]
  · intro hEq
    have hsum : P + P = 1 := by
      calc
        P + P = (1 - P) + P := congrArg (fun X : Mat => X + P) hEq
        _ = 1 := sub_add_cancel 1 P
    have hPone : P = 1 := by
      calc
        P = P * (P + P) := by rw [hsum, mul_one]
        _ = P * P + P * P := by rw [mul_add]
        _ = P + P := by rw [hP]
        _ = 1 := hsum
    have hone : (1 : Mat) = 0 := by
      apply add_left_cancel
      calc
        (1 : Mat) + 1 = P + P := by rw [hPone]
        _ = 1 := hsum
        _ = 1 + 0 := by simp
    exact one_ne_zero hone

/-- For a self-adjoint projection used as a single Schrödinger jump, the
generator kernel is exactly the commutant of that projection. The generator
is minus one half of the idempotent double commutator, and the latter detects
commutation in any characteristic. This statement concerns arbitrary
operators in the full finite matrix algebra; it assumes neither positivity
nor diagonal form. -/
theorem projection_jump_generator_kernel_iff_commutes
    (P X : Mat) (hP : P * P = P) (hPs : star P = P) :
    schrodingerLindbladian 0 (fun _ : Unit => P) X = 0 ↔ P * X = X * P := by
  have hPleft : P * (P * X) = P * X := by
    rw [← mul_assoc, hP]
  have hPright : X * P * P = X * P := by
    rw [mul_assoc, hP]
  have hfactor : schrodingerLindbladian 0 (fun _ : Unit => P) X =
      -(1 / 2 : ℂ) • (P * (P * X - X * P) - (P * X - X * P) * P) := by
    simp [schrodingerLindbladian, hamiltonianTerm, schrodingerDissipator,
      schrodingerDissipatorTerm, hPs, hP, hPleft, hPright, mul_assoc, mul_sub, sub_mul]
    module
  constructor
  · intro hzero
    have hdouble : P * (P * X - X * P) - (P * X - X * P) * P = 0 := by
      have hsmul : (-(1 / 2 : ℂ)) •
          (P * (P * X - X * P) - (P * X - X * P) * P) = 0 := by
        rw [← hfactor, hzero]
      rcases smul_eq_zero.mp hsmul with hscalar | hdouble
      · norm_num at hscalar
      · exact hdouble
    exact (InfoGeometry.Core.JordanAssociator.idempotent_double_commutator_zero_iff hP).mp hdouble
  · intro hcomm
    have hdouble : P * (P * X - X * P) - (P * X - X * P) * P = 0 := by
      exact (InfoGeometry.Core.JordanAssociator.idempotent_double_commutator_zero_iff hP).mpr hcomm
    rw [hfactor, hdouble]
    simp

/-- An operator annihilated by the concrete Schrödinger GKSL generator is
fixed by the full exponential flow. This transfers generator-level stationary
operators to actual stationary trajectories without a limiting argument. -/
theorem gkslFlow_fixed_of_generator_eq_zero
    (H X : Mat) {ι : Type*} [Fintype ι] (V : ι → Mat)
    (hX : schrodingerLindbladian H V X = 0) (t : ℝ) :
    gkslFlow H V t X = X := by
  change InfoGeometry.Lie.ContinuousDerivationExponential.flow
    (generatorEnd H V) t X = X
  apply InfoGeometry.Lie.ContinuousDerivationExponential.flow_apply_eq_self_of_apply_eq_zero
  change generatorCLM H V X = 0
  rw [generatorCLM_apply]
  exact hX

/-- A constant exponential orbit has zero GKSL generator at its initial point. -/
theorem generator_eq_zero_of_gkslFlow_fixed
    (H X : Mat) {ι : Type*} [Fintype ι] (V : ι → Mat)
    (hfix : ∀ t, gkslFlow H V t X = X) :
    schrodingerLindbladian H V X = 0 := by
  have hfun : (fun t : ℝ => gkslFlow H V t X) = fun _ => X := funext hfix
  have horbit := hasDerivAt_gkslFlow_orbit H V X 0
  rw [hfun] at horbit
  have hder := horbit.unique (hasDerivAt_const 0 X)
  simpa [gkslFlow, InfoGeometry.Lie.ContinuousDerivationExponential.flow_zero] using hder

/-- For a self-adjoint idempotent jump and zero Hamiltonian, the full fixed
operator space is exactly the commutant of the jump projection. -/
theorem projection_jump_flow_fixed_iff_commutes
    (P X : Mat) (hP : P * P = P) (hPs : star P = P) :
    (∀ t, gkslFlow 0 (fun _ : Unit => P) t X = X) ↔ P * X = X * P := by
  constructor
  · intro hfix
    apply (projection_jump_generator_kernel_iff_commutes P X hP hPs).mp
    exact generator_eq_zero_of_gkslFlow_fixed 0 X (fun _ : Unit => P) hfix
  · intro hcomm t
    exact gkslFlow_fixed_of_generator_eq_zero 0 X (fun _ : Unit => P)
      ((projection_jump_generator_kernel_iff_commutes P X hP hPs).mpr hcomm) t

/-- For a self-adjoint projection jump, the full Schrödinger generator is
minus one half of the component transverse to the two Peirce corners. This is
an identity on the full matrix carrier, with no diagonal-coordinate model. -/
theorem projection_jump_generator_eq_peirce_offDiagonal
    (P X : Mat) (hP : P * P = P) (hPs : star P = P) :
    schrodingerLindbladian 0 (fun _ : Unit => P) X =
      (-1 / 2 : ℂ) •
        (X - (P * X * P + (1 - P) * X * (1 - P))) := by
  have hPleft : P * (P * X) = P * X := by
    rw [← mul_assoc, hP]
  have hPright : X * P * P = X * P := by
    rw [mul_assoc, hP]
  have hfactor : schrodingerLindbladian 0 (fun _ : Unit => P) X =
      -(1 / 2 : ℂ) • (P * (P * X - X * P) - (P * X - X * P) * P) := by
    simp [schrodingerLindbladian, hamiltonianTerm, schrodingerDissipator,
      schrodingerDissipatorTerm, hPs, hP, hPleft, hPright, mul_assoc, mul_sub, sub_mul]
    module
  have hdouble : P * (P * X - X * P) - (P * X - X * P) * P =
      X - (P * X * P + (1 - P) * X * (1 - P)) := by
    calc
      P * (P * X - X * P) - (P * X - X * P) * P =
          (P * P) * X - P * X * P - P * X * P + X * (P * P) := by noncomm_ring
      _ = P * X - P * X * P - P * X * P + X * P := by rw [hP]
      _ = X - (P * X * P + (1 - P) * X * (1 - P)) := by noncomm_ring
  rw [hfactor, hdouble]
  norm_num

/-- The two-corner Peirce pinching associated with a projection. This map acts
on arbitrary operators by retaining both diagonal corners in the projection
decomposition; it is not a restriction to diagonal matrices. -/
def projectionJumpPeircePinching (P X : Mat) : Mat :=
  P * X * P + (1 - P) * X * (1 - P)

/-- The Peirce pinching is idempotent for an idempotent projection. -/
theorem projectionJumpPeircePinching_idempotent
    (P X : Mat) (hP : P * P = P) :
    projectionJumpPeircePinching P (projectionJumpPeircePinching P X) =
      projectionJumpPeircePinching P X := by
  have hQ : (1 - P) * (1 - P) = 1 - P := by
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hP]; noncomm_ring
  have hPQ : P * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hP, sub_self]
  have hQP : (1 - P) * P = 0 := by
    rw [sub_mul, one_mul, hP, sub_self]
  have hPPcorner : P * (P * X * P) * P = P * X * P := by
    calc
      P * (P * X * P) * P = (P * P) * X * (P * P) := by noncomm_ring
      _ = P * X * P := by rw [hP]
  have hPQcorner : P * ((1 - P) * X * (1 - P)) * P = 0 := by
    calc
      P * ((1 - P) * X * (1 - P)) * P =
          (P * (1 - P)) * X * ((1 - P) * P) := by noncomm_ring
      _ = 0 := by rw [hPQ, hQP]; simp
  have hQPcorner : (1 - P) * (P * X * P) * (1 - P) = 0 := by
    calc
      (1 - P) * (P * X * P) * (1 - P) =
          ((1 - P) * P) * X * (P * (1 - P)) := by noncomm_ring
      _ = 0 := by rw [hQP, hPQ]; simp
  have hQQcorner :
      (1 - P) * ((1 - P) * X * (1 - P)) * (1 - P) =
        (1 - P) * X * (1 - P) := by
    calc
      (1 - P) * ((1 - P) * X * (1 - P)) * (1 - P) =
          ((1 - P) * (1 - P)) * X * ((1 - P) * (1 - P)) := by noncomm_ring
      _ = (1 - P) * X * (1 - P) := by rw [hQ]
  simp only [projectionJumpPeircePinching, mul_add, add_mul]
  rw [hPPcorner, hPQcorner, hQPcorner, hQQcorner]
  simp

/-- The Peirce pinching commutes with the projection that defines its two
corners, so it lies in the fixed algebra of the projection-jump generator. -/
theorem projectionJumpPeircePinching_commutes
    (P X : Mat) (hP : P * P = P) :
    P * projectionJumpPeircePinching P X =
      projectionJumpPeircePinching P X * P := by
  have hPQ : P * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hP, sub_self]
  have hQP : (1 - P) * P = 0 := by
    rw [sub_mul, one_mul, hP, sub_self]
  have hleft : P * projectionJumpPeircePinching P X = P * X * P := by
    unfold projectionJumpPeircePinching
    rw [mul_add]
    calc
      P * (P * X * P) + P * ((1 - P) * X * (1 - P)) =
          (P * P) * X * P + (P * (1 - P)) * X * (1 - P) := by noncomm_ring
      _ = P * X * P := by rw [hP, hPQ]; simp
  have hright : projectionJumpPeircePinching P X * P = P * X * P := by
    unfold projectionJumpPeircePinching
    rw [add_mul]
    calc
      (P * X * P) * P + ((1 - P) * X * (1 - P)) * P =
          P * X * (P * P) + (1 - P) * X * ((1 - P) * P) := by noncomm_ring
      _ = P * X * P := by rw [hP, hQP]; simp
  exact hleft.trans hright.symm

/-- The projection-jump orbit has an explicit two-rate decomposition: its
Peirce-diagonal component is fixed and its off-diagonal component decays at
rate `1/2`. This formula acts on arbitrary complex matrices. -/
theorem projection_jump_gkslFlow_eq_peirce_relaxation
    (P X : Mat) (hP : P * P = P) (hPs : star P = P) (t : ℝ) :
    gkslFlow 0 (fun _ : Unit => P) t X =
      projectionJumpPeircePinching P X +
        (Real.exp (-t / 2) : ℝ) •
          (X - projectionJumpPeircePinching P X) := by
  let A : Mat := projectionJumpPeircePinching P X
  let B : Mat := X - A
  have hAcomm : P * A = A * P := by
    exact projectionJumpPeircePinching_commutes P X hP
  have hAgen : schrodingerLindbladian 0 (fun _ : Unit => P) A = 0 := by
    exact (projection_jump_generator_kernel_iff_commutes P A hP hPs).mpr hAcomm
  have hXgen : schrodingerLindbladian 0 (fun _ : Unit => P) X =
      (-1 / 2 : ℂ) • B := by
    simpa [A, B, projectionJumpPeircePinching] using
      projection_jump_generator_eq_peirce_offDiagonal P X hP hPs
  have hBgen : schrodingerLindbladian 0 (fun _ : Unit => P) B =
      (-1 / 2 : ℂ) • B := by
    have hsub : generatorCLM 0 (fun _ : Unit => P) (X - A) =
        generatorCLM 0 (fun _ : Unit => P) X - generatorCLM 0 (fun _ : Unit => P) A :=
      map_sub (generatorCLM 0 (fun _ : Unit => P)) X A
    rw [← generatorCLM_apply 0 B (fun _ : Unit => P)]
    change generatorCLM 0 (fun _ : Unit => P) (X - A) = _
    rw [hsub,
      generatorCLM_apply 0 X (fun _ : Unit => P),
      generatorCLM_apply 0 A (fun _ : Unit => P), hXgen, hAgen]
    simp
  let f : ℝ → Mat := fun s => A + (Real.exp (-s / 2) : ℝ) • B
  have hf : ∀ s, HasDerivAt f
      (schrodingerLindbladian 0 (fun _ : Unit => P) (f s)) s := by
    intro s
    have harg : HasDerivAt (fun x : ℝ => -x / 2) (-1 / 2) s := by
      convert (hasDerivAt_id s).neg.div_const 2 using 1
      norm_num
    have hexp : HasDerivAt (fun x : ℝ => Real.exp (-x / 2))
        (Real.exp (-s / 2) * (-1 / 2)) s := by
      convert (Real.hasDerivAt_exp (-s / 2)).comp s harg using 1
      rfl
    have hderiv0 := (hasDerivAt_const s A).add (hexp.smul_const B)
    have hderiv : HasDerivAt f (((-1 / 2 : ℝ) * Real.exp (-s / 2)) • B) s := by
      convert hderiv0 using 1
      simp [mul_comm]
    have hgenA : generatorEnd 0 (fun _ : Unit => P) A = 0 := by
      simpa [generatorEnd] using hAgen
    have hgenB : generatorEnd 0 (fun _ : Unit => P) B =
        (-1 / 2 : ℝ) • B := by
      change generatorCLM 0 (fun _ : Unit => P) B = _
      rw [generatorCLM_apply]
      rw [← algebraMap_smul (A := ℂ) (-1 / 2 : ℝ) B]
      norm_num at hBgen ⊢
      exact hBgen
    have hgenEnd := map_add (generatorEnd 0 (fun _ : Unit => P)) A
      ((Real.exp (-s / 2) : ℝ) • B)
    rw [hgenA, map_smul, hgenB, smul_smul] at hgenEnd
    have hgen : schrodingerLindbladian 0 (fun _ : Unit => P) (f s) =
        (Real.exp (-s / 2) * (-1 / 2)) • B := by
      simpa [f, generatorEnd, generatorCLM_apply, smul_smul, mul_comm] using hgenEnd
    convert hderiv using 1
    rw [hgen]
    ring
  have hzero : f 0 = X := by
    simp [f, A, B, projectionJumpPeircePinching]
  have huniq := gkslFlow_unique_of_ode 0 (fun _ : Unit => P) X f hf hzero
  have hfun := congrFun huniq t
  simpa [f, A, B] using hfun.symm

/-- Every full-matrix projection-jump orbit converges to its two-corner
Peirce pinching in the operator norm topology. -/
theorem projection_jump_gkslFlow_tendsto_peircePinching
    (P X : Mat) (hP : P * P = P) (hPs : star P = P) :
    Tendsto (fun t : ℝ => gkslFlow 0 (fun _ : Unit => P) t X)
      atTop (𝓝 (projectionJumpPeircePinching P X)) := by
  rw [show (fun t : ℝ => gkslFlow 0 (fun _ : Unit => P) t X) =
      (fun t => projectionJumpPeircePinching P X +
        (Real.exp (-t / 2) : ℝ) •
          (X - projectionJumpPeircePinching P X)) by
    funext t
    exact projection_jump_gkslFlow_eq_peirce_relaxation P X hP hPs t]
  have hlin : Tendsto (fun t : ℝ => -t / 2) atTop atBot := by
    simpa using ((tendsto_neg_atTop_atBot.comp tendsto_id).atBot_div_const
      (by norm_num : (0 : ℝ) < 2))
  have hexp : Tendsto (fun t : ℝ => Real.exp (-t / 2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  have hsmul : Tendsto (fun t : ℝ => (Real.exp (-t / 2) : ℝ) •
      (X - projectionJumpPeircePinching P X)) atTop (𝓝 0) := by
    simpa using hexp.smul_const (X - projectionJumpPeircePinching P X)
  simpa using tendsto_const_nhds.add hsmul

/-- The Peirce pinching as a continuous real-linear map on the full complex
matrix algebra. The two-sided matrix multiplications retain the operator
ordering; scalar restriction only records the real time parameter space. -/
def projectionJumpPeircePinchingCLM (P : Mat) : Mat →L[ℝ] Mat :=
  (((InfoGeometry.Modular.SchrodingerGKSLFlowBridge.leftMul P).comp
      (InfoGeometry.Modular.SchrodingerGKSLFlowBridge.rightMul P)) +
    ((InfoGeometry.Modular.SchrodingerGKSLFlowBridge.leftMul (1 - P)).comp
      (InfoGeometry.Modular.SchrodingerGKSLFlowBridge.rightMul (1 - P)))).restrictScalars ℝ

@[simp] theorem projectionJumpPeircePinchingCLM_apply (P X : Mat) :
    projectionJumpPeircePinchingCLM P X = projectionJumpPeircePinching P X := by
  simp [projectionJumpPeircePinchingCLM, projectionJumpPeircePinching,
    InfoGeometry.Modular.SchrodingerGKSLFlowBridge.leftMul,
    InfoGeometry.Modular.SchrodingerGKSLFlowBridge.rightMul]
  noncomm_ring

/-- The projection-jump exponential converges as a continuous linear map,
not merely pointwise on each initial operator. Since this is the operator-norm
topology on the finite-dimensional matrix space, it gives uniform convergence
on bounded sets of full matrix inputs. -/
theorem projection_jump_gkslFlow_tendsto_peircePinchingCLM
    (P : Mat) (hP : P * P = P) (hPs : star P = P) :
    Tendsto (fun t : ℝ => gkslFlow 0 (fun _ : Unit => P) t) atTop
      (𝓝 (projectionJumpPeircePinchingCLM P)) := by
  rw [show (fun t : ℝ => gkslFlow 0 (fun _ : Unit => P) t) =
      (fun t => projectionJumpPeircePinchingCLM P +
        (Real.exp (-t / 2) : ℝ) •
          ((ContinuousLinearMap.id ℝ Mat) - projectionJumpPeircePinchingCLM P)) by
    funext t
    apply ContinuousLinearMap.ext
    intro X
    simp only [_root_.add_apply, _root_.smul_apply,
      _root_.sub_apply, ContinuousLinearMap.id_apply,
      projectionJumpPeircePinchingCLM_apply]
    exact projection_jump_gkslFlow_eq_peirce_relaxation P X hP hPs t]
  have hlin : Tendsto (fun t : ℝ => -t / 2) atTop atBot := by
    simpa using ((tendsto_neg_atTop_atBot.comp tendsto_id).atBot_div_const
      (by norm_num : (0 : ℝ) < 2))
  have hexp : Tendsto (fun t : ℝ => Real.exp (-t / 2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  have hsmul : Tendsto (fun t : ℝ => (Real.exp (-t / 2) : ℝ) •
      ((ContinuousLinearMap.id ℝ Mat) - projectionJumpPeircePinchingCLM P))
      atTop (𝓝 0) := by
    have h := hexp.smul_const
      ((ContinuousLinearMap.id ℝ Mat) - projectionJumpPeircePinchingCLM P)
    rw [zero_smul ℝ
      ((ContinuousLinearMap.id ℝ Mat) - projectionJumpPeircePinchingCLM P)] at h
    exact h
  simpa using tendsto_const_nhds.add hsmul

/-- A projection jump therefore has two distinct positive operators fixed by
the entire exponential Schrödinger flow. This is an explicit finite-matrix
NESS nonuniqueness witness at the positive-operator level; trace-one
normalization is intentionally not asserted here. -/
theorem projection_jump_has_distinct_stationary_operators
    [Nonempty n] (P : Mat) (hP : P * P = P) (hPs : star P = P) :
    P.PosSemidef ∧ (1 - P).PosSemidef ∧
      (∀ t, gkslFlow 0 (fun _ : Unit => P) t P = P) ∧
      (∀ t, gkslFlow 0 (fun _ : Unit => P) t (1 - P) = 1 - P) ∧
      P ≠ 1 - P := by
  have h := projection_jump_stationary_positive_pair P hP hPs
  refine ⟨h.1, h.2.1, ?_, ?_, h.2.2.2.2⟩
  · intro t
    exact gkslFlow_fixed_of_generator_eq_zero 0 P (fun _ : Unit => P)
      h.2.2.1 t
  · intro t
    exact gkslFlow_fixed_of_generator_eq_zero 0 (1 - P) (fun _ : Unit => P)
      h.2.2.2.1 t

omit [DecidableEq n] in
/-- The real part of the trace of a nonzero positive semidefinite complex
matrix is strictly positive. -/
private theorem trace_re_pos_of_posSemidef_ne_zero
    (A : Mat) (hA : A.PosSemidef) (hA0 : A ≠ 0) :
    0 < (Matrix.trace A).re := by
  have htr_nonneg : 0 ≤ Matrix.trace A := hA.trace_nonneg
  have htr_zero : Matrix.trace A ≠ 0 := by
    intro h
    exact hA0 ((Matrix.PosSemidef.trace_eq_zero_iff hA).mp h)
  have htr_star : star (Matrix.trace A) = Matrix.trace A := by
    calc
      star (Matrix.trace A) = Matrix.trace (star A) := by
        rw [← Matrix.trace_conjTranspose, star_eq_conjTranspose]
      _ = Matrix.trace A := congrArg Matrix.trace hA.isHermitian.eq
  have him : (Matrix.trace A).im = 0 := by
    have h := congrArg Complex.im htr_star
    have h' : -(Matrix.trace A).im = (Matrix.trace A).im := by
      simpa [Complex.star_def, Complex.conj_im] using h
    linarith
  have hre_nonneg : 0 ≤ (Matrix.trace A).re :=
    (Complex.nonneg_iff.mp htr_nonneg).1
  have hre_ne : (Matrix.trace A).re ≠ 0 := by
    intro hre
    apply htr_zero
    exact Complex.ext hre him
  exact lt_of_le_of_ne hre_nonneg (Ne.symm hre_ne)

omit [DecidableEq n] in
/-- Normalize a nonzero positive matrix by the real part of its trace. -/
private def normalizedPositiveMatrix (A : Mat) : Mat :=
  ((Matrix.trace A).re)⁻¹ • A

omit [DecidableEq n] in
private theorem normalizedPositiveMatrix_pos
    (A : Mat) (hA : A.PosSemidef) (hA0 : A ≠ 0) :
    (normalizedPositiveMatrix A).PosSemidef := by
  unfold normalizedPositiveMatrix
  exact Matrix.PosSemidef.smul hA
    (le_of_lt (inv_pos.mpr (trace_re_pos_of_posSemidef_ne_zero A hA hA0)))

omit [DecidableEq n] in
private theorem normalizedPositiveMatrix_trace
    (A : Mat) (hA : A.PosSemidef) (hA0 : A ≠ 0) :
    Matrix.trace (normalizedPositiveMatrix A) = 1 := by
  have hr := trace_re_pos_of_posSemidef_ne_zero A hA hA0
  have him : (Matrix.trace A).im = 0 := by
    have htr_star : star (Matrix.trace A) = Matrix.trace A := by
      calc
        star (Matrix.trace A) = Matrix.trace (star A) := by
          rw [← Matrix.trace_conjTranspose, star_eq_conjTranspose]
        _ = Matrix.trace A := congrArg Matrix.trace hA.isHermitian.eq
    have h := congrArg Complex.im htr_star
    have h' : -(Matrix.trace A).im = (Matrix.trace A).im := by
      simpa [Complex.star_def, Complex.conj_im] using h
    linarith
  have htrace : Matrix.trace A = ((Matrix.trace A).re : ℂ) :=
    Complex.ext rfl him
  unfold normalizedPositiveMatrix
  rw [Matrix.trace_smul, htrace]
  have hmul : ((Matrix.trace A).re)⁻¹ * (Matrix.trace A).re = 1 :=
    inv_mul_cancel₀ hr.ne'
  simpa [smul_eq_mul] using congrArg (fun x : ℝ => (x : ℂ)) hmul

/-- A self-adjoint projection jump has two distinct trace-one positive
stationary states, namely the normalized range and kernel projections. The
flow fixes both for every real time. The carrier remains the full finite
matrix algebra `Matrix n n ℂ`; no diagonalization or commutativity assumption
is made. -/
theorem projection_jump_has_distinct_stationary_density_matrices
    [Nonempty n] (P : Mat) (hP : P * P = P) (hPs : star P = P)
    (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    let ρ₁ := normalizedPositiveMatrix P
    let ρ₀ := normalizedPositiveMatrix (1 - P)
    ρ₁.PosSemidef ∧ ρ₀.PosSemidef ∧
      Matrix.trace ρ₁ = 1 ∧ Matrix.trace ρ₀ = 1 ∧
      (∀ t, gkslFlow 0 (fun _ : Unit => P) t ρ₁ = ρ₁) ∧
      (∀ t, gkslFlow 0 (fun _ : Unit => P) t ρ₀ = ρ₀) ∧ ρ₁ ≠ ρ₀ := by
  dsimp only
  have hpair := projection_jump_stationary_positive_pair P hP hPs
  have hQ0 : 1 - P ≠ 0 := by
    intro hz
    exact hP1 (sub_eq_zero.mp hz).symm
  have hpos₁ := normalizedPositiveMatrix_pos P hpair.1 hP0
  have hpos₀ := normalizedPositiveMatrix_pos (1 - P) hpair.2.1 hQ0
  have htr₁ := normalizedPositiveMatrix_trace P hpair.1 hP0
  have htr₀ := normalizedPositiveMatrix_trace (1 - P) hpair.2.1 hQ0
  have hfix₁ : ∀ t, gkslFlow 0 (fun _ : Unit => P) t
      (normalizedPositiveMatrix P) = normalizedPositiveMatrix P := by
    intro t
    rw [show normalizedPositiveMatrix P =
      ((Matrix.trace P).re)⁻¹ • P by rfl]
    rw [map_smul, gkslFlow_fixed_of_generator_eq_zero 0 P
      (fun _ : Unit => P) hpair.2.2.1 t]
  have hfix₀ : ∀ t, gkslFlow 0 (fun _ : Unit => P) t
      (normalizedPositiveMatrix (1 - P)) = normalizedPositiveMatrix (1 - P) := by
    intro t
    rw [show normalizedPositiveMatrix (1 - P) =
      ((Matrix.trace (1 - P)).re)⁻¹ • (1 - P) by rfl]
    rw [map_smul, gkslFlow_fixed_of_generator_eq_zero 0 (1 - P)
      (fun _ : Unit => P) hpair.2.2.2.1 t]
  have hPQ : P * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hP, sub_self]
  have hread₁ : (Matrix.trace (P * normalizedPositiveMatrix P)).re = 1 := by
    have hmul : P * normalizedPositiveMatrix P = normalizedPositiveMatrix P := by
      unfold normalizedPositiveMatrix
      rw [Matrix.mul_smul, hP]
    rw [hmul, htr₁]
    rfl
  have hread₀ : (Matrix.trace (P * normalizedPositiveMatrix (1 - P))).re = 0 := by
    rw [show P * normalizedPositiveMatrix (1 - P) = 0 by
      unfold normalizedPositiveMatrix
      rw [Matrix.mul_smul, hPQ, smul_zero], Matrix.trace_zero]
    rfl
  have hne : normalizedPositiveMatrix P ≠ normalizedPositiveMatrix (1 - P) := by
    intro heq
    have hread_eq := congrArg (fun X : Mat => (Matrix.trace (P * X)).re) heq
    exact one_ne_zero (hread₁.symm.trans (hread_eq.trans hread₀))
  exact ⟨hpos₁, hpos₀, htr₁, htr₀, hfix₁, hfix₀, hne⟩

/-- The two normalized stationary states of a projection jump generate a
trace-one positive segment of stationary matrices.  The conserved projection
readout recovers the segment parameter, so this parametrization is injective.
The ambient carrier is still the full matrix algebra; no diagonal form is
chosen for `P` or for the states. -/
theorem projection_jump_stationary_density_segment
    [Nonempty n] (P : Mat) (hP : P * P = P) (hPs : star P = P)
    (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    let ρ₁ := normalizedPositiveMatrix P
    let ρ₀ := normalizedPositiveMatrix (1 - P)
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      let ρs := s • ρ₁ + (1 - s) • ρ₀
      ρs.PosSemidef ∧ Matrix.trace ρs = 1 ∧
        (∀ t, gkslFlow 0 (fun _ : Unit => P) t ρs = ρs) ∧
        (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
          (s • ρ₁ + (1 - s) • ρ₀ = u • ρ₁ + (1 - u) • ρ₀) → s = u) := by
  dsimp only
  have hpair := projection_jump_has_distinct_stationary_density_matrices
    P hP hPs hP0 hP1
  rcases hpair with ⟨hpos₁, hpos₀, htr₁, htr₀, hfix₁, hfix₀, _hne⟩
  intro s hs0 hs1
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Matrix.PosSemidef.add
    · exact Matrix.PosSemidef.smul hpos₁ hs0
    · have hs_complement : 0 ≤ 1 - s := sub_nonneg.mpr hs1
      exact Matrix.PosSemidef.smul hpos₀ hs_complement
  · rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, htr₁, htr₀]
    simp
  · intro t
    rw [map_add, map_smul, map_smul, hfix₁ t, hfix₀ t]
  · intro u hu0 hu1 h_eq
    have hread (x : ℝ) :
        (Matrix.trace (P * (x • normalizedPositiveMatrix P +
          (1 - x) • normalizedPositiveMatrix (1 - P)))).re = x := by
      have hPP : P * normalizedPositiveMatrix P = normalizedPositiveMatrix P := by
        unfold normalizedPositiveMatrix
        rw [Matrix.mul_smul, hP]
      have hPcomp : P * normalizedPositiveMatrix (1 - P) = 0 := by
        have hPc : P * (1 - P) = 0 := by
          rw [mul_sub, mul_one, hP, sub_self]
        unfold normalizedPositiveMatrix
        rw [Matrix.mul_smul, hPc, smul_zero]
      rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, hPP, hPcomp,
        Matrix.trace_add, Matrix.trace_smul, htr₁]
      simp
    have hread_eq := congrArg (fun X : Mat => (Matrix.trace (P * X)).re) h_eq
    rw [hread s, hread u] at hread_eq
    exact hread_eq

set_option maxHeartbeats 1000000 in
/-- A stationary positive matrix splits into two stationary density matrices
whenever the generator is bimodular over an orthogonal projection and its
complement.  The two corner traces are explicit hypotheses: the theorem does
not silently infer faithfulness or positivity of either corner.  This is the
linear operator-algebra step needed before applying a separate GKSL
commutant-to-bimodularity argument. -/
theorem bimodular_generator_splits_stationary_density
    (L : Mat →ₗ[ℝ] Mat) (ρ Q : Mat)
    (hρpos : ρ.PosSemidef)
    (hρstat : L ρ = 0)
    (hQidem : Q * Q = Q) (hQstar : star Q = Q)
    (hQcorner : ∀ X, L (Q * X * Q) = Q * L X * Q)
    (hQcompcorner : ∀ X,
      L ((1 - Q) * X * (1 - Q)) = (1 - Q) * L X * (1 - Q))
    (hQweight : 0 < (Matrix.trace (Q * ρ * Q)).re)
    (hQcompweight : 0 < (Matrix.trace ((1 - Q) * ρ * (1 - Q))).re) :
    let ρQ := normalizedPositiveMatrix (Q * ρ * Q)
    let ρQc := normalizedPositiveMatrix ((1 - Q) * ρ * (1 - Q))
    ρQ.PosSemidef ∧ ρQc.PosSemidef ∧
      Matrix.trace ρQ = 1 ∧ Matrix.trace ρQc = 1 ∧
      L ρQ = 0 ∧ L ρQc = 0 ∧ ρQ ≠ ρQc := by
  dsimp only
  let A := Q * ρ * Q
  let C := (1 - Q) * ρ * (1 - Q)
  have hQcstar : star (1 - Q) = 1 - Q := by simp [hQstar]
  have hQct : Qᴴ = Q := by rw [← Matrix.star_eq_conjTranspose, hQstar]
  have hQcct : (1 - Q)ᴴ = 1 - Q := by
    rw [← Matrix.star_eq_conjTranspose, hQcstar]
  have hApos : A.PosSemidef := by
    dsimp [A]
    simpa only [hQct] using hρpos.mul_mul_conjTranspose_same Q
  have hCpos : C.PosSemidef := by
    dsimp [C]
    have h := hρpos.mul_mul_conjTranspose_same (1 - Q)
    rw [hQcct] at h
    exact h
  have hA0 : A ≠ 0 := by
    intro hz
    have htr := congrArg (fun X : Mat => (Matrix.trace X).re) hz
    have : (Matrix.trace A).re = 0 := by simpa using htr
    exact (ne_of_gt hQweight) (by simpa [A] using this)
  have hC0 : C ≠ 0 := by
    intro hz
    have htr := congrArg (fun X : Mat => (Matrix.trace X).re) hz
    have : (Matrix.trace C).re = 0 := by simpa using htr
    exact (ne_of_gt hQcompweight) (by simpa [C] using this)
  have hAQ : L A = 0 := by
    dsimp [A]
    rw [hQcorner ρ, hρstat]
    simp
  have hCQ : L C = 0 := by
    dsimp [C]
    rw [hQcompcorner ρ, hρstat]
    simp
  let ρQ := normalizedPositiveMatrix A
  let ρQc := normalizedPositiveMatrix C
  have hρQpos := normalizedPositiveMatrix_pos A hApos hA0
  have hρQcpos := normalizedPositiveMatrix_pos C hCpos hC0
  have hρQtr := normalizedPositiveMatrix_trace A hApos hA0
  have hρQctr := normalizedPositiveMatrix_trace C hCpos hC0
  have hρQstat : L ρQ = 0 := by
    dsimp [ρQ]
    rw [show normalizedPositiveMatrix A =
      ((Matrix.trace A).re)⁻¹ • A by rfl, L.map_smul, hAQ, smul_zero]
  have hρQcstat : L ρQc = 0 := by
    dsimp [ρQc]
    rw [show normalizedPositiveMatrix C =
      ((Matrix.trace C).re)⁻¹ • C by rfl, L.map_smul, hCQ, smul_zero]
  have hQmulA : Q * A = A := by
    dsimp [A]
    calc Q * (Q * ρ * Q) = (Q * Q) * ρ * Q := by noncomm_ring
      _ = Q * ρ * Q := by rw [hQidem]
  have hQmulC : Q * C = 0 := by
    have hQcomp : Q * (1 - Q) = 0 := by
      rw [mul_sub, mul_one, hQidem, sub_self]
    dsimp [C]
    calc Q * ((1 - Q) * ρ * (1 - Q)) = (Q * (1 - Q)) * ρ * (1 - Q) := by noncomm_ring
      _ = 0 := by rw [hQcomp]; noncomm_ring
  have hreadQ : (Matrix.trace (Q * ρQ)).re = 1 := by
    have hmul : Q * ρQ = ρQ := by
      dsimp [ρQ]
      unfold normalizedPositiveMatrix
      rw [Matrix.mul_smul, hQmulA]
    rw [hmul, hρQtr]
    rfl
  have hreadQc : (Matrix.trace (Q * ρQc)).re = 0 := by
    have hmul : Q * ρQc = 0 := by
      dsimp [ρQc]
      unfold normalizedPositiveMatrix
      rw [Matrix.mul_smul, hQmulC, smul_zero]
    rw [hmul, Matrix.trace_zero]
    rfl
  have hne : ρQ ≠ ρQc := by
    intro heq
    have hread := congrArg (fun X : Mat => (Matrix.trace (Q * X)).re) heq
    exact one_ne_zero (hreadQ.symm.trans (hread.trans hreadQc))
  exact ⟨hρQpos, hρQcpos, hρQtr, hρQctr, hρQstat, hρQcstat, hne⟩

end InfoGeometry.Modular.CommutantInvariantGKSLFlow

end noncomputable section
