import Mathlib.Analysis.InnerProductSpace.GramMatrix
import InfoGeometry.OperatorAlgebra.OperatorThermodynamics
import InfoGeometry.External.Virasoro.FockSpace

/-!
# Stable Vacuum Layers

This module formalizes the corrected separation of vacuum stability layers.

The point of the file is deliberately narrow:

* spectral stability is a ground-state statement for a physical Hamiltonian;
* KMS/passive stability is an equilibrium statement for a modular or thermal flow;
* deformation stability is a positive semidefinite Gram/Fisher metric statement.

The three objects are compatible, but they are not identified.  In particular,
the Kähler potential, modular Hamiltonian, and physical Hamiltonian remain
separate pieces of data.
-/

noncomputable section

namespace InfoGeometry.Canonical.StableVacuum

open scoped BigOperators

/-! ## Spectral ground-state layer -/

/--
A quadratic-form nonnegative Hamiltonian has no nonzero negative-energy
eigenvectors.

This is the finite Hilbert-space proof kernel behind the usual spectral
stability statement: if `H v = lambda • v` with `lambda < 0`, then positivity
of `⟪v, H v⟫` forces `v = 0`.
-/
theorem eigenvector_eq_zero_of_negative_energy_of_quadratic_nonnegative
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (H : V →ₗ[ℝ] V)
    (hpos : ∀ v : V, 0 ≤ inner ℝ v (H v))
    {v : V} {lambda : ℝ}
    (hneg : lambda < 0)
    (heig : H v = lambda • v) :
    v = 0 := by
  have hnonneg : 0 ≤ inner ℝ v (H v) := hpos v
  rw [heig] at hnonneg
  have hinner_nonneg : 0 ≤ inner ℝ v v := by
    exact inner_self_nonneg (𝕜 := ℝ) (x := v)
  have hle : inner ℝ v v ≤ 0 := by
    by_contra hnot
    have hposinner : 0 < inner ℝ v v := lt_of_not_ge hnot
    have hprodneg : lambda * inner ℝ v v < 0 :=
      mul_neg_of_neg_of_pos hneg hposinner
    rw [real_inner_smul_right] at hnonneg
    linarith
  have hinner_zero : inner ℝ v v = 0 := le_antisymm hle hinner_nonneg
  exact inner_self_eq_zero.mp hinner_zero

/--
A spectral ground-state packet for a physical Hamiltonian.

The field `energy_nonnegative` is the concrete quadratic-form positivity
condition used below.  The no-negative-eigenvectors statement is derived from
that positivity theorem, not stored as a separate property socket.
-/
structure SpectralGroundState
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  /-- Physical Hamiltonian. -/
  H : V →ₗ[ℝ] V

  /-- Vacuum vector. -/
  Omega : V

  /-- Unit normalization of the vacuum in the ambient real Hilbert space. -/
  normalized :
    inner ℝ Omega Omega = 1

  /-- The vacuum lies in the bottom eigenspace. -/
  ground :
    H Omega = 0

  /-- Quadratic-form nonnegativity of the physical Hamiltonian. -/
  energy_nonnegative :
    ∀ v : V, 0 ≤ inner ℝ v (H v)

namespace SpectralGroundState

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable (S : SpectralGroundState V)

/-- The vacuum has unit Hilbert norm, expressed by its inner-product square. -/
theorem omega_normalized :
    inner ℝ S.Omega S.Omega = 1 :=
  S.normalized

/-- The ground-state subspace is the kernel of the physical Hamiltonian. -/
def groundSubspace : Submodule ℝ V :=
  LinearMap.ker S.H

/-- The vacuum belongs to the ground-state subspace. -/
theorem omega_mem_groundSubspace :
    S.Omega ∈ S.groundSubspace :=
  S.ground

/-- Re-export of physical Hamiltonian positivity. -/
theorem hamiltonian_quadratic_nonnegative
    (v : V) :
    0 ≤ inner ℝ v (S.H v) :=
  S.energy_nonnegative v

/--
There are no negative-energy eigenvectors for a positive spectral ground-state
packet.  This is proved from `energy_nonnegative`.
-/
theorem no_negative_eigenvectors
    {v : V} {lambda : ℝ}
    (hneg : lambda < 0)
    (heig : S.H v = lambda • v) :
    v = 0 :=
  eigenvector_eq_zero_of_negative_energy_of_quadratic_nonnegative
    S.H S.energy_nonnegative hneg heig

/--
An operator mode with a definite energy shift on the vacuum.

If `lambda < 0`, this is an energy-lowering mode at the vacuum.
-/
structure EnergyMode where
  /-- Mode operator. -/
  A : V →ₗ[ℝ] V

  /-- Energy shift/eigenvalue on the state `A Omega`. -/
  lambda : ℝ

  /-- The shifted vacuum vector is a Hamiltonian eigenvector. -/
  eigen_on_ground :
    S.H (A S.Omega) = lambda • A S.Omega

namespace EnergyMode

variable {S}
variable (M : S.EnergyMode)

/--
Energy-lowering modes annihilate a stable vacuum.

This is the algebraic content of the physical statement: if `A Omega` had a
negative energy eigenvalue, it would contradict the spectral lower bound.
-/
theorem annihilates_ground_of_negative_energy
    (hneg : M.lambda < 0) :
    M.A S.Omega = 0 :=
  S.no_negative_eigenvectors hneg M.eigen_on_ground

end EnergyMode

/-- Uniqueness of the ground state is an extra condition, not part of stability itself. -/
def GroundStateUnique : Prop :=
  ∀ v : V, S.H v = 0 → ∃ c : ℝ, v = c • S.Omega

/-- A ground vector is a scalar multiple of the vacuum under the uniqueness property. -/
theorem ground_vector_eq_smul_vacuum
    (U : S.GroundStateUnique)
    {v : V}
    (hv : S.H v = 0) :
    ∃ c : ℝ, v = c • S.Omega :=
  U v hv

end SpectralGroundState

/-! ## Highest-weight Fock specialization -/

/--
In the charged Heisenberg Fock representation, positive Heisenberg modes
annihilate the highest-weight vacuum.

With the usual physics convention these are the lowering operators for the
chosen energy polarization.
-/
theorem chargedFock_vacuum_annihilated_by_lowering_modes
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (alpha : 𝕜)
    {k : ℤ}
    (hk : 0 < k) :
    ιUEA 𝕜 (VirasoroProject.HeisenbergAlgebra.jgen 𝕜 k) •
        VirasoroProject.ChargedFockSpace.vacuum 𝕜 alpha = 0 :=
  VirasoroProject.ChargedFockSpace.jgen_pos_vacuum 𝕜 alpha hk

/-! ## Zero excitation volume versus geometric volume -/

/--
Finite positive-weight excitation volume at the scalar expectation level.

This is the readout shadow of a Fock expression `V = sum_i v_i N_i`.  Positivity
is proved below from positive weights and nonnegative occupation readouts.
-/
def finiteExcitationVolumeExpectation
    {Index : Type*} [Fintype Index]
    (weight occupationExpectation : Index → ℝ) : ℝ :=
  ∑ i, weight i * occupationExpectation i

/--
Positive weights and nonnegative occupation readouts give nonnegative
excitation volume expectation.
-/
theorem finiteExcitationVolumeExpectation_nonnegative
    {Index : Type*} [Fintype Index]
    {weight occupationExpectation : Index → ℝ}
    (hweight : ∀ i, 0 < weight i)
    (hocc : ∀ i, 0 ≤ occupationExpectation i) :
    0 ≤ finiteExcitationVolumeExpectation weight occupationExpectation := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (le_of_lt (hweight i)) (hocc i)

/--
If every occupation readout vanishes on the vacuum, the finite excitation-volume
expectation vanishes.
-/
theorem finiteExcitationVolumeExpectation_eq_zero_of_vacuum
    {Index : Type*} [Fintype Index]
    (weight occupationExpectation : Index → ℝ)
    (hocc : ∀ i, occupationExpectation i = 0) :
    finiteExcitationVolumeExpectation weight occupationExpectation = 0 := by
  simp [finiteExcitationVolumeExpectation, hocc]

/--
With positive weights and nonnegative occupation readouts, zero excitation
volume is equivalent to zero occupation in every mode.
-/
theorem finiteExcitationVolumeExpectation_eq_zero_iff_of_nonnegative
    {Index : Type*} [Fintype Index]
    {weight occupationExpectation : Index → ℝ}
    (hweight : ∀ i, 0 < weight i)
    (hocc : ∀ i, 0 ≤ occupationExpectation i) :
    finiteExcitationVolumeExpectation weight occupationExpectation = 0 ↔
      ∀ i, occupationExpectation i = 0 := by
  constructor
  · intro h i
    have hsum : ∑ j, weight j * occupationExpectation j = 0 := by
      simpa [finiteExcitationVolumeExpectation] using h
    have hterm : weight i * occupationExpectation i = 0 := by
      exact
        (Finset.sum_eq_zero_iff_of_nonneg
          (s := Finset.univ)
          (f := fun j => weight j * occupationExpectation j)
          (fun j _ => mul_nonneg (le_of_lt (hweight j)) (hocc j))).mp hsum
          i (Finset.mem_univ i)
    exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hweight i))
  · intro h
    exact finiteExcitationVolumeExpectation_eq_zero_of_vacuum weight occupationExpectation h

/--
Finite positive-weight excitation-volume operator on an abstract real Fock
space.  This is an excitation-content operator, not a geometric volume form.
-/
def finiteExcitationVolume
    {Index Fock : Type*}
    [Fintype Index] [AddCommGroup Fock] [Module ℝ Fock]
    (weight : Index → ℝ)
    (occupation : Index → Fock →ₗ[ℝ] Fock) :
    Fock →ₗ[ℝ] Fock :=
  ∑ i, weight i • occupation i

/--
If every occupation operator annihilates the vacuum, then the finite
excitation-volume operator annihilates the vacuum.
-/
theorem finiteExcitationVolume_apply_vacuum
    {Index Fock : Type*}
    [Fintype Index] [AddCommGroup Fock] [Module ℝ Fock]
    (weight : Index → ℝ)
    (occupation : Index → Fock →ₗ[ℝ] Fock)
    {Omega : Fock}
    (hocc : ∀ i, occupation i Omega = 0) :
    finiteExcitationVolume weight occupation Omega = 0 := by
  simp [finiteExcitationVolume, hocc]

/--
The same zero-excitation-volume statement after applying any expectation
functional that sends the zero vector to zero.
-/
theorem vacuumExpectation_finiteExcitationVolume_eq_zero
    {Index Fock : Type*}
    [Fintype Index] [AddCommGroup Fock] [Module ℝ Fock]
    (weight : Index → ℝ)
    (occupation : Index → Fock →ₗ[ℝ] Fock)
    (expectation : Fock → ℝ)
    {Omega : Fock}
    (hzero : expectation 0 = 0)
    (hocc : ∀ i, occupation i Omega = 0) :
    expectation (finiteExcitationVolume weight occupation Omega) = 0 := by
  rw [finiteExcitationVolume_apply_vacuum weight occupation hocc, hzero]

/--
Proof-carrying packet for a Fock vacuum whose excitation content has zero
finite positive-weight volume.
-/
structure ZeroExcitationVolumeVacuum
    (Index Fock : Type*) [Fintype Index] [AddCommGroup Fock] [Module ℝ Fock] where
  /-- Vacuum vector. -/
  Omega : Fock

  /-- Occupation operators. -/
  occupation : Index → Fock →ₗ[ℝ] Fock

  /-- Positive excitation-volume weights. -/
  weight : Index → ℝ

  /-- Positivity of the excitation-volume weights. -/
  weight_pos : ∀ i, 0 < weight i

  /-- Zero occupation of the vacuum. -/
  occupation_kills_vacuum : ∀ i, occupation i Omega = 0

namespace ZeroExcitationVolumeVacuum

variable {Index Fock : Type*} [Fintype Index] [AddCommGroup Fock] [Module ℝ Fock]
variable (Z : ZeroExcitationVolumeVacuum Index Fock)

/-- The finite excitation-volume operator associated to this vacuum packet. -/
def excitationVolume : Fock →ₗ[ℝ] Fock :=
  finiteExcitationVolume Z.weight Z.occupation

/-- Every occupation operator kills the zero-excitation vacuum. -/
theorem occupation_kills (i : Index) :
    Z.occupation i Z.Omega = 0 :=
  Z.occupation_kills_vacuum i

/-- The finite positive-weight excitation-volume operator kills the vacuum. -/
theorem excitationVolume_kills_vacuum :
    Z.excitationVolume Z.Omega = 0 :=
  finiteExcitationVolume_apply_vacuum Z.weight Z.occupation Z.occupation_kills_vacuum

/-- Expectation of the excitation volume at the vacuum is zero. -/
theorem expectation_excitationVolume_vacuum_eq_zero
    (expectation : Fock → ℝ)
    (hzero : expectation 0 = 0) :
    expectation (Z.excitationVolume Z.Omega) = 0 := by
  rw [Z.excitationVolume_kills_vacuum, hzero]

/-- Scalar readout positivity for the packet's positive weights. -/
theorem excitationVolumeExpectation_nonnegative
    {occupationExpectation : Index → ℝ}
    (hocc : ∀ i, 0 ≤ occupationExpectation i) :
    0 ≤ finiteExcitationVolumeExpectation Z.weight occupationExpectation :=
  finiteExcitationVolumeExpectation_nonnegative Z.weight_pos hocc

end ZeroExcitationVolumeVacuum

/--
Spectral stability plus zero excitation volume share the same vacuum vector.

This packages the exact algebraic content of `H Omega = 0`, `N_i Omega = 0`,
and therefore `V Omega = 0` for excitation-content volume.
-/
structure StableZeroExcitationVacuum
    (Index Fock : Type*) [Fintype Index] [NormedAddCommGroup Fock]
    [InnerProductSpace ℝ Fock] where
  /-- Spectral ground-state layer. -/
  spectral : SpectralGroundState Fock

  /-- Zero-excitation-volume layer. -/
  excitation : ZeroExcitationVolumeVacuum Index Fock

  /-- Both layers refer to the same vacuum vector. -/
  same_vacuum : spectral.Omega = excitation.Omega

namespace StableZeroExcitationVacuum

variable {Index Fock : Type*} [Fintype Index] [NormedAddCommGroup Fock]
    [InnerProductSpace ℝ Fock]
variable (S : StableZeroExcitationVacuum Index Fock)

/-- The common stable vacuum is killed by every occupation operator. -/
theorem occupation_kills_vacuum (i : Index) :
    S.excitation.occupation i S.spectral.Omega = 0 := by
  rw [S.same_vacuum]
  exact S.excitation.occupation_kills i

/-- The common stable vacuum is killed by both Hamiltonian and excitation volume. -/
theorem hamiltonian_and_excitationVolume_kill_vacuum :
    S.spectral.H S.spectral.Omega = 0 ∧
      S.excitation.excitationVolume S.spectral.Omega = 0 := by
  constructor
  · exact S.spectral.ground
  · rw [S.same_vacuum]
    exact S.excitation.excitationVolume_kills_vacuum

/--
The common stable zero-excitation vacuum is simultaneously killed by the
Hamiltonian, every occupation operator, and the finite excitation-volume
operator.
-/
theorem hamiltonian_occupation_and_excitationVolume_kill_vacuum :
    S.spectral.H S.spectral.Omega = 0 ∧
      (∀ i, S.excitation.occupation i S.spectral.Omega = 0) ∧
        S.excitation.excitationVolume S.spectral.Omega = 0 := by
  constructor
  · exact S.spectral.ground
  · constructor
    · exact fun i => S.occupation_kills_vacuum i
    · rw [S.same_vacuum]
      exact S.excitation.excitationVolume_kills_vacuum

end StableZeroExcitationVacuum

/-- Predicate for the stronger geometric claim: the geometric volume is zero. -/
def IsGeometricZeroVolume (geometricVolume : ℝ) : Prop :=
  geometricVolume = 0

/--
Constant Weyl rescaling of a `d`-dimensional geometric volume.

This represents the regular finite transformation
`Vol ↦ exp (d * sigma) * Vol`, not an excitation-number readout.
-/
def constantWeylRescaledVolume
    (d sigma geometricVolume : ℝ) : ℝ :=
  Real.exp (d * sigma) * geometricVolume

/-- A regular finite Weyl rescaling of a strictly positive geometric volume is positive. -/
theorem constantWeylRescaledVolume_pos
    {d sigma geometricVolume : ℝ}
    (hVol : 0 < geometricVolume) :
    0 < constantWeylRescaledVolume d sigma geometricVolume := by
  exact mul_pos (Real.exp_pos _) hVol

/--
A regular finite Weyl rescaling of a strictly positive geometric volume cannot
produce zero geometric volume.
-/
theorem constantWeylRescaledVolume_ne_zero_of_pos
    {d sigma geometricVolume : ℝ}
    (hVol : 0 < geometricVolume) :
    constantWeylRescaledVolume d sigma geometricVolume ≠ 0 :=
  ne_of_gt (constantWeylRescaledVolume_pos hVol)

/-- Positive geometric volume is not a geometric zero-volume state. -/
theorem positive_geometricVolume_not_zeroVolume
    {geometricVolume : ℝ}
    (hVol : 0 < geometricVolume) :
    ¬ IsGeometricZeroVolume geometricVolume := by
  exact fun hzero => (ne_of_gt hVol) hzero

/--
The Weyl-rescaled positive geometric volume remains outside the zero-volume
geometric boundary.
-/
theorem regularWeyl_positive_volume_not_geometricZeroVolume
    {d sigma geometricVolume : ℝ}
    (hVol : 0 < geometricVolume) :
    ¬ IsGeometricZeroVolume (constantWeylRescaledVolume d sigma geometricVolume) := by
  exact positive_geometricVolume_not_zeroVolume (constantWeylRescaledVolume_pos hVol)

/-! ## KMS/passivity layer -/

/--
Hamiltonian passivity for cyclic perturbations.

The work expression is the usual Hamiltonian form
`omega(U^* H U - H)`.  This structure records the inequality; KMS analyticity
is kept separate in `KMSPassiveEquilibrium`.
-/
structure HamiltonianPassivity
    (Op : Type*) [AddMonoid Op] [Mul Op] [Sub Op] [Star Op] where
  /-- Real energy-state readout. -/
  omega : Op →+ ℝ

  /-- Physical Hamiltonian used in the work inequality. -/
  H : Op

  /-- Cyclic perturbations. -/
  cyclic : Op → Prop

  /-- Passive cyclic work inequality. -/
  passive :
    ∀ U : Op, cyclic U → 0 ≤ omega (star U * H * U - H)

namespace HamiltonianPassivity

variable {Op : Type*} [AddMonoid Op] [Mul Op] [Sub Op] [Star Op]
variable (P : HamiltonianPassivity Op)

/-- Work extracted from a cyclic perturbation in Hamiltonian form. -/
def cyclicWork (U : Op) : ℝ :=
  P.omega (star U * P.H * U - P.H)

/-- Passivity: cyclic work is nonnegative. -/
theorem cyclicWork_nonnegative
    {U : Op}
    (hU : P.cyclic U) :
    0 ≤ P.cyclicWork U :=
  P.passive U hU

end HamiltonianPassivity

/--
A finite-temperature equilibrium packet: KMS analyticity plus passivity.

This does not identify thermal equilibrium with a zero-temperature ground
state.  It only packages the two equilibrium controls that belong to the
finite-temperature layer.
-/
structure KMSPassiveEquilibrium
    (Op : Type*) [AddMonoid Op] [Mul Op] [Sub Op] [Star Op]
    (sigma : InfoGeometry.OperatorAlgebra.Thermodynamics.FlowDatum Op)
    (beta : ℝ) where
  /-- KMS state with respect to the chosen flow. -/
  kms : InfoGeometry.OperatorAlgebra.Thermodynamics.KMSState Op sigma beta

  /-- Passive Hamiltonian work inequality for cyclic perturbations. -/
  passivity : HamiltonianPassivity Op

namespace KMSPassiveEquilibrium

variable {Op : Type*} [AddMonoid Op] [Mul Op] [Sub Op] [Star Op]
variable {sigma : InfoGeometry.OperatorAlgebra.Thermodynamics.FlowDatum Op} {beta : ℝ}
variable (E : KMSPassiveEquilibrium Op sigma beta)

/-- KMS states are invariant under real time flow. -/
theorem kms_flow_invariant
    (t : ℝ)
    (A : Op) :
    E.kms.state.eval (sigma.flow t A) = E.kms.state.eval A :=
  InfoGeometry.OperatorAlgebra.Thermodynamics.KMSState.flow_invariant_apply E.kms t A

/-- Re-export of passivity for cyclic perturbations. -/
theorem cyclicWork_nonnegative
    {U : Op}
    (hU : E.passivity.cyclic U) :
    0 ≤ E.passivity.cyclicWork U :=
  E.passivity.cyclicWork_nonnegative hU

end KMSPassiveEquilibrium

/-! ## Positive deformation geometry -/

/--
The real covariance/Fisher deformation metric represented by tangent vectors.

This is the Gram matrix of physical tangent vectors, the finite-dimensional
shadow of `g_{i \bar j} = partial_i partial_bar_j log Z`.
-/
def covarianceDeformationMetric
    {Index Tangent : Type*}
    [Inner ℝ Tangent]
    (tangent : Index → Tangent) :
    Matrix Index Index ℝ :=
  Matrix.gram ℝ tangent

/-- The covariance/Fisher deformation metric is positive semidefinite. -/
theorem covarianceDeformationMetric_posSemidef
    {Index Tangent : Type*}
    [Finite Index]
    [SeminormedAddCommGroup Tangent]
    [InnerProductSpace ℝ Tangent]
    (tangent : Index → Tangent) :
    Matrix.PosSemidef (covarianceDeformationMetric tangent) := by
  simpa [covarianceDeformationMetric] using
    (Matrix.posSemidef_gram (𝕜 := ℝ) tangent)

/--
After quotienting null/gauge directions, independence of physical tangent
directions gives strict positive definiteness.
-/
theorem covarianceDeformationMetric_posDef_of_linearIndependent
    {Index Tangent : Type*}
    [Finite Index]
    [NormedAddCommGroup Tangent]
    [InnerProductSpace ℝ Tangent]
    {tangent : Index → Tangent}
    (hind : LinearIndependent ℝ tangent) :
    Matrix.PosDef (covarianceDeformationMetric tangent) := by
  simpa [covarianceDeformationMetric] using
    (Matrix.posDef_gram_of_linearIndependent (𝕜 := ℝ) hind)

/--
Strict positive definiteness of the Gram/Fisher deformation metric is exactly
linear independence of the physical tangent directions.
-/
theorem covarianceDeformationMetric_posDef_iff_linearIndependent
    {Index Tangent : Type*}
    [Finite Index]
    [NormedAddCommGroup Tangent]
    [InnerProductSpace ℝ Tangent]
    {tangent : Index → Tangent} :
    Matrix.PosDef (covarianceDeformationMetric tangent) ↔ LinearIndependent ℝ tangent := by
  simpa [covarianceDeformationMetric] using
    (Matrix.posDef_gram_iff_linearIndependent (𝕜 := ℝ) (v := tangent))

/-! ## Combined stable-vacuum architecture -/

/--
Stable-vacuum architecture with the three stability layers kept separate.

The physical Hamiltonian is in `spectral.H`; the modular/thermal flow is in
`thermal.kms`; and the deformation geometry is the Gram/Fisher metric of
`deformationTangents`.
-/
structure StableVacuumArchitecture
    (V Op Index Tangent : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [AddMonoid Op] [Mul Op] [Sub Op] [Star Op]
    [SeminormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    (sigma : InfoGeometry.OperatorAlgebra.Thermodynamics.FlowDatum Op)
    (beta : ℝ) where
  /-- Zero-temperature spectral ground-state layer. -/
  spectral : SpectralGroundState V

  /-- Finite-temperature KMS/passive equilibrium layer. -/
  thermal : KMSPassiveEquilibrium Op sigma beta

  /-- Physical deformation tangent vectors. -/
  deformationTangents : Index → Tangent

namespace StableVacuumArchitecture

variable
    {V Op Index Tangent : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [AddMonoid Op] [Mul Op] [Sub Op] [Star Op]
    [SeminormedAddCommGroup Tangent] [InnerProductSpace ℝ Tangent]
    {sigma : InfoGeometry.OperatorAlgebra.Thermodynamics.FlowDatum Op}
    {beta : ℝ}

variable (S : StableVacuumArchitecture V Op Index Tangent sigma beta)

/-- The stable vacuum vector is a spectral ground vector. -/
theorem spectral_ground :
    S.spectral.H S.spectral.Omega = 0 :=
  S.spectral.ground

/-- The deformation metric is positive semidefinite. -/
theorem deformation_metric_posSemidef
    [Finite Index] :
    Matrix.PosSemidef (covarianceDeformationMetric S.deformationTangents) :=
  covarianceDeformationMetric_posSemidef S.deformationTangents

end StableVacuumArchitecture

end InfoGeometry.Canonical.StableVacuum
