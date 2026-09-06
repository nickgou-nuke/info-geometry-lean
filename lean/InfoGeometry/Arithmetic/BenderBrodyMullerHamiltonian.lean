import Mathlib.Tactic

/-!
# Bender--Brody--Müller Hamiltonian socket

Finite/theorem-safe algebraic interfaces for
Carl M. Bender, Dorje C. Brody, Markus P. Müller,
"Hamiltonian for the zeros of the Riemann zeta function",
arXiv:1608.03679v4.

The paper proposes a non-Hermitian operator
`H = Δ⁻¹ (xp + px) Δ` whose boundary condition `ψ_z(0)=0` selects zeta zeros,
and discusses PT symmetry, pseudo-Hermiticity, and self-adjointness as analytic
obligations.

This Lean module proves only closed algebraic fragments:

* the coordinate conversion `E = i(2z-1)` and `z = (1-iE)/2` is inverse;
* if a boundary value is `-ζ(z)` and the boundary condition sets it to zero,
  then the corresponding zeta value is zero;
* a similarity transform transfers eigenvectors from the Berry--Keating block to
  the BBM Hamiltonian whenever the inverse/left-inverse laws are supplied;
* PT/pseudo-Hermitian/self-adjoint/RH consequences are recorded only as socket
  data, never as proved analytic theorems.

#### BUCKET 1: CLOSED FINITE THEOREMS

The coordinate conversion, boundary-zero algebra, similarity-transfer lemma, and
commuting Berry--Keating shadow are fully verified finite theorems.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES

Similarity transfer and the analytic RH implication are stated only from
explicit named premises. No domain or spectral theorem is hidden inside a
record field.

#### BUCKET 3: OPEN CLOSURE DEBT

The module does not prove domain selection for `Δ`, self-adjointness,
pseudo-Hermitian metric positivity, completeness of the eigenfunctions, or RH.
-/

noncomputable section

open Complex

namespace InfoGeometry.Arithmetic.BenderBrodyMullerHamiltonian

/-! ## Spectral coordinate algebra -/

/-- BBM energy coordinate attached to a zeta coordinate `z`: `E = i(2z - 1)`. -/
def bbmEnergy (z : ℂ) : ℂ :=
  Complex.I * (2 * z - 1)

/-- Inverse coordinate used in the paper: `z = (1 - iE) / 2`. -/
def bbmZeroCoordinate (E : ℂ) : ℂ :=
  (1 - Complex.I * E) / 2

/-- The BBM energy/zero coordinate conversion recovers `z`. -/
theorem bbmZeroCoordinate_energy (z : ℂ) :
    bbmZeroCoordinate (bbmEnergy z) = z := by
  simp [bbmZeroCoordinate, bbmEnergy]
  ring_nf
  rw [Complex.I_sq]
  ring_nf

/-- The BBM energy/zero coordinate conversion recovers `E`. -/
theorem bbmEnergy_zeroCoordinate (E : ℂ) :
    bbmEnergy (bbmZeroCoordinate E) = E := by
  simp [bbmZeroCoordinate, bbmEnergy]
  ring_nf
  rw [Complex.I_sq]
  ring_nf

/-- Critical-line zeros (`z = 1/2 + it`) correspond to real BBM energy `-2t`. -/
theorem bbmEnergy_on_critical_line (t : ℝ) :
    bbmEnergy ((1 / 2 : ℂ) + Complex.I * (t : ℂ)) = (-2 * t : ℂ) := by
  simp [bbmEnergy]
  ring_nf
  rw [Complex.I_sq]
  ring_nf

/-- If the BBM energy coordinate is real `E`, its zero coordinate lies on `1/2 - iE/2`. -/
theorem bbmZeroCoordinate_real_energy (E : ℝ) :
    bbmZeroCoordinate (E : ℂ) = (1 / 2 : ℂ) - Complex.I * ((E / 2 : ℝ) : ℂ) := by
  simp [bbmZeroCoordinate]
  ring_nf

/-- Real BBM energy coordinates land on real part `1/2`. -/
theorem bbmZeroCoordinate_real_energy_re (E : ℝ) :
    (bbmZeroCoordinate (E : ℂ)).re = (1 / 2 : ℝ) := by
  rw [bbmZeroCoordinate_real_energy E]
  simp

/-! ## Boundary condition to zeta-zero algebra -/

/--
Pure boundary algebra: if the boundary value is `-ζ(z)` and the boundary
condition forces it to vanish, then the zeta value vanishes.
-/
theorem zeta_zero_of_boundary_zero {A : Type*} [AddGroup A]
    {psiAtZero zetaAtZero : A}
    (h_eval : psiAtZero = -zetaAtZero) (h_boundary : psiAtZero = 0) :
    zetaAtZero = 0 := by
  rw [h_eval] at h_boundary
  exact neg_eq_zero.mp h_boundary

/--
The boundary condition is equivalent to the abstract zeta-zero condition once
the explicit BBM boundary readout `ψ_z(0)=-ζ(z)` is supplied.
-/
theorem boundary_zero_iff_zeta_zero {A : Type*} [AddGroup A]
    {psiAtZero zetaAtZero : A}
    (h_eval : psiAtZero = -zetaAtZero) :
    psiAtZero = 0 ↔ zetaAtZero = 0 := by
  constructor
  · exact zeta_zero_of_boundary_zero h_eval
  · intro hzeta
    rw [h_eval, hzeta, neg_zero]

/-! ## Similarity transform eigenvector transfer -/

/--
A theorem-level expansion of the advertised similarity transform
`H = Δ⁻¹ (xp+px) Δ`.
-/
theorem hamiltonian_apply_of_similarity
    {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (delta deltaInv berryKeating hamiltonian : V →ₗ[R] V)
    (hHamiltonian : hamiltonian = deltaInv.comp (berryKeating.comp delta))
    (v : V) :
    hamiltonian v = deltaInv (berryKeating (delta v)) := by
  rw [hHamiltonian]
  rfl

/--
Eigenvector transfer through the similarity transform: if `Δ ψ` is a
Berry--Keating eigenvector with eigenvalue `E`, then `ψ` is a BBM-Hamiltonian
eigenvector with the same eigenvalue, provided the explicit left-inverse
premise holds on the selected domain.
-/
theorem eigen_of_delta_eigen
    {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (delta deltaInv berryKeating hamiltonian : V →ₗ[R] V)
    (hHamiltonian : hamiltonian = deltaInv.comp (berryKeating.comp delta))
    (hDeltaLeftInverse : ∀ v : V, deltaInv (delta v) = v)
    {E : R} {psi : V}
    (hBK : berryKeating (delta psi) = E • delta psi) :
    hamiltonian psi = E • psi := by
  calc
    hamiltonian psi = deltaInv (berryKeating (delta psi)) :=
      hamiltonian_apply_of_similarity delta deltaInv berryKeating hamiltonian hHamiltonian psi
    _ = deltaInv (E • delta psi) := by rw [hBK]
    _ = E • deltaInv (delta psi) := by simp
    _ = E • psi := by rw [hDeltaLeftInverse psi]

/-! ## Classical Berry--Keating shadow -/

/-- If the classical variables commute, then `xp+px` collapses to `2xp`. -/
theorem berryKeating_commuting_shadow {R : Type*} [Semiring R]
    {x p : R} (hcomm : p * x = x * p) :
    x * p + p * x = (2 : R) * (x * p) := by
  rw [hcomm]
  rw [two_mul]

/-! ## Analytic obligation socket -/

/--
Projection from explicit analytic obligations.  This theorem is intentionally
conditional: it does not construct the BBM domain, metric, self-adjoint closure,
or RH consequence.
-/
theorem rhConsequence_of_selfAdjointClosure
    (domainChosen deltaInverseOnDomain boundaryConditionSelectsNontrivialZeros
      momentumSymmetricOnMetricDomain pseudoHermitianMetricPositive
      selfAdjointClosure rhConsequence : Prop)
    (_hDomain : domainChosen)
    (_hDelta : deltaInverseOnDomain)
    (_hBoundary : boundaryConditionSelectsNontrivialZeros)
    (_hMomentum : momentumSymmetricOnMetricDomain)
    (_hMetric : pseudoHermitianMetricPositive)
    (hAnalytic : selfAdjointClosure → rhConsequence)
    (hSelfAdjoint : selfAdjointClosure) :
    rhConsequence :=
  hAnalytic hSelfAdjoint

end InfoGeometry.Arithmetic.BenderBrodyMullerHamiltonian
