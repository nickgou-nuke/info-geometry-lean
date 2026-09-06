import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# InfoGeometry.Canonical.TorsionSpinorEinsteinFinite

Finite algebraic owner lane for a torsion/spinor/modified-Einstein corridor.

This file does not derive continuum Einstein-Cartan field equations from an
analytic action, does not construct gamma matrices or covariant derivatives,
and does not prove diffeomorphism invariance. It closes only the finite tensor
algebra actually needed as an honest precursor:
- torsion antisymmetry in the lower pair;
- contorsion built from torsion;
- antisymmetry of the induced spinor torsion source when the bilinear source is
  antisymmetric in the lower pair;
- symmetry of the torsion-squared stress tensor;
- quadratic scaling of the torsion-squared stress tensor for spinor-sourced
  torsion;
- symmetry of a modified Einstein residual when its symmetric inputs are packed
  explicitly.
- equivalence between residual vanishing and the finite modified Einstein
  equation.

#### BUCKET 1: CLOSED FINITE THEOREMS
- `contorsion_eq_half_cyclic`
- `spinorTorsion_antisymm`
- `torsionStress_symmetric`
- `torsionContraction_spinorTorsion_scaled`
- `torsionNorm_spinorTorsion_scaled`
- `torsionStress_spinorTorsion_scaled`
- `modifiedEinsteinResidual_symmetric`
- `modifiedEinsteinResidual_eq_zero_iff`

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT HYPOTHESES
- `contorsion_antisymm12_of_total_antisymm`
- `spinorTorsion_antisymm`
- `modifiedEinsteinResidual_symmetric`

#### BUCKET 3: OPEN CLOSURE DEBT
Variational derivation from an action, Bach/curvature-squared calculus,
Dirac operator geometry, covariant conservation, and continuum spin connection
physics.
-/

noncomputable section

namespace InfoGeometry.Canonical.TorsionSpinorEinsteinFinite

abbrev Idx : Type := Fin 4
abbrev Tensor3 : Type := Idx → Idx → Idx → ℝ
abbrev Tensor2 : Type := Idx → Idx → ℝ

/-- Kronecker delta on the finite index set. -/
def delta (μ ν : Idx) : ℝ := if μ = ν then 1 else 0

/-- Torsion with lower-pair antisymmetry. -/
structure TorsionPacket where
  T : Tensor3
  antisymm : ∀ ρ μ ν, T ρ μ ν = -T ρ ν μ

/-- Contorsion built from torsion by the standard cyclic formula. -/
def contorsion (T : Tensor3) (lam mu nu : Idx) : ℝ :=
  (1 / 2 : ℝ) * (T lam mu nu + T mu lam nu + T nu lam mu)

theorem contorsion_eq_half_cyclic (T : Tensor3) (lam mu nu : Idx) :
    contorsion T lam mu nu = (1 / 2 : ℝ) * (T lam mu nu + T mu lam nu + T nu lam mu) := rfl

/-- If torsion is fully antisymmetric, contorsion is antisymmetric in the first two slots. -/
theorem contorsion_antisymm12_of_total_antisymm
    (T : Tensor3)
    (hswap12 : ∀ a b c, T b a c = -T a b c)
    (hcycle : ∀ a b c, T c a b = T a b c)
    (lam mu nu : Idx) :
    contorsion T lam mu nu = -contorsion T mu lam nu := by
  unfold contorsion
  rw [hswap12 lam mu nu, hcycle lam mu nu, hcycle mu lam nu, hswap12 lam mu nu]
  ring_nf

/-- Abstract spinor bilinear source for torsion. -/
structure SpinorSourcePacket where
  S : Tensor3
  antisymm : ∀ lam mu nu, S lam mu nu = -S lam nu mu

/-- Torsion sourced linearly by a spinor bilinear. -/
def spinorTorsion (κ β : ℝ) (S : Tensor3) : Tensor3 :=
  fun lam mu nu => κ * β * S lam mu nu

theorem spinorTorsion_antisymm (κ β : ℝ) (P : SpinorSourcePacket) (lam mu nu : Idx) :
    spinorTorsion κ β P.S lam mu nu = -spinorTorsion κ β P.S lam nu mu := by
  unfold spinorTorsion
  rw [P.antisymm lam mu nu]
  ring

/-- Torsion-squared finite stress tensor. -/
def torsionStress (α : ℝ) (T : Tensor3) (μ ν : Idx) : ℝ :=
  2 * α *
    ((∑ a : Idx, ∑ b : Idx, T μ a b * T ν a b)
      - (1 / 4 : ℝ) * delta μ ν * (∑ a : Idx, ∑ b : Idx, ∑ c : Idx, T a b c * T a b c))

theorem torsionContraction_spinorTorsion_scaled
    (κ β : ℝ) (S : Tensor3) (μ ν : Idx) :
    (∑ a : Idx, ∑ b : Idx,
        spinorTorsion κ β S μ a b * spinorTorsion κ β S ν a b)
      = (κ * β) ^ 2 * (∑ a : Idx, ∑ b : Idx, S μ a b * S ν a b) := by
  unfold spinorTorsion
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem torsionNorm_spinorTorsion_scaled (κ β : ℝ) (S : Tensor3) :
    (∑ a : Idx, ∑ b : Idx, ∑ c : Idx,
        spinorTorsion κ β S a b c * spinorTorsion κ β S a b c)
      = (κ * β) ^ 2 * (∑ a : Idx, ∑ b : Idx, ∑ c : Idx, S a b c * S a b c) := by
  unfold spinorTorsion
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem torsionStress_spinorTorsion_scaled
    (α κ β : ℝ) (S : Tensor3) (μ ν : Idx) :
    torsionStress α (spinorTorsion κ β S) μ ν
      = torsionStress (α * (κ * β) ^ 2) S μ ν := by
  unfold torsionStress
  rw [torsionContraction_spinorTorsion_scaled, torsionNorm_spinorTorsion_scaled]
  ring

theorem torsionStress_symmetric (α : ℝ) (T : Tensor3) (μ ν : Idx) :
    torsionStress α T μ ν = torsionStress α T ν μ := by
  unfold torsionStress
  by_cases h : μ = ν
  · subst h
    rfl
  · have hδ : delta μ ν = delta ν μ := by
      unfold delta
      simp [h, Ne.symm h]
    rw [hδ]
    have hpair :
        (∑ a : Idx, ∑ b : Idx, T μ a b * T ν a b)
          = (∑ a : Idx, ∑ b : Idx, T ν a b * T μ a b) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    rw [hpair]

/-- Symmetric input packet for a finite modified Einstein residual. -/
structure ModifiedEinsteinPacket where
  G : Tensor2
  H : Tensor2
  Tpsi : Tensor2
  GT : Tensor2
  symm_G : ∀ μ ν, G μ ν = G ν μ
  symm_H : ∀ μ ν, H μ ν = H ν μ
  symm_Tpsi : ∀ μ ν, Tpsi μ ν = Tpsi ν μ
  symm_GT : ∀ μ ν, GT μ ν = GT ν μ

/-- Finite modified Einstein residual. -/
def modifiedEinsteinResidual (Λ α : ℝ) (P : ModifiedEinsteinPacket) (μ ν : Idx) : ℝ :=
  P.G μ ν + Λ * delta μ ν + α * P.H μ ν - (P.Tpsi μ ν + P.GT μ ν)

theorem modifiedEinsteinResidual_eq_zero_iff
    (Λ α : ℝ) (P : ModifiedEinsteinPacket) (μ ν : Idx) :
    modifiedEinsteinResidual Λ α P μ ν = 0 ↔
      P.G μ ν + Λ * delta μ ν + α * P.H μ ν = P.Tpsi μ ν + P.GT μ ν := by
  unfold modifiedEinsteinResidual
  constructor
  · intro h
    exact sub_eq_zero.mp h
  · intro h
    exact sub_eq_zero.mpr h

theorem modifiedEinsteinResidual_symmetric
    (Λ α : ℝ) (P : ModifiedEinsteinPacket) (μ ν : Idx) :
    modifiedEinsteinResidual Λ α P μ ν = modifiedEinsteinResidual Λ α P ν μ := by
  unfold modifiedEinsteinResidual
  by_cases h : μ = ν
  · subst h
    rfl
  · have hδ : delta μ ν = delta ν μ := by
      unfold delta
      simp [h, Ne.symm h]
    rw [P.symm_G μ ν, P.symm_H μ ν, P.symm_Tpsi μ ν, P.symm_GT μ ν, hδ]

end InfoGeometry.Canonical.TorsionSpinorEinsteinFinite
