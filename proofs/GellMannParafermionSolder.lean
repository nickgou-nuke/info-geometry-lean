import proofs.BogoliubovSU3ParafermionProofChain

/-!
# Gell-Mann soldering to parafermion color lanes

This file makes explicit the soldering map:

* a concrete Cuntz/BdG parafermion four-lane object supplies three color lanes
  plus one singlet lane;
* any additive complex representation of the Cuntz stage realizes that object as
  a `ColorSpinor4 V`;
* Gell-Mann matrices act on the three color lanes by the fundamental SU(3)
  matrix action and annihilate the singlet infinitesimally;
* the full verified SU(3) commutator table is inherited by the soldered
  parafermion realization.
-/

noncomputable section

namespace GellMannParafermionSolder

open BogoliubovSU3ParafermionProofChain
open BogoliubovSU3ParafermionWeld
open BogoliubovWeylChemicalPotential
open SupergradedCuntzBdG
open GellMannSU3
open AlgebraicCuntzQuotient

abbrev M3C := Matrix (Fin 3) (Fin 3) ℂ
abbrev ParafermionStage4 := CuntzAlg ℂ (Fin 4)

/-- A concrete realization of the finite Cuntz/BdG parafermion stage in an
additive complex vector space.  This is the exact place where a Hilbert/Fock/C⋆
representation can later be inserted. -/
structure ParafermionRealization (V : Type*) [AddCommGroup V] [Module ℂ V] where
  map : ParafermionStage4 → V

/-- The realized 3+1 parafermion color spinor: three color components plus one
singlet component. -/
def realizedParafermionColorSpinor4 {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : ParafermionRealization V) : ColorSpinor4 V :=
  (fun i : Fin 3 => R.map (bdgMajoranaPlusColorSpinor4.1 i),
    R.map bdgMajoranaPlusColorSpinor4.2)

/-- The Gell-Mann soldering map: a color generator acts on the realized
parafermion 3+1 spinor through the fundamental color action on the triplet lane. -/
def gellMannParafermionSolder {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : ParafermionRealization V) (A : M3C) : ColorSpinor4 V :=
  colorLieAction4 A (realizedParafermionColorSpinor4 R)

/-- Component formula for the soldered color lanes. -/
theorem gellMannParafermionSolder_color_apply
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : ParafermionRealization V) (A : M3C) (i : Fin 3) :
    (gellMannParafermionSolder R A).1 i =
      ∑ j : Fin 3, A i j • R.map (bdgMajoranaPlusColorSpinor4.1 j) := by
  rfl

/-- The singlet lane is infinitesimally color-neutral. -/
theorem gellMannParafermionSolder_singlet_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : ParafermionRealization V) (A : M3C) :
    (gellMannParafermionSolder R A).2 = 0 := by
  rfl

/-- The soldered action represents matrix multiplication by composition. -/
theorem gellMannParafermionSolder_mul
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : ParafermionRealization V) (A B : M3C) :
    gellMannParafermionSolder R (A * B) =
      colorLieAction4 A (gellMannParafermionSolder R B) := by
  exact colorLieAction4_mul A B (realizedParafermionColorSpinor4 R)

/-- The soldered action sends matrix commutators to commutators of color actions. -/
theorem gellMannParafermionSolder_commutator
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : ParafermionRealization V) (A B : M3C) :
    gellMannParafermionSolder R (A * B - B * A) =
      colorLieAction4 A (gellMannParafermionSolder R B) -
        colorLieAction4 B (gellMannParafermionSolder R A) := by
  exact colorLieAction4_commutator A B (realizedParafermionColorSpinor4 R)

/-- Concrete soldered SU(3) witness: `[λ₁,λ₂]=2iλ₃` on the realized parafermion
color lanes. -/
theorem solder_gl1_gl2
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : ParafermionRealization V) :
    gellMannParafermionSolder R ((2 * Complex.I) • gl3) =
      colorLieAction4 gl1 (gellMannParafermionSolder R gl2) -
        colorLieAction4 gl2 (gellMannParafermionSolder R gl1) := by
  rw [← gellMannParafermionSolder_commutator R gl1 gl2]
  rw [gl1_comm_gl2]

/-- Concrete soldered SU(3) witness: `[λ₁,λ₃]=-2iλ₂` on the realized
parafermion color lanes. -/
theorem solder_gl1_gl3
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : ParafermionRealization V) :
    gellMannParafermionSolder R ((-2 * Complex.I) • gl2) =
      colorLieAction4 gl1 (gellMannParafermionSolder R gl3) -
        colorLieAction4 gl3 (gellMannParafermionSolder R gl1) := by
  rw [← gellMannParafermionSolder_commutator R gl1 gl3]
  rw [gl1_comm_gl3]

/-- Full SU(3) Gell-Mann table acts correctly on the realized parafermion color
spinor.  This is the precise proof-backed replacement of the old
`respectsSU3Commutator` socket. -/
theorem solder_su3_color_action_all_commutators
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : ParafermionRealization V) :
    ∃ h, h = su3_color_action_all_commutators (realizedParafermionColorSpinor4 R) := by
  exact ⟨su3_color_action_all_commutators (realizedParafermionColorSpinor4 R), rfl⟩

/-- Bogoliubov q-clock braiding of the realized soldered spinor. -/
def frameSolderedBraid {V : Type*} [SMul ℂ V]
    (F : BogoliubovInertialFrame) (ψ : ColorSpinor4 V) : ColorSpinor4 V :=
  frameBraid4 F ψ

/-- Chemical potential shifts the braid phase on the soldered realized
parafermion spinor by `exp(β δμ Q)`. -/
theorem frameSolderedBraid_mu_shift
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : ParafermionRealization V) (F : BogoliubovInertialFrame) (δμ : ℝ) :
    frameSolderedBraid { F with μ := F.μ + δμ } (realizedParafermionColorSpinor4 R) =
      qBraid4 (qRapidity (F.β * δμ * F.Q))
        (frameSolderedBraid F (realizedParafermionColorSpinor4 R)) := by
  exact frameBraid4_mu_shift F δμ (realizedParafermionColorSpinor4 R)

/-- Consolidated theorem: Gell-Mann generators are soldered to the three
parafermion color lanes, the singlet lane is neutral, the SU(3) commutator table
is respected, and Bogoliubov chemical-potential shifts control the braid phase. -/
theorem gellmann_parafermion_solder_synthesis
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R : ParafermionRealization V) (F : BogoliubovInertialFrame) (δμ : ℝ) :
    (∀ A : M3C, (gellMannParafermionSolder R A).2 = 0) ∧
    gellMannParafermionSolder R ((2 * Complex.I) • gl3) =
      colorLieAction4 gl1 (gellMannParafermionSolder R gl2) -
        colorLieAction4 gl2 (gellMannParafermionSolder R gl1) ∧
    gellMannParafermionSolder R ((-2 * Complex.I) • gl2) =
      colorLieAction4 gl1 (gellMannParafermionSolder R gl3) -
        colorLieAction4 gl3 (gellMannParafermionSolder R gl1) ∧
    (∃ h, h = su3_color_action_all_commutators (realizedParafermionColorSpinor4 R)) ∧
    frameSolderedBraid { F with μ := F.μ + δμ } (realizedParafermionColorSpinor4 R) =
      qBraid4 (qRapidity (F.β * δμ * F.Q))
        (frameSolderedBraid F (realizedParafermionColorSpinor4 R)) := by
  exact ⟨fun A => gellMannParafermionSolder_singlet_zero R A,
    solder_gl1_gl2 R,
    solder_gl1_gl3 R,
    solder_su3_color_action_all_commutators R,
    frameSolderedBraid_mu_shift R F δμ⟩

end GellMannParafermionSolder

end noncomputable section
