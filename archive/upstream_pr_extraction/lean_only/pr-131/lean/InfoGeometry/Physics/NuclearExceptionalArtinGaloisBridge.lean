import Mathlib
import InfoGeometry.Physics.NuclearChargeSpinSymmetry
import InfoGeometry.Physics.NuclearCartanGradeNormalizationBridge
import InfoGeometry.Canonical.SL2SpinorLadder
import InfoGeometry.Exceptional.G2ArtinOperatorLift
import InfoGeometry.Algebra.Zorn.G2DoubleStarCyclotomicAction

/-!
# Nuclear five-grade / exceptional Artin / Galois bridge

This module records exact structural compatibility between four existing
corridors without identifying their carriers:

* nuclear balanced Cartan weights `±1`;
* the repository's genuine five-graded `sl₂ ⋉ R²` Lie owner;
* the `G₂ = I₂(6)` Artin operator lift and its projective/spin closure;
* the supplied Bost--Connes Galois action extended trivially on nuclear quantum
  numbers.

Theorems here are relation/representation packets.  They do not assert that
`G₂`, an exceptional group, an Artin braid group, or an absolute Galois group
is the physical nuclear symmetry group without an explicit action preserving
the nuclear packet.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearExceptionalArtinGaloisBridge

open InfoGeometry.Physics.NuclearChargeSpinSymmetry
open InfoGeometry.Physics.NuclearCartanGradeNormalizationBridge
open InfoGeometry.Physics.NuclearQuasiparticleCAR
open InfoGeometry.Canonical.SL2SpinorLadder
open InfoGeometry.Exceptional.ArtinOperators
open InfoGeometry.Algebra.Zorn.G2DoubleStarCyclotomicAction
open InfoGeometry.Algebra.Zorn.G2CyclotomicSignedRootBridge

/-- The canonical five-grade Lie owner already present in the repository. -/
noncomputable def canonicalFiveGrading :
    InfoGeometry.OperatorAlgebra.FiveGradedInformationLedger.FiveGrading
      InfoGeometry.Canonical.SL2SpinorLadder.Alg :=
  InfoGeometry.Canonical.SL2SpinorLadder.Alg.spinorFiveGrading

/-- Nuclear CAR creation/annihilation has exactly the `±1` balanced Cartan
normalization matching the grade-one convention used by the five-grade lane. -/
theorem nuclear_balanced_weight_packet
    {ι A : Type*} [DecidableEq ι] [Ring A] [Algebra ℝ A]
    (car : QuasiparticleCAR ι A) (i : ι) :
    QuasiparticleCAR.comm (balancedOccupationCartan car i) (car.adag i) =
        car.adag i ∧
      QuasiparticleCAR.comm (balancedOccupationCartan car i) (car.a i) =
        -car.a i :=
  ⟨comm_balancedOccupationCartan_adag car i,
    comm_balancedOccupationCartan_a car i⟩

/-- Canonical five-grade Cartan action on the `±1` spinor slots. -/
theorem canonical_five_grade_weight_packet :
    ⁅Alg.basisH, Alg.basisU⁆ = Alg.basisU ∧
      ⁅Alg.basisH, Alg.basisV⁆ = -Alg.basisV := by
  constructor
  · change Alg.br Alg.basisH Alg.basisU = Alg.basisU
    ext <;> dsimp [Alg.br, Alg.basisH, Alg.basisU] <;> norm_num
  · change Alg.br Alg.basisH Alg.basisV = -Alg.basisV
    ext <;> dsimp [Alg.br, Alg.basisH, Alg.basisV] <;> norm_num

/-- Relation-shape agreement of the nuclear balanced ladder and the canonical
five-grade `±1` slots.  This is not an algebra isomorphism. -/
theorem nuclear_five_grade_relation_packet
    {ι A : Type*} [DecidableEq ι] [Ring A] [Algebra ℝ A]
    (car : QuasiparticleCAR ι A) (i : ι) :
    (QuasiparticleCAR.comm (balancedOccupationCartan car i) (car.adag i) =
        car.adag i ∧
      QuasiparticleCAR.comm (balancedOccupationCartan car i) (car.a i) =
        -car.a i) ∧
    (⁅Alg.basisH, Alg.basisU⁆ = Alg.basisU ∧
      ⁅Alg.basisH, Alg.basisV⁆ = -Alg.basisV) :=
  ⟨nuclear_balanced_weight_packet car i, canonical_five_grade_weight_packet⟩

/-- Exact `G₂/I₂(6)` Artin relation together with projective spin closure. -/
theorem g2_artin_spin_packet (ρ : G2SpinOperatorLift) :
    ρ.Bs * ρ.Bl * ρ.Bs * ρ.Bl * ρ.Bs * ρ.Bl =
        ρ.Bl * ρ.Bs * ρ.Bl * ρ.Bs * ρ.Bl * ρ.Bs ∧
      (ρ.Bs * ρ.Bl) ^ 6 = -1 ∧
      (ρ.Bs * ρ.Bl) ^ 12 = 1 :=
  ⟨ρ.artin, ρ.coxeter_pow_six_eq_neg_one, ρ.spin_coxeter_pow_twelve⟩

/-- Re-export the exact theorem that Artin/braid conjugation preserves a
square-zero chiral channel. -/
theorem artin_conjugation_preserves_nuclear_nilpotent_shape
    {H : Type*} [AddCommGroup H] [Module ℂ H]
    (B : (Module.End ℂ H)ˣ) (Q : Module.End ℂ H)
    (hQ : Q ^ 2 = 0) :
    ((B : Module.End ℂ H) * Q * (↑B⁻¹ : Module.End ℂ H)) ^ 2 = 0 :=
  braid_conjugation_preserves_nilpotent B Q hQ

/-- The concrete cyclotomic `G₂` Weyl/Coxeter action preserves the root-sector
label on the doubled short/long root hexagons. -/
theorem g2_cyclotomic_sector_packet
    (r : InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl.Root) :
    InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl.sector
        (cyclotomicS1Perm r) = InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl.sector r ∧
      InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl.sector
        (cyclotomicS2Perm r) = InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl.sector r ∧
      InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl.sector
        (cyclotomicCoxeterPerm r) = InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl.sector r :=
  ⟨InfoGeometry.Algebra.Zorn.G2DoubleStarCyclotomicAction.simple_reflection_one_preserves_sector r,
    InfoGeometry.Algebra.Zorn.G2DoubleStarCyclotomicAction.simple_reflection_two_preserves_sector r,
    InfoGeometry.Algebra.Zorn.G2DoubleStarCyclotomicAction.coxeter_preserves_sector r⟩

/-- Combined structural packet: nuclear grade-one weights coexist with the
exceptional Artin/cyclotomic invariants, without identifying carriers. -/
theorem nuclear_g2_artin_structural_packet
    {ι A : Type*} [DecidableEq ι] [Ring A] [Algebra ℝ A]
    (car : QuasiparticleCAR ι A) (i : ι)
    (ρ : G2SpinOperatorLift)
    (r : InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl.Root) :
    (QuasiparticleCAR.comm (balancedOccupationCartan car i) (car.adag i) = car.adag i ∧
      QuasiparticleCAR.comm (balancedOccupationCartan car i) (car.a i) = -car.a i) ∧
    ((ρ.Bs * ρ.Bl) ^ 6 = -1 ∧ (ρ.Bs * ρ.Bl) ^ 12 = 1) ∧
    InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl.sector
        (cyclotomicCoxeterPerm r) = InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl.sector r :=
  ⟨nuclear_balanced_weight_packet car i,
    ⟨ρ.coxeter_pow_six_eq_neg_one, ρ.spin_coxeter_pow_twelve⟩,
    InfoGeometry.Algebra.Zorn.G2DoubleStarCyclotomicAction.coxeter_preserves_sector r⟩

/-! ## Galois-preserving nuclear extension -/

universe u
variable {G : Type u} [InfoGeometry.Canonical.BostConnesGalois.GaloisActionData G]

/-- The supplied arithmetic Galois action changes only the cyclotomic index,
so all currently owned nuclear charge/spin readouts are exactly preserved. -/
theorem galois_preserves_nuclear_charge_spin
    (g : G) (x : ArithmeticNuclearState) :
    (galoisExtendedAction g x).1.twoJ = x.1.twoJ ∧
      (galoisExtendedAction g x).1.twoT3 = x.1.twoT3 ∧
      (galoisExtendedAction g x).1.occupationNumber = x.1.occupationNumber ∧
      (galoisExtendedAction g x).1.quasiparticleParity = x.1.quasiparticleParity :=
  galoisExtendedAction_preservation_packet g x

end InfoGeometry.Physics.NuclearExceptionalArtinGaloisBridge

end noncomputable section
