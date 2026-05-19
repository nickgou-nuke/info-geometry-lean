import Mathlib
import InfoGeometry.Thermo.FromBregman
import InfoGeometry.Thermo.Gibbs
import InfoGeometry.Thermo.ThermodynamicIdentities
import InfoGeometry.Thermo.SplitChiralPolarizationBasis
import InfoGeometry.Arithmetic.ZetaSouriauComplexLift
import InfoGeometry.Arithmetic.PrimeBooleanCube
import InfoGeometry.Arithmetic.PrimeBitWittenIndex
import InfoGeometry.Probability.HomologicalProbability
import InfoGeometry.Canonical.BogoliubovFockSuper
import InfoGeometry.Canonical.PrimeVirasoroSugawara
import InfoGeometry.Arithmetic.CompletedZetaSouriauDInfinityThermodynamics
import InfoGeometry.External.Virasoro.HeisenbergAlgebra
import InfoGeometry.External.Virasoro.AffineKacMoody
import InfoGeometry.External.Virasoro.ChiralProduct
import InfoGeometry.External.Virasoro.FockSpaceSugawara
import InfoGeometry.OperatorAlgebra.FiveGradeClosureSymmetry
import InfoGeometry.Canonical.ConformalAlgebra
import InfoGeometry.Krein.DoubledSpace

/-!
# InfoGeometry.Arithmetic.PrimonChiralSouriauThermodynamics

Native chiral Souriau thermodynamics for the finite primon gas.

This module keeps the proof surface finite and algebraic:

* chiral cone coordinates are taken from the split-temperature lift;
* prime-register particle counts are taken from the finite prime-bit carrier;
* the hyperbolic Bogoliubov bracket closure is imported from the canonical
  projector-super algebra;
* no sockets, certificates, or CFT central-charge claims are introduced here.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimonChiralSouriauThermodynamics

open InfoGeometry.Thermo.SplitChiralPolarizationBasis
open InfoGeometry.Arithmetic.ZetaSouriauComplexLift
open InfoGeometry.Arithmetic.ZetaSouriauComplexLift.PrimeSpecialization
open InfoGeometry.Arithmetic.PrimeBitWittenIndex
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Krein
open InfoGeometry.Thermo
open InfoGeometry.Convex
open VirasoroProject.HeisenbergAlgebra

/-! ## 1. Chiral cone coordinates -/

/-- Chiral cone angle extracted from the split temperature. -/
@[rep_depth thermo]
def chiralConeAngle (s : ℂ) : ℝ :=
  (splitTemperature s).tau

/-- The chiral cone angle is the imaginary part of the complex temperature. -/
@[simp, rep_depth thermo]
theorem chiralConeAngle_eq_im (s : ℂ) :
    chiralConeAngle s = s.im := by
  rfl

/-- Hyperbolic Bogoliubov parameter obtained from the chiral cone angle. -/
@[rep_depth thermo]
def chiralBogoliubovParams (s : ℂ) : HyperbolicMixingParams :=
  HyperbolicMixingParams.ofAngle (chiralConeAngle s)

/-! ## 2. Particle numbers on the finite prime carrier -/

/-- The prime-register particle number is its finite cardinality. -/
@[simp, rep_depth thermo]
theorem primeRegister_fermionNumber_eq_card (P : PrimeRegister) :
    fermionNumber P = P.primes.card := by
  rfl

/-- The occupied prime-state particle number is its occupied cardinality. -/
@[simp, rep_depth thermo]
theorem primeState_fermionNumberOfState_eq_card
    (P : PrimeRegister) (ψ : PrimeBitState P) :
    fermionNumberOfState P ψ = (occupiedPrimeSet P ψ).card := by
  rfl

/-! ## 3. Full thermodynamic equations -/

/-- Finite primon partition readout. -/
@[simp, rep_depth thermo]
def primonPartition (P : PrimeRegister) (s : ℂ) : ℂ :=
  PrimeSpecialization.finitePrimeBosonPartition P s

/-- Finite primon Massieu readout. -/
@[simp, rep_depth thermo]
def primonMassieu (P : PrimeRegister) (s : ℂ) : ℂ :=
  PrimeSpecialization.finitePrimeMassieu P s

/-- Finite primon free-energy readout. -/
@[simp, rep_depth thermo]
def primonFreeEnergy (P : PrimeRegister) (s : ℂ) : ℂ :=
  PrimeSpecialization.finitePrimeFreeEnergy P s

/-- Finite primon grand-potential readout. -/
@[simp, rep_depth thermo]
def primonGrandPotential (P : PrimeRegister) (s : ℂ) : ℂ :=
  PrimeSpecialization.finitePrimeGrandPotential P s

/-- The finite primon Massieu readout is the logarithm of the partition. -/
@[simp, rep_depth thermo]
theorem primonMassieu_eq_log_partition (P : PrimeRegister) (s : ℂ) :
    primonMassieu P s = Complex.log (primonPartition P s) := by
  rfl

/-- The finite primon free energy is the negative logarithm of the partition. -/
@[simp, rep_depth thermo]
theorem primonFreeEnergy_eq_neg_log_partition (P : PrimeRegister) (s : ℂ) :
    primonFreeEnergy P s = -Complex.log (primonPartition P s) := by
  rfl

/-- The finite primon free energy is the negative Massieu potential. -/
@[simp, rep_depth thermo]
theorem primonFreeEnergy_eq_neg_massieu (P : PrimeRegister) (s : ℂ) :
    primonFreeEnergy P s = -primonMassieu P s := by
  rfl

/-- The finite primon grand potential is `-s⁻¹` times the Massieu potential. -/
@[simp, rep_depth thermo]
theorem primonGrandPotential_eq_neg_inv_mul_massieu (P : PrimeRegister) (s : ℂ) :
    primonGrandPotential P s = -s⁻¹ * primonMassieu P s := by
  rfl

/-- The finite primon bosonic and signed fermionic partitions cancel to one. -/
@[rep_depth thermo]
theorem primon_boson_signed_partition_cancel
    (P : PrimeRegister) (s : ℂ)
    (h : ∀ p ∈ P.primes, 1 - modeWeight s primeEnergy zeroChemicalPotential p ≠ 0) :
    primonPartition P s * PrimeSpecialization.finitePrimeSignedPartition P s = 1 := by
  simpa [primonPartition, PrimeSpecialization.finitePrimeSignedPartition] using
    boson_mul_signedPartition_eq_one
      (modes := P.primes) (s := s) (E := primeEnergy) (μ := zeroChemicalPotential) h

/-- Finite primon thermodynamic equations bundled in one theorem. -/
@[rep_depth thermo]
theorem primonThermodynamicEquation
    (P : PrimeRegister) (s : ℂ)
    (h : ∀ p ∈ P.primes, 1 - modeWeight s primeEnergy zeroChemicalPotential p ≠ 0) :
      primonMassieu P s = Complex.log (primonPartition P s) ∧
      primonFreeEnergy P s = -Complex.log (primonPartition P s) ∧
      primonGrandPotential P s = -s⁻¹ * primonMassieu P s ∧
      primonPartition P s * PrimeSpecialization.finitePrimeSignedPartition P s = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using (primonMassieu_eq_log_partition P s)
  · simpa using (primonFreeEnergy_eq_neg_log_partition P s)
  · simpa using (primonGrandPotential_eq_neg_inv_mul_massieu P s)
  · exact primon_boson_signed_partition_cancel P s h

/-! ## 4. Möbius parity and Bregman divergence -/

/-- The Möbius value of the represented prime register is the fermion parity. -/
@[simp, rep_depth thermo]
theorem primonMobius_eq_fermionParity (P : PrimeRegister) :
    ArithmeticFunction.moebius (representedNat P) = fermionParity P := by
  exact mobius_representedNat_eq_fermionParity P

/-- The Möbius value of an occupied prime state is the occupied fermion parity. -/
@[simp, rep_depth thermo]
theorem primonMobiusOfState_eq_fermionParity
    (P : PrimeRegister) (ψ : PrimeBitState P) :
    ArithmeticFunction.moebius (representedNatOfState P ψ) =
      fermionParityOfState P ψ := by
  exact mobius_representedNatOfState_eq_fermionParity P ψ

/-- The completed-zeta Bregman readout vanishes on the diagonal. -/
@[simp, rep_depth thermo]
theorem completedZetaBregman_self_eq_zero
    (Phi gradPhi : ℂ → ℂ) (s : ℂ) :
    CompletedZetaSouriauDInfinityThermodynamics.completedZetaBregman
      Phi gradPhi s s = 0 := by
  exact CompletedZetaSouriauDInfinityThermodynamics.completedZetaBregman_self_eq_zero
    Phi gradPhi s

/-- The complex thermodynamic Bregman readout vanishes on the diagonal. -/
@[simp, rep_depth thermo]
theorem complexBregman_self_eq_zero
    (Phi gradPhi : ℂ → ℂ) (s : ℂ) :
    bregman Phi gradPhi s s = 0 := by
  exact bregman_self_eq_zero Phi gradPhi s

/-! ## 5. Completed-zeta symmetry and the concrete `D_∞`-style image -/

/-- The functional reflection is an involution. -/
@[simp, rep_depth thermo]
theorem completedFunctionalReflection_involutive (s : ℂ) :
    CompletedZetaSouriauDInfinityThermodynamics.functionalReflection
      (CompletedZetaSouriauDInfinityThermodynamics.functionalReflection s) = s := by
  exact
    (CompletedZetaSouriauDInfinityThermodynamics.functionalReflection_involutive (s := s))

/-- Conjugation is an involution on the completed-zeta symmetry plane. -/
@[simp, rep_depth thermo]
theorem completedConjugationReflection_involutive (s : ℂ) :
    CompletedZetaSouriauDInfinityThermodynamics.conjugationReflection
      (CompletedZetaSouriauDInfinityThermodynamics.conjugationReflection s) = s := by
  exact
    (CompletedZetaSouriauDInfinityThermodynamics.conjugationReflection_involutive (s := s))

/-- The antiunitary reflection is an involution. -/
@[simp, rep_depth thermo]
theorem completedAntiunitaryReflection_involutive (s : ℂ) :
    CompletedZetaSouriauDInfinityThermodynamics.antiunitaryCriticalReflection
      (CompletedZetaSouriauDInfinityThermodynamics.antiunitaryCriticalReflection s) = s := by
  exact
    (CompletedZetaSouriauDInfinityThermodynamics.antiunitaryCriticalReflection_involutive
      (s := s))

/-- The reflection and conjugation commute on the concrete completed-zeta plane. -/
@[rep_depth thermo]
theorem completedFunctional_conjugation_commute (s : ℂ) :
    CompletedZetaSouriauDInfinityThermodynamics.functionalReflection
      (CompletedZetaSouriauDInfinityThermodynamics.conjugationReflection s) =
      CompletedZetaSouriauDInfinityThermodynamics.conjugationReflection
        (CompletedZetaSouriauDInfinityThermodynamics.functionalReflection s) := by
  exact
    (CompletedZetaSouriauDInfinityThermodynamics.functional_conjugation_commute (s := s))

/-- The completed-zeta antiunitary fixed locus is the critical line. -/
@[rep_depth thermo]
theorem completedAntiunitaryReflection_fixed_iff_criticalLine (s : ℂ) :
    s = CompletedZetaSouriauDInfinityThermodynamics.antiunitaryCriticalReflection s ↔
      CompletedZetaSouriauDInfinityThermodynamics.CriticalLine s := by
  simpa [CompletedZetaSouriauDInfinityThermodynamics.antiunitaryCriticalReflection] using
    (CompletedZetaSouriauDInfinityThermodynamics.fixed_antiunitaryCriticalReflection_iff_criticalLine
      (s := s))

/-- The concrete completed-zeta finite symmetry preserves the critical line. -/
@[rep_depth thermo]
theorem completedZetaKleinAct_preserves_criticalLine
    (g : CompletedZetaSouriauDInfinityThermodynamics.CompletedZetaKleinSymmetry) {s : ℂ}
    (hs : CompletedZetaSouriauDInfinityThermodynamics.CriticalLine s) :
    CompletedZetaSouriauDInfinityThermodynamics.CriticalLine
      (CompletedZetaSouriauDInfinityThermodynamics.completedZetaKleinAct g s) := by
  exact CompletedZetaSouriauDInfinityThermodynamics.completedZetaKleinAct_preserves_criticalLine
    g hs

/-- The concrete completed-zeta finite symmetry is involutive. -/
@[simp, rep_depth thermo]
theorem completedZetaKleinAct_involutive
    (g : CompletedZetaSouriauDInfinityThermodynamics.CompletedZetaKleinSymmetry) (s : ℂ) :
    CompletedZetaSouriauDInfinityThermodynamics.completedZetaKleinAct g
      (CompletedZetaSouriauDInfinityThermodynamics.completedZetaKleinAct g s) = s := by
  exact CompletedZetaSouriauDInfinityThermodynamics.completedZetaKleinAct_involutive g s

/-! ## 6. Imported Virasoro closure -/

/--
The imported Virasoro algebra closes on the standard generators: the `L_n`
bracket stays in the Virasoro span, and the central generator commutes with all
elements.
-/
@[rep_depth thermo]
theorem primonVirasoroClosure (n m : ℤ) :
    (⁅VirasoroProject.VirasoroAlgebra.lgen ℂ n,
        VirasoroProject.VirasoroAlgebra.lgen ℂ m⁆ =
        (n - m : ℂ) • VirasoroProject.VirasoroAlgebra.lgen ℂ (n + m) +
          if n + m = 0 then
            ((n^3 - n : ℂ) / 12) • VirasoroProject.VirasoroAlgebra.cgen ℂ
          else 0) ∧
    (⁅VirasoroProject.VirasoroAlgebra.cgen ℂ,
        VirasoroProject.VirasoroAlgebra.lgen ℂ n⁆ = 0) ∧
    (⁅VirasoroProject.VirasoroAlgebra.cgen ℂ,
        VirasoroProject.VirasoroAlgebra.cgen ℂ⁆ = 0) := by
  constructor
  · exact (VirasoroProject.VirasoroAlgebra.lgen_bracket (𝕜 := ℂ) n m)
  constructor
  · exact
      (VirasoroProject.VirasoroAlgebra.cgen_bracket (𝕜 := ℂ)
        (VirasoroProject.VirasoroAlgebra.lgen ℂ n))
  · exact
      (VirasoroProject.VirasoroAlgebra.cgen_bracket (𝕜 := ℂ)
        (VirasoroProject.VirasoroAlgebra.cgen ℂ))

/-- The imported chiral Virasoro product closes by the componentwise bracket. -/
@[rep_depth thermo]
theorem primonChiralVirasoroClosure (n m : ℤ) :
    ⁅VirasoroProject.ChiralVirasoro.lgenLeft (𝕜 := ℂ) n,
      VirasoroProject.ChiralVirasoro.lgenLeft (𝕜 := ℂ) m⁆ =
      VirasoroProject.ChiralVirasoro.inLeft
        (⁅VirasoroProject.VirasoroAlgebra.lgen ℂ n,
          VirasoroProject.VirasoroAlgebra.lgen ℂ m⁆) ∧
    ⁅VirasoroProject.ChiralVirasoro.lgenRight (𝕜 := ℂ) n,
      VirasoroProject.ChiralVirasoro.lgenRight (𝕜 := ℂ) m⁆ =
      VirasoroProject.ChiralVirasoro.inRight
        (⁅VirasoroProject.VirasoroAlgebra.lgen ℂ n,
          VirasoroProject.VirasoroAlgebra.lgen ℂ m⁆) ∧
    ⁅VirasoroProject.ChiralVirasoro.lgenLeft (𝕜 := ℂ) n,
      VirasoroProject.ChiralVirasoro.lgenRight (𝕜 := ℂ) m⁆ = 0 ∧
    ⁅VirasoroProject.ChiralVirasoro.cgenLeft (𝕜 := ℂ),
      VirasoroProject.ChiralVirasoro.cgenRight (𝕜 := ℂ)⁆ = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using (VirasoroProject.ChiralVirasoro.lgenLeft_bracket (𝕜 := ℂ) n m)
  · simpa using (VirasoroProject.ChiralVirasoro.lgenRight_bracket (𝕜 := ℂ) n m)
  · simpa using
      (VirasoroProject.ChiralVirasoro.inLeft_bracket_inRight (𝕜 := ℂ)
        (VirasoroProject.VirasoroAlgebra.lgen ℂ n)
        (VirasoroProject.VirasoroAlgebra.lgen ℂ m))
  · simpa using (VirasoroProject.ChiralVirasoro.cgenLeft_bracket_cgenRight (𝕜 := ℂ))

/-- The imported affine Kac-Moody current bracket closes on the prime packet. -/
@[rep_depth thermo]
theorem primonAffineKacMoodyClosure
    {PrimeLabel Field Coeff Finite Alg : Type*}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    (P : InfoGeometry.Canonical.PrimeVirasoroSugawara.PrimeSugawaraVirasoroPacket
      PrimeLabel Field Coeff Finite Alg)
    (m n : ℤ) (X Y : Finite) :
    ⁅P.affineVirasoro.affine.Current m X, P.affineVirasoro.affine.Current n Y⁆ =
      P.affineVirasoro.affine.Current (m + n) ⁅X, Y⁆ +
        ((m : ℝ) * P.affineVirasoro.affine.killingForm X Y) •
          (if m + n = 0 then P.affineVirasoro.affine.kCentral else 0) := by
  exact P.affine_current_mode_bracket m n X Y

/-- The imported Sugawara construction acts as the identity on the Virasoro central element. -/
@[rep_depth thermo]
theorem primonSugawaraCentralElementAct_eq_id (α : ℂ)
    (v : VirasoroProject.ChargedFockSpace ℂ α) :
    VirasoroProject.ChargedFockSpace.sugawaraRepresentation ℂ α (.cgen ℂ) v = v := by
  exact
    (VirasoroProject.ChargedFockSpace.sugawaraRepresentation_cgen_apply
      (𝕜 := ℂ) α v)

/-- The imported Sugawara construction gives the vacuum its expected `L₀` energy. -/
@[rep_depth thermo]
theorem primonSugawaraVacuumEnergy (α : ℂ) :
    VirasoroProject.ChargedFockSpace.sugawaraRepresentation ℂ α (.lgen ℂ 0)
      (VirasoroProject.ChargedFockSpace.vacuum ℂ α) =
      (α^2 / 2) • VirasoroProject.ChargedFockSpace.vacuum ℂ α := by
  exact
    (VirasoroProject.ChargedFockSpace.sugawaraRepresentation_lgen_zero_apply_vacuum
      (𝕜 := ℂ) α)

/-- The imported Heisenberg generators `K` and `J₀` are central. -/
@[rep_depth thermo]
theorem primonHeisenbergCentral_kgen_jgen_zero
    (Z : VirasoroProject.HeisenbergAlgebra ℂ) :
    ⁅VirasoroProject.HeisenbergAlgebra.kgen ℂ, Z⁆ = 0 ∧
      ⁅VirasoroProject.HeisenbergAlgebra.jgen ℂ 0, Z⁆ = 0 := by
  exact VirasoroProject.HeisenbergAlgebra.central_kgen_jgen_zero ℂ Z

/-- A Heisenberg generator `Jₙ` is central iff it is the zero mode. -/
@[rep_depth thermo]
theorem primonHeisenbergJgen_mem_center_iff (n : ℤ) :
    VirasoroProject.HeisenbergAlgebra.jgen ℂ n ∈
      LieAlgebra.center ℂ (VirasoroProject.HeisenbergAlgebra ℂ) ↔ n = 0 := by
  exact VirasoroProject.HeisenbergAlgebra.jgen_mem_center_iff (𝕜 := ℂ) n

/-- The center of the Heisenberg algebra is exactly the span of `K` and `J₀`. -/
@[rep_depth thermo]
set_option maxHeartbeats 500000 in
theorem primonHeisenbergCenter_eq_span_kgen_jgen_zero :
    LieAlgebra.center ℂ (VirasoroProject.HeisenbergAlgebra ℂ) =
      Submodule.span ℂ
        ({VirasoroProject.HeisenbergAlgebra.kgen ℂ,
            VirasoroProject.HeisenbergAlgebra.jgen ℂ 0} :
          Set (VirasoroProject.HeisenbergAlgebra ℂ)) := by
  classical
  apply le_antisymm
  · intro Z hZ
    have hcentralR : ∀ x : VirasoroProject.HeisenbergAlgebra ℂ, ⁅x, Z⁆ = 0 := by
      simpa [LieAlgebra.center] using hZ
    have hcentral : ∀ x : VirasoroProject.HeisenbergAlgebra ℂ, ⁅Z, x⁆ = 0 := by
      intro x
      have hx : -⁅Z, x⁆ = 0 := by
        simpa [lie_skew] using (hcentralR x)
      exact neg_eq_zero.mp hx
    refine (VirasoroProject.HeisenbergAlgebra.basisJK ℂ).mem_span_image.mpr ?_
    intro i hi
    by_cases hi0 : i = none
    · simp [hi0]
    · by_cases hi1 : i = some 0
      · simp [hi1]
      · rcases i with _ | n
        · exact (hi0 rfl).elim
        · have hn : n ≠ 0 := by
            intro h
            apply hi1
            simp [h]
          have hsum :
              ∑ x ∈ ((VirasoroProject.HeisenbergAlgebra.basisJK ℂ).repr Z).support,
                ((VirasoroProject.HeisenbergAlgebra.basisJK ℂ).repr Z) x •
                  ⁅VirasoroProject.HeisenbergAlgebra.basisJK ℂ x,
                    VirasoroProject.HeisenbergAlgebra.jgen ℂ (-n)⁆ = 0 := by
            have h := hcentral (VirasoroProject.HeisenbergAlgebra.jgen ℂ (-n))
            rw [← (VirasoroProject.HeisenbergAlgebra.basisJK ℂ).linearCombination_repr Z] at h
            rw [Finsupp.linearCombination_apply] at h
            rw [Finsupp.sum] at h
            simpa [sum_lie] using h
          have h0 :
              ∀ b ∈ ((VirasoroProject.HeisenbergAlgebra.basisJK ℂ).repr Z).support,
                b ≠ some n →
                  ((VirasoroProject.HeisenbergAlgebra.basisJK ℂ).repr Z) b •
                    ⁅VirasoroProject.HeisenbergAlgebra.basisJK ℂ b,
                      VirasoroProject.HeisenbergAlgebra.jgen ℂ (-n)⁆ = 0 := by
            intro b hb hne
            rcases b with _ | m
            · simp [VirasoroProject.HeisenbergAlgebra.basisJK_none, hne]
            · have hm : m ≠ n := by
                intro hmn
                apply hne
                simp [hmn]
              simp [VirasoroProject.HeisenbergAlgebra.basisJK_some, VirasoroProject.HeisenbergAlgebra.lie_jgen, hm, hn]
          have h1 :
              some n ∉ ((VirasoroProject.HeisenbergAlgebra.basisJK ℂ).repr Z).support →
                ((VirasoroProject.HeisenbergAlgebra.basisJK ℂ).repr Z) (some n) •
                  ⁅VirasoroProject.HeisenbergAlgebra.basisJK ℂ (some n),
                    VirasoroProject.HeisenbergAlgebra.jgen ℂ (-n)⁆ = 0 := by
            intro hnot
            simp [Finsupp.mem_support_iff] at hnot
            simp [VirasoroProject.HeisenbergAlgebra.basisJK_some, VirasoroProject.HeisenbergAlgebra.lie_jgen, hnot, hn]
          have hsingle :
              ((VirasoroProject.HeisenbergAlgebra.basisJK ℂ).repr Z) (some n) •
                ⁅VirasoroProject.HeisenbergAlgebra.basisJK ℂ (some n),
                  VirasoroProject.HeisenbergAlgebra.jgen ℂ (-n)⁆ = 0 := by
            have hsum' := hsum
            rw [Finset.sum_eq_single (some n) h0 h1] at hsum'
            simpa using hsum'
          have hk : VirasoroProject.HeisenbergAlgebra.kgen ℂ ≠ 0 := by
            simpa [VirasoroProject.HeisenbergAlgebra.kgen_eq'] using
              (VirasoroProject.HeisenbergAlgebra.basisJK ℂ).ne_zero none
          have hscalar :
              (n : ℂ) * (VirasoroProject.HeisenbergAlgebra.basisJK ℂ).repr Z (some n) = 0 := by
            have hsingle' := hsingle
            simpa [VirasoroProject.HeisenbergAlgebra.basisJK_some,
              VirasoroProject.HeisenbergAlgebra.lie_jgen, hn,
              smul_smul, mul_comm, mul_left_comm, mul_assoc] using hsingle'
          exact by
            exact (mul_eq_zero.mp hscalar).resolve_left hn
  · intro hZ
    refine Submodule.span_le.mpr ?_
    intro x hx
    rcases hx with rfl | rfl
    · exact (VirasoroProject.HeisenbergAlgebra.central_kgen_jgen_zero ℂ x).1
    · exact (VirasoroProject.HeisenbergAlgebra.jgen_mem_center_iff (𝕜 := ℂ) 0).2 rfl

/-- The imported five-grade closure keeps grade zero stable and Cartan-decomposed. -/
@[rep_depth thermo]
theorem primonFiveGradeCartanDecomposition
    {L : Type*} [AddCommGroup L] [Module ℝ L]
    (G : InfoGeometry.OperatorAlgebra.FiveGradeClosureSymmetry L)
    {x : L}
    (hx : x ∈ G.gZero) :
    G.closure.SetwiseStable G.gZero ∧
      G.closure.fixedPart x ∈ G.gZero ∧
      G.closure.antiPart x ∈ G.gZero ∧
      G.closure.fixedPart x + G.closure.antiPart x = x := by
  exact ⟨G.zero_setwise_stable, G.zero_cartan_decomposition hx⟩

/-- The imported conformal Cartan split gives the generator decomposition. -/
@[rep_depth thermo]
theorem primonGeneratorCartanDecomposition
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (CBA : InfoGeometry.Canonical.ConformalAlgebra.ConformalBeliefAlgebra E)
    (hCartan : CBA.GeneratorCartanDecomposition) :
    CBA.IsVolumePreservingPart CBA.M ∧ CBA.IsWeylDilationPart CBA.D := by
  exact CBA.cartan_generator_split hCartan

/-! ## 3. Chiral Bogoliubov bracket closure -/

section Bogoliubov

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
The chiral cone parameter induces the finite projector-super algebra closure:
the odd-odd anticommutator is hyperbolic, while the mixed commutator vanishes.
-/
@[rep_depth thermo]
theorem chiralCone_bogoliubov_projector_superalgebra
    (s : ℂ) :
    fockAnticommutator (E := E)
        (bogoliubovAnnihilation (E := E) (chiralBogoliubovParams s))
        (bogoliubovCreation (E := E) (chiralBogoliubovParams s))
      =
      (Real.sinh (2 * chiralConeAngle s)) •
        ContinuousLinearMap.id ℝ (DoubledSpace E)
    ∧
    fockCommutator (E := E)
        (bogoliubovAnnihilation (E := E) (chiralBogoliubovParams s))
        (bogoliubovCreation (E := E) (chiralBogoliubovParams s)) = 0 := by
  refine ⟨?_, ?_⟩
  · simpa [chiralBogoliubovParams, chiralConeAngle] using
      (anticommutator_ofAngle_projector_model (E := E)
        (θ := chiralConeAngle s))
  · simpa [chiralBogoliubovParams, chiralConeAngle] using
      (commutator_bogoliubov_projector_model (E := E)
        (B := HyperbolicMixingParams.ofAngle (chiralConeAngle s)))

end Bogoliubov

/-! ## 4. Finite primon gas readout -/

/-- The finite primon gas particle count is the number of occupied primes. -/
@[simp, rep_depth thermo]
theorem primeGasParticleNumber_eq_fermionNumber (P : PrimeRegister) :
    PrimeBitWittenIndex.fermionNumber P = P.primes.card := by
  rfl

/-- The finite primon gas occupancy count is the occupied-set cardinality. -/
@[simp, rep_depth thermo]
theorem primeGasParticleNumberOfState_eq_fermionNumberOfState
    (P : PrimeRegister) (ψ : PrimeBitState P) :
    PrimeBitWittenIndex.fermionNumberOfState P ψ =
      (occupiedPrimeSet P ψ).card := by
  rfl

/-! ## 5. Real Legendre/KL/Bregman thermodynamics -/

section FiniteLegendre

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-- Real Bregman free energy and partition identities for a finite Legendre lane. -/
@[rep_depth thermo]
theorem primonLegendreThermodynamicEquation
    (L : LegendrePotential) (θ0 : ℝ) (θ : Ω → ℝ) (ε : ℝ)
    (hε : ε ≠ 0) :
    freeEnergyFromBregman (L := L) θ0 θ ε =
      internalEnergy (energyFromBregman (L := L) θ0 θ) ε -
        ε * shannonEntropy (energyFromBregman (L := L) θ0 θ) ε ∧
    freeEnergyDivergence (L := L) θ0 θ ε =
      freeEnergyFromBregman (L := L) θ0 θ ε ∧
    partitionDivergence (L := L) θ0 θ ε =
      Z (E := energyFromBregman (L := L) θ0 θ) ε ∧
    gibbsProbFromBregman (L := L) θ0 θ ε =
      gibbsProb (energyFromBregman (L := L) θ0 θ) ε ∧
    (∀ ω : Ω, 0 ≤ gibbsProbFromBregman (L := L) θ0 θ ε ω) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact freeEnergyFromBregman_eq_internal_sub_scale_entropy
      (L := L) θ0 θ ε hε
  · exact freeEnergyDivergence_eq_freeEnergyFromBregman (L := L) θ0 θ ε
  · exact partitionDivergence_eq_Z (L := L) θ0 θ ε
  · rfl
  · intro ω
    exact gibbsProbFromBregman_nonneg (L := L) θ0 θ ε ω

/-! ## 6. KL/Bregman identity -/

/-- The Legendre/KL parameter divergence is exactly the Bregman gap. -/
@[simp, rep_depth thermo]
theorem primonKL_eq_bregman
    (L : LegendrePotential) (θ θ' : ℝ) :
    InfoGeometry.ConvexDuality.KL_param L.f θ θ' = L.bregman θ' θ := by
  exact KL_param_eq_bregman_energy (L := L) θ θ'

end FiniteLegendre

/-! ## 7. Binary lattice / Klein bottle parity readout -/

/--
Finite Boolean-cube parity and Möbius readout on the prime lattice.

The orientifold/Klein bottle layer remains a separate hypothesis surface; the
native theorem content here is the finite binary-lattice parity law.
-/
@[rep_depth thermo]
theorem primeBooleanCubeParityEquation
    (P : PrimeRegister) (v : PrimeBooleanCube.Vertex P) :
    PrimeBooleanCube.globalChirality P v.val = PrimeBooleanCube.fermionParity v ∧
    ArithmeticFunction.moebius (PrimeBooleanCube.representedNat v) =
      PrimeBooleanCube.fermionParity v := by
  refine ⟨?_, ?_⟩
  · exact PrimeBooleanCube.globalChirality_vertex_eq_fermionParity P v
  · exact PrimeBooleanCube.mobius_representedNat_eq_fermionParity P v

/-! ## 8. Collected native closure -/

/--
Collected native closure for the primon lane.

This packages the pieces already proved in their native owner files:

* the completed-zeta finite symmetry preserves the critical line;
* the five-graded homological pipeline has numerical shadow `5`;
* the prime Sugawara finite specialization reads off the cardinality.
-/
@[rep_depth thermo]
theorem primonCollectedNativeClosure
    {G : Type*} (bracket : G → G → G)
    {PrimeLabel Field Coeff Finite Alg : Type*}
    [AddCommGroup Finite] [Module ℝ Finite] [LieRing Finite] [LieAlgebra ℝ Finite]
    [AddCommGroup Alg] [Module ℝ Alg] [LieRing Alg] [LieAlgebra ℝ Alg]
    (P : InfoGeometry.Canonical.PrimeVirasoroSugawara.PrimeSugawaraVirasoroPacket
      PrimeLabel Field Coeff Finite Alg)
    (S : Finset PrimeLabel)
    (hlevel : P.affineVirasoro.level = 1)
    (hdim : P.affineVirasoro.finiteDimension = (S.card : ℝ))
    (hdual : P.affineVirasoro.dualCoxeterNumber = 0)
    (s : ℂ)
    (hs : CompletedZetaSouriauDInfinityThermodynamics.CriticalLine s) :
    CompletedZetaSouriauDInfinityThermodynamics.CriticalLine
      (CompletedZetaSouriauDInfinityThermodynamics.completedZetaKleinAct
        CompletedZetaSouriauDInfinityThermodynamics.CompletedZetaKleinSymmetry.functional s)
    ∧
    ((InfoGeometry.Probability.Homological.fiveGradedHomologicalPipeline G bracket).toNumericalShadow =
      fun _ => 5)
    ∧
    P.affineVirasoro.centralCharge = (S.card : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      CompletedZetaSouriauDInfinityThermodynamics.completedZetaKleinAct_preserves_criticalLine
        CompletedZetaSouriauDInfinityThermodynamics.CompletedZetaKleinSymmetry.functional hs
  · rfl
  · exact
      InfoGeometry.Canonical.PrimeVirasoroSugawara.centralCharge_eq_card_of_level_one_dualCoxeter_zero
        P S hlevel hdim hdual

end InfoGeometry.Arithmetic.PrimonChiralSouriauThermodynamics
