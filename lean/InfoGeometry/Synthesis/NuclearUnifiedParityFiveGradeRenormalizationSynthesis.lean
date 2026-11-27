/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic
import InfoGeometry.Synthesis.NuclearFiveGradeSuperGrassmannianIntertwiner
import InfoGeometry.Synthesis.QCDColorConfinementParafermionSynthesis
import InfoGeometry.Synthesis.HelicityNuclearKProjectionSynthesis
import InfoGeometry.Synthesis.FeshbachRPASchurRenormalizationFlow
import InfoGeometry.OperatorAlgebra.PeirceSpine.NuclearThoulessDensity
import InfoGeometry.Physics.NuclearKohnShamPeirceBridge
import InfoGeometry.Physics.NuclearInternalExternalParityFactorization
import InfoGeometry.Physics.NuclearChiralMengBridge
import InfoGeometry.Physics.MengChPSelectionRules
import InfoGeometry.Physics.QCDChiralStructuralBridge
import InfoGeometry.Physics.NuclearWignerSupermultipletSymmetry
import InfoGeometry.Physics.NuclearKleinParameterBundle
import InfoGeometry.Physics.NuclearKleinSpectralDescentBridge
import InfoGeometry.Physics.NuclearCartanProjectorParityBridge
import InfoGeometry.Physics.NuclearWignerDensityProjectorBridge
import InfoGeometry.Physics.NuclearCl55CartanParityDictionary
import InfoGeometry.Physics.NuclearFiveGradeParity

/-!
# Unified Synthesis: Nuclear Parity, Five-Graded Intertwiners, QCD Parafermions, and Renormalization

Top-level Milestone M5 synthesis module soldering:
1. **Seam A** (`NuclearFiveGradeSuperGrassmannianIntertwiner`): concrete two-mode CAR–BdG–Soloviev
   5-grading ↔ Super-Grassmannian `(2|1)` OSp / `(2|3)` `Z2Z2ColorGrade` / Günaydin–Gürsey
   intertwiner and `32×32` `MatStage 5` Soloviev no-go boundary.
2. **Seam B** (`QCDColorConfinementParafermionSynthesis`): Zorn baryon / `Cl(5,5)` color singlet /
   Wigner `SU(4)` / `charge6` morphisms ↔ Temperley–Lieb `B3`, Fibonacci parafermions,
   `op^3 = op` defects, and Artin 12-fold monodromy, with explicit conditional 4D confinement
   hypotheses.
3. **Seam C** (`HelicityNuclearKProjectionSynthesis`): massless `U(1)` little-group helicity,
   massive Pauli–Lubanski / `OperatorZornSpinCasimirLift`, and `SDiff` helicity ↔ nuclear
   `RotationalBandhead`, `NuclearTaxonomyPacket`, `KParitySector`, and GDR multipoles.
4. **Seam D** (`FeshbachRPASchurRenormalizationFlow`): dual `NuclearPhononRPAAlgebra`
   reconciliation, discrete Feshbach/Schur/Krein elimination, and `kreinHyperbolicFlow`
   invariance of noncommutative `[a, b]` RPA defects ↔ Iwasawa scale conjugation and
   dilaton–Andreev RG flow, with explicit conditional continuum RG and spectral-gap hypotheses.
5. **Unified Substrate & R2/R3 Integration**:
   - Peirce/Krein Thouless and Kohn–Sham four-sector particle-hole / Gamow–Teller substrate
     (`NuclearThoulessDensity`, `NuclearKohnShamPeirceBridge`),
   - Uncollapsed four-way `FourParityCarrier` (`piOp`, `fermionOp`, `wmOp`, `mengParityOp`),
     triaxial ChP selection rules (`NuclearChiralMengBridge`, `MengChPSelectionRules`),
     structural `ℤ₂` chiral bridge (`QCDChiralStructuralBridge`), and Klein spectral descent
     (`NuclearKleinParameterBundle`, `NuclearKleinSpectralDescentBridge`),
   - Wigner `SU(4)` supermultiplet (`NuclearWignerSupermultipletSymmetry`, namespace
     `InfoGeometry.Physics.NuclearWignerSupermultiplet`),
   - R3 clean complementary owners (`NuclearCartanProjectorParityBridge`,
     `NuclearWignerDensityProjectorBridge`, `NuclearCl55CartanParityDictionary`,
     `NuclearFiveGradeParity`), grounded in Lean owner source while noting Auto-Ontology `:3001`
     index lag on recent `FourParity` declarations and live Alexandria `:8538` retrieval.
-/

set_option autoImplicit false

noncomputable section

namespace InfoGeometry.Synthesis.NuclearUnifiedParityFiveGradeRenormalizationSynthesis

open InfoGeometry.Synthesis.NuclearFiveGradeSuperGrassmannianIntertwiner
open InfoGeometry.Synthesis.QCDColorConfinementParafermionSynthesis
open InfoGeometry.Synthesis.HelicityNuclearKProjectionSynthesis
open InfoGeometry.Synthesis.FeshbachRPASchurRenormalizationFlow
open InfoGeometry.OperatorAlgebra.PeirceSpine
open InfoGeometry.Physics.NuclearInternalExternalParityFactorization
open InfoGeometry.Physics.NuclearChiralMengBridge
open InfoGeometry.Physics.NuclearWignerSupermultiplet
open scoped ScopedOpZornModule

/-! ## 1. Closed Non-Commutativity Witnesses (T16) -/

/-- Closed non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem block2_real_noncomm_witness :
    ∃ A B : Matrix (Fin 2) (Fin 2) ℝ, A * B ≠ B * A :=
  block2_real_exists_noncomm

/-- Closed non-commutativity witness on `Matrix (Fin 4) (Fin 4) ℝ`. -/
theorem m4r_noncomm_witness :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℝ, A * B ≠ B * A :=
  m4r_noncommutative_witness

/-- Closed non-commutativity witness on `Matrix (Fin 2) (Fin 2) ℂ` via isospin ladder `T₃, T₊`. -/
theorem m2c_isospin_noncomm_witness :
    isospin3 * isospinPlus ≠ isospinPlus * isospin3 := by
  intro heq
  have hcomm := isospin_comm_3_plus
  rw [heq, sub_self] at hcomm
  have h01 := congrFun (congrFun hcomm.symm 0) 1
  simp [isospinPlus, pauli1, pauli2] at h01

/-- Closed non-commutativity witness on `Module.End ℂ FourParityCarrier`. -/
theorem fourParityCarrier_k0_wm_noncomm_witness :
    k0Op * wmOp ≠ wmOp * k0Op :=
  four_parity_separation_and_compatibility.2.2.1.1

/-- Closed non-commutativity witness on `Module.End ℂ ChiralParitySpace`. -/
theorem chiralParitySpace_chiture_e2_noncomm_witness :
    triaxialChitureOp * triaxialMultipoleOp .electricTwo ≠
      triaxialMultipoleOp .electricTwo * triaxialChitureOp :=
  triaxialChitureOp_e2_noncomm

/-! ## 2. Unified Unconditional `Type*` Synthesis Packet & T17 Witness -/

/-- Unconditional `Type*` synthesis packet bundling finite algebraic data from Seams A–D,
the uncollapsed `FourParityCarrier` substrate, triaxial ChP involutions, Wigner `SU(4)`
supermultiplet generators, and discrete RPA defect witnesses without collapsing distinct
carriers or using `: Prop` aggregate constructors. -/
structure UnifiedParityFiveGradeSynthesisPacket : Type _ where
  seamA : NuclearFiveGradeSuperGrassmannianIntertwinerData
  seamB : ColorParafermionMorphismPacket 2
  seamC : HelicityToNuclearKPacket
  rpaA : InfoGeometry.Physics.NuclearOperatorSuperSoloviev.Block2 ℝ
  rpaB : InfoGeometry.Physics.NuclearOperatorSuperSoloviev.Block2 ℝ
  rpaDefect_noncomm : rpaA * rpaB ≠ rpaB * rpaA
  chpAlgebra : ChPInvolutions (Module.End ℂ ChiralParitySpace)
  parityCarrierZero : FourParityCarrier
  wignerCasimir : _root_.ChiralTensorRecoupling.SpinPair
  gamowTellerRaise : _root_.ChiralTensorRecoupling.SpinPair

/-- Zero-hypothesis constructive finite-model witness (`T17`) for
`UnifiedParityFiveGradeSynthesisPacket`. -/
def canonicalUnifiedParityFiveGradeSynthesisPacket :
    UnifiedParityFiveGradeSynthesisPacket where
  seamA := canonicalNuclearFiveGradeSuperGrassmannianIntertwiner
  seamB := canonicalColorParafermionMorphismPacket
  seamC := defaultHelicityToNuclearKPacket
  rpaA := rpaWitnessA
  rpaB := rpaWitnessB
  rpaDefect_noncomm := block2_real_noncomm_and_rpa_defect_witness.1
  chpAlgebra := triaxialChPInvolutions
  parityCarrierZero := 0
  wignerCasimir := wignerSU4Casimir
  gamowTellerRaise := gamowTellerPlus 0

/-! ## 3. Peirce/Krein Thouless, Kohn–Sham Four-Sector, and Wigner SU(4) Soldering -/

/-- Unconditional synthesis of the Peirce/Krein Thouless particle-hole algebra
(`NuclearThoulessDensity`), Kohn–Sham four-sector proton/neutron particle/hole & Gamow–Teller
operator resolution (`NuclearKohnShamPeirceBridge`), Wigner `SU(4)` supermultiplet algebra
(`NuclearWignerSupermultipletSymmetry`), rank-one density projector intertwining
(`NuclearWignerDensityProjectorBridge`), and Cartan `±2` alignment
(`NuclearCartanProjectorParityBridge`). -/
theorem unconditional_peirce_thouless_kohn_sham_wigner_synthesis
    {B : Type*} [Ring B] {P Pocc Pp Pn A C W M : B}
    (hP : P * P = P) (hOcc : Pocc * Pocc = Pocc)
    (hpp : Pp * Pp = Pp) (hnn : Pn * Pn = Pn)
    (hpn : Pp * Pn = 0) (hnp : Pn * Pp = 0)
    (hppOcc : Pp * Pocc = Pocc * Pp) (hnnOcc : Pn * Pocc = Pocc * Pn)
    {K Alg : Type*} [Field K] [CharZero K] [Ring Alg] [Algebra K Alg]
    (pt : InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.PauliTriple K Alg)
    (i : Fin 3) (j : Fin 3) (a15 : Fin 15) :
    (thoulessIdempotent P A C * thoulessIdempotent P A C = thoulessIdempotent P A C ∧
      evenGrade P (thoulessIdempotent P A C) = thoulessOccupation P A C ∧
      comm (ksbGenerator P A C) (ksbStationaryDensity P A C) = 0 ∧
      comm (InfoGeometry.OperatorAlgebra.PeirceSpine.isospinCharge Pp Pn)
        (isospinRaise Pp Pn W) = (2 : ℤ) • isospinRaise Pp Pn W ∧
      comm (InfoGeometry.OperatorAlgebra.PeirceSpine.isospinCharge Pp Pn)
        (isospinLower Pp Pn M) = -((2 : ℤ) • isospinLower Pp Pn M)) ∧
    (InfoGeometry.Physics.NuclearKohnShamPeirceBridge.thoulessDensity P A C *
        InfoGeometry.Physics.NuclearKohnShamPeirceBridge.thoulessDensity P A C =
        InfoGeometry.Physics.NuclearKohnShamPeirceBridge.thoulessDensity P A C ∧
      comm (InfoGeometry.Physics.NuclearKohnShamPeirceBridge.bogoliubovOperator P A C)
        (InfoGeometry.Physics.NuclearKohnShamPeirceBridge.selfConsistentDensity P A C) = 0 ∧
      InfoGeometry.Physics.NuclearKohnShamPeirceBridge.gamowTeller Pocc Pp Pn W *
        InfoGeometry.Physics.NuclearKohnShamPeirceBridge.gamowTeller Pocc Pp Pn W = 0 ∧
      comm Pocc (InfoGeometry.Physics.NuclearKohnShamPeirceBridge.gamowTeller Pocc Pp Pn W) =
        -InfoGeometry.Physics.NuclearKohnShamPeirceBridge.gamowTeller Pocc Pp Pn W) ∧
    (wignerSU4Casimir = (15 / 4 : ℂ) • (1 : _root_.ChiralTensorRecoupling.SpinPair) ∧
      InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.tensorBracket
        (InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen pt i 0)
        (InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen pt i 1) =
        pt.iUnit • InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4IsospinGen pt 2 ∧
      InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.tensorBracket
        (InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen pt 0 j)
        (InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4GamowTellerGen pt 1 j) =
        pt.iUnit • InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.su4SpinGen pt 2 ∧
      InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.pairBracket
        (wignerT 2) (gamowTellerPlus i) = gamowTellerPlus i ∧
      InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.twoNucleonSU4CasimirOf pt *
        InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.wignerPairing6AOf pt =
        (5 : K) • InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.wignerPairing6AOf pt ∧
      InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.twoNucleonSU4CasimirOf pt *
        InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.wignerPairing10SOf pt =
        (9 : K) • InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.wignerPairing10SOf pt ∧
      InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.twoNucleonSU4Casimir *
        InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.wignerPairing6A =
        (5 : ℂ) • InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.wignerPairing6A ∧
      InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.totalTwoNucleonGen a15 *
        InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.wignerPairing6A =
        InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.wignerPairing6A *
          InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.totalTwoNucleonGen a15) ∧
    (InfoGeometry.Physics.HestenesSpinDensityXpQuantization.densityMatrix isospinPlus =
        InfoGeometry.Physics.NuclearCartanProjectorParityBridge.isospinPositiveProjector ∧
      InfoGeometry.Physics.HestenesSpinDensityXpQuantization.rightDensityMatrix isospinPlus =
        InfoGeometry.Physics.NuclearCartanProjectorParityBridge.isospinNegativeProjector ∧
      InfoGeometry.Physics.NuclearCartanProjectorParityBridge.isospinPositiveProjector *
        InfoGeometry.Physics.NuclearCartanProjectorParityBridge.isospinNegativeProjector = 0 ∧
      isospin3 * isospinPlus - isospinPlus * isospin3 = isospinPlus) := by
  have hks := InfoGeometry.Physics.NuclearKohnShamPeirceBridge.stageDF43_operator_synthesis
    hP hOcc hpp hnn hpn hnp hppOcc hnnOcc (A := A) (C := C) (W := W) (M := M)
  have hwp := general_wigner_pairing_splitting pt
  have hw6 := wignerPairing6A_casimir_and_invariance a15
  have hdens := InfoGeometry.Physics.NuclearWignerDensityProjectorBridge.wigner_density_projector_packet
  refine ⟨⟨thoulessIdempotent_idempotent hP A C, evenGrade_thoulessIdempotent hP A C,
      ksbGenerator_comm_stationaryDensity hP A C,
      isospinCharge_comm_raise hpp hnn hnp,
      isospinCharge_comm_lower hpp hnn hpn⟩,
    ⟨hks.1, hks.2.2.2.2.1, hks.2.2.2.2.2.2.2.2.2.1, hks.2.2.2.2.2.2.2.2.2.2.2⟩,
    ⟨wigner_su4_casimir,
      gamowTeller_obstruction_generates_isospin pt i,
      gamowTeller_obstruction_generates_spin pt j,
      isospin3_comm_gamowTellerPlus i,
      hwp.1, hwp.2, hw6.1, hw6.2⟩,
    ⟨hdens.1, hdens.2.1, hdens.2.2.2.1, isospin_comm_3_plus⟩⟩

/-! ## 4. Uncollapsed Four-Way Parities, Chiral Meng, Klein Descent & Structural QCD ℤ₂ -/

/-- Unconditional R2 boundary theorem keeping all four commuting `FourParityCarrier` involutions
(`piOp`, `fermionOp`, `wmOp`, `mengParityOp`) strictly uncollapsed and pairwise distinct, linking
`HelicityToNuclearKPacket.toTaxonomyPacket.fourParityProj` (Seam C), `triaxialChPInvolutions` &
`MengChPSelectionRules.Multipole` (`E2`/`M1`/`E3`), `NuclearFiveGradeParity`,
`QCDChiralStructuralBridge`, `NuclearCl55CartanParityDictionary`, and
`NuclearKleinSpectralDescentBridge`. -/
theorem uncollapsed_four_parity_chp_klein_qcd_synthesis
    {ι : Type*} [DecidableEq ι]
    {A : Type*} [Ring A] [Algebra ℝ A]
    (car : InfoGeometry.Physics.NuclearQuasiparticleCAR.QuasiparticleCAR ι A) (i : ι)
    (P : InfoGeometry.Physics.NuclearOperatorSuperSoloviev.InternalParity A) (E0 E1 V W : A)
    (hE0 : P.IsEven E0) (hE1 : P.IsEven E1) (hV : P.IsOdd V) (hW : P.IsOdd W)
    {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    {T : A} (hT : T * T * T = T)
    (H5 : InfoGeometry.Physics.NuclearSuperSolovievPeirceBridge.PeirceCompatibleBlock T)
    (Hklein : InfoGeometry.Physics.NuclearKleinParameterBundle.KleinEquivariantHamiltonian P)
    (Rklein : InfoGeometry.Physics.NuclearOperatorSchurComplement.ResolventData A)
    (cell : InfoGeometry.Physics.NuclearKleinParameterBundle.ParameterCell)
    (pkt : HelicityToNuclearKPacket) (m : InfoGeometry.Physics.MengChPSelectionRules.Multipole) :
    (piOp * piOp = 1 ∧ fermionOp * fermionOp = 1 ∧ wmOp * wmOp = 1 ∧
      mengParityOp * mengParityOp = 1 ∧ chitureOp * chitureOp = 1 ∧ chiplexOp * chiplexOp = 1 ∧
      piOp * fermionOp = fermionOp * piOp ∧ piOp * wmOp = wmOp * piOp ∧
      piOp * mengParityOp = mengParityOp * piOp ∧ fermionOp * wmOp = wmOp * fermionOp ∧
      fermionOp * mengParityOp = mengParityOp * fermionOp ∧
      wmOp * mengParityOp = mengParityOp * wmOp ∧
      k0Op * wmOp ≠ wmOp * k0Op ∧
      piOp ≠ fermionOp ∧ piOp ≠ wmOp ∧ piOp ≠ mengParityOp ∧
      fermionOp ≠ wmOp ∧ fermionOp ≠ mengParityOp ∧ wmOp ≠ mengParityOp ∧
      (∀ b : Fin 4 → Bool, fourParityProjector b ≠ 0)) ∧
    (piOp * pkt.toTaxonomyPacket.fourParityProj =
        (pkt.toTaxonomyPacket.spatialParitySign : ℂ) • pkt.toTaxonomyPacket.fourParityProj ∧
      fermionOp * pkt.toTaxonomyPacket.fourParityProj =
        (pkt.toTaxonomyPacket.base.quasiparticleParity : ℂ) • pkt.toTaxonomyPacket.fourParityProj ∧
      wmOp * pkt.toTaxonomyPacket.fourParityProj =
        (pkt.toTaxonomyPacket.wmSector.sign : ℂ) • pkt.toTaxonomyPacket.fourParityProj ∧
      mengParityOp * pkt.toTaxonomyPacket.fourParityProj =
        (pkt.toTaxonomyPacket.chitureSector.sign : ℂ) • pkt.toTaxonomyPacket.fourParityProj ∧
      pkt.toTaxonomyPacket.fourParityProj ≠ 0) ∧
    (triaxialChPInvolutions.chiplex * triaxialChPInvolutions.chiplex = 1 ∧
      triaxialChitureOp = chpChitureOp ∧
      triaxialIntrinsicParityOp = chpIntrinsicParityOp ∧
      chiralBandBra 1 1 (triaxialMultipoleOp m (chiralBandKet 0 0)) = 0 ∧
      chiralBandBra 1 0 (triaxialMultipoleOp .electricTwo (chiralBandKet 0 0)) ≠ 0) ∧
    (internalParity P *
        InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian E0 E1 V W *
        internalParity P =
        InfoGeometry.Physics.NuclearOperatorSuperSoloviev.reflectOffDiagonal E0 E1 V W ∧
      InfoGeometry.MassSpectrometry.gradingMatrix n *
        InfoGeometry.MassSpectrometry.doubledOperator K *
        InfoGeometry.MassSpectrometry.gradingMatrix n =
        -InfoGeometry.MassSpectrometry.doubledOperator K ∧
      InfoGeometry.Physics.NuclearOperatorSuperSoloviev.totalParity
        (InfoGeometry.Physics.NuclearFiveGradeParity.zeroModeInternalParity T H5.tripotent) *
        H5.toHamiltonian *
        InfoGeometry.Physics.NuclearOperatorSuperSoloviev.totalParity
          (InfoGeometry.Physics.NuclearFiveGradeParity.zeroModeInternalParity T H5.tripotent) =
        H5.toHamiltonian ∧
      InfoGeometry.Physics.NuclearQuasiparticleCAR.QuasiparticleCAR.fermionParity car i *
        InfoGeometry.Physics.NuclearQuasiparticleCAR.QuasiparticleCAR.fermionParity car i = 1 ∧
      InfoGeometry.Physics.Cl55SpinorCartanFock.gammaChiral *
        InfoGeometry.Physics.Cl55SpinorCartanFock.gammaChiral = 1 ∧
      InfoGeometry.Physics.NuclearFiveGradeParity.zeroModeInternalParity T hT =
        InfoGeometry.Physics.NuclearFiveGradeParity.zeroModeInternalParity T hT) ∧
    (Hklein.quotientEffectiveOperator Rklein
        (InfoGeometry.Canonical.D6HexTiledKleinBottleQuotient.quotientMap cell) =
        Hklein.effectiveAt Rklein cell ∧
      Hklein.effectiveAt Rklein (InfoGeometry.Canonical.D6HexTiledKleinBottleQuotient.glide cell) =
        Hklein.effectiveAt Rklein cell ∧
      InfoGeometry.Canonical.D6KleinDiracBands.quotientBandGap
        (InfoGeometry.Canonical.D6HexTiledKleinBottleQuotient.quotientMap cell) =
        InfoGeometry.Canonical.D6KleinDiracBands.bandGap cell) := by
  have hfp := four_parity_separation_and_compatibility
  have htax := InfoGeometry.Physics.NuclearQuantumNumberPacket.NuclearTaxonomyPacket.isospin_and_fourParity_compatibility
    pkt.toTaxonomyPacket
  have hchp := triaxial_opposite_chiplex_allowed_nonzero
  have hqcd := InfoGeometry.Physics.QCDChiralStructuralBridge.nuclear_massspec_chiral_packet
    P E0 E1 V W hE0 hE1 hV hW K
  have h5p := InfoGeometry.Physics.NuclearFiveGradeParity.PeirceCompatibleBlock.totalParity_invariant H5
  have hcl := InfoGeometry.Physics.NuclearCl55CartanParityDictionary.nuclear_cl55_parity_shape_packet car i
  have hkl := InfoGeometry.Physics.NuclearKleinSpectralDescentBridge.common_klein_quotient_packet
    Hklein Rklein cell
  refine ⟨⟨hfp.1.1, hfp.1.2.1, hfp.1.2.2.1, hfp.1.2.2.2.2.2.1, hfp.1.2.2.2.2.1, hfp.1.2.2.2.2.2.2,
      hfp.2.1.1, hfp.2.1.2.1, hfp.2.1.2.2.1, hfp.2.1.2.2.2.1, hfp.2.1.2.2.2.2.1, hfp.2.1.2.2.2.2.2.1,
      hfp.2.2.1.1, hfp.2.2.1.2.1, hfp.2.2.1.2.2.1, hfp.2.2.1.2.2.2.1,
      hfp.2.2.1.2.2.2.2.2.2.1, hfp.2.2.1.2.2.2.2.2.2.2.1,
      hfp.2.2.1.2.2.2.2.2.2.2.2.2.2.1, hfp.2.2.2⟩,
    ⟨htax.2.1.1, htax.2.1.2.1, htax.2.1.2.2.1, htax.2.1.2.2.2, htax.2.2.1.2⟩,
    ⟨triaxialChPInvolutions.chiplex_sq, triaxialChitureOp_eq_chpChitureOp,
      triaxialIntrinsicParityOp_eq_chpIntrinsicParityOp, triaxial_same_chiplex_vanishes m, hchp.1⟩,
    ⟨hqcd.1, hqcd.2, h5p, hcl.1, hcl.2, rfl⟩,
    ⟨hkl.1, hkl.2.1, hkl.2.2.1⟩⟩

/-! ## 5. Unconditional Noncommutative RPA Defect & Finite Seams A–D Soldering -/

/-- Unconditional finite-algebraic synthesis across Seams A–D:
- **Seam A**: `car5ToOpZornEuler` grade preservation, `seamA_rpa_commutator_defect_preserved`,
  and `seamA_soloviev_matStage5_nogo`.
- **Seam B**: `seamB_finite_architecture_compatibility` on `ColorParafermionMorphismPacket n`.
- **Seam C**: `unsigned_bandhead_vs_signed_KParitySector_separation`.
- **Seam D**: `kreinHyperbolicFlow_preserves_car_grade_zero_defect` (linking M1's exact CAR
  `[pairCreation, pairAnnihilation] = gradingOperator ≠ 0` directly with M4's hyperbolic Krein
  flow), `noncommKanRenormalizationData_normalizedStep`, and `iwasawa_commutation_vs_rpa_defect_separation`
  (separating `[scale, unipotent] = 0` from `[a, b] ≠ 0`). -/
theorem unified_rpa_defect_and_finite_seam_synthesis
    {k : ℤ} {Xcar : InfoGeometry.Physics.NuclearFiveGradeGeneratorRepresentation.carLieSubalgebra}
    (hX : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.HasGrade k Xcar.1)
    {ιq ιph A : Type*} [DecidableEq ιq] [DecidableEq ιph] [Ring A] [Algebra ℝ A]
    {grade : ℤ → Submodule ℝ A}
    {M : InfoGeometry.Physics.NuclearGradedBathCommutant.ThermalQuasiparticleModel grade}
    {sys : InfoGeometry.Physics.NuclearPhononRPA.CoupledQuasiparticlePhononSystem ιq ιph A}
    (Eqp ω V : ℂ) (α β lam τ ξ : ℝ)
    {n : ℕ} [DecidableEq (Fin n)] (P : ColorParafermionMorphismPacket n)
    {R : Type*} [Ring R] (Vop Wop Binv : R)
    (aF bF : ℝ) (vF : _root_.FibonacciParafermion.RealDiracSpinor)
    (Xz Yz : InfoGeometry.Canonical.GaugedZornDiracKahler.ZornMatrix ℝ)
    (u vVec w : InfoGeometry.Canonical.GaugedZornDiracKahler.Vec3 ℝ)
    (ψ : InfoGeometry.Physics.ThreeStrandJonesRecoupling.FusionState)
    (r : InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl.Root)
    (a b : A) (hab : a * b ≠ b * a)
    {Riw : Type*} [Ring Riw]
    (Ops : InfoGeometry.Integration.IwasawaTimeRenormalization.RenormalizationData Riw)
    (hIwasawa : (Ops.scale : Riw) * Ops.unipotent = Ops.unipotent * (Ops.scale : Riw))
    {Vkr : Type*} [NormedAddCommGroup Vkr] [InnerProductSpace ℝ Vkr] [CompleteSpace Vkr]
    [InfoGeometry.Krein.KreinSpace Vkr]
    (Pkr Hkr Kres : Vkr →L[ℝ] Vkr) (hPkr : Pkr * Pkr = Pkr) (hPHkr : Pkr * Hkr = Hkr * Pkr)
    (hQRkr : (1 - Pkr) * Kres = Kres) :
    (InfoGeometry.Canonical.AlbertCayleyDickson.SplitQuaternion.opEulerFiveGrading
        (car5ToOpZornEuler Xcar) = (k : ℝ) • car5ToOpZornEuler Xcar ∧
      IsEmpty
        (InfoGeometry.Physics.NuclearSolovievFiveGradedCommutantBridge.SolovievFiveGradedRealization
          grade M sys) ∧
      ((InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian
          InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation
          (-InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation)
          InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation
          (-InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation) *
        InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian
          InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation
          (-InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation)
          InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation
          (-InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation)) 0 1 =
        InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator ∧
        InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator ≠ 0) ∧
      (α * β) • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator =
        (InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian
          (α • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation)
          (-(α • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation))
          (β • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation)
          (-(β • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation)) *
        InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian
          (α • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation)
          (-(α • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation))
          (β • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation)
          (-(β • InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation))) 0 1) ∧
    (P.colorDefect.op ^ 3 = P.colorDefect.op ∧
      P.zornEquiv (InfoGeometry.Canonical.GaugedZornDiracKahler.ZornMatrix.zornMul Xz Yz) =
        P.zornEquiv Xz * P.zornEquiv Yz ∧
      P.zornToCl55Singlet (InfoGeometry.Canonical.ZornColorConfinementBaryon.baryonState
        InfoGeometry.Canonical.ZornColorConfinementBaryon.colorE0
        InfoGeometry.Canonical.ZornColorConfinementBaryon.colorE1
        InfoGeometry.Canonical.ZornColorConfinementBaryon.colorE2) ≠ 0 ∧
      InfoGeometry.Physics.Cl55WignerSU4Embedding.colorSU3Casimir * P.zornToCl55Singlet Xz = 0 ∧
      (P.artinLift.Bs * P.artinLift.Bl) ^ 12 = 1 ∧
      (∀ k12 : ℕ, 0 < k12 → k12 < 12 → (P.artinLift.Bs * P.artinLift.Bl) ^ k12 ≠ 1)) ∧
    ((MasslessHelicityBranch.plusOne.toBandhead.twoK =
        MasslessHelicityBranch.minusOne.toBandhead.twoK) ∧
      (MasslessHelicityBranch.plusOne.toKParitySector.twoK ≠
        MasslessHelicityBranch.minusOne.toKParitySector.twoK) ∧
      ((⟨1, InfoGeometry.Physics.NuclearSymmetrySectors.SpatialParity.positive⟩ :
          InfoGeometry.Physics.NuclearSpinIsospinTensorRepresentation.KParitySector) ≠
        ⟨1, InfoGeometry.Physics.NuclearSymmetrySectors.SpatialParity.negative⟩)) ∧
    ((let aM : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R :=
          InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairCreation
      let bM : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R :=
          InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.pairAnnihilation
      let cM : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R :=
          algebraMap ℝ InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R (Real.cosh (lam * τ))
      let sM : InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R :=
          algebraMap ℝ InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.M4R (Real.sinh (lam * τ))
      let aM' := (cM * cM + sM * sM) * aM - (2 : ℕ) • (cM * sM * bM)
      let bM' := (cM * cM + sM * sM) * bM - (2 : ℕ) • (cM * sM * aM)
      aM' * bM' - bM' * aM' =
        InfoGeometry.Physics.NuclearTwoModeFiveGradeLieModel.gradingOperator ∧ bM' ≠ 0) ∧
      (InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian (1 : ℝ) (-1) 1 1 *
          kreinHyperbolicFlow lam τ *
          InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian (1 : ℝ) (-1) 1 1 =
        (2 : ℝ) • InfoGeometry.Algebra.IwasawaRealKAN.aDiag (lam * τ)) ∧
      (InfoGeometry.Integration.IwasawaTimeRenormalization.normalizedStep
          (noncommKanRenormalizationData lam ξ) =
        InfoGeometry.Algebra.IwasawaRealKAN.nShear (Real.exp (2 * lam) * ξ)) ∧
      (InfoGeometry.Integration.IwasawaTimeRenormalization.normalizedStep Ops = Ops.unipotent ∧
        InfoGeometry.Canonical.BogoliubovRGFlowBridge.schurCorrection Pkr Hkr Kres = 0 ∧
        (InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian a (-a) b (-b) *
          InfoGeometry.Physics.NuclearOperatorSuperSoloviev.blockHamiltonian a (-a) b (-b)) 0 1 ≠ 0)) := by
  have hA_nogo := seamA_soloviev_matStage5_nogo (grade := grade) (M := M) (sys := sys) Eqp ω V
  have hA_rpa := seamA_rpa_commutator_defect_preserved α β
  have hB := seamB_finite_architecture_compatibility P Vop Wop Binv aF bF vF Xz Yz u vVec w ψ r
  have hC := unsigned_bandhead_vs_signed_KParitySector_separation
  have hD_car := kreinHyperbolicFlow_preserves_car_grade_zero_defect lam τ
  have hD_sep := iwasawa_commutation_vs_rpa_defect_separation Ops hIwasawa Pkr Hkr Kres hPkr hPHkr hQRkr a b hab lam τ
  refine ⟨⟨car5ToOpZornEuler_preserves_grade hX, hA_nogo.1, hA_rpa.1, hA_rpa.2.2.1.symm⟩,
    ⟨hB.1.1, hB.2.2.2.1.2.1, hB.2.2.2.1.2.2.2.1, hB.2.2.2.1.2.2.2.2,
      hB.2.2.2.2.2.2.2.2.2.1, hB.2.2.2.2.2.2.2.2.2.2.1⟩,
    ⟨hC.1, hC.2.1, hC.2.2.2.2⟩,
    ⟨⟨hD_car.1, hD_car.2.2⟩,
      hadamard_kreinHyperbolicFlow_eq_two_aDiag lam τ,
      noncommKanRenormalizationData_normalizedStep lam ξ,
      ⟨hD_sep.1, hD_sep.2.1.1, hD_sep.2.2.1⟩⟩⟩

/-- Non-vacuous unconditional canonical witness theorem applying the unified finite synthesis
to `canonicalUnifiedParityFiveGradeSynthesisPacket`. -/
theorem canonical_unified_synthesis_packet_witness :
    let P := canonicalUnifiedParityFiveGradeSynthesisPacket
    P.rpaA * P.rpaB ≠ P.rpaB * P.rpaA ∧
      piOp ≠ fermionOp ∧ fermionOp ≠ wmOp ∧ wmOp ≠ mengParityOp ∧
      k0Op * wmOp ≠ wmOp * k0Op ∧
      P.chpAlgebra.chiplex * P.chpAlgebra.chiplex = 1 ∧
      P.wignerCasimir = (15 / 4 : ℂ) • (1 : _root_.ChiralTensorRecoupling.SpinPair) ∧
      (P.seamB.artinLift.Bs * P.seamB.artinLift.Bl) ^ 12 = 1 ∧
      P.seamC.toSignedKParitySector.twoK = 1 := by
  have hfp := four_parity_separation_and_compatibility
  refine ⟨canonicalUnifiedParityFiveGradeSynthesisPacket.rpaDefect_noncomm,
    hfp.2.2.1.2.1, hfp.2.2.1.2.2.2.2.2.2.1, hfp.2.2.1.2.2.2.2.2.2.2.2.2.2.1,
    hfp.2.2.1.1,
    canonicalUnifiedParityFiveGradeSynthesisPacket.chpAlgebra.chiplex_sq,
    wigner_su4_casimir,
    canonicalUnifiedParityFiveGradeSynthesisPacket.seamB.artinLift.spin_coxeter_pow_twelve,
    rfl⟩

/-! ## 6. Explicit Conditional Continuum Extension Bundle (R2 Separation) -/

/-- Explicit hypothesis-parameterized `Type 1` bundle packaging continuum / nonperturbative
physical extensions across Seams B, C, and D:
- Seam B: `ContinuumQCDConfinementHypothesis` and `DynamicalQCDConfinementBridge` (4D confinement & mass gap),
- Seam C: `QuantizedSDiffHelicityHypothesis` (quantized continuous `SDiff` helicity sector),
- Seam D: `ContinuumRGFlowHypothesis` and `SpectralGapTerminationHypothesis` (multi-scale RG flow & Schur gap bound).

Separated from all unconditional algebraic theorems above per R2. -/
structure UnifiedContinuumExtensionHypothesis : Type 1 where
  qcdConfinement : ContinuumQCDConfinementHypothesis
  qcdBridge : DynamicalQCDConfinementBridge qcdConfinement
  sdiffQuantized : QuantizedSDiffHelicityHypothesis
  continuumRG : ContinuumRGFlowHypothesis
  SpectralV : Type
  instNormed : NormedAddCommGroup SpectralV
  instInner : InnerProductSpace ℝ SpectralV
  instComplete : CompleteSpace SpectralV
  instKrein : InfoGeometry.Krein.KreinSpace SpectralV
  spectralGap :
    @SpectralGapTerminationHypothesis SpectralV instNormed instInner instComplete instKrein

attribute [instance] UnifiedContinuumExtensionHypothesis.instNormed
attribute [instance] UnifiedContinuumExtensionHypothesis.instInner
attribute [instance] UnifiedContinuumExtensionHypothesis.instComplete
attribute [instance] UnifiedContinuumExtensionHypothesis.instKrein

/-- Zero-hypothesis constructive finite-model witness (`T17`) for
`UnifiedContinuumExtensionHypothesis`. -/
def canonicalUnifiedContinuumExtensionHypothesis : UnifiedContinuumExtensionHypothesis where
  qcdConfinement := cl55ModelContinuumHypothesis
  qcdBridge := cl55ModelDynamicalBridge
  sdiffQuantized := defaultQuantizedSDiffHelicityHypothesis
  continuumRG := canonicalContinuumRGFlowHypothesis
  SpectralV := InfoGeometry.Krein.DoubledSpace ℝ
  instNormed := inferInstance
  instInner := inferInstance
  instComplete := inferInstance
  instKrein := inferInstance
  spectralGap := canonicalSpectralGapTerminationHypothesis

/-- Conditional continuum synthesis theorem deriving Seam B dynamical baryon confinement,
Casimir/Drazin annihilation, monodromy mass-gap preservation, Wilson area-law decay,
Seam C `SDiff` coadjoint helicity invariance, and Seam D continuum RG derivative + Schur
spectral-gap bound from `UnifiedContinuumExtensionHypothesis`. -/
theorem unified_conditional_continuum_extension_theorem
    (U : UnifiedContinuumExtensionHypothesis)
    (u v w : InfoGeometry.Canonical.GaugedZornDiracKahler.Vec3 ℝ)
    (g : InfoGeometry.Physics.B3PresentedGroup.B3)
    (ψ : U.qcdConfinement.ContinuumState) (hne : ψ ≠ 0)
    (hker : U.qcdConfinement.singletProjector ψ = 0)
    (area : ℝ) (harea : 0 < area)
    (R : InfoGeometry.Physics.SDiffCoadjoint.LocalSDiffIsometry)
    (h_smul : ∀ (c : ℝ) (v3 : _root_.ChiralVector3), R.toFun (c • v3) = c • R.toFun v3)
    (lambda_param : ℝ) (u3 omega3 : _root_.ChiralVector3) :
    (U.qcdBridge.zornToContinuum (InfoGeometry.Canonical.ZornColorConfinementBaryon.baryonState u v w) =
        (InfoGeometry.Canonical.GaugedZornDiracKahler.dot3
          (InfoGeometry.Canonical.GaugedZornDiracKahler.cross3 u v) w) •
          U.qcdConfinement.embedCl55 InfoGeometry.Physics.Cl55SpinorCartanFock.colorBaryonSingletProj ∧
      (U.qcdConfinement.embedCl55 InfoGeometry.Physics.Cl55WignerSU4Embedding.colorSU3Casimir).comp
        U.qcdConfinement.singletProjector = 0 ∧
      U.qcdConfinement.massGap ≤
        U.qcdConfinement.energy ((U.qcdBridge.monodromyAction g : Module.End ℂ U.qcdConfinement.ContinuumState) ψ) ∧
      U.qcdConfinement.wilsonAreaExponent area < 0) ∧
    (InfoGeometry.Physics.SDiffCoadjoint.totalHelicity
        (InfoGeometry.Physics.SDiffCoadjoint.coadjointFlow R U.sdiffQuantized.state) =
      InfoGeometry.Physics.SDiffCoadjoint.totalHelicity U.sdiffQuantized.state ∧
      sdiffHelicitySignParity
        (InfoGeometry.Physics.SDiffCoadjoint.coadjointFlow R U.sdiffQuantized.state) =
      sdiffHelicitySignParity U.sdiffQuantized.state) ∧
    (HasDerivAt U.continuumRG.flow (U.continuumRG.lam * U.continuumRG.x0) 0 ∧
      ‖InfoGeometry.Physics.NuclearRealKreinFeshbach.effectiveHamiltonian
          U.spectralGap.P₀ U.spectralGap.H U.spectralGap.R -
        U.spectralGap.P₀ * U.spectralGap.H * U.spectralGap.P₀‖ ≤ U.spectralGap.δ) := by
  have hB_bar := dynamical_zorn_baryon_lands_in_continuum_singlet U.qcdBridge u v w
  have hB_cas := dynamical_casimir_and_drazin_annihilate_continuum_singlet U.qcdConfinement
  have hB_gap := dynamical_monodromy_preserves_non_singlet_mass_gap U.qcdBridge g ψ hne hker
  have hB_wil := dynamical_wilson_area_law_strictly_decaying U.qcdConfinement harea
  have hC := sdiff_helicity_coadjoint_and_sign_parity_invariant
    R U.sdiffQuantized.state h_smul lambda_param u3 omega3 U.sdiffQuantized
  have hD_rg := continuum_rg_flow_zero_deriv U.continuumRG
  have hD_gap := spectral_gap_termination_schur_bound U.spectralGap
  exact ⟨⟨hB_bar.1, hB_cas.1, hB_gap.1, hB_wil⟩, ⟨hC.2.2.2.1.1, hC.2.1⟩, ⟨hD_rg, hD_gap⟩⟩

end InfoGeometry.Synthesis.NuclearUnifiedParityFiveGradeRenormalizationSynthesis

end
