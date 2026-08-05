import InfoGeometry.SuperMetriplectic.InformationSuperGas
import InfoGeometry.Algebraic.SplitSuperGeometry

/-!
# Berezinian/Pfaffian Supervolume Functional

Lean-only scalar/body-level packet for the supervolume functional:

`Z = Pf_reg(iD) / sqrt(Ber_reg(M))`

and the entropy readout

`S = log Pf_reg(iD) - (1/2) log Ber_reg(M)`.

This file does not construct infinite-dimensional determinants, zeta analytic
continuation, concrete Pfaffians, or a concrete `Cl(4,4)` matrix model.  Those
analytic/operator facts are represented by explicit fields so downstream owner
modules can discharge them later.
-/

namespace InfoGeometry.SuperMetriplectic

open InfoGeometry.Algebraic.SplitSignature

/--
Scalar Schur/Berezinian packet for a `2 × 2` superblock matrix.

The intended formula is
`Ber(M) = det(A - B D⁻¹ C) / det(D)`.
At this scalar level, determinants and the Schur complement are readouts.
-/
structure BerezinianSchurPacket where
  detA : ℝ
  detD : ℝ
  detDInv : ℝ
  detB : ℝ
  detC : ℝ
  schurComplementDet : ℝ
  berezinianReg : ℝ
  detDInv_is_inverse :
    detD * detDInv = 1
  schurComplementDet_eq :
    schurComplementDet = detA - detB * detDInv * detC
  berezinianReg_eq :
    berezinianReg = schurComplementDet * detDInv

namespace BerezinianSchurPacket

/-- Public scalar Schur complement determinant readout. -/
theorem schurComplementDet_eq_schur
    (B : BerezinianSchurPacket) :
    B.schurComplementDet = B.detA - B.detB * B.detDInv * B.detC :=
  B.schurComplementDet_eq

/-- Public Berezinian readout via the Schur complement and inverse determinant. -/
theorem berezinianReg_eq_schur_mul_detDInv
    (B : BerezinianSchurPacket) :
    B.berezinianReg = B.schurComplementDet * B.detDInv :=
  B.berezinianReg_eq

end BerezinianSchurPacket

/--
Zeta-regularized determinant packet.

`zetaDerivativeAtZero` is the supplied value of `ζ'_Δ(0)`, and `logDetReg`
records `log det_ζ(Δ) = -ζ'_Δ(0)`.
-/
structure ZetaRegularizedDeterminantPacket where
  zetaDerivativeAtZero : ℝ
  logDetReg : ℝ
  casimirResidual : ℝ
  logDetReg_eq_neg_zetaDerivative :
    logDetReg = -zetaDerivativeAtZero
  casimirResidual_is_zeta_residue :
    casimirResidual = zetaDerivativeAtZero + logDetReg

namespace ZetaRegularizedDeterminantPacket

/-- Zeta-regularized log determinant identity. -/
theorem logDetReg_eq
    (Z : ZetaRegularizedDeterminantPacket) :
    Z.logDetReg = -Z.zetaDerivativeAtZero :=
  Z.logDetReg_eq_neg_zetaDerivative

/-- Residual/Casimir readout carried by the packet. -/
theorem casimirResidual_eq
    (Z : ZetaRegularizedDeterminantPacket) :
    Z.casimirResidual = Z.zetaDerivativeAtZero + Z.logDetReg :=
  Z.casimirResidual_is_zeta_residue

end ZetaRegularizedDeterminantPacket

/--
Regularized Majorana Pfaffian packet.

The Weyl variation of the regularized Pfaffian is the central/topological
charge readout in this scalar shadow.
-/
structure RegularizedPfaffianPacket where
  diracSouriauReadout : ℝ
  pfaffianReg : ℝ
  logPfaffianReg : ℝ
  centralCharge : ℝ
  weylVariation : ℝ
  topologicalCharge : ℝ
  weylVariation_eq_topologicalCharge :
    weylVariation = topologicalCharge
  topologicalCharge_eq_centralCharge :
    topologicalCharge = centralCharge

namespace RegularizedPfaffianPacket

/-- Weyl variation of the Pfaffian is the topological charge readout. -/
theorem weylVariation_eq_topological
    (P : RegularizedPfaffianPacket) :
    P.weylVariation = P.topologicalCharge :=
  P.weylVariation_eq_topologicalCharge

/-- The topological charge readout is the central charge lane. -/
theorem topological_eq_central
    (P : RegularizedPfaffianPacket) :
    P.topologicalCharge = P.centralCharge :=
  P.topologicalCharge_eq_centralCharge

/-- Weyl variation directly reads the central charge. -/
theorem weylVariation_eq_centralCharge
    (P : RegularizedPfaffianPacket) :
    P.weylVariation = P.centralCharge := by
  rw [P.weylVariation_eq_topological, P.topological_eq_central]

end RegularizedPfaffianPacket

/--
Supervolume functional packet.

`sqrtBerezinianReg` and logarithms are supplied scalar readouts.  This avoids
introducing analytic square-root/log side conditions at this abstraction level.
-/
structure SupervolumeFunctionalPacket where
  berezinian : BerezinianSchurPacket
  zetaDet : ZetaRegularizedDeterminantPacket
  pfaffian : RegularizedPfaffianPacket
  sqrtBerezinianReg : ℝ
  partitionFunctional : ℝ
  entropyReadout : ℝ
  logBerezinianReg : ℝ
  partitionFunctional_eq :
    partitionFunctional = pfaffian.pfaffianReg / sqrtBerezinianReg
  entropyReadout_eq :
    entropyReadout =
      pfaffian.logPfaffianReg - (1 / 2 : ℝ) * logBerezinianReg

namespace SupervolumeFunctionalPacket

/-- Supervolume partition functional `Z = Pf_reg / sqrt(Ber_reg)`. -/
theorem partitionFunctional_eq_pfaffian_div_sqrtBerezinian
    (S : SupervolumeFunctionalPacket) :
    S.partitionFunctional = S.pfaffian.pfaffianReg / S.sqrtBerezinianReg :=
  S.partitionFunctional_eq

/-- Entropy is logarithmic Pfaffian minus half logarithmic Berezinian. -/
theorem entropyReadout_eq_logPfaffian_sub_half_logBerezinian
    (S : SupervolumeFunctionalPacket) :
    S.entropyReadout =
      S.pfaffian.logPfaffianReg - (1 / 2 : ℝ) * S.logBerezinianReg :=
  S.entropyReadout_eq

/-- Pfaffian Weyl variation reads the central charge. -/
theorem pfaffian_weylVariation_eq_centralCharge
    (S : SupervolumeFunctionalPacket) :
    S.pfaffian.weylVariation = S.pfaffian.centralCharge :=
  S.pfaffian.weylVariation_eq_centralCharge

end SupervolumeFunctionalPacket

/--
Capstone joining the information super-gas with the supervolume functional.
-/
structure InformationSuperGasSupervolumeCapstone (ι : Type*) [Fintype ι] where
  gas : InformationSuperGasCapstone ι
  supervolume : SupervolumeFunctionalPacket
  characterPartition_matches_supervolume :
    gas.functional.weylCharacter = supervolume.partitionFunctional

namespace InformationSuperGasSupervolumeCapstone

variable {ι : Type*} [Fintype ι]

/-- Weyl-character partition readout matches the supervolume functional. -/
theorem characterPartition_eq_supervolume
    (C : InformationSuperGasSupervolumeCapstone ι) :
    C.gas.functional.weylCharacter = C.supervolume.partitionFunctional :=
  C.characterPartition_matches_supervolume

/-- Supervolume entropy formula. -/
theorem entropy_eq_logPfaffian_sub_half_logBerezinian
    (C : InformationSuperGasSupervolumeCapstone ι) :
    C.supervolume.entropyReadout =
      C.supervolume.pfaffian.logPfaffianReg
        - (1 / 2 : ℝ) * C.supervolume.logBerezinianReg :=
  C.supervolume.entropyReadout_eq_logPfaffian_sub_half_logBerezinian

/-- Observable entropy production remains body-nonnegative in the gas layer. -/
theorem body_entropy_nonnegative
    (C : InformationSuperGasSupervolumeCapstone ι) :
    0 ≤ C.gas.entropyBody.production :=
  C.gas.body_entropy_nonnegative

/--
Final supervolume capstone:
character partition equals supervolume, Berezinian/Pfaffian formulas are
exposed, Pfaffian Weyl variation reads central charge, and the body second law
remains the ordered entropy statement.
-/
theorem supervolume_functional_capstone
    (C : InformationSuperGasSupervolumeCapstone ι) :
    C.gas.functional.weylCharacter = C.supervolume.partitionFunctional
      ∧ C.supervolume.partitionFunctional =
          C.supervolume.pfaffian.pfaffianReg / C.supervolume.sqrtBerezinianReg
      ∧ C.supervolume.entropyReadout =
          C.supervolume.pfaffian.logPfaffianReg
            - (1 / 2 : ℝ) * C.supervolume.logBerezinianReg
      ∧ C.supervolume.pfaffian.weylVariation =
          C.supervolume.pfaffian.centralCharge
      ∧ 0 ≤ C.gas.entropyBody.production := by
  exact ⟨C.characterPartition_eq_supervolume,
    C.supervolume.partitionFunctional_eq_pfaffian_div_sqrtBerezinian,
    C.entropy_eq_logPfaffian_sub_half_logBerezinian,
    C.supervolume.pfaffian_weylVariation_eq_centralCharge,
    C.body_entropy_nonnegative⟩

end InformationSuperGasSupervolumeCapstone

/-
Split Clifford translation of the scalar supervolume packet.

The old `Berezinian/Pfaffian` language remains as a body-level shadow, while
the operator-level primitive is now the split Clifford supertrace/Berezinian
readout.
-/
namespace SplitSupervolumeTranslation

/-- Operator-level supervolume shadow on the split Clifford carrier. -/
abbrev SplitSupervolumeShadow (n : ℕ) := SplitCliffordEnd n

namespace SplitSupervolumeShadow

abbrev operator (S : SplitSupervolumeShadow n) : SplitCliffordEnd n := S

end SplitSupervolumeShadow

/-- The supertrace readout is derived from the split-Clifford operator. -/
noncomputable def SplitSupervolumeShadow.supertraceReadout
    {n : ℕ} (S : SplitSupervolumeShadow n) : ℝ :=
  cliffordSupertrace n S.operator

/-- The super-Berezinian readout is derived from the split-Clifford operator. -/
noncomputable def SplitSupervolumeShadow.superBerezinianReadout
    {n : ℕ} (S : SplitSupervolumeShadow n) : ℝ :=
  superBerezinian n S.operator

/-- The supervolume potential is derived from the split-Clifford operator. -/
noncomputable def SplitSupervolumeShadow.supervolumePotential
    {n : ℕ} (S : SplitSupervolumeShadow n) : ℝ :=
  superEffectiveAction n S.operator

@[simp]
theorem supervolumePotential_eq_neg_log_superBerezinian
    (n : ℕ) (x : SplitCliffordEnd n) :
    (superEffectiveAction n) x = - Real.log ((superBerezinian n) x) :=
  rfl

end SplitSupervolumeTranslation

end InfoGeometry.SuperMetriplectic
