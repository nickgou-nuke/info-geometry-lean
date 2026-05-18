import Mathlib
import InfoGeometry.Arithmetic.PrimeMajoranaBitFlip
import InfoGeometry.Arithmetic.PrimeSpinorWittenIndex
import InfoGeometry.Arithmetic.RHQuantumStabilityBridge
import InfoGeometry.Meta.OwnerTarget
import InfoGeometry.Meta.BridgeTarget
import InfoGeometry.Meta.SocketTarget

/-!
# InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket

witness-gated (Native Closure Mandated: Closure Debt) spectral socket for a Majorana/Pólya--Hilbert program.

This file deliberately does **not** construct a self-adjoint operator whose
spectrum proves RH.  It records the exact analytic obligations such a program
would need:

* a real Majorana/Berry--Keating type operator;
* self-adjointness in the chosen real Hilbert/Fock carrier;
* the separation between the Möbius inverse-zeta Witten character and the
  completed-zeta spectral determinant/Pfaffian target;
* a normalizability criterion for Majorana zero modes;
* a separate implication from that criterion to a classical RH statement.

The finite Majorana bit-flip and Pfaffian/Witten character layers remain the
theorem-bearing algebraic owners.  This module is the spectral/analytic socket
above them.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket

open InfoGeometry.Arithmetic.RHQuantumStabilityBridge

/-! ## 1. Berry--Keating / Majorana operator data -/

/--
Mellin/Plancherel normalization packet for the Berry--Keating sector.

The critical line is attributed to the unitary Mellin spectrum of the
Berry--Keating dilation sector, not to ordinary Fock-space summability of
Dirichlet coefficients.
-/
structure MellinPlancherelCriticalLinePacket
    (MellinWave MellinNorm : Type*) where
  realPart : ℝ
  imaginaryHeight : ℝ
  mellinWave : MellinWave
  mellinNorm : MellinNorm
  bk_generalizedEigenvalue_law : Prop
  bk_generalizedEigenvalue_certificate :
    bk_generalizedEigenvalue_law
  selfAdjoint_forces_realEigenvalue_law : Prop
  selfAdjoint_forces_realEigenvalue_certificate :
    selfAdjoint_forces_realEigenvalue_law
  mellinPlancherel_iff_criticalLine_law :
    IsCriticalLineRealPart realPart
  ordinaryFockNorm_not_source_guard : Type*

namespace MellinPlancherelCriticalLinePacket

/-- Re-export of the supplied Berry--Keating generalized-eigenvalue law. -/
theorem bk_generalizedEigenvalue
    {MellinWave MellinNorm : Type*}
    (P : MellinPlancherelCriticalLinePacket MellinWave MellinNorm) :
    P.bk_generalizedEigenvalue_law :=
  P.bk_generalizedEigenvalue_certificate

/-- Re-export of the supplied self-adjoint real-eigenvalue law. -/
theorem selfAdjoint_forces_realEigenvalue
    {MellinWave MellinNorm : Type*}
    (P : MellinPlancherelCriticalLinePacket MellinWave MellinNorm) :
    P.selfAdjoint_forces_realEigenvalue_law :=
  P.selfAdjoint_forces_realEigenvalue_certificate

/-- The supplied Mellin/Plancherel packet places the real part on the critical line. -/
theorem criticalLine
    {MellinWave MellinNorm : Type*}
    (P : MellinPlancherelCriticalLinePacket MellinWave MellinNorm) :
    IsCriticalLineRealPart P.realPart :=
  P.mellinPlancherel_iff_criticalLine_law

end MellinPlancherelCriticalLinePacket

/--
Formal Berry--Keating operator packet.

The intended model is a symmetrized dilation operator of the form
`(xp + px) / 2`, but this structure is intentionally abstract: domain,
closure, boundary conditions, and self-adjoint extension data are analytic
choices supplied by a concrete owner.
-/
structure BerryKeatingOperatorPacket
    (Carrier Operator Domain : Type*) where
  carrier : Carrier
  domain : Domain
  position : Operator
  momentum : Operator
  symmetrizedDilation : Operator
  symmetrizedDilation_formula_law : Prop
  symmetrizedDilation_formula_certificate :
    symmetrizedDilation_formula_law
  symmetric_on_domain_law : Prop
  symmetric_on_domain_certificate :
    symmetric_on_domain_law
  self_adjoint_extension_law : Prop
  self_adjoint_extension_certificate :
    self_adjoint_extension_law

namespace BerryKeatingOperatorPacket

/-- Re-export of the supplied symmetrized `xp + px` formula law. -/
theorem symmetrizedDilation_formula
    {Carrier Operator Domain : Type*}
    (B : BerryKeatingOperatorPacket Carrier Operator Domain) :
    B.symmetrizedDilation_formula_law :=
  B.symmetrizedDilation_formula_certificate

/-- Re-export of the supplied symmetry-on-domain law. -/
theorem symmetric_on_domain
    {Carrier Operator Domain : Type*}
    (B : BerryKeatingOperatorPacket Carrier Operator Domain) :
    B.symmetric_on_domain_law :=
  B.symmetric_on_domain_certificate

/-- Re-export of the supplied self-adjoint extension law. -/
theorem self_adjoint_extension
    {Carrier Operator Domain : Type*}
    (B : BerryKeatingOperatorPacket Carrier Operator Domain) :
    B.self_adjoint_extension_law :=
  B.self_adjoint_extension_certificate

end BerryKeatingOperatorPacket

/--
Majorana modification of a Berry--Keating spectral operator.

The `majoranaDirac` field is the candidate real operator whose zero modes are
to be compared with zeta zero data.  The square-root normalization and
split-Clifford/CAR compatibility are supplied as laws by the concrete model.
-/
structure MajoranaBerryKeatingOperatorPacket
    (Carrier Operator Domain Mode : Type*) where
  berryKeating : BerryKeatingOperatorPacket Carrier Operator Domain
  majoranaMode : Mode → Operator
  thermalOperator : Mode → Operator
  majoranaDirac : Operator
  squareRootEnergyCoefficient : Mode → ℝ
  splitClifford_law : Prop
  splitClifford_certificate : splitClifford_law
  squareRootEnergy_law : Prop
  squareRootEnergy_certificate : squareRootEnergy_law
  dirac_square_law : Prop
  dirac_square_certificate : dirac_square_law
  self_adjoint_law : Prop
  self_adjoint_certificate : self_adjoint_law
  bk_mellin_sector_fixes_criticalLine_law : Prop
  bk_mellin_sector_fixes_criticalLine_certificate :
    bk_mellin_sector_fixes_criticalLine_law
  majorana_fock_sector_produces_pfaffianCharacter_law : Prop
  majorana_fock_sector_produces_pfaffianCharacter_certificate :
    majorana_fock_sector_produces_pfaffianCharacter_law

namespace MajoranaBerryKeatingOperatorPacket

/-- Re-export of the supplied split-Clifford compatibility law. -/
theorem splitClifford
    {Carrier Operator Domain Mode : Type*}
    (M : MajoranaBerryKeatingOperatorPacket Carrier Operator Domain Mode) :
    M.splitClifford_law :=
  M.splitClifford_certificate

/-- Re-export of the supplied `sqrt(log p)` normalization law. -/
theorem squareRootEnergy
    {Carrier Operator Domain Mode : Type*}
    (M : MajoranaBerryKeatingOperatorPacket Carrier Operator Domain Mode) :
    M.squareRootEnergy_law :=
  M.squareRootEnergy_certificate

/-- Re-export of the supplied Dirac-square law. -/
theorem dirac_square
    {Carrier Operator Domain Mode : Type*}
    (M : MajoranaBerryKeatingOperatorPacket Carrier Operator Domain Mode) :
    M.dirac_square_law :=
  M.dirac_square_certificate

/-- Re-export of the supplied self-adjointness law. -/
theorem self_adjoint
    {Carrier Operator Domain Mode : Type*}
    (M : MajoranaBerryKeatingOperatorPacket Carrier Operator Domain Mode) :
    M.self_adjoint_law :=
  M.self_adjoint_certificate

/-- Re-export: the Mellin/BK sector is the critical-line mechanism. -/
theorem bk_mellin_sector_fixes_criticalLine
    {Carrier Operator Domain Mode : Type*}
    (M : MajoranaBerryKeatingOperatorPacket Carrier Operator Domain Mode) :
    M.bk_mellin_sector_fixes_criticalLine_law :=
  M.bk_mellin_sector_fixes_criticalLine_certificate

/-- Re-export: the Majorana/Fock sector is the Pfaffian/Witten-character mechanism. -/
theorem majorana_fock_sector_produces_pfaffianCharacter
    {Carrier Operator Domain Mode : Type*}
    (M : MajoranaBerryKeatingOperatorPacket Carrier Operator Domain Mode) :
    M.majorana_fock_sector_produces_pfaffianCharacter_law :=
  M.majorana_fock_sector_produces_pfaffianCharacter_certificate

end MajoranaBerryKeatingOperatorPacket

/-! ## 2. Real Majorana--Berry--Keating operator problem -/

/--
Finite-cutoff real Majorana--Berry--Keating operator problem.

This names the combined operator

`D_Λ = H_BK ⊗ 1 + ρ ⊗ Q_Λ`

without pretending to construct its analytic closure.  The square law is
separate witness data; it depends on the anticommutation of `ρ` with the real
Berry--Keating block and on the Dirac-square law for `Q_Λ`.
-/
structure RealMajoranaBerryKeatingProblem
    (Carrier Operator Mode Cutoff : Type*) where
  carrier : Carrier
  cutoff : Cutoff
  realBerryKeatingBlock : Operator
  chiralityRho : Operator
  majoranaDiracCutoff : Operator
  combinedDirac : Operator
  combinedDirac_formula_law : Prop
  combinedDirac_formula_certificate :
    combinedDirac_formula_law
  rho_anticommutes_realBK_law : Prop
  rho_anticommutes_realBK_certificate :
    rho_anticommutes_realBK_law
  majoranaDirac_square_law : Prop
  majoranaDirac_square_certificate :
    majoranaDirac_square_law
  combinedDirac_square_law : Prop
  combinedDirac_square_certificate :
    combinedDirac_square_law
  modeEnergyCoefficient : Mode → ℝ
  modeEnergyCoefficient_sqrtLog_law : Prop
  modeEnergyCoefficient_sqrtLog_certificate :
    modeEnergyCoefficient_sqrtLog_law

namespace RealMajoranaBerryKeatingProblem

/-- Re-export of the combined operator formula. -/
theorem combinedDirac_formula
    {Carrier Operator Mode Cutoff : Type*}
    (P : RealMajoranaBerryKeatingProblem Carrier Operator Mode Cutoff) :
    P.combinedDirac_formula_law :=
  P.combinedDirac_formula_certificate

/-- Re-export of the `ρ`/Berry--Keating anticommutation law. -/
theorem rho_anticommutes_realBK
    {Carrier Operator Mode Cutoff : Type*}
    (P : RealMajoranaBerryKeatingProblem Carrier Operator Mode Cutoff) :
    P.rho_anticommutes_realBK_law :=
  P.rho_anticommutes_realBK_certificate

/-- Re-export of the finite-cutoff Majorana Dirac-square law. -/
theorem majoranaDirac_square
    {Carrier Operator Mode Cutoff : Type*}
    (P : RealMajoranaBerryKeatingProblem Carrier Operator Mode Cutoff) :
    P.majoranaDirac_square_law :=
  P.majoranaDirac_square_certificate

/-- Re-export of the combined square law. -/
theorem combinedDirac_square
    {Carrier Operator Mode Cutoff : Type*}
    (P : RealMajoranaBerryKeatingProblem Carrier Operator Mode Cutoff) :
    P.combinedDirac_square_law :=
  P.combinedDirac_square_certificate

/-- Re-export of the `sqrt(log p)` coefficient law. -/
theorem modeEnergyCoefficient_sqrtLog
    {Carrier Operator Mode Cutoff : Type*}
    (P : RealMajoranaBerryKeatingProblem Carrier Operator Mode Cutoff) :
    P.modeEnergyCoefficient_sqrtLog_law :=
  P.modeEnergyCoefficient_sqrtLog_certificate

end RealMajoranaBerryKeatingProblem

/-! ## 2. Zero-mode normalizability and zeta spectral sockets -/

/--
Guard separating ordinary Fock norm from Mellin/Plancherel normalization.

The square-free Möbius spinor/Fock series has its own summability domain; the
critical line in the Berry--Keating program is instead a unitary Mellin
normalization statement.
-/
structure FockVsMellinNormalizabilityGuard
    (FockState MellinState FockNorm MellinNorm : Type*) where
  fockState : FockState
  mellinState : MellinState
  fockNorm : FockNorm
  mellinNorm : MellinNorm
  fockSummabilityDomain_law : Prop
  fockSummabilityDomain_certificate :
    fockSummabilityDomain_law
  mellinCriticalLine_law : Prop
  mellinCriticalLine_certificate :
    mellinCriticalLine_law
  criticalLine_not_from_ordinaryFockNorm_guard : Type*

namespace FockVsMellinNormalizabilityGuard

/-- Re-export of the ordinary Fock summability-domain law. -/
theorem fockSummabilityDomain
    {FockState MellinState FockNorm MellinNorm : Type*}
    (G : FockVsMellinNormalizabilityGuard FockState MellinState FockNorm MellinNorm) :
    G.fockSummabilityDomain_law :=
  G.fockSummabilityDomain_certificate

/-- Re-export of the Mellin critical-line law. -/
theorem mellinCriticalLine
    {FockState MellinState FockNorm MellinNorm : Type*}
    (G : FockVsMellinNormalizabilityGuard FockState MellinState FockNorm MellinNorm) :
    G.mellinCriticalLine_law :=
  G.mellinCriticalLine_certificate

end FockVsMellinNormalizabilityGuard

/--
Majorana zero-mode normalizability packet.

`spectralParameter` is deliberately split into real and imaginary coordinates:
the theorem-safe critical-line predicate is only the algebraic condition
`realPart = 1/2`.
-/
structure MajoranaZeroModeNormalizabilityPacket
    (ZeroMode NormReadout : Type*) where
  realPart : ℝ
  imaginaryHeight : ℝ
  zeroMode : ZeroMode
  normReadout : NormReadout
  isZeroMode_law : Prop
  isZeroMode_certificate : isZeroMode_law
  normalizable_law : Prop
  normalizable_certificate : normalizable_law
  normalizable_iff_criticalLine_law :
    normalizable_law ↔ IsCriticalLineRealPart realPart
  normalizable_iff_criticalLine_certificate :
    normalizable_law ↔ IsCriticalLineRealPart realPart

namespace MajoranaZeroModeNormalizabilityPacket

/-- The supplied zero-mode law is available. -/
theorem isZeroMode
    {ZeroMode NormReadout : Type*}
    (Z : MajoranaZeroModeNormalizabilityPacket ZeroMode NormReadout) :
    Z.isZeroMode_law :=
  Z.isZeroMode_certificate

/-- The supplied normalizability law is available. -/
theorem normalizable
    {ZeroMode NormReadout : Type*}
    (Z : MajoranaZeroModeNormalizabilityPacket ZeroMode NormReadout) :
    Z.normalizable_law :=
  Z.normalizable_certificate

/--
If the supplied analytic packet proves normalizability, the real part lies on
the critical line.

This is not an RH theorem; it is only the readback from the packet's own
normalizability criterion.
-/
theorem criticalLine_of_normalizable
    {ZeroMode NormReadout : Type*}
    (Z : MajoranaZeroModeNormalizabilityPacket ZeroMode NormReadout) :
    IsCriticalLineRealPart Z.realPart :=
  (Z.normalizable_iff_criticalLine_certificate).mp Z.normalizable_certificate

/-- Conversely, the packet says critical-line real part implies normalizability. -/
theorem normalizable_of_criticalLine
    {ZeroMode NormReadout : Type*}
    (Z : MajoranaZeroModeNormalizabilityPacket ZeroMode NormReadout)
    (h : IsCriticalLineRealPart Z.realPart) :
    Z.normalizable_law :=
  (Z.normalizable_iff_criticalLine_certificate).mpr h

end MajoranaZeroModeNormalizabilityPacket

/--
Analytic Pfaffian/zeta spectral identity socket.

This is where a future analytic owner would connect a Majorana Pfaffian or
determinant readout to the meromorphically continued zeta function.  It also
separates zeros of zeta from singularities of reciprocal zeta.
-/
@[socket_debt_tag]
structure MajoranaPfaffianZetaSpectralSocket
    (SpectralParameter PfaffianReadout ZetaReadout : Type*) where
  parameter : SpectralParameter
  pfaffianReadout : PfaffianReadout
  zetaReadout : ZetaReadout
  pfaffian_zeta_identity_law : Prop
  pfaffian_zeta_identity_certificate :
    pfaffian_zeta_identity_law
  zetaZero_law : Prop
  reciprocalZetaSingularity_law : Prop
  zetaZero_implies_reciprocalSingularity :
    zetaZero_law → reciprocalZetaSingularity_law

namespace MajoranaPfaffianZetaSpectralSocket

/-- Re-export of the supplied Pfaffian/zeta identity law. -/
theorem pfaffian_zeta_identity
    {SpectralParameter PfaffianReadout ZetaReadout : Type*}
    (S : MajoranaPfaffianZetaSpectralSocket
      SpectralParameter PfaffianReadout ZetaReadout) :
    S.pfaffian_zeta_identity_law :=
  S.pfaffian_zeta_identity_certificate

/-- Zeta zero data gives reciprocal-zeta singularity data in the supplied socket. -/
theorem reciprocalSingularity_of_zetaZero
    {SpectralParameter PfaffianReadout ZetaReadout : Type*}
    (S : MajoranaPfaffianZetaSpectralSocket
      SpectralParameter PfaffianReadout ZetaReadout)
    (hz : S.zetaZero_law) :
    S.reciprocalZetaSingularity_law :=
  S.zetaZero_implies_reciprocalSingularity hz

end MajoranaPfaffianZetaSpectralSocket

/--
Separation between the inverse-zeta Witten character and the completed-zeta
spectral target.

The Majorana/Fock parity supertrace naturally produces a readout of
`1 / ζ(s)` in the Euler-product half-plane.  A Hilbert--Pólya spectral operator
must instead have a determinant/Pfaffian target proportional to the completed
function on the critical line, commonly written `Ξ(t) = ξ(1/2 + it)`.
-/
@[socket_debt_tag]
structure WittenCharacterVsCompletedXiSocket
    (SpectralParameter WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout : Type*) where
  parameter : SpectralParameter
  wittenCharacter : WittenCharacter
  completedXi : CompletedXiReadout
  spectralPfaffian : SpectralPfaffianReadout
  wittenCharacter_inverseZeta_law : Prop
  wittenCharacter_inverseZeta_certificate :
    wittenCharacter_inverseZeta_law
  spectralPfaffian_completedXi_law : Prop
  spectralPfaffian_completedXi_certificate :
    spectralPfaffian_completedXi_law
  zetaZeros_are_poles_of_inverseZeta_law : Prop
  zetaZeros_are_poles_of_inverseZeta_certificate :
    zetaZeros_are_poles_of_inverseZeta_law
  completedXiZeros_are_spectralZeros_law : Prop
  completedXiZeros_are_spectralZeros_certificate :
    completedXiZeros_are_spectralZeros_law

namespace WittenCharacterVsCompletedXiSocket

/-- Re-export: the Witten character is the inverse-zeta channel. -/
theorem wittenCharacter_inverseZeta
    {SpectralParameter WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout : Type*}
    (S : WittenCharacterVsCompletedXiSocket
      SpectralParameter WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout) :
    S.wittenCharacter_inverseZeta_law :=
  S.wittenCharacter_inverseZeta_certificate

/-- Re-export: the spectral Pfaffian target is the completed `Xi` channel. -/
theorem spectralPfaffian_completedXi
    {SpectralParameter WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout : Type*}
    (S : WittenCharacterVsCompletedXiSocket
      SpectralParameter WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout) :
    S.spectralPfaffian_completedXi_law :=
  S.spectralPfaffian_completedXi_certificate

/-- Re-export: zeros of zeta are poles of the inverse-zeta Witten channel. -/
theorem zetaZeros_are_poles_of_inverseZeta
    {SpectralParameter WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout : Type*}
    (S : WittenCharacterVsCompletedXiSocket
      SpectralParameter WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout) :
    S.zetaZeros_are_poles_of_inverseZeta_law :=
  S.zetaZeros_are_poles_of_inverseZeta_certificate

/-- Re-export: completed-`Xi` zeros are the spectral zero target. -/
theorem completedXiZeros_are_spectralZeros
    {SpectralParameter WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout : Type*}
    (S : WittenCharacterVsCompletedXiSocket
      SpectralParameter WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout) :
    S.completedXiZeros_are_spectralZeros_law :=
  S.completedXiZeros_are_spectralZeros_certificate

end WittenCharacterVsCompletedXiSocket

/--
Owner-target packaging for the Witten / completed-`Xi` separation packet.

This exposes the theorem-bearing surface already present in the packet.
-/
@[owner_target_tag]
theorem WittenCharacterVsCompletedXiOwnerTarget
    {SpectralParameter WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout : Type*}
    (S : WittenCharacterVsCompletedXiSocket
      SpectralParameter WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout) :
    S.wittenCharacter_inverseZeta_law ∧
    S.spectralPfaffian_completedXi_law ∧
    S.zetaZeros_are_poles_of_inverseZeta_law ∧
    S.completedXiZeros_are_spectralZeros_law := by
  exact ⟨S.wittenCharacter_inverseZeta, S.spectralPfaffian_completedXi,
    S.zetaZeros_are_poles_of_inverseZeta, S.completedXiZeros_are_spectralZeros⟩

/-! ## 3. Boson/fermion, Archimedean, and trace-formula sockets -/

/--
Boson/fermion superdeterminant bridge.

The square-free Majorana/Fock supertrace gives the inverse-zeta Witten
character.  A spectral-zero determinant targeting `ζ` or completed `ξ` needs
additional bosonic/Dirichlet data or a supplied superdeterminant inversion
mechanism.
-/
@[socket_debt_tag]
structure BosonFermionSuperdeterminantSocket
    (BosonicReadout FermionicReadout SuperdeterminantReadout
      ZetaReadout InverseZetaReadout : Type*) where
  bosonicReadout : BosonicReadout
  fermionicReadout : FermionicReadout
  superdeterminantReadout : SuperdeterminantReadout
  zetaReadout : ZetaReadout
  inverseZetaReadout : InverseZetaReadout
  bosonic_eq_zeta_law : Prop
  bosonic_eq_zeta_certificate :
    bosonic_eq_zeta_law
  fermionic_eq_inverseZeta_law : Prop
  fermionic_eq_inverseZeta_certificate :
    fermionic_eq_inverseZeta_law
  superdeterminant_inversion_law : Prop
  superdeterminant_inversion_certificate :
    superdeterminant_inversion_law
  zeta_zero_is_inverseZeta_pole_guard : Type*

namespace BosonFermionSuperdeterminantSocket

/-- Re-export: the bosonic/Dirichlet channel is the zeta channel. -/
theorem bosonic_eq_zeta
    {BosonicReadout FermionicReadout SuperdeterminantReadout
      ZetaReadout InverseZetaReadout : Type*}
    (S : BosonFermionSuperdeterminantSocket
      BosonicReadout FermionicReadout SuperdeterminantReadout
      ZetaReadout InverseZetaReadout) :
    S.bosonic_eq_zeta_law :=
  S.bosonic_eq_zeta_certificate

/-- Re-export: the Majorana/Fock parity channel is the inverse-zeta channel. -/
theorem fermionic_eq_inverseZeta
    {BosonicReadout FermionicReadout SuperdeterminantReadout
      ZetaReadout InverseZetaReadout : Type*}
    (S : BosonFermionSuperdeterminantSocket
      BosonicReadout FermionicReadout SuperdeterminantReadout
      ZetaReadout InverseZetaReadout) :
    S.fermionic_eq_inverseZeta_law :=
  S.fermionic_eq_inverseZeta_certificate

/-- Re-export of the supplied superdeterminant inversion law. -/
theorem superdeterminant_inversion
    {BosonicReadout FermionicReadout SuperdeterminantReadout
      ZetaReadout InverseZetaReadout : Type*}
    (S : BosonFermionSuperdeterminantSocket
      BosonicReadout FermionicReadout SuperdeterminantReadout
      ZetaReadout InverseZetaReadout) :
    S.superdeterminant_inversion_law :=
  S.superdeterminant_inversion_certificate

end BosonFermionSuperdeterminantSocket

/--
Archimedean place socket.

The finite-prime Euler product does not contain the factor
`π^{-s/2} Γ(s/2)` or the polynomial `s(s-1)/2`.  A completed-zeta spectral
target must supply an Archimedean/local-infinity readout and a completion law.
-/
@[socket_debt_tag]
structure ArchimedeanGammaFactorSocket
    (SpectralParameter ArchimedeanReadout FinitePrimeReadout
      CompletedZetaReadout : Type*) where
  parameter : SpectralParameter
  archimedeanReadout : ArchimedeanReadout
  finitePrimeReadout : FinitePrimeReadout
  completedZetaReadout : CompletedZetaReadout
  gammaFactor_law : Prop
  gammaFactor_certificate :
    gammaFactor_law
  polynomialCompletion_law : Prop
  polynomialCompletion_certificate :
    polynomialCompletion_law
  completedZeta_factorization_law : Prop
  completedZeta_factorization_certificate :
    completedZeta_factorization_law
  finitePrimes_alone_not_completed_guard : Type*

namespace ArchimedeanGammaFactorSocket

/-- Re-export of the supplied Archimedean gamma-factor law. -/
theorem gammaFactor
    {SpectralParameter ArchimedeanReadout FinitePrimeReadout
      CompletedZetaReadout : Type*}
    (A : ArchimedeanGammaFactorSocket
      SpectralParameter ArchimedeanReadout FinitePrimeReadout CompletedZetaReadout) :
    A.gammaFactor_law :=
  A.gammaFactor_certificate

/-- Re-export of the supplied polynomial completion law. -/
theorem polynomialCompletion
    {SpectralParameter ArchimedeanReadout FinitePrimeReadout
      CompletedZetaReadout : Type*}
    (A : ArchimedeanGammaFactorSocket
      SpectralParameter ArchimedeanReadout FinitePrimeReadout CompletedZetaReadout) :
    A.polynomialCompletion_law :=
  A.polynomialCompletion_certificate

/-- Re-export of the completed-zeta factorization law. -/
theorem completedZeta_factorization
    {SpectralParameter ArchimedeanReadout FinitePrimeReadout
      CompletedZetaReadout : Type*}
    (A : ArchimedeanGammaFactorSocket
      SpectralParameter ArchimedeanReadout FinitePrimeReadout CompletedZetaReadout) :
    A.completedZeta_factorization_law :=
  A.completedZeta_factorization_certificate

end ArchimedeanGammaFactorSocket

/--
Owner-target packaging for the Archimedean completion packet.

This exposes the theorem-bearing surface already present in the packet.
-/
@[owner_target_tag]
theorem ArchimedeanGammaFactorOwnerTarget
    {SpectralParameter ArchimedeanReadout FinitePrimeReadout
      CompletedZetaReadout : Type*}
    (A : ArchimedeanGammaFactorSocket
      SpectralParameter ArchimedeanReadout FinitePrimeReadout CompletedZetaReadout) :
    A.gammaFactor_law ∧
    A.polynomialCompletion_law ∧
    A.completedZeta_factorization_law := by
  exact ⟨A.gammaFactor, A.polynomialCompletion, A.completedZeta_factorization⟩

/--
Boundary/scattering mechanism socket.

The bare Berry--Keating dilation has a continuous Mellin spectrum.  A
Hilbert--Pólya construction must supply boundary conditions, a scattering
matrix, or an absorption-spectrum mechanism that produces the relevant
spectral zero data.
-/
@[socket_debt_tag]
structure BoundaryScatteringDiscretizationSocket
    (BoundaryData ScatteringMatrix ContinuousSpectrum
      DiscreteOrAbsorptionReadout PhaseShiftReadout : Type*) where
  boundaryData : BoundaryData
  scatteringMatrix : ScatteringMatrix
  continuousSpectrum : ContinuousSpectrum
  discreteOrAbsorptionReadout : DiscreteOrAbsorptionReadout
  phaseShiftReadout : PhaseShiftReadout
  boundary_or_scattering_law : Prop
  boundary_or_scattering_certificate :
    boundary_or_scattering_law
  continuous_to_spectralZeroReadout_law : Prop
  continuous_to_spectralZeroReadout_certificate :
    continuous_to_spectralZeroReadout_law
  phaseShift_matches_zetaArgument_law : Prop
  phaseShift_matches_zetaArgument_certificate :
    phaseShift_matches_zetaArgument_law
  bareBK_continuousSpectrum_guard : Type*

namespace BoundaryScatteringDiscretizationSocket

/-- Re-export of the boundary/scattering mechanism law. -/
theorem boundary_or_scattering
    {BoundaryData ScatteringMatrix ContinuousSpectrum
      DiscreteOrAbsorptionReadout PhaseShiftReadout : Type*}
    (B : BoundaryScatteringDiscretizationSocket
      BoundaryData ScatteringMatrix ContinuousSpectrum
      DiscreteOrAbsorptionReadout PhaseShiftReadout) :
    B.boundary_or_scattering_law :=
  B.boundary_or_scattering_certificate

/-- Re-export of the spectral-zero readout law. -/
theorem continuous_to_spectralZeroReadout
    {BoundaryData ScatteringMatrix ContinuousSpectrum
      DiscreteOrAbsorptionReadout PhaseShiftReadout : Type*}
    (B : BoundaryScatteringDiscretizationSocket
      BoundaryData ScatteringMatrix ContinuousSpectrum
      DiscreteOrAbsorptionReadout PhaseShiftReadout) :
    B.continuous_to_spectralZeroReadout_law :=
  B.continuous_to_spectralZeroReadout_certificate

/-- Re-export of the phase-shift/zeta-argument comparison law. -/
theorem phaseShift_matches_zetaArgument
    {BoundaryData ScatteringMatrix ContinuousSpectrum
      DiscreteOrAbsorptionReadout PhaseShiftReadout : Type*}
    (B : BoundaryScatteringDiscretizationSocket
      BoundaryData ScatteringMatrix ContinuousSpectrum
      DiscreteOrAbsorptionReadout PhaseShiftReadout) :
    B.phaseShift_matches_zetaArgument_law :=
  B.phaseShift_matches_zetaArgument_certificate

end BoundaryScatteringDiscretizationSocket

/--
Heat-kernel and explicit-formula socket.

For the combined MBK operator, the square-law suggests a factorized heat trace.
The nontrivial analytic test is that a Mellin transform or scattering trace
formula recovers the Riemann--Weil explicit formula.
-/
@[socket_debt_tag]
structure MBKHeatTraceExplicitFormulaSocket
    (HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout : Type*) where
  heatTrace : HeatTrace
  bkHeatTrace : BKHeatTrace
  arithmeticHeatTrace : ArithmeticHeatTrace
  mellinTransformReadout : MellinTransformReadout
  explicitFormulaReadout : ExplicitFormulaReadout
  heatTrace_factorization_law : Prop
  heatTrace_factorization_certificate :
    heatTrace_factorization_law
  arithmeticHeatTrace_primeSum_law : Prop
  arithmeticHeatTrace_primeSum_certificate :
    arithmeticHeatTrace_primeSum_law
  bkHeatTrace_mellinContinuum_law : Prop
  bkHeatTrace_mellinContinuum_certificate :
    bkHeatTrace_mellinContinuum_law
  mellinTransform_eq_explicitFormula_law : Prop
  mellinTransform_eq_explicitFormula_certificate :
    mellinTransform_eq_explicitFormula_law

namespace MBKHeatTraceExplicitFormulaSocket

/-- Re-export of the factorized heat-trace law. -/
theorem heatTrace_factorization
    {HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout : Type*}
    (T : MBKHeatTraceExplicitFormulaSocket
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout) :
    T.heatTrace_factorization_law :=
  T.heatTrace_factorization_certificate

/-- Re-export of the arithmetic prime-sum heat-trace law. -/
theorem arithmeticHeatTrace_primeSum
    {HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout : Type*}
    (T : MBKHeatTraceExplicitFormulaSocket
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout) :
    T.arithmeticHeatTrace_primeSum_law :=
  T.arithmeticHeatTrace_primeSum_certificate

/-- Re-export of the BK Mellin-continuum heat-trace law. -/
theorem bkHeatTrace_mellinContinuum
    {HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout : Type*}
    (T : MBKHeatTraceExplicitFormulaSocket
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout) :
    T.bkHeatTrace_mellinContinuum_law :=
  T.bkHeatTrace_mellinContinuum_certificate

/-- Re-export of the Mellin-transform explicit-formula law. -/
theorem mellinTransform_eq_explicitFormula
    {HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout : Type*}
    (T : MBKHeatTraceExplicitFormulaSocket
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout) :
    T.mellinTransform_eq_explicitFormula_law :=
  T.mellinTransform_eq_explicitFormula_certificate

end MBKHeatTraceExplicitFormulaSocket

/--
Owner-target packaging for the heat-trace / explicit-formula packet.

This exposes the theorem-bearing surface already present in the packet.
-/
@[owner_target_tag]
theorem MBKHeatTraceExplicitFormulaOwnerTarget
    {HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout : Type*}
    (T : MBKHeatTraceExplicitFormulaSocket
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout) :
    T.heatTrace_factorization_law ∧
    T.arithmeticHeatTrace_primeSum_law ∧
    T.bkHeatTrace_mellinContinuum_law ∧
    T.mellinTransform_eq_explicitFormula_law := by
  exact ⟨T.heatTrace_factorization, T.arithmeticHeatTrace_primeSum,
    T.bkHeatTrace_mellinContinuum, T.mellinTransform_eq_explicitFormula⟩

/-! ## 4. Completed-`Xi` Hilbert--Pólya reduction -/

/--
Conditional Hilbert--Pólya reduction for the completed `Xi` target.

This is the precise shape of the millennium-style target:

* the renormalized spectral Pfaffian/determinant of `D - t` is the completed
  `Xi(t)` readout;
* completed-`Xi` zeros are spectral-kernel points of a self-adjoint operator;
* the height parameter is real because it is a spectral parameter of a
  self-adjoint operator;
* the critical-line-to-RH implication is supplied by the analytic owner.
-/
structure CompletedXiHilbertPolyaReduction
    (SpectralOperator SpectralKernel CompletedXiReadout
      RenormalizedPfaffianReadout : Type*) where
  classicalRHStatement : Prop
  operator : SpectralOperator
  height : ℝ
  completedXiAtHeight : CompletedXiReadout
  renormalizedPfaffianAtHeight : RenormalizedPfaffianReadout
  spectralKernelAtHeight : SpectralKernel
  self_adjoint_law : Prop
  self_adjoint_certificate : self_adjoint_law
  renormalizedPfaffian_eq_completedXi_law : Prop
  renormalizedPfaffian_eq_completedXi_certificate :
    renormalizedPfaffian_eq_completedXi_law
  completedXiZero_law : Prop
  completedXiZero_certificate : completedXiZero_law
  completedXiZero_iff_spectralKernel_law :
    completedXiZero_law ↔ Nonempty SpectralKernel
  completedXiZero_iff_spectralKernel_certificate :
    completedXiZero_law ↔ Nonempty SpectralKernel
  spectralHeight_real_law : Prop
  spectralHeight_real_certificate :
    spectralHeight_real_law
  spectralZero_on_criticalLine_law : IsCriticalLineRealPart (1 / 2 : ℝ)
  criticalLine_completedXiZeros_imply_RH_law :
    IsCriticalLineRealPart (1 / 2 : ℝ) → classicalRHStatement
  no_RH_without_completedXi_spectral_identity_guard : Type*

namespace CompletedXiHilbertPolyaReduction

/-! Re-export of self-adjointness for the supplied spectral operator. -/
@[bridge_target_tag]
theorem self_adjoint
    {SpectralOperator SpectralKernel CompletedXiReadout
      RenormalizedPfaffianReadout : Type*}
    (R : CompletedXiHilbertPolyaReduction
      SpectralOperator SpectralKernel CompletedXiReadout RenormalizedPfaffianReadout) :
    R.self_adjoint_law :=
  R.self_adjoint_certificate

/-! Re-export of the renormalized Pfaffian/completed-`Xi` identity. -/
@[bridge_target_tag]
theorem renormalizedPfaffian_eq_completedXi
    {SpectralOperator SpectralKernel CompletedXiReadout
      RenormalizedPfaffianReadout : Type*}
    (R : CompletedXiHilbertPolyaReduction
      SpectralOperator SpectralKernel CompletedXiReadout RenormalizedPfaffianReadout) :
    R.renormalizedPfaffian_eq_completedXi_law :=
  R.renormalizedPfaffian_eq_completedXi_certificate

/-! Re-export of completed-`Xi` zero data. -/
@[bridge_target_tag]
theorem completedXiZero
    {SpectralOperator SpectralKernel CompletedXiReadout
      RenormalizedPfaffianReadout : Type*}
    (R : CompletedXiHilbertPolyaReduction
      SpectralOperator SpectralKernel CompletedXiReadout RenormalizedPfaffianReadout) :
    R.completedXiZero_law :=
  R.completedXiZero_certificate

/-! Completed-`Xi` zero data gives a spectral kernel by supplied identity. -/
@[bridge_target_tag]
theorem spectralKernel_of_completedXiZero
    {SpectralOperator SpectralKernel CompletedXiReadout
      RenormalizedPfaffianReadout : Type*}
    (R : CompletedXiHilbertPolyaReduction
      SpectralOperator SpectralKernel CompletedXiReadout RenormalizedPfaffianReadout) :
    Nonempty SpectralKernel :=
  (R.completedXiZero_iff_spectralKernel_certificate).mp R.completedXiZero_certificate

/-! Conditional RH readback from the completed-`Xi` spectral reduction. -/
@[bridge_target_tag]
theorem classicalRH_of_completedXi_spectral_reduction
    {SpectralOperator SpectralKernel CompletedXiReadout
      RenormalizedPfaffianReadout : Type*}
    (R : CompletedXiHilbertPolyaReduction
      SpectralOperator SpectralKernel CompletedXiReadout RenormalizedPfaffianReadout) :
    R.classicalRHStatement :=
  R.criticalLine_completedXiZeros_imply_RH_law R.spectralZero_on_criticalLine_law

end CompletedXiHilbertPolyaReduction

/-! ## 5. Full Pólya--Hilbert bridge packet -/

/--
Complete witness-gated (Native Closure Mandated: Closure Debt) Majorana/Pólya--Hilbert bridge.

The final implication to a classical RH proposition is a field, not a theorem
derived by this module.  A concrete analytic construction must supply it.
-/
structure MajoranaPolyaHilbertBridge
    (Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm : Type*) where
  classicalRHStatement : Prop
  operator :
    MajoranaBerryKeatingOperatorPacket Carrier Operator Domain Mode
  mellinPlancherel :
    MellinPlancherelCriticalLinePacket MellinWave MellinNorm
  fockVsMellin :
    FockVsMellinNormalizabilityGuard FockState MellinState FockNorm MellinNorm
  zeroModeNormalizability :
    MajoranaZeroModeNormalizabilityPacket ZeroMode NormReadout
  pfaffianZeta :
    MajoranaPfaffianZetaSpectralSocket
      SpectralParameter PfaffianReadout ZetaReadout
  wittenVsXi :
    WittenCharacterVsCompletedXiSocket
      SpectralParameter WittenCharacter CompletedXiReadout SpectralPfaffianReadout
  selfAdjoint_spectrum_real_law : Prop
  selfAdjoint_spectrum_real_certificate :
    selfAdjoint_spectrum_real_law
  zeroModes_match_zetaZeros_law : Prop
  zeroModes_match_zetaZeros_certificate :
    zeroModes_match_zetaZeros_law
  criticalLine_implies_classicalRH_law :
    IsCriticalLineRealPart zeroModeNormalizability.realPart →
      classicalRHStatement
  no_RH_without_analytic_witness_guard : Type*

namespace MajoranaPolyaHilbertBridge

/-- Re-export of the supplied real-spectrum law. -/
@[bridge_target_tag]
theorem selfAdjoint_spectrum_real
    {Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout : Type*}
    (B : MajoranaPolyaHilbertBridge
      Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm) :
    B.selfAdjoint_spectrum_real_law :=
  B.selfAdjoint_spectrum_real_certificate

/-- Re-export of the supplied zero-mode/zeta-zero matching law. -/
@[bridge_target_tag]
theorem zeroModes_match_zetaZeros
    {Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout : Type*}
    (B : MajoranaPolyaHilbertBridge
      Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm) :
    B.zeroModes_match_zetaZeros_law :=
  B.zeroModes_match_zetaZeros_certificate

/--
Conditional RH readback from the supplied analytic bridge.

The proof uses the packet's normalizability criterion and the packet's own
implication from critical-line real part to the classical RH statement.
-/
@[bridge_target_tag]
theorem classicalRH_of_supplied_majorana_spectral_witness
    {Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout : Type*}
    (B : MajoranaPolyaHilbertBridge
      Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm) :
    B.classicalRHStatement :=
  B.criticalLine_implies_classicalRH_law
    (MajoranaZeroModeNormalizabilityPacket.criticalLine_of_normalizable
      B.zeroModeNormalizability)

/-- The bridge records that the BK/Mellin sector supplies the critical-line condition. -/
@[bridge_target_tag]
theorem criticalLine_from_mellinPlancherel
    {Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm : Type*}
    (B : MajoranaPolyaHilbertBridge
      Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm) :
    IsCriticalLineRealPart B.mellinPlancherel.realPart :=
  MellinPlancherelCriticalLinePacket.criticalLine B.mellinPlancherel

/-- The bridge keeps the inverse-zeta Witten character separate from the `Xi` target. -/
@[bridge_target_tag]
theorem wittenCharacter_inverseZeta_channel
    {Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm : Type*}
    (B : MajoranaPolyaHilbertBridge
      Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm) :
    B.wittenVsXi.wittenCharacter_inverseZeta_law :=
  B.wittenVsXi.wittenCharacter_inverseZeta_certificate

/-- The bridge records that spectral zeros target completed `Xi`, not `1 / ζ`. -/
@[bridge_target_tag]
theorem spectralPfaffian_completedXi_channel
    {Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm : Type*}
    (B : MajoranaPolyaHilbertBridge
      Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm) :
    B.wittenVsXi.spectralPfaffian_completedXi_law :=
  B.wittenVsXi.spectralPfaffian_completedXi_certificate

end MajoranaPolyaHilbertBridge

/-! ## 6. MBK trace-formula completion packet -/

/--
Extended MBK bridge carrying the three additional analytic obstruction
sockets:

* boson/fermion inversion, separating `ζ` from `1 / ζ`;
* the Archimedean gamma/completion factor;
* boundary or scattering data that turns the bare continuous BK spectrum into
  a spectral-zero readout;
* heat-trace/Mellin data targeting the Riemann--Weil explicit formula.

This packet is still witness-gated.  It records the exact obligations but does
not assert an infinite determinant, analytic continuation, or RH proof by
construction.
-/
structure MajoranaBKTraceFormulaBridge
    (Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm
      BosonicReadout FermionicReadout SuperdeterminantReadout
      InverseZetaReadout ArchimedeanReadout FinitePrimeReadout
      BoundaryData ScatteringMatrix ContinuousSpectrum
      DiscreteOrAbsorptionReadout PhaseShiftReadout
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout : Type*) where
  baseBridge :
    MajoranaPolyaHilbertBridge
      Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm
  bosonFermion :
    BosonFermionSuperdeterminantSocket
      BosonicReadout FermionicReadout SuperdeterminantReadout
      ZetaReadout InverseZetaReadout
  archimedean :
    ArchimedeanGammaFactorSocket
      SpectralParameter ArchimedeanReadout FinitePrimeReadout CompletedXiReadout
  discretization :
    BoundaryScatteringDiscretizationSocket
      BoundaryData ScatteringMatrix ContinuousSpectrum
      DiscreteOrAbsorptionReadout PhaseShiftReadout
  heatTraceExplicit :
    MBKHeatTraceExplicitFormulaSocket
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout
  /-- Guardrail: `1 / ζ` is the Witten character, not the spectral-zero determinant. -/
  inverseZeta_not_spectralZeroTarget_guard : Type*
  /-- Guardrail: the completed target needs the Archimedean place. -/
  archimedeanPlace_required_guard : Type*
  /-- Guardrail: the bare BK operator has continuous spectrum without extra data. -/
  bareBK_requires_boundaryOrScattering_guard : Type*
  /-- Guardrail: the real test is the explicit-formula trace identity. -/
  explicitFormula_is_finalTraceTest_guard : Type*

namespace MajoranaBKTraceFormulaBridge

/-- The extended packet inherits the base conditional RH readback. -/
theorem classicalRH_of_base_witness
    {Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm
      BosonicReadout FermionicReadout SuperdeterminantReadout
      InverseZetaReadout ArchimedeanReadout FinitePrimeReadout
      BoundaryData ScatteringMatrix ContinuousSpectrum
      DiscreteOrAbsorptionReadout PhaseShiftReadout
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout : Type*}
    (B : MajoranaBKTraceFormulaBridge
      Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm
      BosonicReadout FermionicReadout SuperdeterminantReadout
      InverseZetaReadout ArchimedeanReadout FinitePrimeReadout
      BoundaryData ScatteringMatrix ContinuousSpectrum
      DiscreteOrAbsorptionReadout PhaseShiftReadout
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout) :
    B.baseBridge.classicalRHStatement :=
  MajoranaPolyaHilbertBridge.classicalRH_of_supplied_majorana_spectral_witness
    B.baseBridge

/-- Re-export: the bosonic channel is the zeta channel, by supplied witness. -/
theorem bosonic_zeta_channel
    {Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm
      BosonicReadout FermionicReadout SuperdeterminantReadout
      InverseZetaReadout ArchimedeanReadout FinitePrimeReadout
      BoundaryData ScatteringMatrix ContinuousSpectrum
      DiscreteOrAbsorptionReadout PhaseShiftReadout
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout : Type*}
    (B : MajoranaBKTraceFormulaBridge
      Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm
      BosonicReadout FermionicReadout SuperdeterminantReadout
      InverseZetaReadout ArchimedeanReadout FinitePrimeReadout
      BoundaryData ScatteringMatrix ContinuousSpectrum
      DiscreteOrAbsorptionReadout PhaseShiftReadout
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout) :
    B.bosonFermion.bosonic_eq_zeta_law :=
  B.bosonFermion.bosonic_eq_zeta_certificate

/-- Re-export: the fermionic Majorana channel is the inverse-zeta channel. -/
theorem fermionic_inverseZeta_channel
    {Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm
      BosonicReadout FermionicReadout SuperdeterminantReadout
      InverseZetaReadout ArchimedeanReadout FinitePrimeReadout
      BoundaryData ScatteringMatrix ContinuousSpectrum
      DiscreteOrAbsorptionReadout PhaseShiftReadout
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout : Type*}
    (B : MajoranaBKTraceFormulaBridge
      Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm
      BosonicReadout FermionicReadout SuperdeterminantReadout
      InverseZetaReadout ArchimedeanReadout FinitePrimeReadout
      BoundaryData ScatteringMatrix ContinuousSpectrum
      DiscreteOrAbsorptionReadout PhaseShiftReadout
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout) :
    B.bosonFermion.fermionic_eq_inverseZeta_law :=
  B.bosonFermion.fermionic_eq_inverseZeta_certificate

/-- Re-export: the completed target includes the supplied Archimedean factor. -/
theorem completedZeta_archimedean_channel
    {Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm
      BosonicReadout FermionicReadout SuperdeterminantReadout
      InverseZetaReadout ArchimedeanReadout FinitePrimeReadout
      BoundaryData ScatteringMatrix ContinuousSpectrum
      DiscreteOrAbsorptionReadout PhaseShiftReadout
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout : Type*}
    (B : MajoranaBKTraceFormulaBridge
      Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm
      BosonicReadout FermionicReadout SuperdeterminantReadout
      InverseZetaReadout ArchimedeanReadout FinitePrimeReadout
      BoundaryData ScatteringMatrix ContinuousSpectrum
      DiscreteOrAbsorptionReadout PhaseShiftReadout
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout) :
    B.archimedean.completedZeta_factorization_law :=
  B.archimedean.completedZeta_factorization_certificate

/-- Re-export: boundary/scattering data supplies the spectral-zero readout lane. -/
theorem boundary_scattering_spectralZero_channel
    {Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm
      BosonicReadout FermionicReadout SuperdeterminantReadout
      InverseZetaReadout ArchimedeanReadout FinitePrimeReadout
      BoundaryData ScatteringMatrix ContinuousSpectrum
      DiscreteOrAbsorptionReadout PhaseShiftReadout
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout : Type*}
    (B : MajoranaBKTraceFormulaBridge
      Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm
      BosonicReadout FermionicReadout SuperdeterminantReadout
      InverseZetaReadout ArchimedeanReadout FinitePrimeReadout
      BoundaryData ScatteringMatrix ContinuousSpectrum
      DiscreteOrAbsorptionReadout PhaseShiftReadout
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout) :
    B.discretization.continuous_to_spectralZeroReadout_law :=
  B.discretization.continuous_to_spectralZeroReadout_certificate

/-- Re-export: the heat-trace Mellin transform targets the explicit formula. -/
theorem heatTrace_explicitFormula_channel
    {Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm
      BosonicReadout FermionicReadout SuperdeterminantReadout
      InverseZetaReadout ArchimedeanReadout FinitePrimeReadout
      BoundaryData ScatteringMatrix ContinuousSpectrum
      DiscreteOrAbsorptionReadout PhaseShiftReadout
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout : Type*}
    (B : MajoranaBKTraceFormulaBridge
      Carrier Operator Domain Mode ZeroMode NormReadout
      SpectralParameter PfaffianReadout ZetaReadout
      MellinWave MellinNorm WittenCharacter CompletedXiReadout
      SpectralPfaffianReadout FockState MellinState FockNorm
      BosonicReadout FermionicReadout SuperdeterminantReadout
      InverseZetaReadout ArchimedeanReadout FinitePrimeReadout
      BoundaryData ScatteringMatrix ContinuousSpectrum
      DiscreteOrAbsorptionReadout PhaseShiftReadout
      HeatTrace BKHeatTrace ArithmeticHeatTrace MellinTransformReadout
      ExplicitFormulaReadout) :
    B.heatTraceExplicit.mellinTransform_eq_explicitFormula_law :=
  B.heatTraceExplicit.mellinTransform_eq_explicitFormula_certificate

end MajoranaBKTraceFormulaBridge

/-! ## 7. Relative determinant/scattering MBK target -/

/--
Relative determinant/scattering packet for the MBK program.

This is the narrow next target after the finite Majorana/Witten-character
layers.  It asks for one real self-adjoint relative MBK operator together with
the analytic data needed to identify its relative determinant or scattering
trace with the completed critical-line readout `Xi(t) = xi(1/2 + it)`.

All hard analytic assertions are fields.  In particular, this structure does
not construct the operator, prove a Fredholm determinant identity, prove the
Riemann--Weil explicit formula, or prove RH.
-/
structure RelativeMBKDeterminantScatteringPacket
    (Carrier Operator Mode Cutoff BoundaryData ScatteringMatrix
      SpectralShiftReadout RelativeDeterminantReadout RelativeTraceReadout
      CompletedXiReadout ExplicitFormulaReadout SpectralKernel : Type*) where
  /-- The finite or limiting MBK operator problem whose closure is being studied. -/
  mbkProblem :
    RealMajoranaBerryKeatingProblem Carrier Operator Mode Cutoff
  /-- Boundary or scattering data used to replace the bare BK continuum. -/
  boundaryData : BoundaryData
  /-- Scattering matrix/readout for the relative spectral problem. -/
  scatteringMatrix : ScatteringMatrix
  /-- Krein/spectral-shift readout for the relative trace. -/
  spectralShift : SpectralShiftReadout
  /-- Renormalized relative determinant/Pfaffian readout. -/
  relativeDeterminant : RelativeDeterminantReadout
  /-- Relative trace/scattering trace readout. -/
  relativeTrace : RelativeTraceReadout
  /-- Completed critical-line target, morally `xi(1/2 + it)`. -/
  completedXi : CompletedXiReadout
  /-- Riemann--Weil explicit-formula readout. -/
  explicitFormulaReadout : ExplicitFormulaReadout
  /-- Spectral kernel/absorption-line readout at a completed-`Xi` zero. -/
  spectralKernel : SpectralKernel

  /-- Essential/self-adjointness of the relative MBK realization. -/
  self_adjoint_relativeMBK_law : Prop
  self_adjoint_relativeMBK_certificate :
    self_adjoint_relativeMBK_law
  /-- Relative determinant/Pfaffian equals the completed critical-line target. -/
  relativeDeterminant_eq_completedXi_law : Prop
  relativeDeterminant_eq_completedXi_certificate :
    relativeDeterminant_eq_completedXi_law
  /-- Relative scattering trace reproduces the Riemann--Weil explicit formula. -/
  scatteringTrace_eq_explicitFormula_law : Prop
  scatteringTrace_eq_explicitFormula_certificate :
    scatteringTrace_eq_explicitFormula_law
  /-- Spectral shift is the relative trace density used by the scattering formula. -/
  spectralShift_traceFormula_law : Prop
  spectralShift_traceFormula_certificate :
    spectralShift_traceFormula_law
  /-- Completed-`Xi` zeros are exactly the spectral-kernel/absorption readout. -/
  completedXiZero_iff_spectralKernel_law : Prop
  completedXiZero_iff_spectralKernel_certificate :
    completedXiZero_iff_spectralKernel_law

  /--
  Classical RH statement owned by the future analytic construction.

  The packet may carry a supplied Hilbert--Polya reduction to this proposition,
  but this file does not derive it from finite prime algebra.
  -/
  classicalRHStatement : Prop
  hilbertPolya_reduction_law : Prop
  hilbertPolya_reduction_certificate :
    hilbertPolya_reduction_law
  hilbertPolya_reduction_implies_RH :
    hilbertPolya_reduction_law → classicalRHStatement

  /-- Guardrail: the raw Majorana Witten character is `1 / zeta`, not this target. -/
  inverseZetaWittenCharacter_not_relativeDeterminant_guard : Type*
  /-- Guardrail: zeros-as-minima are not asserted without relative determinant data. -/
  no_zeroAsMinimum_without_scatteringTrace_guard : Type*
  /-- Guardrail: self-adjointness is an analytic input, not finite-CAR syntax. -/
  selfAdjointness_not_from_finiteCAR_guard : Type*

namespace RelativeMBKDeterminantScatteringPacket

/-! Re-export of the supplied self-adjoint relative MBK law. -/
@[bridge_target_tag]
theorem self_adjoint_relativeMBK
    {Carrier Operator Mode Cutoff BoundaryData ScatteringMatrix
      SpectralShiftReadout RelativeDeterminantReadout RelativeTraceReadout
      CompletedXiReadout ExplicitFormulaReadout SpectralKernel : Type*}
    (P : RelativeMBKDeterminantScatteringPacket
      Carrier Operator Mode Cutoff BoundaryData ScatteringMatrix
      SpectralShiftReadout RelativeDeterminantReadout RelativeTraceReadout
      CompletedXiReadout ExplicitFormulaReadout SpectralKernel) :
    P.self_adjoint_relativeMBK_law :=
  P.self_adjoint_relativeMBK_certificate

/-! Re-export of the supplied relative determinant/completed-`Xi` identity. -/
@[bridge_target_tag]
theorem relativeDeterminant_eq_completedXi
    {Carrier Operator Mode Cutoff BoundaryData ScatteringMatrix
      SpectralShiftReadout RelativeDeterminantReadout RelativeTraceReadout
      CompletedXiReadout ExplicitFormulaReadout SpectralKernel : Type*}
    (P : RelativeMBKDeterminantScatteringPacket
      Carrier Operator Mode Cutoff BoundaryData ScatteringMatrix
      SpectralShiftReadout RelativeDeterminantReadout RelativeTraceReadout
      CompletedXiReadout ExplicitFormulaReadout SpectralKernel) :
    P.relativeDeterminant_eq_completedXi_law :=
  P.relativeDeterminant_eq_completedXi_certificate

/-! Re-export of the supplied scattering-trace/explicit-formula identity. -/
@[bridge_target_tag]
theorem scatteringTrace_eq_explicitFormula
    {Carrier Operator Mode Cutoff BoundaryData ScatteringMatrix
      SpectralShiftReadout RelativeDeterminantReadout RelativeTraceReadout
      CompletedXiReadout ExplicitFormulaReadout SpectralKernel : Type*}
    (P : RelativeMBKDeterminantScatteringPacket
      Carrier Operator Mode Cutoff BoundaryData ScatteringMatrix
      SpectralShiftReadout RelativeDeterminantReadout RelativeTraceReadout
      CompletedXiReadout ExplicitFormulaReadout SpectralKernel) :
    P.scatteringTrace_eq_explicitFormula_law :=
  P.scatteringTrace_eq_explicitFormula_certificate

/-! Re-export of the supplied spectral-shift trace formula law. -/
@[bridge_target_tag]
theorem spectralShift_traceFormula
    {Carrier Operator Mode Cutoff BoundaryData ScatteringMatrix
      SpectralShiftReadout RelativeDeterminantReadout RelativeTraceReadout
      CompletedXiReadout ExplicitFormulaReadout SpectralKernel : Type*}
    (P : RelativeMBKDeterminantScatteringPacket
      Carrier Operator Mode Cutoff BoundaryData ScatteringMatrix
      SpectralShiftReadout RelativeDeterminantReadout RelativeTraceReadout
      CompletedXiReadout ExplicitFormulaReadout SpectralKernel) :
    P.spectralShift_traceFormula_law :=
  P.spectralShift_traceFormula_certificate

/-! Re-export of the supplied completed-`Xi` zero/spectral-kernel law. -/
@[bridge_target_tag]
theorem completedXiZero_iff_spectralKernel
    {Carrier Operator Mode Cutoff BoundaryData ScatteringMatrix
      SpectralShiftReadout RelativeDeterminantReadout RelativeTraceReadout
      CompletedXiReadout ExplicitFormulaReadout SpectralKernel : Type*}
    (P : RelativeMBKDeterminantScatteringPacket
      Carrier Operator Mode Cutoff BoundaryData ScatteringMatrix
      SpectralShiftReadout RelativeDeterminantReadout RelativeTraceReadout
      CompletedXiReadout ExplicitFormulaReadout SpectralKernel) :
    P.completedXiZero_iff_spectralKernel_law :=
  P.completedXiZero_iff_spectralKernel_certificate

/-! Conditional RH readback from the supplied Hilbert--Polya reduction.

This theorem only consumes the packet's own analytic certificate; it is not an
unconditional proof of RH.
-/
@[bridge_target_tag]
theorem classicalRH_of_relativeMBK_witness
    {Carrier Operator Mode Cutoff BoundaryData ScatteringMatrix
      SpectralShiftReadout RelativeDeterminantReadout RelativeTraceReadout
      CompletedXiReadout ExplicitFormulaReadout SpectralKernel : Type*}
    (P : RelativeMBKDeterminantScatteringPacket
      Carrier Operator Mode Cutoff BoundaryData ScatteringMatrix
      SpectralShiftReadout RelativeDeterminantReadout RelativeTraceReadout
      CompletedXiReadout ExplicitFormulaReadout SpectralKernel) :
    P.classicalRHStatement :=
  P.hilbertPolya_reduction_implies_RH P.hilbertPolya_reduction_certificate

end RelativeMBKDeterminantScatteringPacket

/-! ## 8. Analytic frontier sockets -/

/--
Essential self-adjointness and infinite-cutoff limit socket.

The finite-cutoff MBK operator is algebraic.  The infinite operator requires a
choice of dense core, closure, and an essential self-adjointness proof.  This
packet records that obligation without asserting a Kato--Rellich or Nelson
commutator theorem.
-/
@[socket_debt_tag]
structure EssentialSelfAdjointLimitSocket
    (FiniteCutoff InfiniteCarrier InfiniteOperator DenseCore ClosureReadout
      CommutatorControl RepresentationLimit : Type*) where
  finiteCutoff : FiniteCutoff
  infiniteCarrier : InfiniteCarrier
  infiniteOperator : InfiniteOperator
  denseCore : DenseCore
  closureReadout : ClosureReadout
  commutatorControl : CommutatorControl
  representationLimit : RepresentationLimit
  finiteCutoff_essentialSelfAdjoint_law : Prop
  finiteCutoff_essentialSelfAdjoint_certificate :
    finiteCutoff_essentialSelfAdjoint_law
  denseCore_invariant_law : Prop
  denseCore_invariant_certificate :
    denseCore_invariant_law
  infiniteLimit_exists_law : Prop
  infiniteLimit_exists_certificate :
    infiniteLimit_exists_law
  infiniteOperator_essentialSelfAdjoint_law : Prop
  infiniteOperator_essentialSelfAdjoint_certificate :
    infiniteOperator_essentialSelfAdjoint_law
  /-- Guardrail: the infinite prime limit is not automatic from finite cutoff algebra. -/
  finiteCutoff_does_not_imply_infiniteSelfAdjoint_guard : Type*
  /-- Guardrail: unbounded `Q∞` requires real analytic commutator/control data. -/
  unboundedQ_requires_commutatorMethod_guard : Type*

namespace EssentialSelfAdjointLimitSocket

/-- Re-export of the supplied invariant-core law. -/
theorem denseCore_invariant
    {FiniteCutoff InfiniteCarrier InfiniteOperator DenseCore ClosureReadout
      CommutatorControl RepresentationLimit : Type*}
    (S : EssentialSelfAdjointLimitSocket
      FiniteCutoff InfiniteCarrier InfiniteOperator DenseCore ClosureReadout
      CommutatorControl RepresentationLimit) :
    S.denseCore_invariant_law :=
  S.denseCore_invariant_certificate

/-- Re-export of the supplied infinite-limit law. -/
theorem infiniteLimit_exists
    {FiniteCutoff InfiniteCarrier InfiniteOperator DenseCore ClosureReadout
      CommutatorControl RepresentationLimit : Type*}
    (S : EssentialSelfAdjointLimitSocket
      FiniteCutoff InfiniteCarrier InfiniteOperator DenseCore ClosureReadout
      CommutatorControl RepresentationLimit) :
    S.infiniteLimit_exists_law :=
  S.infiniteLimit_exists_certificate

/-- Re-export of the supplied essential self-adjointness law for the infinite operator. -/
theorem infiniteOperator_essentialSelfAdjoint
    {FiniteCutoff InfiniteCarrier InfiniteOperator DenseCore ClosureReadout
      CommutatorControl RepresentationLimit : Type*}
    (S : EssentialSelfAdjointLimitSocket
      FiniteCutoff InfiniteCarrier InfiniteOperator DenseCore ClosureReadout
      CommutatorControl RepresentationLimit) :
    S.infiniteOperator_essentialSelfAdjoint_law :=
  S.infiniteOperator_essentialSelfAdjoint_certificate

end EssentialSelfAdjointLimitSocket

/--
Zeta/Ray--Singer regularized Pfaffian socket.

Ordinary determinants and Pfaffians require trace-class control.  The MBK
program needs a heat-kernel subtraction/finite-part construction that turns a
divergent trace into a renormalized spectral Pfaffian.
-/
@[socket_debt_tag]
structure ZetaRegularizedPfaffianSocket
    (Operator HeatKernel SmallTimeAsymptotics Counterterm FinitePart
      RegularizedPfaffian MeromorphicReadout : Type*) where
  operator : Operator
  heatKernel : HeatKernel
  smallTimeAsymptotics : SmallTimeAsymptotics
  counterterm : Counterterm
  finitePart : FinitePart
  regularizedPfaffian : RegularizedPfaffian
  meromorphicReadout : MeromorphicReadout
  heatKernel_asymptotic_law : Prop
  heatKernel_asymptotic_certificate :
    heatKernel_asymptotic_law
  counterterm_subtraction_law : Prop
  counterterm_subtraction_certificate :
    counterterm_subtraction_law
  finitePart_exists_law : Prop
  finitePart_exists_certificate :
    finitePart_exists_law
  regularizedPfaffian_meromorphic_law : Prop
  regularizedPfaffian_meromorphic_certificate :
    regularizedPfaffian_meromorphic_law
  /-- Guardrail: ordinary trace-class determinant is not assumed. -/
  not_traceClassDeterminant_guard : Type*
  /-- Guardrail: renormalization counterterms must be explicitly supplied. -/
  counterterms_are_data_not_simp_guard : Type*

namespace ZetaRegularizedPfaffianSocket

/-- Re-export of the supplied heat-kernel asymptotic law. -/
theorem heatKernel_asymptotic
    {Operator HeatKernel SmallTimeAsymptotics Counterterm FinitePart
      RegularizedPfaffian MeromorphicReadout : Type*}
    (S : ZetaRegularizedPfaffianSocket
      Operator HeatKernel SmallTimeAsymptotics Counterterm FinitePart
      RegularizedPfaffian MeromorphicReadout) :
    S.heatKernel_asymptotic_law :=
  S.heatKernel_asymptotic_certificate

/-- Re-export of the supplied finite-part existence law. -/
theorem finitePart_exists
    {Operator HeatKernel SmallTimeAsymptotics Counterterm FinitePart
      RegularizedPfaffian MeromorphicReadout : Type*}
    (S : ZetaRegularizedPfaffianSocket
      Operator HeatKernel SmallTimeAsymptotics Counterterm FinitePart
      RegularizedPfaffian MeromorphicReadout) :
    S.finitePart_exists_law :=
  S.finitePart_exists_certificate

/-- Re-export of the supplied regularized-Pfaffian meromorphic law. -/
theorem regularizedPfaffian_meromorphic
    {Operator HeatKernel SmallTimeAsymptotics Counterterm FinitePart
      RegularizedPfaffian MeromorphicReadout : Type*}
    (S : ZetaRegularizedPfaffianSocket
      Operator HeatKernel SmallTimeAsymptotics Counterterm FinitePart
      RegularizedPfaffian MeromorphicReadout) :
    S.regularizedPfaffian_meromorphic_law :=
  S.regularizedPfaffian_meromorphic_certificate

end ZetaRegularizedPfaffianSocket

/--
Completed-`ξ` superdeterminant identity socket.

This is the exact place where a future owner must prove that the bosonic,
fermionic, and Archimedean factors combine into the completed zeta function,
not merely the inverse-zeta Witten character.
-/
@[socket_debt_tag]
structure CompletedXiSuperdeterminantIdentitySocket
    (BosonicSector FermionicSector ArchimedeanSector SuperdeterminantReadout
      CompletedXiReadout SpectralZeroReadout : Type*) where
  bosonicSector : BosonicSector
  fermionicSector : FermionicSector
  archimedeanSector : ArchimedeanSector
  superdeterminantReadout : SuperdeterminantReadout
  completedXiReadout : CompletedXiReadout
  spectralZeroReadout : SpectralZeroReadout
  boson_fermion_inversion_law : Prop
  boson_fermion_inversion_certificate :
    boson_fermion_inversion_law
  archimedean_completion_law : Prop
  archimedean_completion_certificate :
    archimedean_completion_law
  superdeterminant_eq_completedXi_law : Prop
  superdeterminant_eq_completedXi_certificate :
    superdeterminant_eq_completedXi_law
  completedXiZero_iff_spectralZero_law : Prop
  completedXiZero_iff_spectralZero_certificate :
    completedXiZero_iff_spectralZero_law
  /-- Guardrail: inverse-zeta poles do not directly give Majorana zero modes. -/
  inverseZeta_poles_not_zeroModes_guard : Type*
  /-- Guardrail: the Archimedean factor is part of the determinant identity. -/
  archimedeanFactor_not_optional_guard : Type*

namespace CompletedXiSuperdeterminantIdentitySocket

/-- Re-export of the supplied boson/fermion inversion law. -/
theorem boson_fermion_inversion
    {BosonicSector FermionicSector ArchimedeanSector SuperdeterminantReadout
      CompletedXiReadout SpectralZeroReadout : Type*}
    (S : CompletedXiSuperdeterminantIdentitySocket
      BosonicSector FermionicSector ArchimedeanSector SuperdeterminantReadout
      CompletedXiReadout SpectralZeroReadout) :
    S.boson_fermion_inversion_law :=
  S.boson_fermion_inversion_certificate

/-- Re-export of the supplied Archimedean completion law. -/
theorem archimedean_completion
    {BosonicSector FermionicSector ArchimedeanSector SuperdeterminantReadout
      CompletedXiReadout SpectralZeroReadout : Type*}
    (S : CompletedXiSuperdeterminantIdentitySocket
      BosonicSector FermionicSector ArchimedeanSector SuperdeterminantReadout
      CompletedXiReadout SpectralZeroReadout) :
    S.archimedean_completion_law :=
  S.archimedean_completion_certificate

/-- Re-export of the supplied superdeterminant/completed-`Xi` identity. -/
theorem superdeterminant_eq_completedXi
    {BosonicSector FermionicSector ArchimedeanSector SuperdeterminantReadout
      CompletedXiReadout SpectralZeroReadout : Type*}
    (S : CompletedXiSuperdeterminantIdentitySocket
      BosonicSector FermionicSector ArchimedeanSector SuperdeterminantReadout
      CompletedXiReadout SpectralZeroReadout) :
    S.superdeterminant_eq_completedXi_law :=
  S.superdeterminant_eq_completedXi_certificate

/-- Re-export of the supplied completed-`Xi` zero/spectral-zero law. -/
theorem completedXiZero_iff_spectralZero
    {BosonicSector FermionicSector ArchimedeanSector SuperdeterminantReadout
      CompletedXiReadout SpectralZeroReadout : Type*}
    (S : CompletedXiSuperdeterminantIdentitySocket
      BosonicSector FermionicSector ArchimedeanSector SuperdeterminantReadout
      CompletedXiReadout SpectralZeroReadout) :
    S.completedXiZero_iff_spectralZero_law :=
  S.completedXiZero_iff_spectralZero_certificate

end CompletedXiSuperdeterminantIdentitySocket

/--
The three-front analytic frontier for the MBK program.

Supplying this packet still does not construct RH in this file; it merely
packages the three analytic fronts that a serious operator proof must close:
essential self-adjointness, zeta-regularized Pfaffian construction, and the
completed-`ξ` superdeterminant identity.
-/
structure MBKAnalyticFrontier
    (FiniteCutoff InfiniteCarrier InfiniteOperator DenseCore ClosureReadout
      CommutatorControl RepresentationLimit HeatKernel SmallTimeAsymptotics
      Counterterm FinitePart RegularizedPfaffian MeromorphicReadout
      BosonicSector FermionicSector ArchimedeanSector SuperdeterminantReadout
      CompletedXiReadout SpectralZeroReadout : Type*) where
  selfAdjointLimit :
    EssentialSelfAdjointLimitSocket
      FiniteCutoff InfiniteCarrier InfiniteOperator DenseCore ClosureReadout
      CommutatorControl RepresentationLimit
  regularizedPfaffian :
    ZetaRegularizedPfaffianSocket
      InfiniteOperator HeatKernel SmallTimeAsymptotics Counterterm FinitePart
      RegularizedPfaffian MeromorphicReadout
  completedXiIdentity :
    CompletedXiSuperdeterminantIdentitySocket
      BosonicSector FermionicSector ArchimedeanSector SuperdeterminantReadout
      CompletedXiReadout SpectralZeroReadout
  all_three_fronts_closed_law : Prop
  all_three_fronts_closed_certificate :
    all_three_fronts_closed_law
  /-- Guardrail: this is the analytic task list, not an unconditional RH proof. -/
  not_unconditional_RH_proof_guard : Type*

namespace MBKAnalyticFrontier

/-- Re-export of the supplied statement that the three analytic fronts are closed. -/
theorem all_three_fronts_closed
    {FiniteCutoff InfiniteCarrier InfiniteOperator DenseCore ClosureReadout
      CommutatorControl RepresentationLimit HeatKernel SmallTimeAsymptotics
      Counterterm FinitePart RegularizedPfaffian MeromorphicReadout
      BosonicSector FermionicSector ArchimedeanSector SuperdeterminantReadout
      CompletedXiReadout SpectralZeroReadout : Type*}
    (F : MBKAnalyticFrontier
      FiniteCutoff InfiniteCarrier InfiniteOperator DenseCore ClosureReadout
      CommutatorControl RepresentationLimit HeatKernel SmallTimeAsymptotics
      Counterterm FinitePart RegularizedPfaffian MeromorphicReadout
      BosonicSector FermionicSector ArchimedeanSector SuperdeterminantReadout
      CompletedXiReadout SpectralZeroReadout) :
    F.all_three_fronts_closed_law :=
  F.all_three_fronts_closed_certificate

/-- The frontier includes an essential self-adjointness witness for the infinite operator. -/
theorem infiniteOperator_essentialSelfAdjoint
    {FiniteCutoff InfiniteCarrier InfiniteOperator DenseCore ClosureReadout
      CommutatorControl RepresentationLimit HeatKernel SmallTimeAsymptotics
      Counterterm FinitePart RegularizedPfaffian MeromorphicReadout
      BosonicSector FermionicSector ArchimedeanSector SuperdeterminantReadout
      CompletedXiReadout SpectralZeroReadout : Type*}
    (F : MBKAnalyticFrontier
      FiniteCutoff InfiniteCarrier InfiniteOperator DenseCore ClosureReadout
      CommutatorControl RepresentationLimit HeatKernel SmallTimeAsymptotics
      Counterterm FinitePart RegularizedPfaffian MeromorphicReadout
      BosonicSector FermionicSector ArchimedeanSector SuperdeterminantReadout
      CompletedXiReadout SpectralZeroReadout) :
    F.selfAdjointLimit.infiniteOperator_essentialSelfAdjoint_law :=
  F.selfAdjointLimit.infiniteOperator_essentialSelfAdjoint_certificate

/-- The frontier includes a zeta-regularized Pfaffian/meromorphic readout witness. -/
theorem regularizedPfaffian_meromorphic
    {FiniteCutoff InfiniteCarrier InfiniteOperator DenseCore ClosureReadout
      CommutatorControl RepresentationLimit HeatKernel SmallTimeAsymptotics
      Counterterm FinitePart RegularizedPfaffian MeromorphicReadout
      BosonicSector FermionicSector ArchimedeanSector SuperdeterminantReadout
      CompletedXiReadout SpectralZeroReadout : Type*}
    (F : MBKAnalyticFrontier
      FiniteCutoff InfiniteCarrier InfiniteOperator DenseCore ClosureReadout
      CommutatorControl RepresentationLimit HeatKernel SmallTimeAsymptotics
      Counterterm FinitePart RegularizedPfaffian MeromorphicReadout
      BosonicSector FermionicSector ArchimedeanSector SuperdeterminantReadout
      CompletedXiReadout SpectralZeroReadout) :
    F.regularizedPfaffian.regularizedPfaffian_meromorphic_law :=
  F.regularizedPfaffian.regularizedPfaffian_meromorphic_certificate

/-- The frontier includes the completed-`Xi` superdeterminant identity witness. -/
theorem superdeterminant_eq_completedXi
    {FiniteCutoff InfiniteCarrier InfiniteOperator DenseCore ClosureReadout
      CommutatorControl RepresentationLimit HeatKernel SmallTimeAsymptotics
      Counterterm FinitePart RegularizedPfaffian MeromorphicReadout
      BosonicSector FermionicSector ArchimedeanSector SuperdeterminantReadout
      CompletedXiReadout SpectralZeroReadout : Type*}
    (F : MBKAnalyticFrontier
      FiniteCutoff InfiniteCarrier InfiniteOperator DenseCore ClosureReadout
      CommutatorControl RepresentationLimit HeatKernel SmallTimeAsymptotics
      Counterterm FinitePart RegularizedPfaffian MeromorphicReadout
      BosonicSector FermionicSector ArchimedeanSector SuperdeterminantReadout
      CompletedXiReadout SpectralZeroReadout) :
    F.completedXiIdentity.superdeterminant_eq_completedXi_law :=
  F.completedXiIdentity.superdeterminant_eq_completedXi_certificate

end MBKAnalyticFrontier

end InfoGeometry.Arithmetic.MajoranaPolyaHilbertSocket
