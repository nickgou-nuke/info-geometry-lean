import InfoGeometry.GromovWittenErlangen.DrazinLocalization

/-!
# Localized Drazin-Frobenius Bridge

This module records the theorem-safe version of the slogan:

```text
Fredholm/localization operator
  -> Drazin regular core + singular obstruction residue
  -> equivariant divisor/Euler-weight calibration
  -> localized finite Frobenius readout
  -> semisimple residue/division-block certificate
```

It does **not** prove virtual localization, Fredholm index theory,
Wedderburn-Artin, Dubrovin semisimplicity, or Moore-Penrose existence.  Those
remain model-specific certificates.  The theorem-bearing content here is the
algebra already available from `RelativeCoreNilpotentDecomposition`: the
regular inverse kills the singular residue and produces Drazin inverse data for
the localized operator.
-/

noncomputable section

namespace InfoGeometry
namespace GromovWittenErlangen

open InfoGeometry.OperatorAlgebra.DrazinProjectionLocalization

/--
Fredholm/moduli operator equipped with a Drazin regular/singular
decomposition inside a finite localized algebra.

`ModuliOperator` is intentionally abstract.  In a concrete GW model it may be a
Cauchy-Riemann/Fredholm linearization, obstruction operator, or any finite
algebraic readout of that analytic surface.
-/
structure FredholmDrazinLocalizationPacket
    (ModuliOperator Algebra : Type*) [Ring Algebra] where
  /-- The model-specific Fredholm/localization operator. -/
  fredholmOperator : ModuliOperator

  /-- Algebraic realization of the operator in the localized coefficient algebra. -/
  operatorToAlgebra : ModuliOperator → Algebra

  /-- Drazin regular/singular decomposition of the realized operator. -/
  drazinDecomposition :
    RelativeCoreNilpotentDecomposition Algebra

  /-- The Drazin-decomposed element is the realized Fredholm operator. -/
  drazin_element_eq_operator :
    drazinDecomposition.element = operatorToAlgebra fredholmOperator

  /-- Equivariant Euler/divisor classes used by the localization model. -/
  EquivariantDivisor : Type*

  /-- Algebraic weight/readout of each equivariant divisor. -/
  divisorWeight : EquivariantDivisor → Algebra

  /--
  Model-specific law saying that inverting/calibrating the equivariant divisors
  isolates the Drazin regular core.
  -/
  divisors_isolate_regular_core_law : Prop

  /-- Certificate for divisor/core isolation. -/
  divisors_isolate_regular_core_certificate :
    divisors_isolate_regular_core_law

  /--
  Model-specific law identifying the singular/nilpotent residue with the
  obstruction sector.
  -/
  obstruction_residue_law : Prop

  /-- Certificate for the obstruction/residue law. -/
  obstruction_residue_certificate :
    obstruction_residue_law

namespace FredholmDrazinLocalizationPacket

variable {ModuliOperator Algebra : Type*} [Ring Algebra]
variable (P : FredholmDrazinLocalizationPacket ModuliOperator Algebra)

/-- The Drazin regular core of the realized Fredholm/localization operator. -/
def regularCore : Algebra :=
  P.drazinDecomposition.localizedRegularCore

/-- The singular obstruction residue of the realized operator. -/
def obstructionResidue : Algebra :=
  P.drazinDecomposition.localizedDrazinResidue

/-- The regular inverse of the Drazin core. -/
def regularInverse : Algebra :=
  P.drazinDecomposition.localizedRegularInverse

/-- The realized operator supplies Drazin inverse data. -/
def toDrazinInverseData : DrazinInverseData Algebra :=
  P.drazinDecomposition.toDrazinInverseData

/-- The Drazin data element is the realized Fredholm/localization operator. -/
theorem drazinData_element_eq_operator :
    P.toDrazinInverseData.element = P.operatorToAlgebra P.fredholmOperator :=
  P.drazin_element_eq_operator

/-- The obstruction residue is killed on the right by the regular inverse. -/
theorem obstructionResidue_mul_regularInverse :
    P.obstructionResidue * P.regularInverse = 0 :=
  P.drazinDecomposition.residue_mul_regularInverse

/-- The obstruction residue is killed on the left by the regular inverse. -/
theorem regularInverse_mul_obstructionResidue :
    P.regularInverse * P.obstructionResidue = 0 :=
  P.drazinDecomposition.regularInverse_mul_residue

/-- The supplied divisor/core isolation law is available. -/
theorem divisors_isolate_regular_core_valid :
    P.divisors_isolate_regular_core_law :=
  P.divisors_isolate_regular_core_certificate

/-- The supplied obstruction/residue law is available. -/
theorem obstruction_residue_valid :
    P.obstruction_residue_law :=
  P.obstruction_residue_certificate

end FredholmDrazinLocalizationPacket

/--
Localized Drazin-Frobenius bridge.

This connects a Fredholm/moduli-operator Drazin split to the existing
Gromov-Witten fixed-sector Drazin localization packet and its localized
Frobenius/semisimple readout.
-/
structure LocalizedDrazinFrobeniusBridge
    (G T Target Coeff Algebra ModuliOperator : Type*) [Ring Algebra] where
  /-- Existing GW fixed-sector Drazin localization bridge. -/
  gwDrazin :
    DrazinGromovWittenLocalizationBridge G T Target Coeff Algebra

  /-- Fredholm/moduli-operator Drazin decomposition. -/
  fredholmDrazin :
    FredholmDrazinLocalizationPacket ModuliOperator Algebra

  /--
  The Fredholm/moduli Drazin regular core and the graph-localized Drazin
  denominators are compatible.
  -/
  fredholm_core_matches_localization_law : Prop

  /-- Certificate for Fredholm/core localization compatibility. -/
  fredholm_core_matches_localization_certificate :
    fredholm_core_matches_localization_law

  /--
  The localized Frobenius pairing is the self-dual readout for the Drazin
  regular fixed-sector algebra.
  -/
  frobenius_self_dual_readout_law : Prop

  /-- Certificate for Frobenius self-dual readout compatibility. -/
  frobenius_self_dual_readout_certificate :
    frobenius_self_dual_readout_law

  /--
  In the semisimple regime, the supplied residue blocks are the division-block
  readout of the Drazin-regular localized algebra.
  -/
  semisimple_division_blocks_law : Prop

  /-- Certificate for semisimple division-block compatibility. -/
  semisimple_division_blocks_certificate :
    semisimple_division_blocks_law

namespace LocalizedDrazinFrobeniusBridge

variable {G T Target Coeff Algebra ModuliOperator : Type*} [Ring Algebra]
variable (B :
  LocalizedDrazinFrobeniusBridge G T Target Coeff Algebra ModuliOperator)

/-- The GW localization assembly law carried by the base bridge is available. -/
theorem localizationAssembly_valid :
    B.gwDrazin.drazinLocalization.localizationAssemblyLaw :=
  B.gwDrazin.localizationAssembly_valid

/-- The divisor/Drazin compatibility law carried by the base bridge is available. -/
theorem divisorDrazinCompatibility_valid :
    B.gwDrazin.divisorDrazinCompatibilityLaw :=
  B.gwDrazin.divisorDrazinCompatibility_valid

/-- The localized Frobenius semisimplicity law is available. -/
theorem semisimplicity_valid :
    B.gwDrazin.frobeniusSemisimple.semisimplicityLaw :=
  B.gwDrazin.semisimplicity_valid

/-- The Fredholm/moduli operator supplies Drazin inverse data. -/
def fredholmDrazinData : DrazinInverseData Algebra :=
  B.fredholmDrazin.toDrazinInverseData

/-- The Fredholm/moduli obstruction residue is killed by the regular inverse. -/
theorem obstructionResidue_mul_regularInverse :
    B.fredholmDrazin.obstructionResidue *
        B.fredholmDrazin.regularInverse = 0 :=
  B.fredholmDrazin.obstructionResidue_mul_regularInverse

/-- The regular inverse kills the Fredholm/moduli obstruction residue. -/
theorem regularInverse_mul_obstructionResidue :
    B.fredholmDrazin.regularInverse *
        B.fredholmDrazin.obstructionResidue = 0 :=
  B.fredholmDrazin.regularInverse_mul_obstructionResidue

/-- The supplied Fredholm/core localization compatibility law is available. -/
theorem fredholm_core_matches_localization_valid :
    B.fredholm_core_matches_localization_law :=
  B.fredholm_core_matches_localization_certificate

/-- The supplied Frobenius self-dual readout law is available. -/
theorem frobenius_self_dual_readout_valid :
    B.frobenius_self_dual_readout_law :=
  B.frobenius_self_dual_readout_certificate

/-- The supplied semisimple division-block compatibility law is available. -/
theorem semisimple_division_blocks_valid :
    B.semisimple_division_blocks_law :=
  B.semisimple_division_blocks_certificate

/-- Frobenius compatibility of the localized self-dual pairing. -/
  theorem frobenius_pairing_mul_left_eq_pairing_mul_right
    (a b c : Algebra) :
    B.gwDrazin.frobeniusSemisimple.frobenius.pairing (a * b) c =
      B.gwDrazin.frobeniusSemisimple.frobenius.pairing a (b * c) :=
  LocalizedFrobeniusSemisimplePacket.pairing_mul_left_eq_pairing_mul_right
    B.gwDrazin.frobeniusSemisimple a b c

/-- Edge-level Drazin residues still vanish against their regular inverses. -/
theorem edgeResidue_mul_regularInverse
    (e : B.gwDrazin.drazinLocalization.virtualLocalization.graph.Edge) :
    B.gwDrazin.edgeLocalizedDrazinResidue e *
        B.gwDrazin.edgeLocalizedRegularInverse e = 0 :=
  B.gwDrazin.edgeResidue_mul_regularInverse e

end LocalizedDrazinFrobeniusBridge

end GromovWittenErlangen
end InfoGeometry
