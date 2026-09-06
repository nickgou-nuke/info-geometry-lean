import InfoGeometry.GromovWittenErlangen.DrazinLocalization

/-!
# Localized Drazin-Frobenius Readout

This module records the theorem-safe version of the slogan:

```text
Fredholm/localization operator
  -> Drazin regular core + singular obstruction residue
  -> localized finite Frobenius readout
```

It does **not** prove virtual localization, Fredholm index theory,
Wedderburn-Artin, Dubrovin semisimplicity, or Moore-Penrose existence.  Those
remain outside this file.  The theorem-bearing content here is the
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
    (ModuliOperator Algebra : Type*) [Ring Algebra] [StarRing Algebra] where
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

namespace FredholmDrazinLocalizationPacket

variable {ModuliOperator Algebra : Type*} [Ring Algebra] [StarRing Algebra]
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

end FredholmDrazinLocalizationPacket

/--
Localized Drazin-Frobenius readout.

This connects a Fredholm/moduli-operator Drazin split to the existing
Gromov-Witten fixed-sector Drazin localization packet.  The only exported
facts are direct Drazin residue annihilation and the Frobenius associativity
already carried by the localized Frobenius packet.
-/
structure LocalizedDrazinFrobeniusBridge
    (G T Target Coeff Algebra ModuliOperator : Type*) [Ring Algebra] [StarRing Algebra] where
  /-- Existing GW fixed-sector Drazin localization data. -/
  gwDrazin :
    @DrazinGromovWittenLocalizationBridge G T Target Coeff Algebra _ _

  /-- Fredholm/moduli-operator Drazin decomposition. -/
  fredholmDrazin :
    @FredholmDrazinLocalizationPacket ModuliOperator Algebra _ _

namespace LocalizedDrazinFrobeniusBridge

variable {G T Target Coeff Algebra ModuliOperator : Type*} [Ring Algebra] [StarRing Algebra]
variable (B :
  LocalizedDrazinFrobeniusBridge G T Target Coeff Algebra ModuliOperator)

/-- The localized algebra carries the semisimple ring instance supplied by the base data. -/
def semisimpleRing : IsSemisimpleRing Algebra :=
  B.gwDrazin.frobeniusSemisimple.semisimple

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
