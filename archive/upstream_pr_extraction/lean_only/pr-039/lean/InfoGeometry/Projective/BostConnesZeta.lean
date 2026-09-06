import InfoGeometry.Projective.BostConnesAmplituhedronSynthesis

/-!
# Bost-Connes / Zeta Readouts for the Amplituhedron Lane

This file keeps the historical `BostConnesZeta` import name, but removes the
old vacuous bridge surface that made the comparison automatically true.

#### BUCKET 1: CLOSED FINITE THEOREMS
- `zeta_volume_eval_of_explicit_comparison`: a pointwise equality can be read
  back only from an explicit pointwise equality premise.
- `zeta_volume_family_of_explicit_comparison`: a family equality can be read
  back only from an explicit family equality premise.

#### BUCKET 2: CONDITIONAL THEOREMS FROM EXPLICIT WITNESSES
- Both readouts are conditional on named comparison premises supplied by future
  arithmetic and amplituhedron owner files.

#### BUCKET 3: OPEN CLOSURE DEBT
- Define the actual Bost-Connes partition function used by this lane.
- Define the actual amplituhedron volume/integrand model used by this lane.
- Prove any zeta/MZV/integrand comparison theorem through the
  Hestenes--Krein/categorical colimit owner.
- Prove any compatibility with the Arnold, Rohozhkin, or D-module property
  layers in separate owner modules.
-/

namespace InfoGeometry.Projective.BostConnes

open InfoGeometry.Projective.BostConnesAmplituhedronSynthesis

/-- Historical name for an arithmetic partition-function readout. -/
abbrev BostConnesPartitionData (R : Type*) :=
  R → R

/-- Historical name for an amplituhedron volume/integrand readout. -/
abbrev AmplituhedronVolumeData (R : Type*) :=
  ℕ → R

/--
Pointwise zeta/volume readout.

This is intentionally only a premise readback.  It does not prove that a
Bost-Connes partition function equals an amplituhedron volume.
-/
theorem zeta_volume_eval_of_explicit_comparison
    {R : Type*}
    (Z : BostConnesPartitionData R)
    (Vol : AmplituhedronVolumeData R)
    (β : R) (L : ℕ)
    (hComparison : Z β = Vol L) :
    Z β = Vol L :=
  hComparison

/--
Family-level zeta/volume readout from an explicit comparison premise.
-/
theorem zeta_volume_family_of_explicit_comparison
    {R : Type*}
    (Z : BostConnesPartitionData R)
    (Vol : AmplituhedronVolumeData R)
    (hComparison : ∀ (β : R) (L : ℕ), Z β = Vol L) :
    ∀ (β : R) (L : ℕ), Z β = Vol L :=
  hComparison

/--
The same pointwise readout routed through the projective synthesis interface.
-/
theorem zeta_volume_eval_via_synthesis_interface
    {R : Type*}
    (Z : BostConnesPartitionData R)
    (Vol : AmplituhedronVolumeData R)
    (β : R) (L : ℕ)
    (hComparison : (fun Z' : BostConnesPartitionData R => Z' β) Z = Vol L) :
    (fun Z' : BostConnesPartitionData R => Z' β) Z = Vol L :=
  synthesis_readout_of_explicit_comparison
    (fun Z' : BostConnesPartitionData R => Z' β) Z (Vol L) hComparison

end InfoGeometry.Projective.BostConnes
