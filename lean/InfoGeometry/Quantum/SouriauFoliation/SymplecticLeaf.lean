/-
InfoGeometry/Quantum/SouriauFoliation/SymplecticLeaf.lean
-/

noncomputable section

namespace InfoGeometry.Quantum.SouriauFoliation

/--
A finite/projective Souriau leaf.

The leaf is represented only by the data needed by the current sidecar:
membership, an entropy readout, and a Weyl-scale readout which are constant on
the carrier.  This is not a construction of a coadjoint orbit or a symplectic
form.
-/
structure SymplecticLeaf
    (State : Type*) where
  /-- States belonging to the leaf. -/
  carrier : Set State

  /-- Entropy/action readout. -/
  entropyReadout : State → ℝ

  /-- Weyl/conformal scale readout. -/
  weylScaleReadout : State → ℝ

  /-- Leaf entropy value. -/
  leafEntropy : ℝ

  /-- Leaf Weyl-scale value. -/
  leafWeylScale : ℝ

  /-- Entropy is constant on the leaf. -/
  entropy_constant :
    ∀ ⦃x : State⦄, x ∈ carrier → entropyReadout x = leafEntropy

  /-- Weyl scale is constant on the leaf. -/
  weylScale_constant :
    ∀ ⦃x : State⦄, x ∈ carrier → weylScaleReadout x = leafWeylScale

namespace SymplecticLeaf

variable {State : Type*}
variable (L : SymplecticLeaf State)

/-- Two states on the same leaf have the same entropy readout. -/
theorem entropy_eq_of_mem
    {x y : State}
    (hx : x ∈ L.carrier)
    (hy : y ∈ L.carrier) :
    L.entropyReadout x = L.entropyReadout y := by
  rw [L.entropy_constant hx, L.entropy_constant hy]

/-- Two states on the same leaf have the same Weyl-scale readout. -/
theorem weylScale_eq_of_mem
    {x y : State}
    (hx : x ∈ L.carrier)
    (hy : y ∈ L.carrier) :
    L.weylScaleReadout x = L.weylScaleReadout y := by
  rw [L.weylScale_constant hx, L.weylScale_constant hy]

end SymplecticLeaf

end InfoGeometry.Quantum.SouriauFoliation
