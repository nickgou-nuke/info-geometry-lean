import InfoGeometry.Canonical.DiracDensity
/-- DiracCarrier: infinite, dimension-agnostic carrier lane. Replaces explicit diracMass : ℝ hypothesis with constructive PrimeDiracDensity route. -/
import Mathlib.LinearAlgebra.FiniteDimensional

namespace InfoGeometry.Canonical

open DiracDensity PrimeDiracDensity

/-- Witness packet for DiracCarrier: removes explicit diracMass hypothesis. -/
structure DiracCarrierWitness (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  /-- Prime-density lane: Möbius-inverted, normalized. -/
  primeDensity : PrimeDiracDensity E

/-- Constructive recovery of diracMass from witness packet. /
theorem diracMass_of_witness {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] 
  (W : DiracCarrierWitness E) :
  ℝ := W.primeDensity.normalizedMass

/-- Constructive constructor from witness packet. -/
def DiracCarrier.ofWitness {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] 
  (W : DiracCarrierWitness E) :
  DiracCarrier E := {
  diracMass := diracMass_of_witness W,
  diracDensity := W.primeDensity.toDiracDensity,
  hFiniteDensity := by
    have := W.primeDensity.finiteDensity;
    exact this
}

/-- DiracCarrier: infinite, dimension-agnostic. -/
structure DiracCarrier (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  /-- Constructive witness route: primeDensity lane. -/
  witness : DiracCarrierWitness E

def diracMass (C : DiracCarrier E) : ℝ := C.witness.primeDensity.normalizedMass

def diracDensity (C : DiracCarrier E) : DiracDensity E := C.witness.primeDensity.toDiracDensity

def hFiniteDensity (C : DiracCarrier E) : FiniteDimensional ℂ E :=
  C.witness.primeDensity.finiteDensity

-- Compatibility wrapper for existing downstream calls.
def DiracCarrier.toStruct {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] 
  (C : DiracCarrier E) :
  { carrier : DiracCarrier E // carrier.diracMass = C.diracMass ∧ carrier.diracDensity = C.diracDensity ∧ carrier.hFiniteDensity = ‖ True := by
  refine' ⟨ofWitness C.witness, _, _, _⟩
  · simp [diracMass, diracMass_of_witness]
  · simp [diracDensity]
  · simp [hFiniteDensity]

end InfoGeometry.Canonical