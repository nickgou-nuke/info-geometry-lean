/-
InfoGeometry/Quantum/SouriauFoliation/PositiveTemperatureLeaf.lean
-/
import InfoGeometry.Thermodynamics.SouriauTemperatureProjective
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.SouriauFoliation.SymplecticLeaf

noncomputable section

namespace InfoGeometry.Quantum.SouriauFoliation

open InfoGeometry.Thermodynamics

/--
Positive-Souriau-temperature leaf alias.

This exposes the projective-temperature carrier without asserting that every
positive temperature leaf is a coadjoint orbit.
-/
abbrev PositiveTemperatureLeaf :=
  SymplecticLeaf PositiveSouriauTemperature

end InfoGeometry.Quantum.SouriauFoliation
