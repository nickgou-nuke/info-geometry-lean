import InfoGeometry.Clifford.Grading
import InfoGeometry.Quantum.RealKCategory
import InfoGeometry.Canonical.OperatorDictionary
import InfoGeometry.Canonical.HadjiivanovMonodromyProjection

-- Finite Lean packet mirroring `tools/sympy/hestenes_krein_klein_witness.py`.
-- This is a witness-alias surface for:
-- grading split / fixed-point decomposition,
-- square-zero nilpotent shear,
-- rotor composition and power law,
-- sector swap under the modular reflection `J`.

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinKleinWitnessPacket

open scoped BigOperators
open InfoGeometry.Krein

section Grading

variable {E : Type 0} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- SymPy witness: grading split.
theorem grading_fixed_point_split (v : DoubledSpace E) :
    v = spectralPlusProj (E := E) v + spectralMinusProj (E := E) v := by
  simpa using krein_projector_decomposition (E := E) v

omit [CompleteSpace E] in
-- SymPy witness: modular reflection swaps the spectral sectors.
theorem sector_swap_projectors :
    (modular_j (E := E)).comp (spectralPlusProj (E := E))
      = (spectralMinusProj (E := E)).comp (modular_j (E := E)) ∧
    (modular_j (E := E)).comp (spectralMinusProj (E := E))
      = (spectralPlusProj (E := E)).comp (modular_j (E := E)) := by
  simpa using
    InfoGeometry.Canonical.OperatorDictionary.modular_j_sectorSwap_projectors (E := E)

end Grading

section Rotor

variable (X : InfoGeometry.Quantum.RealKCategory.RealKVect)
variable (θ₁ θ₂ h : ℝ)
variable (N : InfoGeometry.Quantum.RealKCategory.NilpotentHom X)
variable (n : ℕ)

-- SymPy witness: K² = -I.
theorem clockAxis_sq_neg_id :
    X.K.comp X.K = -(LinearMap.id : X →ₗ[ℝ] X) := by
  exact X.K_sq

-- SymPy witness: nilpotent shear squares to zero.
theorem nilpotent_shear_sq_zero :
    N.toHom.hom.comp N.toHom.hom = 0 := by
  simpa using N.nilpotent

-- SymPy witness: rotor composition.
theorem rotor_composition :
    (InfoGeometry.Quantum.RealKCategory.rotor X θ₁).hom.comp
      (InfoGeometry.Quantum.RealKCategory.rotor X θ₂).hom =
      (InfoGeometry.Quantum.RealKCategory.rotor X (θ₁ + θ₂)).hom := by
  simpa using InfoGeometry.Quantum.RealKCategory.rotor_mul X θ₁ θ₂

-- SymPy witness: monodromy power law.
theorem monodromy_power_law :
    (InfoGeometry.Quantum.RealKCategory.monodromyProjection X h N).hom ^ n =
      (InfoGeometry.Quantum.RealKCategory.rotor X
        (-2 * Real.pi * (n : ℝ) * h)).hom.comp
        (LinearMap.id + (-2 * Real.pi * (n : ℝ)) • N.toHom.hom) := by
  simpa using
    InfoGeometry.Quantum.RealKCategory.monodromy_power_binomial X h N n

end Rotor

end InfoGeometry.Canonical.HestenesKreinKleinWitnessPacket
