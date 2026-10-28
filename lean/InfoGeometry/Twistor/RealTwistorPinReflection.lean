/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Twistor.RealPluckerCl55Reflection
import InfoGeometry.Clifford.Cl55WittPinAction

/-!
# The native algebraic Pin lift of the real two-mode reflection

The product of the existing negative Clifford generators in modes `0` and
`4` belongs to the native real `Pin55` subgroup. Its twisted adjoint is
exactly the partial reflection used by the real Plücker embedding, and its
Clifford square is `-1`. This establishes the algebraic Pin lift of `F04`.
This file does not identify the four-dimensional `TwistorSpace` action
`R0^n` with a `Pin55` spinor-module action, construct an associated bundle,
or establish a topological Pin structure.
-/

noncomputable section

namespace InfoGeometry.Twistor.RealTwistorPinReflection

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Projective.KleinQuadricPlucker
open RealTwistorBlockInversion RealPluckerCl55Reflection

/-- The actual Clifford Pin product covering the two negative-mode reflections. -/
def nativePinRotation : Pin55 := fNegPin 0 * fNegPin 4

@[simp] theorem nativePinRotation_coe :
    (nativePinRotation : Cl55) = ι55 (f_neg 0) * ι55 (f_neg 4) := by
  simp [nativePinRotation]

/-- The existing Pin twisted adjoint agrees with the actual algebra automorphism. -/
theorem nativePinRotation_twistedAdj (v : V55) :
    pinTwistedAdj nativePinRotation v = partialReflectionAlg (ι55 v) := by
  exact pinTwistedAdj_fNegPin_mul 0 4 v

/-- Injectivity of the native Clifford inclusion recovers the vector action. -/
theorem nativePinRotation_vector_action (v : V55) :
    pinTwistedAction nativePinRotation v = partialReflection v := by
  apply ι55_injective
  rw [pinTwistedAction_apply_ι, nativePinRotation_twistedAdj,
    partialReflectionAlg_apply_ι]

/-- The same algebraic Pin element realizes the signed real Plücker intertwiner. -/
theorem nativePinRotation_plucker (P : Plucker6 ℝ) :
    pinTwistedAdj nativePinRotation (pluckerToV55 P) =
      ι55 (pluckerToV55 (pluckerRotation P)) := by
  rw [nativePinRotation_twistedAdj, native_reflection_intertwiner]

/-- Two distinct negative generators retain the central minus sign before projection. -/
theorem nativePinRotation_clifford_sq :
    (nativePinRotation : Cl55) * (nativePinRotation : Cl55) = -1 := by
  simp only [nativePinRotation_coe]
  have hanti : ι55 (f_neg 4) * ι55 (f_neg 0) =
      -(ι55 (f_neg 0) * ι55 (f_neg 4)) :=
    CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
      (Q := InfoGeometry.Clifford.Clifford55.Q55)
      (f_neg_isOrtho_of_ne (show (4 : Fin 5) ≠ 0 by decide))
  calc
    (ι55 (f_neg 0) * ι55 (f_neg 4)) *
        (ι55 (f_neg 0) * ι55 (f_neg 4)) =
        ι55 (f_neg 0) * (ι55 (f_neg 4) * ι55 (f_neg 0)) *
          ι55 (f_neg 4) := by noncomm_ring
    _ = ι55 (f_neg 0) * (-(ι55 (f_neg 0) * ι55 (f_neg 4))) *
          ι55 (f_neg 4) := by rw [hanti]
    _ = -(ι55 (f_neg 0) * ι55 (f_neg 0)) *
          (ι55 (f_neg 4) * ι55 (f_neg 4)) := by noncomm_ring
    _ = -1 := by rw [f_neg_mul_self, f_neg_mul_self]; simp

end InfoGeometry.Twistor.RealTwistorPinReflection
