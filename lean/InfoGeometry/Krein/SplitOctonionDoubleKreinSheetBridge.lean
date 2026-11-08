/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Krein.MajoranaSheetConnectors
import InfoGeometry.Superalgebra.SplitOctonionMajoranaSymplecticTriad
import InfoGeometry.Superalgebra.CayleyDicksonMajoranaG2Lightcone

/-!
# Coordinate bridge from doubled real Krein sheets to split-octonion sheets

This bridge records only a coordinate encoding of the two chiral sheets and
the compatibility of the existing CAR connector maps with that encoding. It
does not identify the two products or turn a connector vector into a
Hamiltonian zero mode.
-/

open scoped InnerProductSpace

namespace InfoGeometry.Krein.SplitOctonionDoubleKreinSheetBridge

open InfoGeometry.Krein
open InfoGeometry.Krein.SplitQuadraticSheets
open InfoGeometry.Krein.MajoranaSheetConnectors
open InfoGeometry.Canonical.BogoliubovFockSuper
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Superalgebra.MajoranaSplitOctonions

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev H3 := DoubledSpace E3

/-- Read the three Euclidean coordinates in the split-octonion color carrier. -/
def vec3OfEuclidean (x : E3) : Vec3 ℝ :=
  ⟨x 0, x 1, x 2⟩

/-- Encode a doubled vector as a split-octonion with zero diagonal coordinates. -/
def doubledToSplitOctonion (z : H3) : SplitOctonion ℝ :=
  ⟨0, vec3OfEuclidean (WithLp.fst z), vec3OfEuclidean (WithLp.snd z), 0⟩

/-- Exchange the two chiral coordinates while retaining the diagonal slots. -/
def exchangeChiralCoordinates (X : SplitOctonion ℝ) : SplitOctonion ℝ :=
  ⟨X.a, X.v, X.u, X.b⟩

/-- The doubled modular swap becomes exchange of the encoded chiral coordinates. -/
theorem modularSwap_intertwines_chiralCoordinateExchange (z : H3) :
    doubledToSplitOctonion (modular_j (E := E3) z) =
      exchangeChiralCoordinates (doubledToSplitOctonion z) := by
  ext <;> simp [doubledToSplitOctonion, exchangeChiralCoordinates, modular_j,
    vec3OfEuclidean]

/-- Positive split-octonion sheet embedding: (0, u, 0, 0). -/
def sheetPlus (u : Vec3 ℝ) : SplitOctonion ℝ := ⟨0, u, ⟨0, 0, 0⟩, 0⟩

/-- Negative split-octonion sheet embedding: (0, 0, v, 0). -/
def sheetMinus (v : Vec3 ℝ) : SplitOctonion ℝ := ⟨0, ⟨0, 0, 0⟩, v, 0⟩

/-- Creation sends every encoded doubled vector to the positive split-octonion
sheet determined by its second coordinate. -/
theorem creation_encodes_as_positiveSheet (z : H3) :
    doubledToSplitOctonion (concreteCARCreation (E := E3) z) =
      sheetPlus (vec3OfEuclidean (WithLp.snd z)) := by
  have hz : to_doubled (WithLp.fst z) (WithLp.snd z) = z := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [← hz, cliffordConcreteCreation_apply_to_doubled]
  simp [doubledToSplitOctonion, vec3OfEuclidean, sheetPlus]

/-- Annihilation sends every encoded doubled vector to the negative
split-octonion sheet determined by its first coordinate. -/
theorem annihilation_encodes_as_negativeSheet (z : H3) :
    doubledToSplitOctonion (concreteCARAnnihilation (E := E3) z) =
      sheetMinus (vec3OfEuclidean (WithLp.fst z)) := by
  have hz : to_doubled (WithLp.fst z) (WithLp.snd z) = z := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [← hz, cliffordConcreteAnnihilation_apply_to_doubled]
  simp [doubledToSplitOctonion, vec3OfEuclidean, sheetMinus]

/-- Creation connects the negative Krein sheet to the positive split-octonion sheet. -/
theorem creation_maps_splitOctonion_minusSheet_to_plusSheet (ξ : E3) :
    doubledToSplitOctonion
        (concreteCARCreation (E := E3) (minusPoint (E := E3) ξ)) =
      sheetPlus (vec3OfEuclidean ξ) := by
  rw [creation_maps_minusPoint_to_plusPoint]
  simp [doubledToSplitOctonion, vec3OfEuclidean, plusPoint, sheetPlus]

/-- Annihilation connects the positive Krein sheet to the negative split-octonion sheet. -/
theorem annihilation_maps_splitOctonion_plusSheet_to_minusSheet (x : E3) :
    doubledToSplitOctonion
        (concreteCARAnnihilation (E := E3) (plusPoint (E := E3) x)) =
      sheetMinus (vec3OfEuclidean x) := by
  rw [annihilation_maps_plusPoint_to_minusPoint]
  simp [doubledToSplitOctonion, vec3OfEuclidean, minusPoint, sheetMinus]

end InfoGeometry.Krein.SplitOctonionDoubleKreinSheetBridge
