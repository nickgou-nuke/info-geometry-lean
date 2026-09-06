import proofs.ZornChiralLightcone
import InfoGeometry.Physics.SplitOctonionBraidSU3
import InfoGeometry.Canonical.CanonicalZornCompositionTriality

noncomputable section

open CliffordAlgebra LinearMap
open InfoGeometry.Physics.SplitOctonionBraidSU3 CanonicalZornCompositionTriality
open CanonicalZornCliffordRepresentation
open ZornChiralLightcone

lemma upperLightconeVector_ne_zero (r : Fin 3) : upperLightconeVector r ≠ 0 := by
  intro h
  fin_cases r
  · have hc := congrArg (fun X : Vector8 =>
        (copyLinearEquivCoordinates .vector X) 1) h
    simp only [map_zero, Pi.zero_apply] at hc
    simp [upperLightconeVector, E_k, e_k,
      copyLinearEquivCoordinates, copyEquivCoordinates,
      CanonicalZornCompositionTriality.zornCoordinates] at hc
  · have hc := congrArg (fun X : Vector8 =>
        (copyLinearEquivCoordinates .vector X) 2) h
    simp only [map_zero, Pi.zero_apply] at hc
    simp [upperLightconeVector, E_k, e_k,
      copyLinearEquivCoordinates, copyEquivCoordinates,
      CanonicalZornCompositionTriality.zornCoordinates] at hc
  · have hc := congrArg (fun X : Vector8 =>
        (copyLinearEquivCoordinates .vector X) 3) h
    simp only [map_zero, Pi.zero_apply] at hc
    simp [upperLightconeVector, E_k, e_k,
      copyLinearEquivCoordinates, copyEquivCoordinates,
      CanonicalZornCompositionTriality.zornCoordinates] at hc
