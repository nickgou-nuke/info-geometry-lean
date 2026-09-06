import InfoGeometry.Topology.MobiusGeometry

/-!
# MobiusFiniteTripleNormalization

A small honest normalization packet for finite Möbius triples.
It isolates the concrete `0, 1, ∞` normalization used by the 3-transitivity story.
-/

namespace InfoGeometry.Topology.MobiusFiniteTripleNormalization

open Complex

/--
A concrete Möbius transformation sending three distinct finite points to
`0`, `1`, and `∞`.
-/
def normalizeTriple (z1 z2 z3 : ℂ) (h12 : z1 ≠ z2) (h23 : z2 ≠ z3) (h13 : z1 ≠ z3) :
    InfoGeometry.MobiusTransform :=
  { a := z2 - z3,
    b := -(z2 - z3) * z1,
    c := z2 - z1,
    d := -(z2 - z1) * z3,
    det_ne_zero := by
      have hdet :
          (z2 - z3) * (-(z2 - z1) * z3) - (-(z2 - z3) * z1) * (z2 - z1) =
            (z2 - z3) * (z2 - z1) * (z1 - z3) := by
        ring
      rw [hdet]
      apply mul_ne_zero
      · apply mul_ne_zero
        · exact sub_ne_zero.mpr h23
        · exact sub_ne_zero.mpr h12.symm
      · exact sub_ne_zero.mpr h13 }

/--
Auxiliary normalization theorem: a concrete finite triple can be sent to
`0`, `1`, and `∞` by an explicit Möbius transformation.
-/
theorem maps_to_01inf_finite
    (z1 z2 z3 : ℂ) (h12 : z1 ≠ z2) (h23 : z2 ≠ z3) (h13 : z1 ≠ z3) :
    ∃ M : InfoGeometry.MobiusTransform,
      M.eval (some z1) = some 0 ∧
      M.eval (some z2) = some 1 ∧
      M.eval (some z3) = none := by
  refine ⟨normalizeTriple z1 z2 z3 h12 h23 h13, ?_, ?_, ?_⟩
  · have hden1 : (z2 - z1) * z1 + (z1 - z2) * z3 ≠ 0 := by
      have hneq : (z2 - z1) * (z1 - z3) ≠ 0 := by
        apply mul_ne_zero
        · exact sub_ne_zero.mpr h12.symm
        · exact sub_ne_zero.mpr h13
      have hiden : (z2 - z1) * z1 + (z1 - z2) * z3 = (z2 - z1) * (z1 - z3) := by
        ring
      rw [hiden]
      exact hneq
    have hq : ((z2 - z3) * z1 + (z3 - z2) * z1) / ((z2 - z1) * z1 + (z1 - z2) * z3) = 0 := by
      field_simp [hden1]
      ring
    simpa [normalizeTriple, InfoGeometry.MobiusTransform.eval, hden1, hq]
  · have hden2 : (z2 - z1) * z2 + (z1 - z2) * z3 ≠ 0 := by
      have hneq : (z2 - z1) * (z2 - z3) ≠ 0 := by
        apply mul_ne_zero
        · exact sub_ne_zero.mpr h12.symm
        · exact sub_ne_zero.mpr h23
      have hiden : (z2 - z1) * z2 + (z1 - z2) * z3 = (z2 - z1) * (z2 - z3) := by
        ring
      rw [hiden]
      exact hneq
    have hq : ((z2 - z3) * z2 + (z3 - z2) * z1) / ((z2 - z1) * z2 + (z1 - z2) * z3) = 1 := by
      have hnumden :
          (z2 - z3) * z2 + (z3 - z2) * z1 = (z2 - z1) * z2 + (z1 - z2) * z3 := by
        ring
      rw [hnumden]
      exact div_self hden2
    simpa [normalizeTriple, InfoGeometry.MobiusTransform.eval, hden2, hq]
  · have hden3 : (z2 - z1) * z3 + (z1 - z2) * z3 = 0 := by
      ring
    simp [normalizeTriple, InfoGeometry.MobiusTransform.eval, hden3]

end InfoGeometry.Topology.MobiusFiniteTripleNormalization
