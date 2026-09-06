import InfoGeometry.Lie.CanonicalZornRootPairing

/-!
# Literature root-label readout for the native Cartan decomposition

The labels are the six positive and six negative roots used in the standard
split-real `G₂` basis.  This owner only records their already computed native
weights and the simple-root calibration.
-/

namespace InfoGeometry.Lie.CanonicalZornG2LiteratureBridge

open InfoGeometry.Lie.CanonicalZornCartanAdjointRootDecomposition
open InfoGeometry.Lie.CanonicalZornRootPairing
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen
open InfoGeometry.Lie.SplitOctonionAxialCartanErlangen

theorem paper_e10_weight : rootWeight 10 = coordWeight 0 := by
  rfl

theorem paper_e01_weight : rootWeight 1 = coordWeight 1 - coordWeight 0 := by
  rfl

theorem paper_e11_weight : rootWeight 9 = coordWeight 1 := by
  rfl

theorem paper_e21_weight : rootWeight 8 = -coordWeight 2 := by
  rfl

theorem paper_e31_weight : rootWeight 11 = coordWeight 0 - coordWeight 2 := by
  rfl

theorem paper_e32_weight : rootWeight 12 = coordWeight 1 - coordWeight 2 := by
  rfl

theorem paper_f10_weight : rootWeight 0 = -coordWeight 0 := by
  rfl

theorem paper_f01_weight : rootWeight 5 = coordWeight 0 - coordWeight 1 := by
  rfl

theorem paper_f11_weight : rootWeight 3 = -coordWeight 1 := by
  rfl

theorem paper_f21_weight : rootWeight 4 = coordWeight 2 := by
  rfl

theorem paper_f31_weight : rootWeight 2 = coordWeight 2 - coordWeight 0 := by
  rfl

theorem paper_f32_weight : rootWeight 7 = coordWeight 2 - coordWeight 1 := by
  rfl

theorem paper_simple_root_calibration :
    rootWeight 10 shortSimpleCoroot = 2 ∧
      rootWeight 10 longSimpleCoroot = -1 ∧
      rootWeight 1 shortSimpleCoroot = -3 ∧
      rootWeight 1 longSimpleCoroot = 2 := by
  exact ⟨rootWeight_shortSimple_pairing,
    rootWeight_short_long_pairing,
    rootWeight_long_short_pairing,
    rootWeight_longSimple_pairing⟩

theorem paper_positive_root_chain :
    rootWeight 10 = simpleWeight 0 ∧
      rootWeight 1 = simpleWeight 1 ∧
      rootWeight 9 = simpleWeight 0 + simpleWeight 1 ∧
      rootWeight 8 = 2 • simpleWeight 0 + simpleWeight 1 ∧
      rootWeight 11 = 3 • simpleWeight 0 + simpleWeight 1 ∧
      rootWeight 12 = 3 • simpleWeight 0 + 2 • simpleWeight 1 := by
  have traceless_sum (k : TracelessWeight) :
      k.1 0 + k.1 1 + k.1 2 = 0 := by
    have hk := k.2
    change ∑ i, k.1 i = 0 at hk
    simpa only [Fin.sum_univ_three] using hk
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [simpleWeight] using paper_e10_weight
  · simpa [simpleWeight] using paper_e01_weight
  · rw [paper_e11_weight]
    ext k
    simp [simpleWeight, coordWeight]
  · rw [paper_e21_weight]
    ext k
    simp [simpleWeight, coordWeight]
    linarith [traceless_sum k]
  · rw [paper_e31_weight]
    ext k
    simp [simpleWeight, coordWeight]
    linarith [traceless_sum k]
  · rw [paper_e32_weight]
    ext k
    simp [simpleWeight, coordWeight]
    linarith [traceless_sum k]

theorem paper_positive_root_weights :
    ({rootWeight 10, rootWeight 1, rootWeight 9, rootWeight 8,
        rootWeight 11, rootWeight 12} : Set Weight) =
      {simpleWeight 0, simpleWeight 1,
        simpleWeight 0 + simpleWeight 1,
        2 • simpleWeight 0 + simpleWeight 1,
        3 • simpleWeight 0 + simpleWeight 1,
        3 • simpleWeight 0 + 2 • simpleWeight 1} := by
  rcases paper_positive_root_chain with ⟨h10, h01, h11, h21, h31, h32⟩
  simp [h10, h01, h11, h21, h31, h32]

theorem paper_cartan_matrix :
    (fun i j => simpleWeight i (simpleCoroot j)) = simpleCartanMatrix := by
  funext i j
  exact simpleWeight_simpleCoroot_pairing i j

end InfoGeometry.Lie.CanonicalZornG2LiteratureBridge
