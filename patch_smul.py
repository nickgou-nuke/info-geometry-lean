import re

with open('lean/InfoGeometry/Lie/CanonicalZornG2CartanWeylEquivariantEnsemble.lean', 'r') as f:
    content = f.read()

# expectedDirectionalCharge_covariance
edc_old = """  rw [h1]
  apply Finset.sum_congr rfl
  intro m _
  rw [probability_diagonal_invariant]
  have h2 : (∑ i, parameterLeftAction w v i * D.base.momentMap (w • m) i) =
            ∑ i, v i * D.base.momentMap m i := by
    dsimp [parameterLeftAction, MulAction.smul]
    exact D.pairing_diagonal_invariant w v m
  rw [h2]"""
edc_new = """  rw [h1]
  apply Finset.sum_congr rfl
  intro m _
  change realGibbsWeight D.base (parameterLeftAction w beta) (w • m) * (∑ i, parameterLeftAction w v i * D.base.momentMap (w • m) i) = _
  rw [probability_diagonal_invariant]
  have h2 : (∑ i, parameterLeftAction w v i * D.base.momentMap (w • m) i) =
            ∑ i, v i * D.base.momentMap m i := by
    exact D.pairing_diagonal_invariant w v m
  rw [h2]"""
content = content.replace(edc_old, edc_new)

# centeredDirectionalCharge_covariance
cdc_old = """  dsimp [centeredDirectionalCharge, parameterLeftAction, MulAction.smul]
  rw [D.pairing_diagonal_invariant]"""
cdc_new = """  dsimp [centeredDirectionalCharge]
  have h_pair : (∑ i, parameterLeftAction w v i * D.base.momentMap (w • m) i) = ∑ i, v i * D.base.momentMap m i := D.pairing_diagonal_invariant w v m
  rw [h_pair]"""
content = content.replace(cdc_old, cdc_new)

# fisherSouriau_covariance
fsc_old = """  rw [h1]
  apply Finset.sum_congr rfl
  intro m _
  rw [probability_diagonal_invariant]
  rw [centeredDirectionalCharge_covariance]
  rw [centeredDirectionalCharge_covariance]"""
fsc_new = """  rw [h1]
  apply Finset.sum_congr rfl
  intro m _
  change realGibbsWeight D.base (parameterLeftAction w beta) (w • m) *
    centeredDirectionalCharge (parameterLeftAction w beta) (parameterLeftAction w u) (w • m) *
    centeredDirectionalCharge (parameterLeftAction w beta) (parameterLeftAction w v) (w • m) = _
  rw [probability_diagonal_invariant]
  rw [centeredDirectionalCharge_covariance]
  rw [centeredDirectionalCharge_covariance]"""
content = content.replace(fsc_old, fsc_new)

with open('lean/InfoGeometry/Lie/CanonicalZornG2CartanWeylEquivariantEnsemble.lean', 'w') as f:
    f.write(content)

