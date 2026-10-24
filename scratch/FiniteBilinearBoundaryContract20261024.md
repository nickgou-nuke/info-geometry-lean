# Finite bilinear boundary consolidation contract

Source: upstream/feat/car-majorana-pfaffian-bridge at eaa2efff0f476d7da62ed3df49b0df63df957391, MajoranaLinearKernel.finite_bilinear_boundary_commutes.
Native owner: Canonical/KitaevChainMajoranaZeroModes.lean, left_boundary_majorana_zero_mode.
For any ring, finite index set s, an element q anticommuting with a_i and b_i and commuting with t_i for each i in s commutes with sum_i t_i(a_i b_i).
No CAR normalization, real scalar algebra, star, or nontriviality is needed. Native Commute.sum_right and Commute.mul_right transport the existing proved two-factor calculation. This generalizes the branch's common coefficient and normalized CAR hypotheses and provides its full finite-index consequence, without duplicating its field carrier.
No spectrum or state-space zero mode is claimed. Existing endpoint consumers remain valid.
