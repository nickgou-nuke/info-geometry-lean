import InfoGeometry.Canonical.SplitOctonionZ2ThreeCochainBridge

/-!
# Split Octonion Cochain Monoidal Coherence Bridge

This file establishes that the native algebraic nonassociativity of the split-octonion 
basis actually yields a categorically coherent monoidal structure. 

The 3-cocycle identity exactly mirrors the categorical Pentagon identity, 
meaning that while the ring multiplication is nonassociative ($a(bc) \neq (ab)c$),
the categorical coherence associator satisfies the Pentagon and the Joyce $q$-defect is trivial.
-/

namespace InfoGeometry.Canonical.SplitOctonionCochainMonoidalCoherenceBridge

open InfoGeometry.Canonical.SplitOctonionZ2ThreeCochainBridge

/-- The categorical associator derived from the split-octonion basis cochain. -/
def splitCategoricalAssociator (x y z : Grade) : ℚ :=
  associatorCochain x y z

theorem splitCategoricalAssociator_ne_zero (x y z : Grade) :
    splitCategoricalAssociator x y z ≠ 0 := by
  intro h
  have hsq := associatorCochain_sq x y z
  change splitCategoricalAssociator x y z * splitCategoricalAssociator x y z = 1 at hsq
  rw [h] at hsq
  norm_num at hsq

/-- The left path of the categorical Pentagon: $((xy)z)w \to (xy)(zw) \to x(y(zw))$ -/
def splitPentagonLeftPath (x y z w : Grade) : ℚ :=
  splitCategoricalAssociator (gradeAdd x y) z w * splitCategoricalAssociator x y (gradeAdd z w)

/-- The right path of the categorical Pentagon: $((xy)z)w \to (x(yz))w \to x((yz)w) \to x(y(zw))$ -/
def splitPentagonRightPath (x y z w : Grade) : ℚ :=
  splitCategoricalAssociator y z w * splitCategoricalAssociator x (gradeAdd y z) w * splitCategoricalAssociator x y z

theorem splitPentagonRightPath_ne_zero (x y z w : Grade) :
    splitPentagonRightPath x y z w ≠ 0 := by
  unfold splitPentagonRightPath
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  exact splitCategoricalAssociator_ne_zero y z w
  exact splitCategoricalAssociator_ne_zero x (gradeAdd y z) w
  exact splitCategoricalAssociator_ne_zero x y z

/-- The strict equality of the two categorical evaluation paths (The Pentagon Identity). -/
theorem splitPentagonPaths_eq (x y z w : Grade) :
    splitPentagonLeftPath x y z w = splitPentagonRightPath x y z w := by
  unfold splitPentagonLeftPath splitPentagonRightPath splitCategoricalAssociator
  exact (native_associator_three_cocycle x y z w).symm

/-- The Joyce q-defect is defined as the categorical ratio of the two Pentagon paths. -/
def splitJoycePentagonDefect (x y z w : Grade) : ℚ :=
  splitPentagonLeftPath x y z w / splitPentagonRightPath x y z w

/-- The Joyce q-defect of the split-octonions is exactly trivial! -/
theorem splitJoycePentagonDefect_eq_id (x y z w : Grade) :
    splitJoycePentagonDefect x y z w = 1 := by
  unfold splitJoycePentagonDefect
  rw [splitPentagonPaths_eq]
  exact div_self (splitPentagonRightPath_ne_zero x y z w)

end InfoGeometry.Canonical.SplitOctonionCochainMonoidalCoherenceBridge
