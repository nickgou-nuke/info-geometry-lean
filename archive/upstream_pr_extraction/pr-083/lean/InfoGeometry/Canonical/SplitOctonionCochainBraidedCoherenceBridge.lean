import InfoGeometry.Canonical.SplitOctonionCochainMonoidalCoherenceBridge

/-!
# Split Octonion Cochain Braided Coherence Bridge

This file completes the globalization of the native split-octonion multiplication
into a full categorical coherent structure. 

By defining the categorical exchange morphism $c = R_{split}$, we show that
it obeys the Mac Lane Hexagon identities with the split associator $\alpha_{split}$. 
Crucially, we also prove $\Psi^2 = \mathrm{id}$, confirming that the split-octonion
grading forms a strictly symmetric (not merely braided/anyonic) monoidal structure.
-/

namespace InfoGeometry.Canonical.SplitOctonionCochainBraidedCoherenceBridge

open InfoGeometry.Canonical.SplitOctonionZ2ThreeCochainBridge
open InfoGeometry.Canonical.SplitOctonionCochainMonoidalCoherenceBridge

/-- The categorical braiding is realized via the exchange cochain $R_{split}$. -/
def splitCategoricalBraiding (x y : Grade) : ℚ :=
  exchangeCochain x y

/-- The split-octonion braiding is strictly symmetric: $\Psi^2 = \mathrm{id}$. -/
theorem splitSymmetricBraiding (x y : Grade) :
    splitCategoricalBraiding x y * splitCategoricalBraiding y x = 1 := by
  unfold splitCategoricalBraiding exchangeCochain
  have h1 : cochainF x y ≠ 0 := cochainF_ne_zero x y
  have h2 : cochainF y x ≠ 0 := cochainF_ne_zero y x
  calc
    (cochainF x y / cochainF y x) * (cochainF y x / cochainF x y)
      = (cochainF x y * cochainF y x) / (cochainF y x * cochainF x y) := div_mul_div_comm _ _ _ _
    _ = (cochainF x y * cochainF y x) / (cochainF x y * cochainF y x) := by rw [mul_comm (cochainF y x)]
    _ = 1 := div_self (mul_ne_zero h1 h2)

/-- 
The left Hexagon identity: 
$\alpha_{x,y,z} \cdot c_{x, y+z} \cdot \alpha_{y,z,x} = c_{x,y} \cdot \alpha_{y,x,z} \cdot c_{x,z}$ 
-/
theorem splitHexagon_left (x y z : Grade) :
    splitCategoricalAssociator x y z * splitCategoricalBraiding x (gradeAdd y z) * splitCategoricalAssociator y z x =
      splitCategoricalBraiding x y * splitCategoricalAssociator y x z * splitCategoricalBraiding x z := by
  unfold splitCategoricalAssociator splitCategoricalBraiding associatorCochain exchangeCochain
  revert x y z
  native_decide

/-- 
The right Hexagon identity: 
$\alpha_{x,y,z}^{-1} \cdot c_{x+y, z} \cdot \alpha_{z,x,y}^{-1} = c_{y,z} \cdot \alpha_{x,z,y}^{-1} \cdot c_{x,z}$
Written multiplicatively:
$c_{x+y, z} = \alpha_{x,y,z} \cdot c_{y,z} \cdot \alpha_{x,z,y}^{-1} \cdot c_{x,z} \cdot \alpha_{z,x,y}$
-/
theorem splitHexagon_right (x y z : Grade) :
    splitCategoricalBraiding (gradeAdd x y) z * splitCategoricalAssociator z x y * splitCategoricalAssociator x z y =
      splitCategoricalAssociator x y z * splitCategoricalBraiding y z * splitCategoricalBraiding x z := by
  unfold splitCategoricalAssociator splitCategoricalBraiding associatorCochain exchangeCochain
  revert x y z
  native_decide

end InfoGeometry.Canonical.SplitOctonionCochainBraidedCoherenceBridge
