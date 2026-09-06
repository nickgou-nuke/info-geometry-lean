import InfoGeometry.Canonical.KleinBottleA2RootMonodromy

/-!
# Cyclotomic chiral lift of the Klein-bottle colour monodromy

The clock multiplies the two non-trivial colour sectors by `w` and `w^2`.
The exchange is the orientation-reversing reflection.  Under `w^3 = 1` the
reflection conjugates the clock to its inverse, represented here by its square.
-/

namespace InfoGeometry.Canonical

variable {K : Type*} [CommRing K]

def kleinCubicCharge (w : K) : A2ColourFiber K →ₗ[K] A2ColourFiber K where
  toFun v := ![v 0, w * v 1, (w ^ 2) * v 2]
  map_add' v u := by
    funext i
    fin_cases i <;> simp [mul_add]
  map_smul' c v := by
    funext i
    fin_cases i <;> simp
    · ring
    · ring

def chiralExchange : A2ColourFiber K →ₗ[K] A2ColourFiber K :=
  a2Reflection

theorem kleinCubicCharge_cube (w : K) (hw : w ^ 3 = 1) :
    (kleinCubicCharge w).comp ((kleinCubicCharge w).comp (kleinCubicCharge w)) =
      LinearMap.id := by
  have hw6 : w ^ 6 = 1 := by
    calc
      w ^ 6 = (w ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hw]; ring
  apply LinearMap.ext
  intro v
  funext i
  fin_cases i
  · rfl
  · change w * (w * (w * v 1)) = v 1
    calc
      w * (w * (w * v 1)) = (w ^ 3) * v 1 := by ring
      _ = v 1 := by rw [hw]; simp
  · change w ^ 2 * (w ^ 2 * (w ^ 2 * v 2)) = v 2
    calc
      w ^ 2 * (w ^ 2 * (w ^ 2 * v 2)) = (w ^ 6) * v 2 := by ring
      _ = v 2 := by rw [hw6]; simp

theorem chiralExchange_square :
    (chiralExchange (K := K)).comp (chiralExchange (K := K)) =
      LinearMap.id :=
  a2Reflection_square (K := K)

theorem chiralExchange_conj_kleinCubicCharge (w : K) (hw : w ^ 3 = 1) :
    (chiralExchange (K := K)).comp
        ((kleinCubicCharge w).comp (chiralExchange (K := K))) =
      (kleinCubicCharge w).comp (kleinCubicCharge w) := by
  apply LinearMap.ext
  intro v
  funext i
  fin_cases i <;>
    simp [chiralExchange, kleinCubicCharge, a2Reflection, LinearMap.comp_apply]
  · ring
  · calc
      w * v 2 = (w ^ 4) * v 2 := by
        have hw4 : w ^ 4 = w := by
          calc
            w ^ 4 = (w ^ 3) * w := by ring
            _ = w := by rw [hw]; simp
        rw [hw4]
      _ = w ^ 2 * (w ^ 2 * v 2) := by ring

end InfoGeometry.Canonical
