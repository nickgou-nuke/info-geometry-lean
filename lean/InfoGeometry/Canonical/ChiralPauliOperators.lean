import InfoGeometry.Canonical.ThreeColorChiralLieSuperalgebra
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Internal chirality Pauli operators

On the off-diagonal carrier `ChiralOdd R = R^3_+ × R^3_-`, the two
chirality operations are defined directly by coordinates.  They expose the
split-Pauli algebra without turning the non-associative Zorn element carrier
into an associative operator algebra.
-/

namespace InfoGeometry.Canonical

variable {R : Type*} [CommRing R]

def chiralityZ (x : ChiralOdd R) : ChiralOdd R :=
  (x.1, fun i => -x.2 i)

def chiralityJ (x : ChiralOdd R) : ChiralOdd R :=
  (x.2, x.1)

def chiralityT (x : ChiralOdd R) : ChiralOdd R :=
  chiralityJ (chiralityZ x)

def chiralityOddNeg (x : ChiralOdd R) : ChiralOdd R :=
  (-x.1, -x.2)

theorem chiralityZ_sq (x : ChiralOdd R) :
    chiralityZ (chiralityZ x) = x := by
  ext i <;> simp [chiralityZ]

theorem chiralityJ_sq (x : ChiralOdd R) :
    chiralityJ (chiralityJ x) = x := by
  rfl

theorem chiralityJ_chiralityZ_anticommute (x : ChiralOdd R) :
    chiralityJ (chiralityZ x) =
      chiralityOddNeg (chiralityZ (chiralityJ x)) := by
  ext i <;> simp [chiralityJ, chiralityZ, chiralityOddNeg]

theorem chiralityT_apply (x : ChiralOdd R) :
    chiralityT x = (fun i => -x.2 i, x.1) := by
  rfl

theorem chiralityT_sq (x : ChiralOdd R) :
    chiralityT (chiralityT x) = chiralityOddNeg x := by
  ext i <;> simp [chiralityT, chiralityJ, chiralityZ, chiralityOddNeg]

theorem chiralityZ_chiralityT_anticommute (x : ChiralOdd R) :
    chiralityZ (chiralityT x) =
      chiralityOddNeg (chiralityT (chiralityZ x)) := by
  ext i <;> simp [chiralityT, chiralityJ, chiralityZ, chiralityOddNeg]

theorem chiralityJ_chiralityT_anticommute (x : ChiralOdd R) :
    chiralityJ (chiralityT x) =
      chiralityOddNeg (chiralityT (chiralityJ x)) := by
  ext i <;> simp [chiralityT, chiralityJ, chiralityZ, chiralityOddNeg]

theorem chiralityClock_action (x : ChiralOdd R) :
    bracketEvenOdd (0, 1) x =
      (fun i => 2 * x.1 i, fun i => -2 * x.2 i) := by
  ext i <;> simp [bracketEvenOdd]

end InfoGeometry.Canonical
