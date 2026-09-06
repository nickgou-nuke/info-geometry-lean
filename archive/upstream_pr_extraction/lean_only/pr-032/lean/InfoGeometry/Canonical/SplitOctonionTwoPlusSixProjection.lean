import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Basic

namespace InfoGeometry.Canonical

variable {R : Type*} [CommRing R]

/-- The 8-dimensional split-octonion representation. -/
@[ext]
structure SplitOctonion (R : Type*) where
  e0 : R
  el : R
  ei : R
  eli : R
  ej : R
  elj : R
  ek : R
  elk : R

namespace SplitOctonion

/-- Additive structure. -/
def add (X Y : SplitOctonion R) : SplitOctonion R :=
  ⟨X.e0 + Y.e0, X.el + Y.el, X.ei + Y.ei, X.eli + Y.eli, X.ej + Y.ej, X.elj + Y.elj, X.ek + Y.ek, X.elk + Y.elk⟩

/-- Leptonic Plane (L = span{1, l}) -/
def leptonicPlane (X : SplitOctonion R) : SplitOctonion R :=
  ⟨X.e0, X.el, 0, 0, 0, 0, 0, 0⟩

/-- Color Complement (C = span{i, li, j, lj, k, lk}) -/
def colorComplement (X : SplitOctonion R) : SplitOctonion R :=
  ⟨0, 0, X.ei, X.eli, X.ej, X.elj, X.ek, X.elk⟩

/-- Local Two+Six Split Reconstruction -/
theorem two_plus_six_reconstruction (X : SplitOctonion R) :
    add (leptonicPlane X) (colorComplement X) = X := by
  dsimp [leptonicPlane, colorComplement, add]
  ext <;> simp

end SplitOctonion
end InfoGeometry.Canonical
