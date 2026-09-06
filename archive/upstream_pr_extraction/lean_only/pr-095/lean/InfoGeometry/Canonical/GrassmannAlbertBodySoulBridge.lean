import Mathlib.Algebra.Module.Basic

namespace InfoGeometry.Canonical

variable {R : Type*} [CommRing R]

/-- Extreme simplification of a Grassmann algebra z = z_B + z_S -/
@[ext]
structure GrassmannNumber (R : Type*) where
  body : R
  soul : R

namespace GrassmannNumber

def add (x y : GrassmannNumber R) : GrassmannNumber R :=
  ⟨x.body + y.body, x.soul + y.soul⟩

def deWittBodyMap (z : GrassmannNumber R) : GrassmannNumber R :=
  ⟨z.body, 0⟩

def deWittSoulMap (z : GrassmannNumber R) : GrassmannNumber R :=
  ⟨0, z.soul⟩

theorem dewitt_grassmann_reconstruction (z : GrassmannNumber R) :
    add (deWittBodyMap z) (deWittSoulMap z) = z := by
  dsimp [deWittBodyMap, deWittSoulMap, add]
  ext <;> simp

end GrassmannNumber
end InfoGeometry.Canonical
