import InfoGeometry.Canonical.ZornChiralPeirceDecomposition

/-!
# Chiral action of the algebraic Zorn scaling

The deformation below scales the two off-diagonal Peirce sectors by prescribed
scalars and fixes the diagonal sectors.  The inverse relation between the two
scalars is recorded as an explicit property for later multiplicative
questions; the basis-action lemmas themselves are purely coordinate facts.
-/

namespace InfoGeometry.Canonical

open ZornMatrix

variable {R : Type*} [CommRing R]

def zornScale (q q_inv : R) (Z : ZornMatrix R) : ZornMatrix R where
  a := Z.a
  b := Z.b
  x := fun i => q * Z.x i
  y := fun i => q_inv * Z.y i

private theorem smul_coord (r : R) (Z : ZornMatrix R) :
    r • Z =
      { a := r * Z.a, b := r * Z.b, x := fun i => r * Z.x i, y := fun i => r * Z.y i } := by
  ext <;> rw [Equiv.smul_def coordEquiv] <;> rfl

@[simp] theorem zornScale_zornPlus (q q_inv : R) :
    zornScale q q_inv zornPlus = zornPlus := by
  apply ZornMatrix.ext
  · simp [zornScale, zornPlus]
  · simp [zornScale, zornPlus]
  · funext i
    simp [zornScale, zornPlus]
  · funext i
    simp [zornScale, zornPlus]

@[simp] theorem zornScale_zornMinus (q q_inv : R) :
    zornScale q q_inv zornMinus = zornMinus := by
  apply ZornMatrix.ext
  · simp [zornScale, zornMinus]
  · simp [zornScale, zornMinus]
  · funext i
    simp [zornScale, zornMinus]
  · funext i
    simp [zornScale, zornMinus]

@[simp] theorem zornScale_chiralUpperBasis (q q_inv : R) (i : Fin 3) :
    zornScale q q_inv (chiralUpperBasis i) = q • chiralUpperBasis i := by
  rw [smul_coord]
  ext <;> simp [zornScale, chiralUpperBasis]

@[simp] theorem zornScale_chiralLowerBasis (q q_inv : R) (i : Fin 3) :
    zornScale q q_inv (chiralLowerBasis i) = q_inv • chiralLowerBasis i := by
  rw [smul_coord]
  ext <;> simp [zornScale, chiralLowerBasis]

theorem zornScale_add (q q_inv : R) (X Y : ZornMatrix R) :
    zornScale q q_inv (X + Y) = zornScale q q_inv X + zornScale q q_inv Y := by
  ext <;> simp [zornScale, ZornMatrix.add_def, mul_add]

theorem zornScale_smul (q q_inv r : R) (X : ZornMatrix R) :
    zornScale q q_inv (r • X) = r • zornScale q q_inv X := by
  rw [smul_coord, smul_coord]
  ext <;> simp [zornScale]
  · ring
  · ring

/-- The scaling action packaged as a linear endomorphism of the native Zorn carrier. -/
def zornScaleLinear (q q_inv : R) : ZornMatrix R →ₗ[R] ZornMatrix R where
  toFun := zornScale q q_inv
  map_add' := zornScale_add q q_inv
  map_smul' := zornScale_smul q q_inv

@[simp] theorem zornScaleLinear_apply (q q_inv : R) (Z : ZornMatrix R) :
    zornScaleLinear q q_inv Z = zornScale q q_inv Z := rfl

end InfoGeometry.Canonical
