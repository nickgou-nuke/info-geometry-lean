import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.ZornSpinor

/-!
# Cyclotomic charge and the three native Peirce sectors

This owner uses the canonical additive/module structure on `ZornMatrix`.
The cubic phase is an explicit parameter; no analytic choice of a complex
root of unity is hidden in the definitions.
-/

namespace InfoGeometry.Canonical

open ZornMatrix

variable {K : Type*} [CommRing K]

private lemma smul_a_coord (c : K) (Z : ZornMatrix K) :
    (c • Z).a = c * Z.a := by
  rw [Equiv.smul_def coordEquiv]
  rfl

private lemma smul_b_coord (c : K) (Z : ZornMatrix K) :
    (c • Z).b = c * Z.b := by
  rw [Equiv.smul_def coordEquiv]
  rfl

private lemma smul_x_coord (c : K) (Z : ZornMatrix K) (i : Fin 3) :
    (c • Z).x i = c * Z.x i := by
  rw [Equiv.smul_def coordEquiv]
  rfl

private lemma smul_y_coord (c : K) (Z : ZornMatrix K) (i : Fin 3) :
    (c • Z).y i = c * Z.y i := by
  rw [Equiv.smul_def coordEquiv]
  rfl

def cubicCharge (ω : K) : ZornMatrix K →ₗ[K] ZornMatrix K where
  toFun Z :=
    { a := Z.a, b := Z.b, x := ω • Z.x, y := (ω ^ 2) • Z.y }
  map_add' X Y := by
    cases X
    cases Y
    apply ZornMatrix.ext
    · simp [ZornMatrix.add_def]
    · simp [ZornMatrix.add_def]
    · funext i
      simp [ZornMatrix.add_def, mul_add]
    · funext i
      simp [ZornMatrix.add_def, mul_add]
  map_smul' c X := by
    apply ZornMatrix.ext
    · simp [smul_a_coord]
    · simp [smul_b_coord]
    · funext i
      simp [smul_x_coord]
      ring
    · funext i
      simp [smul_y_coord]
      ring

def cubicProjectorZero : ZornMatrix K →ₗ[K] ZornMatrix K where
  toFun Z := { a := Z.a, b := Z.b, x := 0, y := 0 }
  map_add' X Y := by
    cases X
    cases Y
    apply ZornMatrix.ext
    · simp [ZornMatrix.add_def]
    · simp [ZornMatrix.add_def]
    · funext i
      simp [ZornMatrix.add_def, mul_add]
    · funext i
      simp [ZornMatrix.add_def, mul_add]
  map_smul' c X := by
    apply ZornMatrix.ext
    · simp [smul_a_coord]
    · simp [smul_b_coord]
    · funext i
      simp [smul_x_coord]
    · funext i
      simp [smul_y_coord]

def cubicProjectorPlus : ZornMatrix K →ₗ[K] ZornMatrix K where
  toFun Z := { a := 0, b := 0, x := Z.x, y := 0 }
  map_add' X Y := by
    cases X
    cases Y
    apply ZornMatrix.ext
    · simp [ZornMatrix.add_def]
    · simp [ZornMatrix.add_def]
    · funext i
      simp [ZornMatrix.add_def, mul_add]
    · funext i
      simp [ZornMatrix.add_def, mul_add]
  map_smul' c X := by
    apply ZornMatrix.ext
    · simp [smul_a_coord]
    · simp [smul_b_coord]
    · funext i
      simp [smul_x_coord]
    · funext i
      simp [smul_y_coord]

def cubicProjectorMinus : ZornMatrix K →ₗ[K] ZornMatrix K where
  toFun Z := { a := 0, b := 0, x := 0, y := Z.y }
  map_add' X Y := by
    cases X
    cases Y
    apply ZornMatrix.ext
    · simp [ZornMatrix.add_def]
    · simp [ZornMatrix.add_def]
    · funext i
      simp [ZornMatrix.add_def, mul_add]
    · funext i
      simp [ZornMatrix.add_def, mul_add]
  map_smul' c X := by
    apply ZornMatrix.ext
    · simp [smul_a_coord]
    · simp [smul_b_coord]
    · funext i
      simp [smul_x_coord]
    · funext i
      simp [smul_y_coord]

@[simp] theorem cubicProjectorZero_apply (Z : ZornMatrix K) :
    cubicProjectorZero Z = { a := Z.a, b := Z.b, x := 0, y := 0 } := rfl

@[simp] theorem cubicProjectorPlus_apply (Z : ZornMatrix K) :
    cubicProjectorPlus Z = { a := 0, b := 0, x := Z.x, y := 0 } := rfl

@[simp] theorem cubicProjectorMinus_apply (Z : ZornMatrix K) :
    cubicProjectorMinus Z = { a := 0, b := 0, x := 0, y := Z.y } := rfl

theorem cubicCharge_pow_three (ω : K) (hω : ω ^ 3 = 1) :
    (cubicCharge ω).comp ((cubicCharge ω).comp (cubicCharge ω)) = LinearMap.id := by
  apply LinearMap.ext
  intro Z
  apply ZornMatrix.ext
  · simp [cubicCharge]
  · simp [cubicCharge]
  · funext i
    change ω * (ω * (ω * Z.x i)) = Z.x i
    rw [show ω * (ω * (ω * Z.x i)) = (ω ^ 3) * Z.x i by ring, hω, one_mul]
  · funext i
    have hω6 : ω ^ 6 = 1 := by
      calc
        ω ^ 6 = (ω ^ 3) ^ 2 := by rw [show 6 = 3 * 2 by norm_num, pow_mul]
        _ = 1 := by rw [hω, one_pow]
    change ω ^ 2 * (ω ^ 2 * (ω ^ 2 * Z.y i)) = Z.y i
    rw [show ω ^ 2 * (ω ^ 2 * (ω ^ 2 * Z.y i)) = (ω ^ 6) * Z.y i by ring, hω6,
      one_mul]

theorem cubicCharge_mul (ω : K) (hω : ω ^ 3 = 1)
    (X Y : ZornMatrix K) :
    cubicCharge ω (X * Y) = cubicCharge ω X * cubicCharge ω Y := by
  have hω32 : ω * ω ^ 2 = 1 := by
    calc
      ω * ω ^ 2 = ω ^ 3 := by ring
      _ = 1 := hω
  have hω23 : ω ^ 2 * ω = 1 := by
    calc
      ω ^ 2 * ω = ω ^ 3 := by ring
      _ = 1 := hω
  have hω4 : ω ^ 2 * ω ^ 2 = ω := by
    calc
      ω ^ 2 * ω ^ 2 = ω * (ω ^ 3) := by ring
      _ = ω := by rw [hω, mul_one]
  have hquad (a b : K) : ω ^ 2 * a * (ω ^ 2 * b) = ω * (a * b) := by
    calc
      ω ^ 2 * a * (ω ^ 2 * b) = (ω ^ 2 * ω ^ 2) * (a * b) := by ring
      _ = ω * (a * b) := by rw [hω4]
  have hmul (a b : K) : ω * a * (ω ^ 2 * b) = a * b := by
    calc
      ω * a * (ω ^ 2 * b) = (ω * ω ^ 2) * (a * b) := by ring
      _ = a * b := by rw [hω32, one_mul]
  have hmul' (a b : K) : ω ^ 2 * a * (ω * b) = a * b := by
    calc
      ω ^ 2 * a * (ω * b) = (ω ^ 2 * ω) * (a * b) := by ring
      _ = a * b := by rw [hω23, one_mul]
  have hdot (u v : Fin 3 → K) :
      ZornMatrix.dot (ω • u) (ω ^ 2 • v) = ZornMatrix.dot u v := by
    simp only [ZornMatrix.dot, Pi.smul_apply, smul_eq_mul]
    rw [hmul, hmul, hmul]
  have hdot' (u v : Fin 3 → K) :
      ZornMatrix.dot (ω ^ 2 • u) (ω • v) = ZornMatrix.dot u v := by
    simp only [ZornMatrix.dot, Pi.smul_apply, smul_eq_mul]
    rw [hmul', hmul', hmul']
  have hcross (u v : Fin 3 → K) :
      ZornMatrix.cross (ω ^ 2 • u) (ω ^ 2 • v) = ω • ZornMatrix.cross u v := by
    funext i
    fin_cases i <;>
      simp [ZornMatrix.cross, Pi.smul_apply, smul_eq_mul, hquad] <;> ring
  have hcross' (u v : Fin 3 → K) :
      ZornMatrix.cross (ω • u) (ω • v) = ω ^ 2 • ZornMatrix.cross u v := by
    funext i
    fin_cases i <;>
      simp [ZornMatrix.cross, Pi.smul_apply, smul_eq_mul, hω32] <;> ring
  apply ZornMatrix.ext
  · change X.a * Y.a + ZornMatrix.dot X.x Y.y =
      X.a * Y.a + ZornMatrix.dot (ω • X.x) (ω ^ 2 • Y.y)
    rw [hdot]
  · change X.b * Y.b + ZornMatrix.dot X.y Y.x =
      X.b * Y.b + ZornMatrix.dot (ω ^ 2 • X.y) (ω • Y.x)
    rw [hdot']
  · change ω • (X.a • Y.x + Y.b • X.x - ZornMatrix.cross X.y Y.y) =
      X.a • (ω • Y.x) + Y.b • (ω • X.x) -
        ZornMatrix.cross (ω ^ 2 • X.y) (ω ^ 2 • Y.y)
    rw [hcross]
    ext i
    simp [Pi.smul_apply, smul_eq_mul]
    ring
  · change ω ^ 2 • (X.b • Y.y + Y.a • X.y + ZornMatrix.cross X.x Y.x) =
      X.b • (ω ^ 2 • Y.y) + Y.a • (ω ^ 2 • X.y) +
        ZornMatrix.cross (ω • X.x) (ω • Y.x)
    rw [hcross']
    ext i
    simp [Pi.smul_apply, smul_eq_mul]
    ring

theorem cubicCharge_zero_eigen (ω : K) (Z : ZornMatrix K) :
    cubicCharge ω (cubicProjectorZero Z) = cubicProjectorZero Z := by
  simpa [cubicCharge, Equiv.smul_def, coordEquiv] using
    (rfl : cubicCharge ω (cubicProjectorZero Z) = cubicProjectorZero Z)

theorem cubicCharge_plus_eigen (ω : K) (Z : ZornMatrix K) :
    cubicCharge ω (cubicProjectorPlus Z) = ω • cubicProjectorPlus Z := by
  simpa [cubicCharge, Equiv.smul_def, coordEquiv] using
    (rfl : cubicCharge ω (cubicProjectorPlus Z) = ω • cubicProjectorPlus Z)

theorem cubicCharge_minus_eigen (ω : K) (Z : ZornMatrix K) :
    cubicCharge ω (cubicProjectorMinus Z) = (ω ^ 2) • cubicProjectorMinus Z := by
  simpa [cubicCharge, Equiv.smul_def, coordEquiv] using
    (rfl : cubicCharge ω (cubicProjectorMinus Z) = (ω ^ 2) • cubicProjectorMinus Z)

theorem cubicProjectors_sum_eq_id (Z : ZornMatrix K) :
    cubicProjectorZero Z + cubicProjectorPlus Z + cubicProjectorMinus Z = Z := by
  cases Z
  ext <;> simp [cubicProjectorZero, cubicProjectorPlus, cubicProjectorMinus,
    add_def]

theorem cubicProjectorZero_idempotent (Z : ZornMatrix K) :
    cubicProjectorZero (cubicProjectorZero Z) = cubicProjectorZero Z := by
  rfl

theorem cubicProjectorPlus_idempotent (Z : ZornMatrix K) :
    cubicProjectorPlus (cubicProjectorPlus Z) = cubicProjectorPlus Z := by
  rfl

theorem cubicProjectorMinus_idempotent (Z : ZornMatrix K) :
    cubicProjectorMinus (cubicProjectorMinus Z) = cubicProjectorMinus Z := by
  rfl

theorem cubicProjectorZero_plus_orthogonal (Z : ZornMatrix K) :
    cubicProjectorZero (cubicProjectorPlus Z) = 0 := by
  rfl

theorem cubicProjectorPlus_minus_orthogonal (Z : ZornMatrix K) :
    cubicProjectorPlus (cubicProjectorMinus Z) = 0 := by
  rfl

theorem cubicProjectorMinus_zero_orthogonal (Z : ZornMatrix K) :
    cubicProjectorMinus (cubicProjectorZero Z) = 0 := by
  rfl

theorem cubicProjectorZero_eq_diagonalProject (Z : ZornMatrix K) :
    cubicProjectorZero Z =
      Z.a • zornPlus + Z.b • zornMinus := by
  cases Z
  ext <;> simp [cubicProjectorZero, zornPlus, zornMinus, add_def,
    smul_a_coord, smul_b_coord, smul_x_coord, smul_y_coord]

theorem cubicProjectorPlus_eq_colorProject (Z : ZornMatrix K) :
    cubicProjectorPlus Z = colorProject Z := by
  rw [colorProject_apply]
  rfl

theorem cubicProjectorMinus_eq_anticolorProject (Z : ZornMatrix K) :
    cubicProjectorMinus Z = anticolorProject Z := by
  rw [anticolorProject_apply]
  rfl

end InfoGeometry.Canonical
