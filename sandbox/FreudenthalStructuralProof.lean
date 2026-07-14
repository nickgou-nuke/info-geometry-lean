import Mathlib
import InfoGeometry.OperatorAlgebra.SplitOctonionMultiplication

open InfoGeometry.OperatorAlgebra.SplitOctonions.Multiplication

namespace InfoGeometry.Algebra.Sandbox

@[ext]
structure AlbertMatrixZ where
  α₁ : ℤ
  α₂ : ℤ
  α₃ : ℤ
  z₁ : SplitOct
  z₂ : SplitOct
  z₃ : SplitOct
  deriving DecidableEq

def octTrace (Z : SplitOct) : ℤ := trZ Z

def normCubicZ (X : AlbertMatrixZ) : ℤ :=
  X.α₁ * X.α₂ * X.α₃ -
    X.α₁ * detZ X.z₁ -
    X.α₂ * detZ X.z₂ -
    X.α₃ * detZ X.z₃ +
    octTrace (mulZ (mulZ X.z₁ X.z₂) X.z₃)

def adjointQuadZ (X : AlbertMatrixZ) : AlbertMatrixZ :=
  { α₁ := X.α₂ * X.α₃ - detZ X.z₁
    α₂ := X.α₁ * X.α₃ - detZ X.z₂
    α₃ := X.α₁ * X.α₂ - detZ X.z₃
    z₁ := subZ (mulZ (conjZ X.z₃) (conjZ X.z₂)) (scaleZ X.α₁ X.z₁)
    z₂ := subZ (mulZ (conjZ X.z₁) (conjZ X.z₃)) (scaleZ X.α₂ X.z₂)
    z₃ := subZ (mulZ (conjZ X.z₂) (conjZ X.z₁)) (scaleZ X.α₃ X.z₃) }

instance : SMul ℤ AlbertMatrixZ where
  smul r X :=
    { α₁ := r * X.α₁
      α₂ := r * X.α₂
      α₃ := r * X.α₃
      z₁ := scaleZ r X.z₁
      z₂ := scaleZ r X.z₂
      z₃ := scaleZ r X.z₃ }

lemma ext_albertZ (X Y : AlbertMatrixZ)
    (hα₁ : X.α₁ = Y.α₁) (hα₂ : X.α₂ = Y.α₂) (hα₃ : X.α₃ = Y.α₃)
    (hz₁ : X.z₁ = Y.z₁) (hz₂ : X.z₂ = Y.z₂) (hz₃ : X.z₃ = Y.z₃) : X = Y := by
  rcases X with ⟨a1,a2,a3,zx1,zx2,zx3⟩
  rcases Y with ⟨b1,b2,b3,zy1,zy2,zy3⟩
  subst hα₁; subst hα₂; subst hα₃; subst hz₁; subst hz₂; subst hz₃; rfl

-- Helper scalar and subZ rules
lemma conjZ_subZ (X Y : SplitOct) : conjZ (subZ X Y) = subZ (conjZ X) (conjZ Y) := by
  cases X; cases Y; ext <;> { simp [conjZ, subZ]; try ring }

lemma conjZ_scaleZ (r : ℤ) (X : SplitOct) : conjZ (scaleZ r X) = scaleZ r (conjZ X) := by
  cases X; ext <;> { simp [conjZ, scaleZ]; try ring }

lemma conjZ_mulZ_reverse (X Y : SplitOct) : conjZ (mulZ X Y) = mulZ (conjZ Y) (conjZ X) := conjZ_mulZ X Y

lemma conjZ_conjZ_eq (X : SplitOct) : conjZ (conjZ X) = X := conjZ_conjZ X

lemma mulZ_subZ_subZ (A B C D : SplitOct) :
  mulZ (subZ A B) (subZ C D) = subZ (subZ (mulZ A C) (mulZ A D)) (subZ (mulZ B C) (mulZ B D)) := by
  cases A; cases B; cases C; cases D; ext <;> { simp [mulZ, subZ]; try ring }

lemma scaleZ_mulZ_left (r : ℤ) (X Y : SplitOct) : mulZ (scaleZ r X) Y = scaleZ r (mulZ X Y) := by
  cases X; cases Y; ext <;> { simp [mulZ, scaleZ]; try ring }

lemma scaleZ_mulZ_right (r : ℤ) (X Y : SplitOct) : mulZ X (scaleZ r Y) = scaleZ r (mulZ X Y) := by
  cases X; cases Y; ext <;> { simp [mulZ, scaleZ]; try ring }

lemma mulZ_conjZ_mulZ (X Y : SplitOct) : mulZ (conjZ X) (mulZ X Y) = scaleZ (detZ X) Y := by
  cases X; cases Y; ext <;> { simp [mulZ, conjZ, scaleZ, detZ]; try ring }

lemma mulZ_mulZ_conjZ (X Y : SplitOct) : mulZ (mulZ Y X) (conjZ X) = scaleZ (detZ X) Y := by
  cases X; cases Y; ext <;> { simp [mulZ, conjZ, scaleZ, detZ]; try ring }

lemma scaleZ_scaleZ (r s : ℤ) (X : SplitOct) : scaleZ r (scaleZ s X) = scaleZ (r * s) X := by
  cases X; ext <;> { simp [scaleZ]; try ring }

lemma sub_scaleZ (r s : ℤ) (X : SplitOct) : scaleZ (r - s) X = subZ (scaleZ r X) (scaleZ s X) := by
  cases X; ext <;> { simp [scaleZ, subZ]; try ring }

lemma scaleZ_subZ (r : ℤ) (X Y : SplitOct) : scaleZ r (subZ X Y) = subZ (scaleZ r X) (scaleZ r Y) := by
  cases X; cases Y; ext <;> { simp [scaleZ, subZ]; try ring }

lemma mul_scaleZ (r s : ℤ) (X : SplitOct) : scaleZ (r * s) X = scaleZ r (scaleZ s X) := by
  cases X; ext <;> { simp [scaleZ]; try ring }

lemma detZ_scaleZ (r : ℤ) (X : SplitOct) : detZ (scaleZ r X) = r * r * detZ X := by
  cases X; simp [detZ, scaleZ]; ring

lemma detZ_subZ (X Y : SplitOct) : detZ (subZ X Y) = detZ X + detZ Y - trZ (mulZ X (conjZ Y)) := by
  cases X; cases Y; simp [detZ, subZ, trZ, mulZ, conjZ]; ring

lemma detZ_conjZ_eq (X : SplitOct) : detZ (conjZ X) = detZ X := detZ_conjZ X

lemma trZ_mulZ_scaleZ_conjZ (r : ℤ) (X Y Z : SplitOct) : 
  trZ (mulZ (mulZ X Y) (conjZ (scaleZ r Z))) = r * trZ (mulZ (mulZ X Y) (conjZ Z)) := by
  cases X; cases Y; cases Z; simp [trZ, mulZ, conjZ, scaleZ]; ring

lemma trZ_alpha1 (z1 z2 z3 : SplitOct) : 
  trZ (mulZ (mulZ (conjZ z3) (conjZ z2)) (conjZ z1)) = trZ (mulZ (mulZ z1 z2) z3) := by
  cases z1; cases z2; cases z3; simp [trZ, mulZ, conjZ]; ring

lemma trZ_alpha2 (z1 z2 z3 : SplitOct) : 
  trZ (mulZ (mulZ (conjZ z1) (conjZ z3)) (conjZ z2)) = trZ (mulZ (mulZ z1 z2) z3) := by
  cases z1; cases z2; cases z3; simp [trZ, mulZ, conjZ]; ring

lemma trZ_alpha3 (z1 z2 z3 : SplitOct) : 
  trZ (mulZ (mulZ (conjZ z2) (conjZ z1)) (conjZ z3)) = trZ (mulZ (mulZ z1 z2) z3) := by
  cases z1; cases z2; cases z3; simp [trZ, mulZ, conjZ]; ring

lemma adjointQuadZ_alpha1 (X : AlbertMatrixZ) :
  (adjointQuadZ (adjointQuadZ X)).α₁ = normCubicZ X * X.α₁ := by
  simp [adjointQuadZ, normCubicZ, octTrace]
  rw [detZ_subZ]
  rw [detZ_mul]
  rw [detZ_conjZ_eq, detZ_conjZ_eq]
  rw [detZ_scaleZ]
  rw [trZ_mulZ_scaleZ_conjZ]
  rw [trZ_alpha1]
  ring

lemma adjointQuadZ_alpha2 (X : AlbertMatrixZ) :
  (adjointQuadZ (adjointQuadZ X)).α₂ = normCubicZ X * X.α₂ := by
  simp [adjointQuadZ, normCubicZ, octTrace]
  rw [detZ_subZ]
  rw [detZ_mul]
  rw [detZ_conjZ_eq, detZ_conjZ_eq]
  rw [detZ_scaleZ]
  rw [trZ_mulZ_scaleZ_conjZ]
  rw [trZ_alpha2]
  ring

lemma adjointQuadZ_alpha3 (X : AlbertMatrixZ) :
  (adjointQuadZ (adjointQuadZ X)).α₃ = normCubicZ X * X.α₃ := by
  simp [adjointQuadZ, normCubicZ, octTrace]
  rw [detZ_subZ]
  rw [detZ_mul]
  rw [detZ_conjZ_eq, detZ_conjZ_eq]
  rw [detZ_scaleZ]
  rw [trZ_mulZ_scaleZ_conjZ]
  rw [trZ_alpha3]
  ring

set_option maxHeartbeats 4000000

lemma z1_expansion (a1 a2 a3 : ℤ) (z1 z2 z3 : SplitOct) :
  subZ (mulZ (conjZ (subZ (mulZ (conjZ z2) (conjZ z1)) (scaleZ a3 z3)))
            (conjZ (subZ (mulZ (conjZ z1) (conjZ z3)) (scaleZ a2 z2))))
       (scaleZ (a2 * a3 - detZ z1) (subZ (mulZ (conjZ z3) (conjZ z2)) (scaleZ a1 z1))) =
  scaleZ (a1 * a2 * a3 - a1 * detZ z1 - a2 * detZ z2 - a3 * detZ z3 + trZ (mulZ (mulZ z1 z2) z3)) z1 := by
  simp only [conjZ_subZ, conjZ_scaleZ, conjZ_mulZ_reverse, conjZ_conjZ_eq]
  simp only [mulZ_subZ_subZ, scaleZ_mulZ_right, scaleZ_mulZ_left, mulZ_mulZ_conjZ, mulZ_conjZ_mulZ, scaleZ_scaleZ]
  simp only [sub_scaleZ, scaleZ_subZ, mul_scaleZ]
  cases z1; cases z2; cases z3
  ext <;> { simp [subZ, mulZ, scaleZ, detZ, conjZ, trZ]; try ring }

lemma z2_expansion (a1 a2 a3 : ℤ) (z1 z2 z3 : SplitOct) :
  subZ (mulZ (conjZ (subZ (mulZ (conjZ z3) (conjZ z2)) (scaleZ a1 z1)))
            (conjZ (subZ (mulZ (conjZ z2) (conjZ z1)) (scaleZ a3 z3))))
       (scaleZ (a1 * a3 - detZ z2) (subZ (mulZ (conjZ z1) (conjZ z3)) (scaleZ a2 z2))) =
  scaleZ (a1 * a2 * a3 - a1 * detZ z1 - a2 * detZ z2 - a3 * detZ z3 + trZ (mulZ (mulZ z1 z2) z3)) z2 := by
  simp only [conjZ_subZ, conjZ_scaleZ, conjZ_mulZ_reverse, conjZ_conjZ_eq]
  simp only [mulZ_subZ_subZ, scaleZ_mulZ_right, scaleZ_mulZ_left, mulZ_mulZ_conjZ, mulZ_conjZ_mulZ, scaleZ_scaleZ]
  simp only [sub_scaleZ, scaleZ_subZ, mul_scaleZ]
  cases z1; cases z2; cases z3
  ext <;> { simp [subZ, mulZ, scaleZ, detZ, conjZ, trZ]; try ring }

lemma z3_expansion (a1 a2 a3 : ℤ) (z1 z2 z3 : SplitOct) :
  subZ (mulZ (conjZ (subZ (mulZ (conjZ z1) (conjZ z3)) (scaleZ a2 z2)))
            (conjZ (subZ (mulZ (conjZ z3) (conjZ z2)) (scaleZ a1 z1))))
       (scaleZ (a1 * a2 - detZ z3) (subZ (mulZ (conjZ z2) (conjZ z1)) (scaleZ a3 z3))) =
  scaleZ (a1 * a2 * a3 - a1 * detZ z1 - a2 * detZ z2 - a3 * detZ z3 + trZ (mulZ (mulZ z1 z2) z3)) z3 := by
  simp only [conjZ_subZ, conjZ_scaleZ, conjZ_mulZ_reverse, conjZ_conjZ_eq]
  simp only [mulZ_subZ_subZ, scaleZ_mulZ_right, scaleZ_mulZ_left, mulZ_mulZ_conjZ, mulZ_conjZ_mulZ, scaleZ_scaleZ]
  simp only [sub_scaleZ, scaleZ_subZ, mul_scaleZ]
  cases z1; cases z2; cases z3
  ext <;> { simp [subZ, mulZ, scaleZ, detZ, conjZ, trZ]; try ring }

lemma adjointQuadZ_z1 (X : AlbertMatrixZ) :
  (adjointQuadZ (adjointQuadZ X)).z₁ = scaleZ (normCubicZ X) X.z₁ := by
  rcases X with ⟨a1, a2, a3, z1, z2, z3⟩
  unfold adjointQuadZ normCubicZ octTrace
  exact z1_expansion a1 a2 a3 z1 z2 z3

lemma adjointQuadZ_z2 (X : AlbertMatrixZ) :
  (adjointQuadZ (adjointQuadZ X)).z₂ = scaleZ (normCubicZ X) X.z₂ := by
  rcases X with ⟨a1, a2, a3, z1, z2, z3⟩
  unfold adjointQuadZ normCubicZ octTrace
  exact z2_expansion a1 a2 a3 z1 z2 z3

lemma adjointQuadZ_z3 (X : AlbertMatrixZ) :
  (adjointQuadZ (adjointQuadZ X)).z₃ = scaleZ (normCubicZ X) X.z₃ := by
  rcases X with ⟨a1, a2, a3, z1, z2, z3⟩
  unfold adjointQuadZ normCubicZ octTrace
  exact z3_expansion a1 a2 a3 z1 z2 z3

theorem freudenthal_identityZ (X : AlbertMatrixZ) : 
    adjointQuadZ (adjointQuadZ X) = (normCubicZ X) • X := by
  apply ext_albertZ
  · exact adjointQuadZ_alpha1 X
  · exact adjointQuadZ_alpha2 X
  · exact adjointQuadZ_alpha3 X
  · exact adjointQuadZ_z1 X
  · exact adjointQuadZ_z2 X
  · exact adjointQuadZ_z3 X

end InfoGeometry.Algebra.Sandbox
