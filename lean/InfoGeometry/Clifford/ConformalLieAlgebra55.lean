import Mathlib.LinearAlgebra.CliffordAlgebra.Even
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Lie.OfAssociative
import InfoGeometry.Clifford.ClNN
import InfoGeometry.Clifford.ConformalLift55
import InfoGeometry.Canonical.ConformalFiveGradeInversion
import InfoGeometry.Clifford.ConformalGeneratorLemmas55
import Mathlib.Tactic.NoncommRing

open InfoGeometry.CliffordTower
open InfoGeometry.Clifford.ClNN
open InfoGeometry.Clifford.ConformalLift55
open InfoGeometry.Canonical.ConformalFiveGradeInversion

noncomputable section

namespace InfoGeometry.Clifford.ConformalLieAlgebra55

def toInt : ConformalGrade → ℤ
  | ConformalGrade.negTwo => -2
  | ConformalGrade.negOne => -1
  | ConformalGrade.zero => 0
  | ConformalGrade.posOne => 1
  | ConformalGrade.posTwo => 2

-- The Lie bracket on the full algebra
def adD : Alg 5 →ₗ[ℝ] Alg 5 where
  toFun x := D * x - x * D
  map_add' x y := by
    simp [mul_add, add_mul]
    abel
  map_smul' c x := by
    dsimp
    rw [smul_sub]
    congr 1
    · exact (Algebra.mul_smul_comm c D x)
    · exact (Algebra.smul_mul_assoc c x D)

def gradeSpace (g : ConformalGrade) : Submodule ℝ (Alg 5) :=
  LinearMap.ker (adD - (toInt g : ℝ) • (LinearMap.id : Alg 5 →ₗ[ℝ] Alg 5))

/-! ### Structural Morphism Rules -/

/-- `adD` acts as a derivation (Leibniz rule). -/
theorem adD_mul (a b : Alg 5) : adD (a * b) = adD a * b + a * adD b := by
  dsimp [adD]
  noncomm_ring

theorem gradeSpace_mul_of_sum
    (g h k : ConformalGrade) {x y : Alg 5}
    (hx : x ∈ gradeSpace g) (hy : y ∈ gradeSpace h)
    (hgrade : toInt k = toInt g + toInt h) :
    x * y ∈ gradeSpace k := by
  have hx' : adD x = (toInt g : ℝ) • x :=
    sub_eq_zero.mp (LinearMap.mem_ker.mp hx)
  have hy' : adD y = (toInt h : ℝ) • y :=
    sub_eq_zero.mp (LinearMap.mem_ker.mp hy)
  have hxy : adD (x * y) =
      ((toInt g : ℝ) + (toInt h : ℝ)) • (x * y) := by
    rw [adD_mul, hx', hy', smul_mul_assoc, Algebra.mul_smul_comm]
    rw [add_smul]
  dsimp [gradeSpace]
  rw [LinearMap.mem_ker]
  change adD (x * y) - (toInt k : ℝ) • (x * y) = 0
  rw [hxy, hgrade, Int.cast_add]
  exact sub_self _

theorem gradeSpace_commutator_of_sum
    (g h k : ConformalGrade) {x y : Alg 5}
    (hx : x ∈ gradeSpace g) (hy : y ∈ gradeSpace h)
    (hgrade : toInt k = toInt g + toInt h) :
    x * y - y * x ∈ gradeSpace k := by
  have hxy := gradeSpace_mul_of_sum g h k hx hy hgrade
  have hyx : y * x ∈ gradeSpace k := by
    apply gradeSpace_mul_of_sum h g k hy hx
    rw [hgrade, add_comm]
  exact sub_mem hxy hyx

theorem gradeSpace_anticommutator_of_sum
    (g h k : ConformalGrade) {x y : Alg 5}
    (hx : x ∈ gradeSpace g) (hy : y ∈ gradeSpace h)
    (hgrade : toInt k = toInt g + toInt h) :
    x * y + y * x ∈ gradeSpace k := by
  have hxy := gradeSpace_mul_of_sum g h k hx hy hgrade
  have hyx : y * x ∈ gradeSpace k := by
    apply gradeSpace_mul_of_sum h g k hy hx
    rw [hgrade, add_comm]
  exact add_mem hxy hyx
/-- `thetaOp` intertwines with `adD` up to a sign. -/
theorem theta_adD (x : Alg 5) : thetaOp (adD x) = - adD (thetaOp x) := by
  dsimp [adD]
  have h_sub : thetaOp (D * x - x * D) = thetaOp (D * x) - thetaOp (x * D) := by
    dsimp [thetaOp]; noncomm_ring
  rw [h_sub, theta_mul, theta_mul, theta_D]
  noncomm_ring

theorem theta_maps (g : ConformalGrade) (x : Alg 5) (hx : x ∈ gradeSpace g) : 
    thetaOp x ∈ gradeSpace (ConformalGrade.swap g) := by
  have h_adD : adD x = (toInt g : ℝ) • x := by
    have h1 : adD x - ((toInt g : ℝ) • (LinearMap.id : Alg 5 →ₗ[ℝ] Alg 5)) x = 0 := by
      calc adD x - ((toInt g : ℝ) • (LinearMap.id : Alg 5 →ₗ[ℝ] Alg 5)) x = (adD - (toInt g : ℝ) • (LinearMap.id : Alg 5 →ₗ[ℝ] Alg 5)) x := by exact (LinearMap.sub_apply adD ((toInt g : ℝ) • (LinearMap.id : Alg 5 →ₗ[ℝ] Alg 5)) x).symm
           _ = 0 := hx
    exact sub_eq_zero.mp h1
  have h_goal : adD (thetaOp x) = (toInt (ConformalGrade.swap g) : ℝ) • thetaOp x := by
    calc
      adD (thetaOp x) = - thetaOp (adD x) := by rw [theta_adD]; simp
      _ = - thetaOp ((toInt g : ℝ) • x) := by rw [h_adD]
      _ = - ((toInt g : ℝ) • thetaOp x) := by dsimp [thetaOp]; rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
      _ = (- (toInt g : ℝ)) • thetaOp x := by rw [neg_smul]
      _ = (toInt (ConformalGrade.swap g) : ℝ) • thetaOp x := by
        congr 1
        rcases g with _ | _ | _ | _ | _ <;> norm_num [toInt, ConformalGrade.swap]
  dsimp [gradeSpace]
  rw [LinearMap.mem_ker]
  have h_sub2 : (adD - (toInt (ConformalGrade.swap g) : ℝ) • (LinearMap.id : Alg 5 →ₗ[ℝ] Alg 5)) (thetaOp x) = adD (thetaOp x) - ((toInt (ConformalGrade.swap g) : ℝ) • (LinearMap.id : Alg 5 →ₗ[ℝ] Alg 5)) (thetaOp x) := by exact LinearMap.sub_apply adD ((toInt (ConformalGrade.swap g) : ℝ) • (LinearMap.id : Alg 5 →ₗ[ℝ] Alg 5)) (thetaOp x)
  rw [h_sub2]
  rw [h_goal]
  dsimp
  rw [sub_eq_zero]

/-- The grade subspaces intersected with the even Clifford subalgebra. -/
def gradeSpaceEven (g : ConformalGrade) : Submodule ℝ (CliffordAlgebra.even (Qsplit 5)) :=
  (gradeSpace g).comap (Subalgebra.toSubmodule (CliffordAlgebra.even (Qsplit 5))).subtype

def thetaOpEven (x : CliffordAlgebra.even (Qsplit 5)) : CliffordAlgebra.even (Qsplit 5) :=
  by
    refine ⟨thetaOp x, ?_⟩
    have hu5 : u5 ∈ CliffordAlgebra.evenOdd (Qsplit 5) 1 := by
      simpa [u5] using (CliffordAlgebra.ι_mem_evenOdd_one (Q := Qsplit 5) (headNullMinus 4))
    have hv5 : v5 ∈ CliffordAlgebra.evenOdd (Qsplit 5) 1 := by
      simpa [v5] using (CliffordAlgebra.ι_mem_evenOdd_one (Q := Qsplit 5) (headNullPlus 4))
    have hu4 : u4 ∈ CliffordAlgebra.evenOdd (Qsplit 5) 1 := by
      simpa [u4] using (CliffordAlgebra.ι_mem_evenOdd_one (Q := Qsplit 5) (tailLift 4 (headNullMinus 3)))
    have hv4 : v4 ∈ CliffordAlgebra.evenOdd (Qsplit 5) 1 := by
      simpa [v4] using (CliffordAlgebra.ι_mem_evenOdd_one (Q := Qsplit 5) (tailLift 4 (headNullPlus 3)))
    have hJ5 : J5 ∈ CliffordAlgebra.evenOdd (Qsplit 5) 1 := by
      simpa [J5] using (sub_mem hu5 hv5)
    have hJ4 : J4 ∈ CliffordAlgebra.evenOdd (Qsplit 5) 1 := by
      simpa [J4] using (sub_mem hu4 hv4)
    have hJ : J ∈ CliffordAlgebra.evenOdd (Qsplit 5) 0 := by
      simpa [J] using (SetLike.mul_mem_graded hJ5 hJ4 : J5 * J4 ∈ CliffordAlgebra.evenOdd (Qsplit 5) (1 + 1))
    have hx0 : x.1 ∈ CliffordAlgebra.evenOdd (Qsplit 5) 0 := by
      simpa [CliffordAlgebra.even_toSubmodule] using x.2
    have hJx : J * x.1 ∈ CliffordAlgebra.evenOdd (Qsplit 5) 0 := by
      simpa using (SetLike.mul_mem_graded hJ hx0 : J * x.1 ∈ CliffordAlgebra.evenOdd (Qsplit 5) (0 + 0))
    have hJxJ : J * x.1 * J ∈ CliffordAlgebra.evenOdd (Qsplit 5) 0 := by
      simpa using (SetLike.mul_mem_graded hJx hJ : (J * x.1) * J ∈ CliffordAlgebra.evenOdd (Qsplit 5) (0 + 0))
    simpa [thetaOp] using (neg_mem hJxJ)

theorem theta_maps_even (g : ConformalGrade) (x : CliffordAlgebra.even (Qsplit 5)) (hx : x ∈ gradeSpaceEven g) :
    thetaOpEven x ∈ gradeSpaceEven (ConformalGrade.swap g) := by
  dsimp [gradeSpaceEven, thetaOpEven]
  exact theta_maps g x.val hx

def HomogeneousElementEven := Σ (g : ConformalGrade), gradeSpaceEven g

def homogeneousGradeEven (x : HomogeneousElementEven) : ConformalGrade := x.1

def homogeneousThetaEven (x : HomogeneousElementEven) : HomogeneousElementEven :=
  ⟨ConformalGrade.swap x.1, ⟨thetaOpEven x.2.1, theta_maps_even x.1 x.2.1 x.2.2⟩⟩

/-- 
  D2: Instantiate FiveGradedConformalInversion over the even Clifford subalgebra.
-/
def instanceFiveGraded : FiveGradedConformalInversion HomogeneousElementEven where
  theta := homogeneousThetaEven
  grade := homogeneousGradeEven
  theta_involutive := by
    intro ⟨g, ⟨x, hx⟩⟩
    dsimp [homogeneousThetaEven, homogeneousGradeEven]
    rcases g with _ | _ | _ | _ | _
    all_goals {
      dsimp [ConformalGrade.swap]
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        ext
        dsimp [thetaOpEven]
        simp [theta_inv]
    }
  grade_swap := by
    intro ⟨g, ⟨x, hx⟩⟩
    rfl



end InfoGeometry.Clifford.ConformalLieAlgebra55
