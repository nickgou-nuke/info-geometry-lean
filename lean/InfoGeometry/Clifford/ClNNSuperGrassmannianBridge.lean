import InfoGeometry.Clifford.ClNN
import InfoGeometry.Algebra.SuperGrassmannianClifford

/-!
# Recursive split Clifford generators in the super-Grassmannian tower

This bridge joins the recursive `Cl(N,N)` owner to the stage-indexed
Clifford/exterior tower. It records the tail generator map and transports
the native odd Clifford grade through that map. Exterior generators of the
head null modes lie in the corresponding exterior super-grade. These are
parity and carrier statements; they do not identify wedge multiplication
with the Clifford geometric product or assert a full supermanifold model.
-/

noncomputable section

namespace InfoGeometry.Clifford.ClNNSuperGrassmannianBridge

open InfoGeometry.Clifford.ClNN
open InfoGeometry.CliffordTower
open InfoGeometry.Algebra.SuperGrassmannianClifford

/-- The super-Grassmannian Clifford stage map sends an old generator to the
recursive tail generator of `Cl(N+1,N+1)`. -/
theorem splitStageCliffordMap_generator_eq_gammaTail
    (n : ℕ) (x : Carrier n) :
    splitStageCliffordMap n (CliffordAlgebra.ι (Qsplit n) x) =
      gammaTail n x := by
  change CliffordAlgebra.map (splitStageIsometry n)
      (CliffordAlgebra.ι (Qsplit n) x) =
    CliffordAlgebra.ι (Qsplit (n + 1)) (tailLift n x)
  rw [CliffordAlgebra.map_apply_ι, splitStageIsometry_apply]
  rfl

/-- The recursively embedded tail generator remains odd in Mathlib's native
`evenOdd` grading of the larger split Clifford algebra. -/
theorem gammaTail_mem_odd (n : ℕ) (x : Carrier n) :
    gammaTail n x ∈ CliffordAlgebra.evenOdd (Qsplit (n + 1)) 1 := by
  have hx : CliffordAlgebra.ι (Qsplit n) x ∈
      CliffordAlgebra.evenOdd (Qsplit n) 1 :=
    CliffordAlgebra.ι_mem_evenOdd_one (Q := Qsplit n) x
  have hmap := splitStageCliffordMap_preserves_evenOdd n 1
    (Submodule.mem_map_of_mem hx)
  change splitStageCliffordMap n (CliffordAlgebra.ι (Qsplit n) x) ∈ _ at hmap
  rw [splitStageCliffordMap_generator_eq_gammaTail] at hmap
  exact hmap

/-- The normalized CAR pair at one recursive head remains a normalized CAR
pair when the stage embedding places it in the next Clifford algebra's tail. -/
theorem gammaTail_headNullPair_CAR (n : ℕ) :
    gammaTail (n + 1) (headNullMinus n) * gammaTail (n + 1) (headNullPlus n) +
      gammaTail (n + 1) (headNullPlus n) * gammaTail (n + 1) (headNullMinus n) =
        (1 : Alg (n + 2)) := by
  have hmap := congrArg (splitStageCliffordMap (n + 1))
    (gammaHeadNullMinus_mul_gammaHeadNullPlus_add_swap n)
  simp only [map_add, map_mul, map_one] at hmap
  change splitStageCliffordMap (n + 1)
        (CliffordAlgebra.ι (Qsplit (n + 1)) (headNullMinus n)) *
      splitStageCliffordMap (n + 1)
        (CliffordAlgebra.ι (Qsplit (n + 1)) (headNullPlus n)) +
    splitStageCliffordMap (n + 1)
        (CliffordAlgebra.ι (Qsplit (n + 1)) (headNullPlus n)) *
      splitStageCliffordMap (n + 1)
        (CliffordAlgebra.ι (Qsplit (n + 1)) (headNullMinus n)) = 1 at hmap
  rw [splitStageCliffordMap_generator_eq_gammaTail (n + 1) (headNullMinus n),
    splitStageCliffordMap_generator_eq_gammaTail (n + 1) (headNullPlus n)] at hmap
  exact hmap

/-- The exterior-algebra representative of each recursive head null mode is
in super-grade one. The statement uses the existing Clifford-to-exterior
equivalence, so it does not identify the two products. -/
theorem headNullMinus_exterior_mem_superGrade (n : ℕ) :
    CliffordAlgebra.equivExterior (Qsplit (n + 1))
        (gammaHeadNullMinus n) ∈
      superGrade (Qsplit (n + 1)) (1 : ZMod 2) := by
  change (cliffordExteriorEquiv (Qsplit (n + 1))).symm
      ((cliffordExteriorEquiv (Qsplit (n + 1)))
        (CliffordAlgebra.ι (Qsplit (n + 1)) (headNullMinus n))) ∈
    CliffordAlgebra.evenOdd (Qsplit (n + 1)) 1
  simpa using CliffordAlgebra.ι_mem_evenOdd_one
    (Q := Qsplit (n + 1)) (headNullMinus n)

/-- The positive head null mode has the same odd exterior super-grade. -/
theorem headNullPlus_exterior_mem_superGrade (n : ℕ) :
    CliffordAlgebra.equivExterior (Qsplit (n + 1))
        (gammaHeadNullPlus n) ∈
      superGrade (Qsplit (n + 1)) (1 : ZMod 2) := by
  change (cliffordExteriorEquiv (Qsplit (n + 1))).symm
      ((cliffordExteriorEquiv (Qsplit (n + 1)))
        (CliffordAlgebra.ι (Qsplit (n + 1)) (headNullPlus n))) ∈
    CliffordAlgebra.evenOdd (Qsplit (n + 1)) 1
  simpa using CliffordAlgebra.ι_mem_evenOdd_one
    (Q := Qsplit (n + 1)) (headNullPlus n)

/-- The exterior-algebra generators corresponding to the two recursive head
modes. Their geometric product below is not the wedge product. -/
def headNullMinusExterior (n : ℕ) : SplitExteriorStage (n + 1) :=
  ExteriorAlgebra.ι ℝ (headNullMinus n)

def headNullPlusExterior (n : ℕ) : SplitExteriorStage (n + 1) :=
  ExteriorAlgebra.ι ℝ (headNullPlus n)

/-- The Clifford-to-exterior module equivalence sends each recursive head
generator to its exterior-algebra generator. -/
@[simp] theorem headNullMinusExterior_eq_equivExterior (n : ℕ) :
    headNullMinusExterior n =
      CliffordAlgebra.equivExterior (Qsplit (n + 1)) (gammaHeadNullMinus n) := by
  simp [headNullMinusExterior, gammaHeadNullMinus,
    CliffordAlgebra.equivExterior, CliffordAlgebra.changeForm_ι]

@[simp] theorem headNullPlusExterior_eq_equivExterior (n : ℕ) :
    headNullPlusExterior n =
      CliffordAlgebra.equivExterior (Qsplit (n + 1)) (gammaHeadNullPlus n) := by
  simp [headNullPlusExterior, gammaHeadNullPlus,
    CliffordAlgebra.equivExterior, CliffordAlgebra.changeForm_ι]

/-- In the exterior carrier, the geometric square of the first recursive head
mode vanishes by its null quadratic value and Mathlib's vector-square law. -/
@[simp] theorem headNullMinusExterior_geometricProduct_sq (n : ℕ) :
    geometricProduct (Qsplit (n + 1)) (headNullMinusExterior n)
      (headNullMinusExterior n) = 0 := by
  change geometricProduct (Qsplit (n + 1))
    (ExteriorAlgebra.ι ℝ (headNullMinus n))
    (ExteriorAlgebra.ι ℝ (headNullMinus n)) = 0
  rw [geometricProduct_vector_square]
  change algebraMap ℝ (SplitExteriorStage (n + 1))
    (Quad (n + 1) (headNullMinus n)) = 0
  rw [headNullMinus_isotropic, map_zero]

/-- The second recursive head mode also has zero geometric square in the
exterior carrier. -/
@[simp] theorem headNullPlusExterior_geometricProduct_sq (n : ℕ) :
    geometricProduct (Qsplit (n + 1)) (headNullPlusExterior n)
      (headNullPlusExterior n) = 0 := by
  change geometricProduct (Qsplit (n + 1))
    (ExteriorAlgebra.ι ℝ (headNullPlus n))
    (ExteriorAlgebra.ι ℝ (headNullPlus n)) = 0
  rw [geometricProduct_vector_square]
  change algebraMap ℝ (SplitExteriorStage (n + 1))
    (Quad (n + 1) (headNullPlus n)) = 0
  rw [headNullPlus_isotropic, map_zero]

/-- Both exterior representatives remain in the odd component of the native
Mathlib Clifford grading transported to the exterior carrier. -/
theorem headNullMinusExterior_mem_superGrade (n : ℕ) :
    headNullMinusExterior n ∈
      superGrade (Qsplit (n + 1)) (1 : ZMod 2) := by
  rw [headNullMinusExterior_eq_equivExterior]
  exact headNullMinus_exterior_mem_superGrade n

theorem headNullPlusExterior_mem_superGrade (n : ℕ) :
    headNullPlusExterior n ∈
      superGrade (Qsplit (n + 1)) (1 : ZMod 2) := by
  rw [headNullPlusExterior_eq_equivExterior]
  exact headNullPlus_exterior_mem_superGrade n

/-- The recursive split head CAR relation holds in the exterior carrier when
the product is the Mathlib-transported geometric product. -/
theorem headNullExterior_geometricProduct_CAR (n : ℕ) :
    geometricProduct (Qsplit (n + 1)) (headNullMinusExterior n)
        (headNullPlusExterior n) +
      geometricProduct (Qsplit (n + 1)) (headNullPlusExterior n)
        (headNullMinusExterior n) = 1 := by
  change geometricProduct (Qsplit (n + 1))
      (ExteriorAlgebra.ι ℝ (headNullMinus n))
      (ExteriorAlgebra.ι ℝ (headNullPlus n)) +
    geometricProduct (Qsplit (n + 1))
      (ExteriorAlgebra.ι ℝ (headNullPlus n))
      (ExteriorAlgebra.ι ℝ (headNullMinus n)) = 1
  rw [geometricProduct_vector_decomposition,
    geometricProduct_vector_decomposition]
  have hpolar :
      (2 : ℝ) • metricInner (Qsplit (n + 1))
        (headNullMinus n) (headNullPlus n) =
      QuadraticMap.polar (Qsplit (n + 1)) (headNullMinus n) (headNullPlus n) := by
    have h := congrArg (fun B => B (headNullMinus n) (headNullPlus n))
      (QuadraticMap.two_nsmul_associated (S := ℝ) (Qsplit (n + 1)))
    simp only [LinearMap.smul_apply,
      QuadraticMap.polarBilin_apply_apply] at h
    rw [← Nat.cast_smul_eq_nsmul ℝ] at h
    change (2 : ℝ) • QuadraticMap.associated (Qsplit (n + 1))
        (headNullMinus n) (headNullPlus n) =
      QuadraticMap.polar (Qsplit (n + 1))
        (headNullMinus n) (headNullPlus n) at h
    exact h
  have hmetric :
      metricInner (Qsplit (n + 1)) (headNullMinus n) (headNullPlus n) +
        metricInner (Qsplit (n + 1)) (headNullPlus n) (headNullMinus n) = 1 := by
    rw [metricInner_symmetric (Qsplit (n + 1))
      (headNullPlus n) (headNullMinus n)]
    rw [← two_smul ℝ (metricInner (Qsplit (n + 1))
      (headNullMinus n) (headNullPlus n)), hpolar,
      polar_headNullMinus_headNullPlus]
  have hwedge := outerProduct_vectors_anticommute (R := ℝ)
    (headNullMinus n) (headNullPlus n)
  calc
    (algebraMap ℝ (SplitExteriorStage (n + 1))
          (metricInner (Qsplit (n + 1)) (headNullMinus n) (headNullPlus n)) +
        outerProduct (headNullMinusExterior n) (headNullPlusExterior n)) +
      (algebraMap ℝ (SplitExteriorStage (n + 1))
          (metricInner (Qsplit (n + 1)) (headNullPlus n) (headNullMinus n)) +
        outerProduct (headNullPlusExterior n) (headNullMinusExterior n)) =
        (algebraMap ℝ (SplitExteriorStage (n + 1))
            (metricInner (Qsplit (n + 1)) (headNullMinus n) (headNullPlus n)) +
          algebraMap ℝ (SplitExteriorStage (n + 1))
            (metricInner (Qsplit (n + 1)) (headNullPlus n) (headNullMinus n))) +
          (outerProduct (headNullMinusExterior n) (headNullPlusExterior n) +
            outerProduct (headNullPlusExterior n) (headNullMinusExterior n)) := by
              abel
    _ = algebraMap ℝ (SplitExteriorStage (n + 1))
          (metricInner (Qsplit (n + 1)) (headNullMinus n) (headNullPlus n) +
            metricInner (Qsplit (n + 1)) (headNullPlus n) (headNullMinus n)) := by
          rw [headNullMinusExterior, headNullPlusExterior]
          rw [← map_add, hwedge, hmetric]
          simp
    _ = 1 := by rw [hmetric]; simp

end InfoGeometry.Clifford.ClNNSuperGrassmannianBridge

end noncomputable section
