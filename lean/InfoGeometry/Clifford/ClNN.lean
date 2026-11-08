import InfoGeometry.Clifford.Tower
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Meta.Architecture

open scoped TensorProduct

/-!
# InfoGeometry.Clifford.ClNN

Root owner surface for the recursive split `Cl(n,n)` tower already present in
`CliffordTower`.

This file packages the existing split tower as a real owner layer:

- recursive head/tail decomposition of the split carrier,
- normalized lightlike head modes,
- exact Clifford relations for those head null generators,
- orthogonality of the head null seeds against the recursive tail.

Authority note:

- this file owns the recursive split-tower presentation already present in the
  repository,
- it does **not** own the corrected neutral phase-space ontology on `E × E*`,
- that corrected owner lives in `NeutralPhaseSpaceCore`,
- so downstream files should treat `ClNN` as the split-tower root and
  `NeutralPhaseSpaceCore` as the semantic root of the corrected phase-space
  lane.
-/

namespace InfoGeometry.Clifford.ClNN

open InfoGeometry.CliffordTower

/-- Carrier for the split `Cl(n,n)` tower. -/
abbrev Carrier (n : ℕ) := SplitSpace n

/-- Quadratic form for the split `Cl(n,n)` tower. -/
noncomputable abbrev Quad (n : ℕ) : QuadraticForm ℝ (Carrier n) := Qsplit n

/-- Clifford algebra for the split `Cl(n,n)` tower. -/
abbrev Alg (n : ℕ) := Clsplit n

/-- Head-factor inclusion into the recursive split carrier. -/
@[rep_depth krein]
noncomputable def headPair (n : ℕ) (x : ℝ × ℝ) : Carrier (n + 1) :=
  (x, 0)

/-- Tail inclusion into the recursive split carrier. -/
@[rep_depth krein]
noncomputable def tailLift (n : ℕ) (xs : Carrier n) : Carrier (n + 1) :=
  ((0, 0), xs)

/-- Normalized lightlike `u_-` mode in the head `Cl(1,1)` factor. -/
@[rep_depth krein]
noncomputable def headNullMinus (n : ℕ) : Carrier (n + 1) :=
  headPair n ((1 / 2 : ℝ), (1 / 2 : ℝ))

/-- Normalized lightlike `u_+` mode in the head `Cl(1,1)` factor. -/
@[rep_depth krein]
noncomputable def headNullPlus (n : ℕ) : Carrier (n + 1) :=
  headPair n ((1 / 2 : ℝ), (-(1 / 2 : ℝ)))

@[rep_depth krein, simp] theorem quad_headPair
    (n : ℕ) (x : ℝ × ℝ) :
    Quad (n + 1) (headPair n x) = Q11 x := by
  change Qsplit (n + 1) (x, (0 : Carrier n)) = Q11 x
  rw [Qsplit_succ_apply]
  simp [Q11]

@[rep_depth krein, simp] theorem quad_tailLift
    (n : ℕ) (xs : Carrier n) :
    Quad (n + 1) (tailLift n xs) = Quad n xs := by
  change Qsplit (n + 1) ((0, 0), xs) = Qsplit n xs
  rw [Qsplit_succ_apply]
  simp

@[rep_depth krein] theorem head_tail_decompose
    (n : ℕ) (x : ℝ × ℝ) (xs : Carrier n) :
    (x, xs) = headPair n x + tailLift n xs := by
  cases x with
  | mk a b =>
      change ((a, b), xs) = ((a, b), 0) + ((0, 0), xs)
      simp

@[rep_depth krein, simp] theorem polar_headPair_tailLift
    (n : ℕ) (x : ℝ × ℝ) (xs : Carrier n) :
    QuadraticMap.polar (Quad (n + 1)) (headPair n x) (tailLift n xs) = 0 := by
  have hsum : headPair n x + tailLift n xs = (x, xs) := (head_tail_decompose n x xs).symm
  rw [QuadraticMap.polar, hsum]
  rw [Qsplit_succ_apply, quad_headPair, quad_tailLift]
  simp

@[rep_depth krein, simp] theorem headNullMinus_isotropic
    (n : ℕ) :
    Quad (n + 1) (headNullMinus n) = 0 := by
  rw [headNullMinus, quad_headPair]
  simp [Q11]

@[rep_depth krein, simp] theorem headNullPlus_isotropic
    (n : ℕ) :
    Quad (n + 1) (headNullPlus n) = 0 := by
  rw [headNullPlus, quad_headPair]
  simp [Q11]

@[rep_depth krein, simp] theorem polar_headNullMinus_headNullPlus
    (n : ℕ) :
    QuadraticMap.polar (Quad (n + 1)) (headNullMinus n) (headNullPlus n) = 1 := by
  have hsum :
      headNullMinus n + headNullPlus n = headPair n ((1 : ℝ), 0) := by
    change (((1 / 2 : ℝ), (1 / 2 : ℝ)), (0 : Carrier n))
        + (((1 / 2 : ℝ), (-(1 / 2 : ℝ))), (0 : Carrier n))
        = (((1 : ℝ), 0), (0 : Carrier n))
    simp
    norm_num
  rw [QuadraticMap.polar, hsum, headNullMinus_isotropic, headNullPlus_isotropic]
  rw [quad_headPair]
  norm_num [Q11]

@[rep_depth krein]
noncomputable def gammaHeadNullMinus (n : ℕ) : Alg (n + 1) :=
  CliffordAlgebra.ι (Quad (n + 1)) (headNullMinus n)

@[rep_depth krein]
noncomputable def gammaHeadNullPlus (n : ℕ) : Alg (n + 1) :=
  CliffordAlgebra.ι (Quad (n + 1)) (headNullPlus n)

@[rep_depth krein]
noncomputable def gammaTail (n : ℕ) (xs : Carrier n) : Alg (n + 1) :=
  CliffordAlgebra.ι (Quad (n + 1)) (tailLift n xs)

@[rep_depth krein, simp] theorem gammaHeadNullMinus_sq
    (n : ℕ) :
    gammaHeadNullMinus n * gammaHeadNullMinus n = 0 := by
  rw [gammaHeadNullMinus, CliffordAlgebra.ι_sq_scalar]
  rw [headNullMinus_isotropic, map_zero]

@[rep_depth krein, simp] theorem gammaHeadNullPlus_sq
    (n : ℕ) :
    gammaHeadNullPlus n * gammaHeadNullPlus n = 0 := by
  rw [gammaHeadNullPlus, CliffordAlgebra.ι_sq_scalar]
  rw [headNullPlus_isotropic, map_zero]

@[rep_depth krein, simp] theorem gammaHeadNullMinus_mul_gammaHeadNullPlus_add_swap
    (n : ℕ) :
    gammaHeadNullMinus n * gammaHeadNullPlus n
      + gammaHeadNullPlus n * gammaHeadNullMinus n = 1 := by
  have h :=
    CliffordAlgebra.ι_mul_ι_add_swap
      (Q := Quad (n + 1)) (headNullMinus n) (headNullPlus n)
  rw [polar_headNullMinus_headNullPlus, map_one] at h
  exact h

@[rep_depth krein, simp] theorem gammaHeadNullPlus_mul_gammaHeadNullMinus_add_swap
    (n : ℕ) :
    gammaHeadNullPlus n * gammaHeadNullMinus n
      + gammaHeadNullMinus n * gammaHeadNullPlus n = 1 := by
  simpa only [add_comm] using gammaHeadNullMinus_mul_gammaHeadNullPlus_add_swap n

@[rep_depth krein, simp] theorem gammaHeadNullMinus_mul_gammaTail_add_swap
    (n : ℕ) (xs : Carrier n) :
    gammaHeadNullMinus n * gammaTail n xs
      + gammaTail n xs * gammaHeadNullMinus n = 0 := by
  rw [gammaHeadNullMinus, gammaTail, CliffordAlgebra.ι_mul_ι_add_swap]
  change algebraMap ℝ (CliffordAlgebra (Quad (n + 1)))
      (QuadraticMap.polar (Quad (n + 1))
        (headPair n ((1 / 2 : ℝ), (1 / 2 : ℝ))) (tailLift n xs)) = 0
  rw [polar_headPair_tailLift, map_zero]

@[rep_depth krein, simp] theorem gammaHeadNullPlus_mul_gammaTail_add_swap
    (n : ℕ) (xs : Carrier n) :
    gammaHeadNullPlus n * gammaTail n xs
      + gammaTail n xs * gammaHeadNullPlus n = 0 := by
  rw [gammaHeadNullPlus, gammaTail, CliffordAlgebra.ι_mul_ι_add_swap]
  change algebraMap ℝ (CliffordAlgebra (Quad (n + 1)))
      (QuadraticMap.polar (Quad (n + 1))
        (headPair n ((1 / 2 : ℝ), (-(1 / 2 : ℝ)))) (tailLift n xs)) = 0
  rw [polar_headPair_tailLift, map_zero]

end InfoGeometry.Clifford.ClNN
