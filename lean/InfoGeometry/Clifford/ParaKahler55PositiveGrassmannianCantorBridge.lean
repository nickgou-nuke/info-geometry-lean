import InfoGeometry.Clifford.Cl11TensorTowerSupergraded
import InfoGeometry.Clifford.Cl55MatStageCarrierEquiv
import InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure
import InfoGeometry.Projective.MatrixPluckerPositiveBridge
import InfoGeometry.Projective.ExteriorPowerPluckerBridge
import InfoGeometry.Projective.ExteriorKleinCoordinateIncidence
import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
import InfoGeometry.Algebra.SupergradedBracket
import InfoGeometry.Algebra
import InfoGeometry.Exceptional.STUJordanTripleSystem
import InfoGeometry.CliffordWeyl.SplitCliffordGrades

/-!
# Positive exterior states and represented Cantor products

This module makes two concrete composition bridges: positive `Gr(2,4)` chart
representatives are read as positive decomposable exterior two-vectors, and
finite binary Cantor prefixes are represented multiplicatively in any abstract
`O₂` carrier.  The associator claims below concern associative products; the
separate STU Jordan triple identity is imported from its concrete owner.
-/

noncomputable section

namespace InfoGeometry.Clifford.ParaKahler55PositiveGrassmannianCantorBridge

open InfoGeometry.Projective.MatrixPluckerPositiveBridge
open InfoGeometry.Projective.ExteriorPowerPluckerBridge
open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.OperatorAlgebra.ErlangenNet
open InfoGeometry.Topology
open InfoGeometry.Clifford.Cl11TensorTowerSupergraded
open InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure
open InfoGeometry.CliffordTower
open scoped TensorProduct DirectSum

/-- Addition of parities in the superbracket, with `true` denoting odd. -/
def parityAdd (p q : Bool) : Bool := if p then !q else q

/-! ## Concrete positive Grassmannian chart points -/

/-- A concrete point of the strictly positive `Gr(2,4)` chart owner. It
records a matrix representative together with the owner's strict-minor
condition; no quotient by row operations is silently assumed. -/
structure PositiveGrassmannianChartPoint where
  representative : Matrix2x4
  positive : representative ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
    (k := 2) (n := 4)

theorem PositiveGrassmannianChartPoint.plucker_positive
    (P : PositiveGrassmannianChartPoint) (i : Fin 6) :
    0 < matrixPluckerCoords P.representative i :=
  positiveGrassmannianInterior_mem_matrixPluckerPositive
    P.representative P.positive i

/-! ## Positive row-orbit quotient and normalized Plücker readout

The chart matrices are representatives.  Positive-determinant row changes
preserve the oriented plane and multiply every Plücker coordinate by the same
positive scalar.  Normalizing by the sum of the six coordinates therefore
gives a canonical readout on the quotient.
-/

/-- The ordered column pair corresponding to one of the six `Gr(2,4)` Plücker
coordinates. -/
def pluckerPair : Fin 6 → Fin 2 → Fin 4
  | 0 => ![0, 1]
  | 1 => ![0, 2]
  | 2 => ![0, 3]
  | 3 => ![1, 2]
  | 4 => ![1, 3]
  | 5 => ![2, 3]

private theorem maximalMinor_fin2_for_plucker (M : Matrix2x4) (a b : Fin 4) :
    InfoGeometry.Canonical.maximalMinor M ![a, b] =
      M 0 a * M 1 b - M 0 b * M 1 a := by
  unfold InfoGeometry.Canonical.maximalMinor
  exact Matrix.det_fin_two _

theorem matrixPluckerCoords_eq_maximalMinor (M : Matrix2x4) (i : Fin 6) :
    matrixPluckerCoords M i =
      InfoGeometry.Canonical.maximalMinor M (pluckerPair i) := by
  fin_cases i <;> simp only [matrixPluckerCoords_apply, pluckerPair]
  all_goals rw [maximalMinor_fin2_for_plucker]

/-- Under a general `2 × 2` row change, each Plücker coordinate has the
expected determinant weight. -/
theorem matrixPluckerCoords_left_mul
    (A : Matrix (Fin 2) (Fin 2) ℝ) (M : Matrix2x4) (i : Fin 6) :
    matrixPluckerCoords (A * M) i = Matrix.det A * matrixPluckerCoords M i := by
  rw [matrixPluckerCoords_eq_maximalMinor, matrixPluckerCoords_eq_maximalMinor,
    InfoGeometry.Canonical.maximalMinor_left_mul]

/-- Sum of the six positive Plücker coordinates; this is a positive
normalizing scalar on the strict-positive chart. -/
def pluckerNormalizationDenom (M : Matrix2x4) : ℝ :=
  ∑ i : Fin 6, matrixPluckerCoords M i

/-- The projectively normalized Plücker-coordinate vector. -/
def normalizedPluckerCoords (M : Matrix2x4) :
    InfoGeometry.Algebra.FiniteSpin.Vec6R :=
  fun i => matrixPluckerCoords M i / pluckerNormalizationDenom M

theorem pluckerNormalizationDenom_pos (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    0 < pluckerNormalizationDenom M := by
  apply Finset.sum_pos
  · intro i hi
    exact positiveGrassmannianInterior_mem_matrixPluckerPositive M hM i
  · exact Finset.univ_nonempty

theorem pluckerNormalizationDenom_left_mul
    (A : Matrix (Fin 2) (Fin 2) ℝ) (M : Matrix2x4) :
    pluckerNormalizationDenom (A * M) =
      Matrix.det A * pluckerNormalizationDenom M := by
  unfold pluckerNormalizationDenom
  calc
    (∑ i : Fin 6, matrixPluckerCoords (A * M) i) =
        ∑ i : Fin 6, Matrix.det A * matrixPluckerCoords M i := by
          congr 1
          funext i
          exact matrixPluckerCoords_left_mul A M i
    _ = Matrix.det A * ∑ i : Fin 6, matrixPluckerCoords M i := by
          rw [← Finset.mul_sum]

/-- The normalized Plücker point is invariant under every positive-determinant
row change. -/
theorem normalizedPluckerCoords_left_mul
    (A : Matrix (Fin 2) (Fin 2) ℝ) (M : Matrix2x4)
    (hA : 0 < Matrix.det A)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    normalizedPluckerCoords (A * M) = normalizedPluckerCoords M := by
  funext i
  unfold normalizedPluckerCoords
  rw [matrixPluckerCoords_left_mul, pluckerNormalizationDenom_left_mul]
  have hden : pluckerNormalizationDenom M ≠ 0 :=
    ne_of_gt (pluckerNormalizationDenom_pos M hM)
  have hdet : Matrix.det A ≠ 0 := ne_of_gt hA
  field_simp [hdet, hden]

/-- The row-orbit relation on strictly positive `Gr(2,4)` chart matrices. -/
def positiveRowOrbitRel (P Q : PositiveGrassmannianChartPoint) : Prop :=
  ∃ A : Matrix (Fin 2) (Fin 2) ℝ,
    0 < Matrix.det A ∧ Q.representative = A * P.representative

theorem positiveRowOrbitRel_refl (P : PositiveGrassmannianChartPoint) :
    positiveRowOrbitRel P P := by
  refine ⟨1, by simp, ?_⟩
  simp

theorem positiveRowOrbitRel_symm {P Q : PositiveGrassmannianChartPoint}
    (h : positiveRowOrbitRel P Q) : positiveRowOrbitRel Q P := by
  rcases h with ⟨A, hA, hAQ⟩
  have hdetUnit : IsUnit (Matrix.det A) :=
    (isUnit_iff_ne_zero).2 (ne_of_gt hA)
  have hinvDet : 0 < Matrix.det A⁻¹ := by
    have hprod := Matrix.det_nonsing_inv_mul_det A hdetUnit
    nlinarith
  refine ⟨A⁻¹, hinvDet, ?_⟩
  rw [hAQ]
  calc
    P.representative = (1 : Matrix (Fin 2) (Fin 2) ℝ) * P.representative := by simp
    _ = (A⁻¹ * A) * P.representative := by
      rw [Matrix.nonsing_inv_mul A hdetUnit]
    _ = A⁻¹ * (A * P.representative) := by rw [Matrix.mul_assoc]

theorem positiveRowOrbitRel_trans {P Q R : PositiveGrassmannianChartPoint}
    (hPQ : positiveRowOrbitRel P Q) (hQR : positiveRowOrbitRel Q R) :
    positiveRowOrbitRel P R := by
  rcases hPQ with ⟨A, hA, hAQ⟩
  rcases hQR with ⟨B, hB, hBR⟩
  refine ⟨B * A, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact mul_pos hB hA
  · rw [hBR, hAQ, Matrix.mul_assoc]

/-- The setoid quotient of positive chart matrices by orientation-preserving
row changes. -/
def positiveGrassmannianRowSetoid : Setoid PositiveGrassmannianChartPoint where
  r := positiveRowOrbitRel
  iseqv := ⟨positiveRowOrbitRel_refl, positiveRowOrbitRel_symm,
    positiveRowOrbitRel_trans⟩

/-- The positive `Gr(2,4)` orbit space represented by strict-positive charts
modulo positive-determinant row changes. -/
abbrev PositiveGrassmannian := Quotient positiveGrassmannianRowSetoid

theorem positiveRowOrbitRel_normalizedPlucker
    {P Q : PositiveGrassmannianChartPoint}
    (h : positiveRowOrbitRel P Q) :
    normalizedPluckerCoords P.representative =
      normalizedPluckerCoords Q.representative := by
  rcases h with ⟨A, hA, hAQ⟩
  rw [hAQ, normalizedPluckerCoords_left_mul A P.representative hA P.positive]

/-- The normalized Plücker vector descends to the row-orbit quotient. -/
def positiveGrassmannianPluckerReadout :
    PositiveGrassmannian → InfoGeometry.Algebra.FiniteSpin.Vec6R :=
  Quotient.lift (fun P => normalizedPluckerCoords P.representative) (by
    intro P Q h
    exact positiveRowOrbitRel_normalizedPlucker h)


/-! ## Two exterior towers and the graded tensor sign -/

/-- The degree-`d` piece of the finite exterior tower at stage `n`. -/
abbrev ExteriorTowerDegree (n d : ℕ) :=
  ⋀[ℝ]^d (InfoGeometry.CliffordTower.SplitSpace n)

/-- The graded tensor product of two copies of the existing exterior tower.
Mathlib identifies it with the exterior algebra on the direct sum. -/
abbrev PairedExteriorTowerStage (n : ℕ) :=
  (fun d : ℕ => ExteriorTowerDegree n d) ᵍ⊗[ℝ]
    (fun d : ℕ => ExteriorTowerDegree n d)

noncomputable def pairedExteriorTowerEquiv (n : ℕ) :
    ExteriorAlgebra ℝ
        (InfoGeometry.CliffordTower.SplitSpace n ×
          InfoGeometry.CliffordTower.SplitSpace n) ≃ₐ[ℝ]
      PairedExteriorTowerStage n :=
  ExteriorAlgebra.prodEquivTensor ℝ _ _

/-- The two exterior towers supercommute with the Koszul sign
`(-1)^(degreeRight * degreeLeft)`, as fixed by Mathlib's native graded tensor
product construction. -/
theorem pairedExteriorTower_cross_sign {n i j : ℕ}
    (a : ExteriorTowerDegree n i) (b : ExteriorTowerDegree n j) :
    (ExteriorAlgebra.map
        (LinearMap.inl ℝ (InfoGeometry.CliffordTower.SplitSpace n)
          (InfoGeometry.CliffordTower.SplitSpace n))) a.val *
      (ExteriorAlgebra.map
        (LinearMap.inr ℝ (InfoGeometry.CliffordTower.SplitSpace n)
          (InfoGeometry.CliffordTower.SplitSpace n))) b.val =
    (-1 : ℤ) ^ (j * i) •
      ((ExteriorAlgebra.map
        (LinearMap.inr ℝ (InfoGeometry.CliffordTower.SplitSpace n)
          (InfoGeometry.CliffordTower.SplitSpace n))) b.val *
       (ExteriorAlgebra.map
        (LinearMap.inl ℝ (InfoGeometry.CliffordTower.SplitSpace n)
          (InfoGeometry.CliffordTower.SplitSpace n))) a.val) := by
  exact ExteriorAlgebra.map_inl_inr_anticomm ℝ i j a b

/-- In bidegree `(1,1)`, exchanging the two odd factors contributes exactly
`-1`; this is the concrete generator Koszul sign in the paired tower. -/
theorem pairedExteriorTower_odd_cross_sign {n : ℕ}
    (a : ExteriorTowerDegree n 1) (b : ExteriorTowerDegree n 1) :
    (ExteriorAlgebra.map
        (LinearMap.inl ℝ (InfoGeometry.CliffordTower.SplitSpace n)
          (InfoGeometry.CliffordTower.SplitSpace n))) a.val *
      (ExteriorAlgebra.map
        (LinearMap.inr ℝ (InfoGeometry.CliffordTower.SplitSpace n)
          (InfoGeometry.CliffordTower.SplitSpace n))) b.val =
      (-1 : ℝ) • ((ExteriorAlgebra.map
        (LinearMap.inr ℝ (InfoGeometry.CliffordTower.SplitSpace n)
          (InfoGeometry.CliffordTower.SplitSpace n))) b.val *
       (ExteriorAlgebra.map
        (LinearMap.inl ℝ (InfoGeometry.CliffordTower.SplitSpace n)
          (InfoGeometry.CliffordTower.SplitSpace n))) a.val) := by
  simpa [pow_one] using pairedExteriorTower_cross_sign a b

/-- Add one mode to each vector factor of the paired exterior tower. -/
def pairedSplitSpaceSuccessor (n : ℕ) :
    (InfoGeometry.CliffordTower.SplitSpace n ×
      InfoGeometry.CliffordTower.SplitSpace n) →ₗ[ℝ]
    (InfoGeometry.CliffordTower.SplitSpace (n + 1) ×
      InfoGeometry.CliffordTower.SplitSpace (n + 1)) where
  toFun p :=
    (LinearMap.inr ℝ (ℝ × ℝ) (InfoGeometry.CliffordTower.SplitSpace n) p.1,
      LinearMap.inr ℝ (ℝ × ℝ) (InfoGeometry.CliffordTower.SplitSpace n) p.2)
  map_add' p q := by ext <;> simp
  map_smul' c p := by ext <;> simp

/-- Bonding homomorphism for the paired exterior towers. -/
noncomputable def pairedExteriorTowerBond (n : ℕ) :
    ExteriorAlgebra ℝ
        (InfoGeometry.CliffordTower.SplitSpace n ×
          InfoGeometry.CliffordTower.SplitSpace n) →ₐ[ℝ]
      ExteriorAlgebra ℝ
        (InfoGeometry.CliffordTower.SplitSpace (n + 1) ×
          InfoGeometry.CliffordTower.SplitSpace (n + 1)) :=
  ExteriorAlgebra.lift ℝ ⟨
    (ExteriorAlgebra.ι ℝ).comp (pairedSplitSpaceSuccessor n),
    by intro x; simp⟩

@[simp] theorem pairedExteriorTowerBond_generator (n : ℕ)
    (x y : InfoGeometry.CliffordTower.SplitSpace n) :
    pairedExteriorTowerBond n (ExteriorAlgebra.ι ℝ (x, y)) =
      ExteriorAlgebra.ι ℝ
        (LinearMap.inr ℝ (ℝ × ℝ) (InfoGeometry.CliffordTower.SplitSpace n) x,
          LinearMap.inr ℝ (ℝ × ℝ) (InfoGeometry.CliffordTower.SplitSpace n) y) := by
  simp [pairedExteriorTowerBond, pairedSplitSpaceSuccessor,
    ExteriorAlgebra.lift_ι_apply]

/-! ## A genuine tower of finite exterior algebras -/

/-- The exterior algebra at a finite number of hyperbolic modes. -/
abbrev ExteriorStage (n : ℕ) :=
  ExteriorAlgebra ℝ (InfoGeometry.CliffordTower.SplitSpace n)

/-- Add one hyperbolic mode by the canonical zero-coordinate inclusion. -/
def splitSpaceSuccessor (n : ℕ) : SplitSpace n →ₗ[ℝ] SplitSpace (n + 1) where
  toFun := LinearMap.inr ℝ (ℝ × ℝ) (SplitSpace n)
  map_add' := map_add (LinearMap.inr ℝ (ℝ × ℝ) (SplitSpace n))
  map_smul' := map_smul (LinearMap.inr ℝ (ℝ × ℝ) (SplitSpace n))

theorem splitSpaceSuccessor_injective (n : ℕ) :
    Function.Injective (splitSpaceSuccessor n) := by
  intro x y h
  simpa [splitSpaceSuccessor] using h

/-- The exterior-algebra tower map induced by the mode inclusion. -/
noncomputable def exteriorTowerSuccessor (n : ℕ) :
    ExteriorStage n →ₐ[ℝ] ExteriorStage (n + 1) :=
  ExteriorAlgebra.lift ℝ ⟨
    (ExteriorAlgebra.ι ℝ).comp (splitSpaceSuccessor n), by
      intro x
      simp⟩

@[simp] theorem exteriorTowerSuccessor_ι (n : ℕ) (x : SplitSpace n) :
    exteriorTowerSuccessor n (ExteriorAlgebra.ι ℝ x) =
      ExteriorAlgebra.ι ℝ (splitSpaceSuccessor n x) := by
  exact ExteriorAlgebra.lift_ι_apply ℝ _ _ x

/-- The exterior tower bonding map is the functorial map induced by the
underlying linear inclusion. -/
theorem exteriorTowerSuccessor_eq_map (n : ℕ) :
    exteriorTowerSuccessor n = ExteriorAlgebra.map (splitSpaceSuccessor n) := by
  apply ExteriorAlgebra.hom_ext
  ext x
  change exteriorTowerSuccessor n (ExteriorAlgebra.ι ℝ x) =
    ExteriorAlgebra.map (splitSpaceSuccessor n) (ExteriorAlgebra.ι ℝ x)
  rw [exteriorTowerSuccessor_ι, ExteriorAlgebra.map_apply_ι]

/-- Every exterior-algebra stage embeds into the next one. -/
theorem exteriorTowerSuccessor_injective (n : ℕ) :
    Function.Injective (exteriorTowerSuccessor n) := by
  rw [exteriorTowerSuccessor_eq_map]
  apply ExteriorAlgebra.map_injective
  refine ⟨LinearMap.snd ℝ (ℝ × ℝ) (SplitSpace n), ?_⟩
  ext x
  rfl

/-- The induced tower map preserves the exterior anticommutation relation on
all degree-one generators. -/
theorem exteriorTowerSuccessor_anticomm (n : ℕ) (x y : SplitSpace n) :
    exteriorTowerSuccessor n
        (ExteriorAlgebra.ι ℝ x * ExteriorAlgebra.ι ℝ y +
          ExteriorAlgebra.ι ℝ y * ExteriorAlgebra.ι ℝ x) = 0 := by
  rw [map_add, map_mul, map_mul, exteriorTowerSuccessor_ι, exteriorTowerSuccessor_ι]
  exact ExteriorAlgebra.ι_add_mul_swap
    (splitSpaceSuccessor n x) (splitSpaceSuccessor n y)

/-- The algebra maps in the exterior tower preserve the abstract graded
commutator/anticommutator operation. -/
theorem exteriorTowerSuccessor_superBracket (n : ℕ) (px py : Bool)
    (x y : ExteriorStage n) :
    exteriorTowerSuccessor n
        (InfoGeometry.Algebra.SupergradedBracket.superBracket px py x y) =
      InfoGeometry.Algebra.SupergradedBracket.superBracket px py
        (exteriorTowerSuccessor n x) (exteriorTowerSuccessor n y) := by
  exact InfoGeometry.Algebra.SupergradedBracket.map_superBracket
    (exteriorTowerSuccessor n).toRingHom px py x y

/-- In particular, odd degree-one generators retain their exterior
anticommutation relation after one tower inclusion. -/
theorem exteriorTowerSuccessor_oddGenerator_bracket (n : ℕ)
    (x y : SplitSpace n) :
    InfoGeometry.Algebra.SupergradedBracket.superBracket true true
        (ExteriorAlgebra.ι ℝ (splitSpaceSuccessor n x))
        (ExteriorAlgebra.ι ℝ (splitSpaceSuccessor n y)) = 0 := by
  rw [InfoGeometry.Algebra.SupergradedBracket.superBracket_odd_odd]
  exact ExteriorAlgebra.ι_add_mul_swap _ _

/-! ## Positive Grassmannian data in the exterior square -/

/-- The literal exterior two-vector represented by the rows of a `2 × 4`
chart matrix. -/
def exteriorPluckerVector (M : Matrix2x4) : ⋀[ℝ]^2 Vec4 :=
  exteriorPower.ιMulti ℝ 2 ![rowVec4 M 0, rowVec4 M 1]

/-- Its six exterior coordinates are exactly the six matrix minors. -/
theorem exteriorPluckerVector_readout (M : Matrix2x4) :
    pluckerExteriorMap (exteriorPluckerVector M) = matrixPluckerCoords M := by
  simpa [exteriorPluckerVector, matrixPluckerCoords] using
    pluckerExteriorMap_ιMulti (rowVec4 M 0) (rowVec4 M 1)

/-- Strict positivity of all ordered maximal minors gives strict positivity of
every coordinate of the exterior Plücker readout. -/
theorem positive_chart_exteriorPluckerVector
    (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    ∀ i : Fin 6, 0 < pluckerExteriorMap (exteriorPluckerVector M) i := by
  intro i
  rw [exteriorPluckerVector_readout]
  exact positiveGrassmannianInterior_mem_matrixPluckerPositive M hM i

/-- The same exterior vector is decomposable and its coordinates obey the
Klein relation. -/
theorem exteriorPluckerVector_decomposable_klein
    (M : Matrix2x4) :
    (∃ u v : Vec4,
      exteriorPluckerVector M = exteriorPower.ιMulti ℝ 2 ![u, v]) ∧
    (pluckerExteriorMap (exteriorPluckerVector M) 0) *
        (pluckerExteriorMap (exteriorPluckerVector M) 5) -
      (pluckerExteriorMap (exteriorPluckerVector M) 1) *
        (pluckerExteriorMap (exteriorPluckerVector M) 4) +
      (pluckerExteriorMap (exteriorPluckerVector M) 2) *
        (pluckerExteriorMap (exteriorPluckerVector M) 3) = 0 := by
  constructor
  · exact ⟨rowVec4 M 0, rowVec4 M 1, rfl⟩
  · rw [exteriorPluckerVector_readout]
    exact matrixPluckerCoords_klein_relation M

/-! ## One Grassmannian blade through the exterior and spinor representations

The Plücker readout is carried by `⋀² Vec4`, while the five-mode spinor uses
`ExteriorAlgebra ℝ (Fin 5 → ℝ)`. The coordinate inclusion below induces an
algebra map between those exterior-algebra carriers; its value on the chart
blade is exactly the blade used by the concrete `Cl(5,5)` spinor representation. -/

/-- Include the four chart coordinates as the first four modes of the
five-mode exterior spinor, leaving the fifth mode zero. -/
def vec4ToMode55 : Vec4 →ₗ[ℝ] (Fin 5 → ℝ) where
  toFun u j := if h : j.val < 4 then
    u (InfoGeometry.Projective.ExteriorKleinCoordinateIncidence.finFourIndex
      ⟨j.val, h⟩) else 0
  map_add' u v := by
    funext j
    by_cases h : j.val < 4 <;> simp [h]
  map_smul' r u := by
    funext j
    by_cases h : j.val < 4 <;> simp [h]

/-- The algebra homomorphism induced by the finite-mode coordinate inclusion. -/
noncomputable def grassmannianExteriorRepresentation :
    ExteriorAlgebra ℝ Vec4 →ₐ[ℝ]
      InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure.Exterior55 :=
  ExteriorAlgebra.lift ℝ ⟨
    (ExteriorAlgebra.ι ℝ).comp vec4ToMode55,
    by intro x; simp⟩

/-- The algebraic exterior blade formed by the two rows of a `Gr(2,4)` chart. -/
def grassmannianExteriorBlade (M : Matrix2x4) : ExteriorAlgebra ℝ Vec4 :=
  ExteriorAlgebra.ι ℝ (rowVec4 M 0) * ExteriorAlgebra.ι ℝ (rowVec4 M 1)

theorem vec4ToMode55_rowVec4 (M : Matrix2x4) (r : Fin 2) :
    vec4ToMode55 (rowVec4 M r) =
      grassmannianRow55 M r := by
  funext j
  fin_cases j <;>
    simp [vec4ToMode55, rowVec4, grassmannianRow55,
      InfoGeometry.Projective.ExteriorKleinCoordinateIncidence.finFourIndex]

/-- The exterior-algebra map sends the `Gr(2,4)` chart blade to the
corresponding two-vector in the five-mode spinor carrier. -/
theorem grassmannianExteriorRepresentation_blade (M : Matrix2x4) :
    grassmannianExteriorRepresentation (grassmannianExteriorBlade M) =
      InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure.positiveGrassmannianBlade M := by
  simp [grassmannianExteriorRepresentation, grassmannianExteriorBlade,
    InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure.positiveGrassmannianBlade,
    vec4ToMode55_rowVec4]

/-- The composite representation of the four-dimensional exterior algebra in
the concrete `Cl(5,5)` spinor matrices preserves the chart's product blade. -/
theorem positiveGrassmannianBlade_in_spinorRepresentation (M : Matrix2x4) :
    InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure.twistorSpinorRepresentation
        (grassmannianExteriorRepresentation (grassmannianExteriorBlade M)) =
      InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure.twistorSpinorRepresentation
        (InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure.positiveGrassmannianBlade M) := by
  rw [grassmannianExteriorRepresentation_blade]

/-- For a strictly positive `Gr(2,4)` chart, record both its positive Plücker
coordinates and its realization by the concrete spinor representation. -/
theorem positiveGrassmannian_chart_representation
    (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    (∀ i : Fin 6, 0 < pluckerExteriorMap (exteriorPluckerVector M) i) ∧
    grassmannianExteriorRepresentation (grassmannianExteriorBlade M) =
      InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure.positiveGrassmannianBlade M := by
  exact ⟨positive_chart_exteriorPluckerVector M hM,
    grassmannianExteriorRepresentation_blade M⟩

/-! ## The representation seam into the Cantor matrix limit

The exterior blade, its null-Clifford image, and the Cantor operator are
different carriers.  This composite records the actual algebra maps between
them, so a positive chart blade has one well-defined image in the existing
Cantor limit representation.
-/

open InfoGeometry.Clifford.Cl55MatStageCarrierEquiv

/-- Represent the five-mode exterior algebra in the established stage-five
matrix/Cantor limit, through its null-Clifford map. -/
noncomputable def exterior55CantorRepresentation :
    Exterior55 →+* InfoGeometry.Canonical.JordanWignerCantorRepresentation.RealCantorOpInf :=
  cl55CantorRepresentation.comp (twistorMapAlgHom.toRingHom)

/-- The four-mode Grassmannian exterior algebra represented in the Cantor
limit through the chart inclusion and the five-mode null-Clifford action. -/
noncomputable def grassmannianCantorRepresentation :
    ExteriorAlgebra ℝ Vec4 →+*
      InfoGeometry.Canonical.JordanWignerCantorRepresentation.RealCantorOpInf :=
  exterior55CantorRepresentation.comp
    (grassmannianExteriorRepresentation.toRingHom)

/-- The positive Grassmannian chart blade follows the same route as its
five-mode exterior image, with no change of representative between the two
algebra maps. -/
theorem grassmannianBlade_cantor_representation (M : Matrix2x4) :
    grassmannianCantorRepresentation (grassmannianExteriorBlade M) =
      exterior55CantorRepresentation (positiveGrassmannianBlade M) := by
  simp [grassmannianCantorRepresentation, exterior55CantorRepresentation,
    grassmannianExteriorRepresentation_blade]

/-- Single endpoint theorem for a strictly positive chart: its six Plücker
coordinates are positive and its decomposable blade is represented in the
existing Cantor limit by the five-mode null-Clifford route. -/
theorem positiveGrassmannian_chart_cantor
    (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    (∀ i : Fin 6, 0 < pluckerExteriorMap (exteriorPluckerVector M) i) ∧
      grassmannianCantorRepresentation (grassmannianExteriorBlade M) =
        exterior55CantorRepresentation (positiveGrassmannianBlade M) := by
  exact ⟨positive_chart_exteriorPluckerVector M hM,
    grassmannianBlade_cantor_representation M⟩

/-- The normalized exterior blade on the quotient, reconstructed through the
existing Plücker-coordinate linear equivalence. -/
def positiveGrassmannianExteriorBlade (P : PositiveGrassmannian) : Exterior55 :=
  grassmannianExteriorRepresentation
    ((pluckerExteriorLinearEquiv.symm
      (positiveGrassmannianPluckerReadout P)).val)

/-- The quotient point's normalized exterior blade represented in the
stage-five Cantor matrix limit. -/
def positiveGrassmannianCantorReadout (P : PositiveGrassmannian) :
    InfoGeometry.Canonical.JordanWignerCantorRepresentation.RealCantorOpInf :=
  exterior55CantorRepresentation (positiveGrassmannianExteriorBlade P)

/-- The exterior-to-Cantor representation preserves the parity-controlled
graded commutator, including the odd/odd anticommutator. -/
theorem exterior55CantorRepresentation_superBracket
    (p q : Bool) (x y : Exterior55) :
    exterior55CantorRepresentation
        (InfoGeometry.Algebra.SupergradedBracket.superBracket p q x y) =
      InfoGeometry.Algebra.SupergradedBracket.superBracket p q
        (exterior55CantorRepresentation x) (exterior55CantorRepresentation y) := by
  exact InfoGeometry.Algebra.SupergradedBracket.map_superBracket
    exterior55CantorRepresentation p q x y

/-- Both levels of a nested graded triple product are preserved by the
exterior-to-Cantor representation. -/
theorem exterior55CantorRepresentation_superTriple
    (p q r : Bool) (x y z : Exterior55) :
    exterior55CantorRepresentation
        (InfoGeometry.Algebra.SupergradedBracket.superBracket p q x
          (InfoGeometry.Algebra.SupergradedBracket.superBracket q r y z)) =
      InfoGeometry.Algebra.SupergradedBracket.superBracket p q
        (exterior55CantorRepresentation x)
        (InfoGeometry.Algebra.SupergradedBracket.superBracket q r
          (exterior55CantorRepresentation y) (exterior55CantorRepresentation z)) := by
  rw [exterior55CantorRepresentation_superBracket,
    exterior55CantorRepresentation_superBracket]

/-- Associators vanish in the represented Cantor limit.  This records the
associative algebra law at the representation endpoint, separately from the
graded Jacobi and STU Jordan triple identities below. -/
theorem exterior55CantorRepresentation_associator_zero
    (x y z : Exterior55) :
    (exterior55CantorRepresentation x * exterior55CantorRepresentation y) *
        exterior55CantorRepresentation z -
      exterior55CantorRepresentation x *
        (exterior55CantorRepresentation y * exterior55CantorRepresentation z) = 0 := by
  simp [mul_assoc]

/-- The ordinary triple product of exterior states is represented as the
corresponding triple product in the Cantor operator limit. -/
theorem exterior55CantorRepresentation_mul_triple
    (x y z : Exterior55) :
    exterior55CantorRepresentation ((x * y) * z) =
      (exterior55CantorRepresentation x * exterior55CantorRepresentation y) *
        exterior55CantorRepresentation z := by
  simp only [map_mul]

/-! ## Concrete CAR atoms and their graded tower representation

The exterior Plücker readout and the CAR tower have different carriers.  The
composition bridge records the concrete generator identities in the finite
Cl(1,1) atom, then uses the existing stage and direct-limit maps to transport
graded commutators and anticommutators without identifying those carriers.
-/

open InfoGeometry.Clifford.Cl11TensorTower

theorem realWitt_creation_nilpotent :
    realEncodedWittCreationBase * realEncodedWittCreationBase = 0 :=
  realEncodedWittCreationBase_sq

theorem realWitt_annihilation_nilpotent :
    realEncodedWittAnnihilationBase * realEncodedWittAnnihilationBase = 0 :=
  realEncodedWittAnnihilationBase_sq

theorem realWitt_CAR_anticommutator :
    realEncodedWittCreationBase * realEncodedWittAnnihilationBase +
      realEncodedWittAnnihilationBase * realEncodedWittCreationBase = 1 :=
  realEncodedWitt_anticomm

theorem tower_oddBracket_is_anticommutator {n : ℕ}
    (A B : Cl11TensorTowerSupergraded.Stage n) :
    stageSuperBracket true true A B = A * B + B * A :=
  stageSuperBracket_odd_odd A B

theorem tower_evenBracket_is_commutator {n : ℕ} (py : Bool)
    (A B : Cl11TensorTowerSupergraded.Stage n) :
    stageSuperBracket false py A B = A * B - B * A :=
  stageSuperBracket_even_left py A B

/-- The finite matrix representation into the algebraic tensor limit preserves
the parity-controlled bracket, including its odd--odd anticommutator case. -/
theorem tower_limit_preserves_superBracket
    (px py : Bool) {n : ℕ} (A B : Cl11TensorTowerSupergraded.Stage n) :
    Cl11TensorTowerSupergraded.ofStage n (stageSuperBracket px py A B) =
      InfoGeometry.Algebra.SupergradedBracket.superBracket px py
        (Cl11TensorTowerSupergraded.ofStage n A)
        (Cl11TensorTowerSupergraded.ofStage n B) :=
  Cl11TensorTowerSupergraded.ofStage_superBracket px py A B

/-- Associativity is retained by the tower's direct-limit representation; it
is distinct from the non-associative STU Jordan triple identity below. -/
theorem tower_limit_associator {n : ℕ}
    (A B C : Cl11TensorTowerSupergraded.Stage n) :
    (Cl11TensorTowerSupergraded.ofStage n A *
        Cl11TensorTowerSupergraded.ofStage n B) *
        Cl11TensorTowerSupergraded.ofStage n C =
      Cl11TensorTowerSupergraded.ofStage n A *
        (Cl11TensorTowerSupergraded.ofStage n B *
          Cl11TensorTowerSupergraded.ofStage n C) :=
  mul_assoc _ _ _

/-- The full mixed CAR relations of the five exterior modes survive the
existing matrix-stage to Cantor-limit representation.  The diagonal case is
the creator-annihilator anticommutator; off-diagonal modes anticommute. -/
theorem cantorRepresentation_mixed_car (i j : Fin 5) :
    cl55CantorRepresentation (transportedCreation55 i) *
        cl55CantorRepresentation (transportedAnnihilation55 j) +
      cl55CantorRepresentation (transportedAnnihilation55 j) *
        cl55CantorRepresentation (transportedCreation55 i) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simpa using cl55CantorRepresentation_same_site_car i
  · rw [cl55CantorRepresentation_creation,
      cl55CantorRepresentation_annihilation]
    have h := congrArg matStageToCl55
      (InfoGeometry.Canonical.Cl55WittCAR.creation_annihilation_cross_anticommute hij)
    have h' := congrArg cl55CantorRepresentation h
    simpa [hij, transportedCreation55, transportedAnnihilation55,
      cl55CantorRepresentation] using h'

/-- Creation modes from distinct sites anticommute in the Cantor limit. -/
theorem cantorRepresentation_creation_cross_car
    {i j : Fin 5} (hij : i ≠ j) :
    cl55CantorRepresentation (transportedCreation55 i) *
        cl55CantorRepresentation (transportedCreation55 j) +
      cl55CantorRepresentation (transportedCreation55 j) *
        cl55CantorRepresentation (transportedCreation55 i) = 0 := by
  rw [cl55CantorRepresentation_creation, cl55CantorRepresentation_creation]
  have h := congrArg matStageToCl55
    (InfoGeometry.Canonical.Cl55WittCAR.creation_cross_anticommute hij)
  have h' := congrArg cl55CantorRepresentation h
  simpa [transportedCreation55, cl55CantorRepresentation] using h'

/-- Annihilation modes from distinct sites anticommute in the Cantor limit. -/
theorem cantorRepresentation_annihilation_cross_car
    {i j : Fin 5} (hij : i ≠ j) :
    cl55CantorRepresentation (transportedAnnihilation55 i) *
        cl55CantorRepresentation (transportedAnnihilation55 j) +
      cl55CantorRepresentation (transportedAnnihilation55 j) *
        cl55CantorRepresentation (transportedAnnihilation55 i) = 0 := by
  rw [cl55CantorRepresentation_annihilation,
    cl55CantorRepresentation_annihilation]
  have h := congrArg matStageToCl55
    (InfoGeometry.Canonical.Cl55WittCAR.annihilation_cross_anticommute hij)
  have h' := congrArg cl55CantorRepresentation h
  simpa [transportedAnnihilation55, cl55CantorRepresentation] using h'

/-! ## Binary Cantor prefixes in an abstract Cuntz operator algebra -/

/-- The binary symbols select the two generators of the abstract `O₂` carrier. -/
def sectorIndex : BinarySector → Fin 2
  | .plus => 0
  | .minus => 1

/-- The operator represented by a finite binary prefix. -/
def cylinderOperator {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) : List BinarySector → Op
  | [] => 1
  | s :: word => C.S (sectorIndex s) * cylinderOperator C word

/-- Concatenating two prefixes is represented by multiplying their operators. -/
theorem cylinderOperator_append {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (u v : List BinarySector) :
    cylinderOperator C (u ++ v) = cylinderOperator C u * cylinderOperator C v := by
  induction u with
  | nil => simp [cylinderOperator]
  | cons s u ih =>
      simp only [List.cons_append, cylinderOperator]
      rw [ih, mul_assoc]
@[simp] theorem cylinderOperator_single {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (s : BinarySector) :
    cylinderOperator C [s] = C.S (sectorIndex s) := by
  simp [cylinderOperator]

/-- The letter generators in the binary Cantor representation satisfy the
defining Cuntz isometry relations, including orthogonality of the two ranges. -/
theorem cantorGenerator_relation {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (s t : BinarySector) :
    star (cylinderOperator C [s]) * cylinderOperator C [t] =
      if s = t then 1 else 0 := by
  rw [cylinderOperator_single, cylinderOperator_single]
  cases s <;> cases t <;> simp [sectorIndex, C.isometry]

@[simp] theorem cantorGenerator_isometry {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (s : BinarySector) :
    star (cylinderOperator C [s]) * cylinderOperator C [s] = 1 := by
  simpa using cantorGenerator_relation C s s

/-- A binary prefix is odd exactly when its length is odd. -/
def cantorWordParity : List BinarySector → Bool
  | [] => false
  | _ :: word => !cantorWordParity word

@[simp] theorem cantorWordParity_append (u v : List BinarySector) :
    cantorWordParity (u ++ v) = parityAdd (cantorWordParity u) (cantorWordParity v) := by
  induction u with
  | nil => simp [cantorWordParity, parityAdd]
  | cons s u ih =>
      simp only [List.cons_append, cantorWordParity, ih]
      cases hu : cantorWordParity u <;>
        cases hv : cantorWordParity v <;>
        simp [parityAdd]

/-- The graded Cantor bracket of two represented finite prefixes. -/
def gradedCantorBracket {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (p q : Bool)
    (u v : List BinarySector) : Op :=
  InfoGeometry.Algebra.SupergradedBracket.superBracket p q
    (cylinderOperator C u) (cylinderOperator C v)

/-- The iterated graded triple product of three represented Cantor prefixes. -/
def gradedCantorTripleProduct {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (p q r : Bool)
    (u v w : List BinarySector) : Op :=
  InfoGeometry.Algebra.SupergradedBracket.superBracket p (parityAdd q r)
    (cylinderOperator C u)
    (InfoGeometry.Algebra.SupergradedBracket.superBracket q r
      (cylinderOperator C v) (cylinderOperator C w))

/-- The graded Jacobi identity for the parity-controlled commutator. This is
the triple-product relation used by the Cantor representation. -/
theorem superBracket_graded_jacobi {A : Type*} [Ring A]
    (p q r : Bool) (x y z : A) :
    (if p && r then (-1 : A) else 1) *
        InfoGeometry.Algebra.SupergradedBracket.superBracket p (parityAdd q r)
          x (InfoGeometry.Algebra.SupergradedBracket.superBracket q r y z) +
      (if q && p then (-1 : A) else 1) *
        InfoGeometry.Algebra.SupergradedBracket.superBracket q (parityAdd r p)
          y (InfoGeometry.Algebra.SupergradedBracket.superBracket r p z x) +
      (if r && q then (-1 : A) else 1) *
        InfoGeometry.Algebra.SupergradedBracket.superBracket r (parityAdd p q)
          z (InfoGeometry.Algebra.SupergradedBracket.superBracket p q x y) = 0 := by
  cases p <;> cases q <;> cases r <;>
    simp [parityAdd, InfoGeometry.Algebra.SupergradedBracket.superBracket,
      InfoGeometry.Algebra.SupergradedBracket.commutator,
      InfoGeometry.Algebra.SupergradedBracket.anticommutator] <;>
    noncomm_ring

/-- The exterior-spinor representation in the actual Cantor operator limit
satisfies the same parity-signed triple-product identity. -/
theorem exterior55CantorRepresentation_graded_jacobi
    (p q r : Bool) (x y z : Exterior55) :
    (if p && r then
        (-1 : InfoGeometry.Canonical.JordanWignerCantorRepresentation.RealCantorOpInf)
      else 1) *
        InfoGeometry.Algebra.SupergradedBracket.superBracket p (parityAdd q r)
          (exterior55CantorRepresentation x)
          (InfoGeometry.Algebra.SupergradedBracket.superBracket q r
            (exterior55CantorRepresentation y) (exterior55CantorRepresentation z)) +
      (if q && p then
        (-1 : InfoGeometry.Canonical.JordanWignerCantorRepresentation.RealCantorOpInf)
      else 1) *
        InfoGeometry.Algebra.SupergradedBracket.superBracket q (parityAdd r p)
          (exterior55CantorRepresentation y)
          (InfoGeometry.Algebra.SupergradedBracket.superBracket r p
            (exterior55CantorRepresentation z) (exterior55CantorRepresentation x)) +
      (if r && q then
        (-1 : InfoGeometry.Canonical.JordanWignerCantorRepresentation.RealCantorOpInf)
      else 1) *
        InfoGeometry.Algebra.SupergradedBracket.superBracket r (parityAdd p q)
          (exterior55CantorRepresentation z)
          (InfoGeometry.Algebra.SupergradedBracket.superBracket p q
            (exterior55CantorRepresentation x) (exterior55CantorRepresentation y)) = 0 := by
  exact superBracket_graded_jacobi p q r
    (exterior55CantorRepresentation x)
    (exterior55CantorRepresentation y)
    (exterior55CantorRepresentation z)

/-- The represented Cantor prefix operators obey the graded triple-product
Jacobi law, with the Koszul signs determined by their declared parities. -/
theorem gradedCantorTripleProduct_jacobi {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (p q r : Bool)
    (u v w : List BinarySector) :
    (if p && r then (-1 : Op) else 1) *
        gradedCantorTripleProduct C p q r u v w +
      (if q && p then (-1 : Op) else 1) *
        InfoGeometry.Algebra.SupergradedBracket.superBracket q (parityAdd r p)
          (cylinderOperator C v)
          (InfoGeometry.Algebra.SupergradedBracket.superBracket r p
            (cylinderOperator C w) (cylinderOperator C u)) +
      (if r && q then (-1 : Op) else 1) *
        InfoGeometry.Algebra.SupergradedBracket.superBracket r (parityAdd p q)
          (cylinderOperator C w)
          (InfoGeometry.Algebra.SupergradedBracket.superBracket p q
            (cylinderOperator C u) (cylinderOperator C v)) = 0 := by
  exact superBracket_graded_jacobi p q r
    (cylinderOperator C u) (cylinderOperator C v) (cylinderOperator C w)

/-- Binary-prefix parity determines the three Koszul signs in the represented
Cantor graded Jacobi/triple-product identity. -/
theorem gradedCantorTripleProduct_word_jacobi {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (u v w : List BinarySector) :
    (if cantorWordParity u && cantorWordParity w then (-1 : Op) else 1) *
        gradedCantorTripleProduct C (cantorWordParity u) (cantorWordParity v)
          (cantorWordParity w) u v w +
      (if cantorWordParity v && cantorWordParity u then (-1 : Op) else 1) *
        gradedCantorTripleProduct C (cantorWordParity v) (cantorWordParity w)
          (cantorWordParity u) v w u +
      (if cantorWordParity w && cantorWordParity v then (-1 : Op) else 1) *
        gradedCantorTripleProduct C (cantorWordParity w) (cantorWordParity u)
          (cantorWordParity v) w u v = 0 := by
  simpa [gradedCantorTripleProduct] using
    gradedCantorTripleProduct_jacobi C (cantorWordParity u)
      (cantorWordParity v) (cantorWordParity w) u v w

/-- Explicit even-even and odd-odd generator relations: the former is the
commutator, while the latter is the anticommutator. -/
theorem cantorGenerator_graded_relations {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (s t : BinarySector) :
    (InfoGeometry.Algebra.SupergradedBracket.superBracket false false
        (cylinderOperator C [s]) (cylinderOperator C [t]) =
      cylinderOperator C [s] * cylinderOperator C [t] -
        cylinderOperator C [t] * cylinderOperator C [s]) ∧
    (InfoGeometry.Algebra.SupergradedBracket.superBracket true true
        (cylinderOperator C [s]) (cylinderOperator C [t]) =
      cylinderOperator C [s] * cylinderOperator C [t] +
        cylinderOperator C [t] * cylinderOperator C [s]) := by
  constructor <;> rfl

/-- The CAR creation/annihilation pair already constructed from the Cantor
`O₂` generators has odd--odd bracket one. -/
theorem cantorCAR_oddBracket_eq_one {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (n : ℕ) :
    InfoGeometry.Algebra.SupergradedBracket.superBracket true true
      (star (InfoGeometry.Algebra.kawamuraCARSequence C n))
      (InfoGeometry.Algebra.kawamuraCARSequence C n) = 1 := by
  rw [InfoGeometry.Algebra.SupergradedBracket.superBracket_odd_odd]
  have h := InfoGeometry.Algebra.kawamuraCAR_anticomm C n
  change InfoGeometry.Algebra.kawamuraCARSequence C n *
      star (InfoGeometry.Algebra.kawamuraCARSequence C n) +
    star (InfoGeometry.Algebra.kawamuraCARSequence C n) *
      InfoGeometry.Algebra.kawamuraCARSequence C n = 1 at h
  rw [add_comm] at h
  exact h

/-- Each recursive Cantor CAR creation operator is odd and squares to zero in
its odd--odd superbracket. -/
theorem cantorCAR_creation_oddBracket_eq_zero {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (n : ℕ) :
    InfoGeometry.Algebra.SupergradedBracket.superBracket true true
      (InfoGeometry.Algebra.kawamuraCARSequence C n)
      (InfoGeometry.Algebra.kawamuraCARSequence C n) = 0 := by
  rw [InfoGeometry.Algebra.SupergradedBracket.superBracket_odd_odd]
  have h := InfoGeometry.Algebra.kawamuraCAR_nilpotent C n
  change InfoGeometry.Algebra.kawamuraCARSequence C n *
      InfoGeometry.Algebra.kawamuraCARSequence C n +
    InfoGeometry.Algebra.kawamuraCARSequence C n *
      InfoGeometry.Algebra.kawamuraCARSequence C n = 0 at h
  exact h

/-- The represented triple prefix product is the product of its three pieces. -/
theorem cylinderOperator_triple_product {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (u v w : List BinarySector) :
    cylinderOperator C ((u ++ v) ++ w) =
      (cylinderOperator C u * cylinderOperator C v) * cylinderOperator C w := by
  rw [cylinderOperator_append, cylinderOperator_append]

/-- The two parenthesizations of a represented triple Cantor product agree by
the ambient associative-algebra law. -/
theorem cylinderOperator_associator {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (u v w : List BinarySector) :
    (cylinderOperator C u * cylinderOperator C v) * cylinderOperator C w =
      cylinderOperator C u * (cylinderOperator C v * cylinderOperator C w) :=
  mul_assoc _ _ _

/-- Prefix concatenation has the corresponding parenthesization-independent
triple product. -/
theorem cylinderOperator_append_associator {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (u v w : List BinarySector) :
    cylinderOperator C ((u ++ v) ++ w) =
      cylinderOperator C (u ++ (v ++ w)) := by
  rw [cylinderOperator_triple_product, cylinderOperator_append,
    cylinderOperator_append]
  exact cylinderOperator_associator C u v w

/-- Associativity after taking a graded Cantor bracket as the first factor.
This states the operator associator law on the represented triple products,
not an associativity claim for the superbracket itself. -/
theorem gradedCantorProduct_associator {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (p q : Bool)
    (u v w x : List BinarySector) :
    (gradedCantorBracket C p q u v * cylinderOperator C w) *
        cylinderOperator C x =
      gradedCantorBracket C p q u v *
        (cylinderOperator C w * cylinderOperator C x) :=
  mul_assoc _ _ _

/-! ## Triple-product identity in the concrete Jordan owner -/

/-- The concrete coordinatewise STU triple product obeys the Jordan triple
identity in its native owner carrier. -/
theorem stuTripleProduct_jordan_identity
    (x y u v w : InfoGeometry.Exceptional.STUDatum.STUCarrier) :
    InfoGeometry.Exceptional.STUDatum.stuTripleProduct x y
        (InfoGeometry.Exceptional.STUDatum.stuTripleProduct u v w) -
      InfoGeometry.Exceptional.STUDatum.stuTripleProduct u v
        (InfoGeometry.Exceptional.STUDatum.stuTripleProduct x y w) =
    InfoGeometry.Exceptional.STUDatum.stuTripleProduct
        (InfoGeometry.Exceptional.STUDatum.stuTripleProduct x y u) v w -
      InfoGeometry.Exceptional.STUDatum.stuTripleProduct u
        (InfoGeometry.Exceptional.STUDatum.stuTripleProduct y x v) w :=
  InfoGeometry.Exceptional.STUDatum.stuJordan_identity x y u v w

end InfoGeometry.Clifford.ParaKahler55PositiveGrassmannianCantorBridge
