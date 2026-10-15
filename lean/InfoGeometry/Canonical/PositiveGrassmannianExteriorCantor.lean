import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
import Mathlib.RingTheory.GradedAlgebra.Basic
import InfoGeometry.Canonical.GradedMellinReadout
import InfoGeometry.Projective.MatrixPluckerPositiveBridge
import InfoGeometry.Projective.ExteriorPowerPluckerBridge
import InfoGeometry.Clifford.ParaKahler55PositiveGrassmannianCantorBridge

/-!
# Positive Grassmannian, graded exterior towers, and Cantor triples

This is a composition layer.  The positive-chart/minor and Plücker/exterior
readouts are imported from their owners; the paired exterior algebra uses
Mathlib's native graded tensor product; the Cantor prefix representation and
its Cuntz relations are reused from the existing bridge.

The graded exterior algebra is genuinely `ℕ`-graded.  Its Koszul signs are
recorded on homogeneous degree pieces, with the `(-1)^(ij)` crossing sign.
The Cantor triple below is a homogeneous signed product; its associator is the
Koszul coherence law.  It is distinct from the nested superbracket Jacobi law
and from the ordinary Cuntz prefix-product associator.
-/

noncomputable section

open scoped TensorProduct DirectSum

namespace InfoGeometry.Canonical.PositiveGrassmannianExteriorCantor

open InfoGeometry.Canonical.FierzKleinFoundation
open InfoGeometry.Canonical.GradedMellinReadout
open InfoGeometry.Projective.MatrixPluckerPositiveBridge
open InfoGeometry.Projective.ExteriorPowerPluckerBridge
open InfoGeometry.Clifford.ParaKahler55PositiveGrassmannianCantorBridge
open InfoGeometry.Topology
open InfoGeometry.OperatorAlgebra.ErlangenNet

/-- The two finite exterior-algebra towers used for the `Gr(2,4)` chart. -/
abbrev TowerA := ExteriorAlgebra ℝ Vec4
abbrev TowerB := ExteriorAlgebra ℝ Vec4

/-- The joint carrier, whose native `ℕ`-grading is the total exterior degree. -/
abbrev PairedExterior := ExteriorAlgebra ℝ (Vec4 × Vec4)

/-- Degree-`d` submodule of the paired exterior algebra. -/
abbrev PairedExteriorDegree (d : ℕ) := ⋀[ℝ]^d (Vec4 × Vec4)

/-- Native Mathlib equivalence between the exterior algebra on the product
space and the graded tensor product of the two exterior towers. -/
noncomputable def twoTowerGradedTensorEquiv :
    PairedExterior ≃ₐ[ℝ]
      (fun d : ℕ => ⋀[ℝ]^d Vec4) ᵍ⊗[ℝ]
        (fun d : ℕ => ⋀[ℝ]^d Vec4) :=
  ExteriorAlgebra.prodEquivTensor ℝ Vec4 Vec4

/-- The graded-algebra readout for the paired exterior tower.  Its multiplication
law is the standard exterior-degree addition supplied by Mathlib. -/
def pairedExteriorGradedReadout :
    GradedAlgebraReadout ℝ PairedExterior ℕ where
  piece d := PairedExteriorDegree d
  mul_compat := by
    intro i j x y hx hy
    exact SetLike.GradedMonoid.toGradedMul.mul_mem hx hy
  one_mem := SetLike.GradedOne.one_mem

/-- The two canonical algebra maps into the joint exterior algebra. -/
noncomputable def includeTowerA : TowerA →ₐ[ℝ] PairedExterior :=
  ExteriorAlgebra.map (LinearMap.inl ℝ Vec4 Vec4)

noncomputable def includeTowerB : TowerB →ₐ[ℝ] PairedExterior :=
  ExteriorAlgebra.map (LinearMap.inr ℝ Vec4 Vec4)

/-- Homogeneous exterior factors from the two towers cross with the Koszul sign
`(-1)^(right degree * left degree)`. -/
theorem twoTower_cross_sign {i j : ℕ}
    (a : ⋀[ℝ]^i Vec4) (b : ⋀[ℝ]^j Vec4) :
    includeTowerA a.val * includeTowerB b.val =
      (-1 : ℤ) ^ (j * i) • (includeTowerB b.val * includeTowerA a.val) := by
  exact ExteriorAlgebra.map_inl_inr_anticomm ℝ i j a b

/-- Boolean Koszul sign, for use with `Z₂`-homogeneous operator readouts. -/
def koszulSign (p q : Bool) : ℤ := if p && q then -1 else 1

/-- Graded commutator `[x,y]_g = xy - (-1)^(|x||y|) yx`. -/
def gradedCommutator {A : Type*} [Ring A]
    (p q : Bool) (x y : A) : A :=
  x * y - koszulSign p q • (y * x)

/-- Graded anticommutator `{x,y}_g = xy + (-1)^(|x||y|) yx`. -/
def gradedAnticommutator {A : Type*} [Ring A]
    (p q : Bool) (x y : A) : A :=
  x * y + koszulSign p q • (y * x)

@[simp] theorem gradedCommutator_even_even {A : Type*} [Ring A] (x y : A) :
    gradedCommutator false false x y = x * y - y * x := by
  simp [gradedCommutator, koszulSign]

@[simp] theorem gradedCommutator_odd_odd {A : Type*} [Ring A] (x y : A) :
    gradedCommutator true true x y = x * y + y * x := by
  simp [gradedCommutator, koszulSign]

@[simp] theorem gradedAnticommutator_even_even {A : Type*} [Ring A] (x y : A) :
    gradedAnticommutator false false x y = x * y + y * x := by
  simp [gradedAnticommutator, koszulSign]

@[simp] theorem gradedAnticommutator_odd_odd {A : Type*} [Ring A] (x y : A) :
    gradedAnticommutator true true x y = x * y - y * x := by
  simp only [gradedAnticommutator, koszulSign, Bool.and_self, if_pos]
  rw [neg_one_zsmul, sub_eq_add_neg]

/-- The commutator of left- and right-tower homogeneous factors vanishes after
their graded crossing sign is applied. -/
theorem twoTower_cross_gradedCommutator_zero {i j : ℕ}
    (a : ⋀[ℝ]^i Vec4) (b : ⋀[ℝ]^j Vec4) :
    includeTowerA a.val * includeTowerB b.val -
      (-1 : ℤ) ^ (j * i) • (includeTowerB b.val * includeTowerA a.val) = 0 := by
  rw [twoTower_cross_sign]
  simp

/-- The positive chart's six Plücker coordinates are the exterior-power
readout of the owner-defined decomposable two-vector. -/
theorem positiveChart_plucker_readout
    (M : Matrix2x4) :
    pluckerExteriorMap (exteriorPluckerVector M) = matrixPluckerCoords M :=
  exteriorPluckerVector_readout M

/-- A nonnegative positive-Grassmannian chart gives nonnegative exterior
Plücker coordinates, using the chart and minor owners. -/
theorem positiveChart_plucker_nonnegative
    (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianChart
      (k := 2) (n := 4)) :
    ∀ i : Fin 6, 0 ≤ pluckerExteriorMap (exteriorPluckerVector M) i := by
  intro i
  rw [positiveChart_plucker_readout]
  exact positiveGrassmannianChart_mem_matrixPluckerNonnegative M hM i

/-- In the strictly positive chart interior, all six exterior Plücker
coordinates are strictly positive. -/
theorem positiveChart_plucker_positive
    (M : Matrix2x4)
    (hM : M ∈ InfoGeometry.Canonical.positiveGrassmannianInterior
      (k := 2) (n := 4)) :
    ∀ i : Fin 6, 0 < pluckerExteriorMap (exteriorPluckerVector M) i := by
  exact positive_chart_exteriorPluckerVector M hM

/-- The same chart blade is represented in the existing five-mode spinor
owner; this module does not duplicate its Clifford/spinor construction. -/
theorem positiveChart_spinor_blade (M : Matrix2x4) :
    grassmannianExteriorRepresentation (grassmannianExteriorBlade M) =
      InfoGeometry.Clifford.ParaKahler55FiveGradedSUSYClosure.positiveGrassmannianBlade M :=
  grassmannianExteriorRepresentation_blade M

/-- The Grassmannian blade placed in the first factor of the paired exterior
algebra; the factor inclusion is the native Mathlib map. -/
def pairedGrassmannianBlade (M : Matrix2x4) : PairedExterior :=
  includeTowerA (grassmannianExteriorBlade M)

theorem positiveChart_pairedBlade_factorization (M : Matrix2x4) :
    pairedGrassmannianBlade M = includeTowerA (grassmannianExteriorBlade M) := rfl

theorem positiveChart_pairedPlucker_Klein (M : Matrix2x4) :
    matrixPluckerCoords M 0 * matrixPluckerCoords M 5 -
      matrixPluckerCoords M 1 * matrixPluckerCoords M 4 +
      matrixPluckerCoords M 2 * matrixPluckerCoords M 3 = 0 :=
  matrixPluckerCoords_klein_relation M

/-- One binary Cantor prefix has its canonical length parity. -/
def cantorPrefixParity (u : List BinarySector) : Bool :=
  cantorWordParity u

/-- Homogeneous graded product of two represented Cantor prefixes. -/
def gradedProduct {A : Type*} [Ring A] (p q : Bool) (x y : A) : A :=
  (if p && q then (-1 : A) else 1) * x * y

/-- Homogeneous graded product of two represented Cantor prefixes. -/
def cantorGradedProduct {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (p q : Bool)
    (u v : List BinarySector) : Op :=
  gradedProduct p q (cylinderOperator C u) (cylinderOperator C v)

/-- Graded triple Cantor product `A ⊗g B ⊗g C`, with the parenthesization
chosen as `(A ⊗g B) ⊗g C`. -/
def cantorGradedTripleProduct {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (p q r : Bool)
    (u v w : List BinarySector) : Op :=
  gradedProduct (parityAdd p q) r
    (cantorGradedProduct C p q u v) (cylinderOperator C w)

/-- Koszul associator coherence for the represented homogeneous Cantor factors.
The parity on a pair is Boolean addition, and the two sides apply the Koszul
sign once for each odd pair. -/
theorem gradedProduct_associator {A : Type*} [Ring A]
    (p q r : Bool) (x y z : A) :
    gradedProduct (parityAdd p q) r (gradedProduct p q x y) z =
      gradedProduct p (parityAdd q r) x (gradedProduct q r y z) := by
  cases p <;> cases q <;> cases r <;>
    simp [gradedProduct, parityAdd, mul_assoc]

theorem cantorGradedProduct_associator {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (p q r : Bool)
    (u v w : List BinarySector) :
    cantorGradedTripleProduct C p q r u v w =
      gradedProduct p (parityAdd q r)
        (cylinderOperator C u) (cantorGradedProduct C q r v w) := by
  exact gradedProduct_associator p q r
    (cylinderOperator C u) (cylinderOperator C v) (cylinderOperator C w)

/-- The nested superbracket triple Cantor operation reuses the existing owner
and satisfies its graded Jacobi identity on prefix-derived parities. -/
def cantorGradedTripleBracket {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (p q r : Bool)
    (u v w : List BinarySector) : Op :=
  InfoGeometry.Clifford.ParaKahler55PositiveGrassmannianCantorBridge.gradedCantorTripleProduct
    C p q r u v w

theorem cantorGradedTripleBracket_jacobi {Op : Type*} [Ring Op] [StarRing Op]
    (C : CuntzO2Carrier Op) (u v w : List BinarySector) :
    (if cantorPrefixParity u && cantorPrefixParity w then (-1 : Op) else 1) *
        cantorGradedTripleBracket C (cantorPrefixParity u) (cantorPrefixParity v)
          (cantorPrefixParity w) u v w +
      (if cantorPrefixParity v && cantorPrefixParity u then (-1 : Op) else 1) *
        cantorGradedTripleBracket C (cantorPrefixParity v) (cantorPrefixParity w)
          (cantorPrefixParity u) v w u +
      (if cantorPrefixParity w && cantorPrefixParity v then (-1 : Op) else 1) *
        cantorGradedTripleBracket C (cantorPrefixParity w) (cantorPrefixParity u)
          (cantorPrefixParity v) w u v = 0 := by
  simpa [cantorGradedTripleBracket, cantorPrefixParity] using
    gradedCantorTripleProduct_word_jacobi C u v w

end InfoGeometry.Canonical.PositiveGrassmannianExteriorCantor

end noncomputable section
