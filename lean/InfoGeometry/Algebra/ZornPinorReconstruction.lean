import InfoGeometry.Algebra.ZornVectorMatrix
import Mathlib.Algebra.Quaternion
import Mathlib.Tactic

/-!
# The quaternion and Peirce sectors of the existing Zorn carrier

The submitted product has the opposite cross-product convention to
`ZornVectorMatrix.mul`. Negating both off-diagonal vectors intertwines the
products. No second vector type, octonion type, or associative instance is
introduced. The symbols `creation` and `annihilation` below name Zorn elements;
operator composition is treated separately in `ZornLeftCAR`.
-/

namespace InfoGeometry.Algebra.ZornPinorReconstruction

open InfoGeometry.Algebra

noncomputable section

abbrev V := ZornVec3 ℝ
abbrev Z := ZornVectorMatrix ℝ

/-- The source convention on the *existing* eight-dimensional carrier. -/
def sourceProduct (X Y : Z) : Z :=
  ⟨X.a * Y.a + ZornVec3.dot X.v Y.w,
   fun i => X.a * Y.v i + Y.b * X.v i + ZornVec3.cross X.w Y.w i,
   fun i => Y.a * X.w i + X.b * Y.w i - ZornVec3.cross X.v Y.v i,
   ZornVec3.dot X.w Y.v + X.b * Y.b⟩

/-- Change of cross-product convention, not an automorphism of one product. -/
def orientation : Z ≃ₗ[ℝ] Z where
  toFun X := ⟨X.a, -X.v, -X.w, X.b⟩
  invFun X := ⟨X.a, -X.v, -X.w, X.b⟩
  left_inv X := by ext i <;> simp
  right_inv X := by ext i <;> simp
  map_add' X Y := by ext i <;> simp [ZornVectorMatrix.add]
  map_smul' r X := by ext i <;> simp [ZornVectorMatrix.smul]

/-- The precise product-preserving dictionary between the two conventions. -/
theorem orientation_sourceProduct (X Y : Z) :
    orientation (sourceProduct X Y) =
      ZornVectorMatrix.mul (orientation X) (orientation Y) := by
  ext i <;> (try fin_cases i) <;>
    simp [orientation, sourceProduct, ZornVectorMatrix.mul,
      ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;> ring

theorem orientation_norm (X : Z) :
    ZornVectorMatrix.norm (orientation X) = ZornVectorMatrix.norm X := by
  simp [orientation, ZornVectorMatrix.norm, ZornVec3.dot, Fin.sum_univ_three]

/-- The two poles are the pre-existing complementary diagonal elements. -/
abbrev polePlus : Z := ZornVectorMatrix.E11
abbrev poleMinus : Z := ZornVectorMatrix.E22

/-- Upper and lower source elements transported to the repository convention. -/
def creation (u : V) : Z := ZornVectorMatrix.offDiagonal (-u) 0
def annihilation (u : V) : Z := ZornVectorMatrix.offDiagonal 0 (-u)

/-- Imaginary quaternion direction, not by itself a faithful Pin representation. -/
def gamma (u : V) : Z := ZornVectorMatrix.offDiagonal (-u) u

/-- Positive-square direction in the split carrier. -/
def kappa (u : V) : Z := ZornVectorMatrix.offDiagonal (-u) (-u)

theorem poles_distinct : polePlus ≠ poleMinus := by
  intro h
  have h0 := congrArg ZornVectorMatrix.a h
  norm_num [polePlus, poleMinus, ZornVectorMatrix.E11, ZornVectorMatrix.E22] at h0

theorem poles_complete : polePlus + poleMinus = ZornVectorMatrix.one := by
  ext i <;> simp [polePlus, poleMinus, ZornVectorMatrix.E11,
    ZornVectorMatrix.E22, ZornVectorMatrix.add, ZornVectorMatrix.one]

/-- Transport preserves the original Clifford-like element square law. -/
theorem gamma_square (u : V) :
    ZornVectorMatrix.mul (gamma u) (gamma u) =
      (-ZornVec3.dot u u) • ZornVectorMatrix.one := by
  ext i <;> (try fin_cases i) <;>
    simp [gamma, ZornVectorMatrix.offDiagonal, ZornVectorMatrix.mul,
      ZornVectorMatrix.smul, ZornVectorMatrix.one,
      ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;> ring

theorem kappa_square (u : V) :
    ZornVectorMatrix.mul (kappa u) (kappa u) =
      ZornVec3.dot u u • ZornVectorMatrix.one := by
  ext i <;> (try fin_cases i) <;>
    simp [kappa, ZornVectorMatrix.offDiagonal, ZornVectorMatrix.mul,
      ZornVectorMatrix.smul, ZornVectorMatrix.one,
      ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;> ring

/-- The full dot/cross quaternion multiplication law, for arbitrary vectors. -/
theorem gamma_product (u v : V) :
    ZornVectorMatrix.mul (gamma u) (gamma v) =
      (-ZornVec3.dot u v) • ZornVectorMatrix.one + gamma (ZornVec3.cross u v) := by
  ext i <;> (try fin_cases i) <;>
    simp [gamma, ZornVectorMatrix.offDiagonal, ZornVectorMatrix.mul,
      ZornVectorMatrix.smul, ZornVectorMatrix.one, ZornVectorMatrix.add,
      ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;> ring

theorem gamma_basis_product :
    ZornVectorMatrix.mul (gamma (ZornVec3.basis 0)) (gamma (ZornVec3.basis 1)) =
      gamma (ZornVec3.basis 2) := by
  rw [gamma_product]
  simp

/-- The element volume collapses to a scalar in this quaternion sector. -/
theorem gamma_element_volume :
    ZornVectorMatrix.mul
        (ZornVectorMatrix.mul (gamma (ZornVec3.basis 0)) (gamma (ZornVec3.basis 1)))
        (gamma (ZornVec3.basis 2)) = -ZornVectorMatrix.one := by
  rw [gamma_basis_product, gamma_square]
  simp

theorem creation_square (u : V) :
    ZornVectorMatrix.mul (creation u) (creation u) = 0 := by
  ext i <;> (try fin_cases i) <;>
    simp [creation, ZornVectorMatrix.offDiagonal, ZornVectorMatrix.mul,
      ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross] <;> ring

theorem annihilation_square (u : V) :
    ZornVectorMatrix.mul (annihilation u) (annihilation u) = 0 := by
  ext i <;> (try fin_cases i) <;>
    simp [annihilation, ZornVectorMatrix.offDiagonal, ZornVectorMatrix.mul,
      ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross] <;> ring

theorem creation_annihilation (u v : V) :
    ZornVectorMatrix.mul (creation u) (annihilation v) =
      ZornVec3.dot u v • polePlus := by
  ext i <;> (try fin_cases i) <;>
    simp [creation, annihilation, polePlus, ZornVectorMatrix.E11,
      ZornVectorMatrix.offDiagonal, ZornVectorMatrix.mul,
      ZornVectorMatrix.smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;> ring

theorem annihilation_creation (u v : V) :
    ZornVectorMatrix.mul (annihilation v) (creation u) =
      ZornVec3.dot u v • poleMinus := by
  ext i <;> (try fin_cases i) <;>
    simp [creation, annihilation, poleMinus, ZornVectorMatrix.E22,
      ZornVectorMatrix.offDiagonal, ZornVectorMatrix.mul,
      ZornVectorMatrix.smul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three] <;> ring

theorem element_car (u v : V) :
    ZornVectorMatrix.mul (creation u) (annihilation v) +
        ZornVectorMatrix.mul (annihilation v) (creation u) =
      ZornVec3.dot u v • ZornVectorMatrix.one := by
  rw [creation_annihilation, annihilation_creation, ← smul_add, poles_complete]

/-- Same-sector products are cross products, although their anticommutator is zero. -/
theorem creation_creation (u v : V) :
    ZornVectorMatrix.mul (creation u) (creation v) =
      -annihilation (ZornVec3.cross u v) := by
  ext i <;> (try fin_cases i) <;>
    simp [creation, annihilation, ZornVectorMatrix.offDiagonal,
      ZornVectorMatrix.mul, ZornVectorMatrix.neg, ZornVec3.dot, ZornVec3.cross] <;> ring

theorem annihilation_annihilation (u v : V) :
    ZornVectorMatrix.mul (annihilation u) (annihilation v) =
      creation (ZornVec3.cross u v) := by
  ext i <;> (try fin_cases i) <;>
    simp [creation, annihilation, ZornVectorMatrix.offDiagonal,
      ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.cross] <;> ring

theorem gamma_reconstruction (u : V) : gamma u = creation u - annihilation u := by
  ext i <;> simp [gamma, creation, annihilation, ZornVectorMatrix.offDiagonal,
    ZornVectorMatrix.sub, ZornVectorMatrix.add, ZornVectorMatrix.neg]

theorem kappa_reconstruction (u : V) : kappa u = creation u + annihilation u := by
  ext i <;> simp [kappa, creation, annihilation, ZornVectorMatrix.offDiagonal,
    ZornVectorMatrix.add]

theorem creation_anticommutator (u v : V) :
    ZornVectorMatrix.mul (creation u) (creation v) +
      ZornVectorMatrix.mul (creation v) (creation u) = 0 := by
  ext i <;> (try fin_cases i) <;>
    simp [creation, ZornVectorMatrix.offDiagonal, ZornVectorMatrix.mul,
      ZornVectorMatrix.add, ZornVectorMatrix.zero,
      ZornVec3.dot, ZornVec3.cross] <;> ring

theorem annihilation_anticommutator (u v : V) :
    ZornVectorMatrix.mul (annihilation u) (annihilation v) +
      ZornVectorMatrix.mul (annihilation v) (annihilation u) = 0 := by
  ext i <;> (try fin_cases i) <;>
    simp [annihilation, ZornVectorMatrix.offDiagonal, ZornVectorMatrix.mul,
      ZornVectorMatrix.add, ZornVectorMatrix.zero,
      ZornVec3.dot, ZornVec3.cross] <;> ring

theorem polePlus_creation (u : V) :
    ZornVectorMatrix.mul polePlus (creation u) = creation u := by
  ext i <;> (try fin_cases i) <;>
    simp [polePlus, creation, ZornVectorMatrix.E11, ZornVectorMatrix.offDiagonal,
      ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.cross]

theorem creation_polePlus (u : V) :
    ZornVectorMatrix.mul (creation u) polePlus = 0 := by
  ext i <;> (try fin_cases i) <;>
    simp [polePlus, creation, ZornVectorMatrix.E11, ZornVectorMatrix.offDiagonal,
      ZornVectorMatrix.mul, ZornVectorMatrix.zero, ZornVec3.dot, ZornVec3.cross]

theorem creation_poleMinus (u : V) :
    ZornVectorMatrix.mul (creation u) poleMinus = creation u := by
  ext i <;> (try fin_cases i) <;>
    simp [poleMinus, creation, ZornVectorMatrix.E22, ZornVectorMatrix.offDiagonal,
      ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.cross]

/-- The actual quaternion carrier, embedded linearly in the Zorn carrier. -/
def quaternionEmbedding : Quaternion ℝ →ₗ[ℝ] Z where
  toFun q := ⟨q.re, ![-q.imI, -q.imJ, -q.imK], ![q.imI, q.imJ, q.imK], q.re⟩
  map_add' p q := by
    ext i <;> (try fin_cases i) <;> simp [ZornVectorMatrix.add]
  map_smul' r q := by
    ext i <;> (try fin_cases i) <;> simp [ZornVectorMatrix.smul]

/-- Multiplication is preserved without installing associativity on all Zorn elements. -/
theorem quaternionEmbedding_mul (p q : Quaternion ℝ) :
    quaternionEmbedding (p * q) =
      ZornVectorMatrix.mul (quaternionEmbedding p) (quaternionEmbedding q) := by
  ext i <;> (try fin_cases i) <;>
    simp [quaternionEmbedding, ZornVectorMatrix.mul, ZornVec3.dot,
      ZornVec3.cross, Fin.sum_univ_three] <;> ring

theorem quaternionEmbedding_injective : Function.Injective quaternionEmbedding := by
  intro p q h
  have hr := congrArg ZornVectorMatrix.a h
  have hi := congrArg (fun X : Z => X.w 0) h
  have hj := congrArg (fun X : Z => X.w 1) h
  have hk := congrArg (fun X : Z => X.w 2) h
  apply QuaternionAlgebra.ext
  · exact hr
  · exact hi
  · exact hj
  · exact hk

/-- Associativity holds on the embedded quaternion sector. -/
theorem quaternion_sector_associative (p q r : Quaternion ℝ) :
    ZornVectorMatrix.mul
        (ZornVectorMatrix.mul (quaternionEmbedding p) (quaternionEmbedding q))
        (quaternionEmbedding r) =
      ZornVectorMatrix.mul (quaternionEmbedding p)
        (ZornVectorMatrix.mul (quaternionEmbedding q) (quaternionEmbedding r)) := by
  simp only [← quaternionEmbedding_mul, mul_assoc]

end
end InfoGeometry.Algebra.ZornPinorReconstruction
