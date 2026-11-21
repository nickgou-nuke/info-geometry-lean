/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ZornAssociatorGram

/-!
# The Zorn associator Gram form with quaternion probes

The state ranges over the existing full real Zorn algebra. Both probe slots
are projected onto the image of the existing multiplicative quaternion
embedding. The projector is constructed from the actual eight coordinates
and is orthogonal for the existing positive coefficient pairing.

The form sums all 64 ordered pairs of the existing signed split basis after
this probe projection. Its kernel is exactly the ordinary quaternion image.
This differs from the full ambient-probe form, whose kernel is the scalar
line. The projected probes are two copies of one half of each quaternion
basis vector; those factors are retained, with no averaging normalization.

The converse kernel implication uses actual Zorn multiplication. With
`ell = diagonal 1 (-1)`, the ordered defect is
`[embedding q * ell, embedding i, embedding j] =
  2 • (embedding (q * k) * ell)`.
The factor acts on the right inside the quaternion product. No associativity
instance on the full Zorn algebra or assumed kernel field is introduced.
-/

noncomputable section

namespace InfoGeometry.Algebra.ZornQuaternionAssociatorGram

open ZornPinorReconstruction ZornCARAdjoint ZornAssociatorGram
open InfoGeometry.Canonical.GunaydinGursey
open scoped BigOperators

/-- The quaternion component of the calibrated real `4 + 4` decomposition. -/
def quaternionPart : Z →ₗ[ℝ] Quaternion ℝ where
  toFun X :=
    ⟨(X.a + X.b) / 2,
      (X.w 0 - X.v 0) / 2,
      (X.w 1 - X.v 1) / 2,
      (X.w 2 - X.v 2) / 2⟩
  map_add' X Y := by
    apply QuaternionAlgebra.ext <;> simp [ZornVectorMatrix.add] <;> ring
  map_smul' r X := by
    apply QuaternionAlgebra.ext <;> simp [ZornVectorMatrix.smul] <;> ring

/-- The coefficient of the right `ell` component in the same decomposition. -/
def transversePart : Z →ₗ[ℝ] Quaternion ℝ where
  toFun X :=
    ⟨(X.a - X.b) / 2,
      (X.v 0 + X.w 0) / 2,
      (X.v 1 + X.w 1) / 2,
      (X.v 2 + X.w 2) / 2⟩
  map_add' X Y := by
    apply QuaternionAlgebra.ext <;> simp [ZornVectorMatrix.add] <;> ring
  map_smul' r X := by
    apply QuaternionAlgebra.ext <;> simp [ZornVectorMatrix.smul] <;> ring

/-- Projection of a probe onto the existing ordinary quaternion image. -/
def quaternionProjector : Module.End ℝ Z :=
  quaternionEmbedding.comp quaternionPart

theorem quaternionProjector_apply (X : Z) :
    quaternionProjector X =
      ⟨(X.a + X.b) / 2,
        (fun i => (X.v i - X.w i) / 2),
        (fun i => (X.w i - X.v i) / 2),
        (X.a + X.b) / 2⟩ := by
  ext i <;> (try fin_cases i) <;>
    simp [quaternionProjector, quaternionPart, quaternionEmbedding] <;> ring

theorem quaternionPart_embedding (q : Quaternion ℝ) :
    quaternionPart (quaternionEmbedding q) = q := by
  apply QuaternionAlgebra.ext <;>
    simp [quaternionPart, quaternionEmbedding] <;> ring

theorem quaternionProjector_embedding (q : Quaternion ℝ) :
    quaternionProjector (quaternionEmbedding q) = quaternionEmbedding q := by
  change quaternionEmbedding (quaternionPart (quaternionEmbedding q)) = _
  rw [quaternionPart_embedding]

theorem quaternionProjector_idempotent :
    quaternionProjector.comp quaternionProjector = quaternionProjector := by
  apply LinearMap.ext
  intro X
  exact quaternionProjector_embedding (quaternionPart X)

theorem quaternionProjector_mem_range (X : Z) :
    quaternionProjector X ∈ quaternionEmbedding.range :=
  LinearMap.mem_range_self quaternionEmbedding (quaternionPart X)

theorem quaternionProjector_eq_self_iff (X : Z) :
    quaternionProjector X = X ↔ X ∈ quaternionEmbedding.range := by
  constructor
  · intro h
    exact LinearMap.mem_range.mpr ⟨quaternionPart X, h⟩
  · intro h
    obtain ⟨q, rfl⟩ := LinearMap.mem_range.mp h
    exact quaternionProjector_embedding q

/-- The residual is orthogonal to the full quaternion image for the actual
positive coefficient pairing, not for the split multiplicative norm. -/
theorem quaternionProjector_orthogonal (X : Z) (q : Quaternion ℝ) :
    coefficientPairing (X - quaternionProjector X) (quaternionEmbedding q) = 0 := by
  simp [coefficientPairing, quaternionProjector, quaternionPart,
    quaternionEmbedding, _root_.sub_eq_add_neg, ZornVectorMatrix.add,
    ZornVectorMatrix.neg, ZornVec3.dot, Fin.sum_univ_three]
  ring

/-- The actual positive-square diagonal element fixing the multiplication
convention in the `H + H ell` decomposition. -/
def ell : Z := ZornVectorMatrix.diagonal 1 (-1)

theorem quaternion_mul_ell (q : Quaternion ℝ) :
    quaternionEmbedding q * ell =
      ⟨q.re, ![q.imI, q.imJ, q.imK], ![q.imI, q.imJ, q.imK], -q.re⟩ := by
  ext i <;> (try fin_cases i) <;>
    simp [quaternionEmbedding, ell, ZornVectorMatrix.diagonal,
      ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.cross, Fin.sum_univ_three]

/-- Every native Zorn element has the explicit ordinary-quaternion
decomposition, with the transverse quaternion multiplied by `ell` on the right. -/
theorem quaternion_decomposition (X : Z) :
    X = quaternionEmbedding (quaternionPart X) +
      quaternionEmbedding (transversePart X) * ell := by
  rw [quaternion_mul_ell]
  ext i <;> (try fin_cases i) <;>
    simp [quaternionEmbedding, quaternionPart, transversePart,
      ZornVectorMatrix.add] <;> ring

theorem transversePart_quaternion_mul_ell (q : Quaternion ℝ) :
    transversePart (quaternionEmbedding q * ell) = q := by
  rw [quaternion_mul_ell]
  apply QuaternionAlgebra.ext <;> simp [transversePart] <;> ring

theorem quaternion_mul_ell_eq_zero_iff (q : Quaternion ℝ) :
    quaternionEmbedding q * ell = 0 ↔ q = 0 := by
  constructor
  · intro h
    have hq := congrArg transversePart h
    simpa only [transversePart_quaternion_mul_ell, map_zero] using hq
  · rintro rfl
    rw [map_zero, zero_mul]

/-- The pair/Zorn multiplication adapter is proved from the actual native
product. In quaternion-pair coordinates it is `(0,q) * (p,0) = (0,q * star p)`. -/
theorem quaternion_mul_ell_mul_quaternion (q p : Quaternion ℝ) :
    (quaternionEmbedding q * ell) * quaternionEmbedding p =
      quaternionEmbedding (q * star p) * ell := by
  ext i <;> (try fin_cases i) <;>
    simp [quaternionEmbedding, ell, ZornVectorMatrix.diagonal,
      ZornVectorMatrix.mul, ZornVec3.dot, ZornVec3.cross,
      Fin.sum_univ_three] <;> ring

/-- The three imaginary units of the existing native quaternion carrier. -/
def quaternionUnit (i : Fin 3) : Quaternion ℝ :=
  ⟨0, (ZornVec3.basis i : ZornVec3 ℝ) 0,
    (ZornVec3.basis i : ZornVec3 ℝ) 1,
    (ZornVec3.basis i : ZornVec3 ℝ) 2⟩

theorem star_quaternionUnit (i : Fin 3) :
    star (quaternionUnit i) = -quaternionUnit i := by
  apply QuaternionAlgebra.ext <;> simp [quaternionUnit]

theorem quaternionUnit_zero_mul_one :
    quaternionUnit 0 * quaternionUnit 1 = quaternionUnit 2 := by
  apply QuaternionAlgebra.ext <;> norm_num [quaternionUnit, ZornVec3.basis]

theorem quaternionUnit_two_ne_zero : quaternionUnit 2 ≠ 0 := by
  intro h
  have hk := congrArg (fun q : Quaternion ℝ => q.imK) h
  norm_num [quaternionUnit, ZornVec3.basis] at hk

/-- The sign, factor, and right multiplication by `k` follow from the native
product adapter. Swapping either the probe order or the pair convention
would change this identity. -/
theorem associator_quaternion_mul_ell_i_j (q : Quaternion ℝ) :
    _root_.associator (quaternionEmbedding q * ell)
      (quaternionEmbedding (quaternionUnit 0))
      (quaternionEmbedding (quaternionUnit 1)) =
        (2 : ℝ) • (quaternionEmbedding (q * quaternionUnit 2) * ell) := by
  have hij : quaternionEmbedding (quaternionUnit 0) *
      quaternionEmbedding (quaternionUnit 1) =
      quaternionEmbedding (quaternionUnit 2) := by
    change ZornVectorMatrix.mul (quaternionEmbedding (quaternionUnit 0))
      (quaternionEmbedding (quaternionUnit 1)) = quaternionEmbedding (quaternionUnit 2)
    rw [← quaternionEmbedding_mul, quaternionUnit_zero_mul_one]
  have hq : (q * star (quaternionUnit 0)) * star (quaternionUnit 1) =
      q * quaternionUnit 2 := by
    simp only [star_quaternionUnit, _root_.mul_neg, _root_.neg_mul,
      _root_.neg_neg, _root_.mul_assoc, quaternionUnit_zero_mul_one]
  have hk : q * star (quaternionUnit 2) = -(q * quaternionUnit 2) := by
    rw [star_quaternionUnit, _root_.mul_neg]
  calc
    _ = quaternionEmbedding
          ((q * star (quaternionUnit 0)) * star (quaternionUnit 1)) * ell -
        quaternionEmbedding (q * star (quaternionUnit 2)) * ell := by
      simp only [_root_.associator_apply, hij, quaternion_mul_ell_mul_quaternion]
    _ = quaternionEmbedding (q * quaternionUnit 2) * ell -
        quaternionEmbedding (-(q * quaternionUnit 2)) * ell := by rw [hq, hk]
    _ = (2 : ℝ) • (quaternionEmbedding (q * quaternionUnit 2) * ell) := by
      simp only [map_neg, _root_.neg_mul, _root_.sub_neg_eq_add, _root_.two_smul]

theorem associator_quaternion_triple (p q r : Quaternion ℝ) :
    _root_.associator (quaternionEmbedding p)
      (quaternionEmbedding q) (quaternionEmbedding r) = 0 := by
  rw [_root_.associator_apply]
  exact _root_.sub_eq_zero.mpr (quaternion_sector_associative p q r)

/-- One ordered pair of ordinary quaternion probes detects every transverse
quaternion component, using the already constructed full decomposition. -/
theorem associator_quaternion_i_j (X : Z) :
    _root_.associator X (quaternionEmbedding (quaternionUnit 0))
      (quaternionEmbedding (quaternionUnit 1)) =
        (2 : ℝ) •
          (quaternionEmbedding (transversePart X * quaternionUnit 2) * ell) := by
  have h := congrArg
    (leftRightCommutator (R := ℝ)
      (quaternionEmbedding (quaternionUnit 0))
      (quaternionEmbedding (quaternionUnit 1)))
    (quaternion_decomposition X)
  rw [map_add] at h
  simp only [leftRightCommutator_apply_first] at h
  rw [associator_quaternion_triple, _root_.zero_add,
    associator_quaternion_mul_ell_i_j] at h
  exact h

theorem associator_quaternion_i_j_zero_iff (X : Z) :
    _root_.associator X (quaternionEmbedding (quaternionUnit 0))
      (quaternionEmbedding (quaternionUnit 1)) = 0 ↔
        X ∈ quaternionEmbedding.range := by
  constructor
  · intro h
    rw [associator_quaternion_i_j] at h
    have hmul : quaternionEmbedding (transversePart X * quaternionUnit 2) * ell = 0 :=
      (smul_eq_zero.mp h).resolve_left (by norm_num)
    have hqk := (quaternion_mul_ell_eq_zero_iff _).mp hmul
    have hq : transversePart X = 0 :=
      (mul_eq_zero.mp hqk).resolve_right quaternionUnit_two_ne_zero
    apply LinearMap.mem_range.mpr
    refine ⟨quaternionPart X, ?_⟩
    have hX := quaternion_decomposition X
    rw [hq, map_zero, zero_mul, _root_.add_zero] at hX
    exact hX.symm
  · intro h
    obtain ⟨q, rfl⟩ := LinearMap.mem_range.mp h
    exact associator_quaternion_triple q _ _

/-- The projection is applied only to the two probe slots. -/
def quaternionProbe (i : BasisIndex) : Z :=
  quaternionProjector (signedBasis (R := ℝ) i)

theorem quaternionProbe_mem_range (i : BasisIndex) :
    quaternionProbe i ∈ quaternionEmbedding.range :=
  quaternionProjector_mem_range _

/-- Both diagonal signed-basis probes project to one half of the unit. -/
theorem quaternionProbe_singlets :
    quaternionProbe (.inl ()) = (1 / 2 : ℝ) • quaternionEmbedding 1 ∧
    quaternionProbe (.inr (.inl ())) = (1 / 2 : ℝ) • quaternionEmbedding 1 := by
  constructor
  · rw [quaternionProbe, (signedBasis_singlets (R := ℝ)).1]
    ext i <;> (try fin_cases i) <;>
      norm_num [quaternionProjector, quaternionPart, quaternionEmbedding,
        uZero, ZornVectorMatrix.E22, ZornVectorMatrix.smul]
  · rw [quaternionProbe, (signedBasis_singlets (R := ℝ)).2]
    ext i <;> (try fin_cases i) <;>
      norm_num [quaternionProjector, quaternionPart, quaternionEmbedding,
        uStarZero, ZornVectorMatrix.E11, ZornVectorMatrix.smul]

/-- The two color families give two copies of one half of each imaginary
quaternion basis vector, not unit-normalized probes. -/
theorem quaternionProbe_colors (k : Fin 3) :
    quaternionProbe (.inr (.inr (.inl k))) =
        (1 / 2 : ℝ) • quaternionEmbedding (quaternionUnit k) ∧
    quaternionProbe (.inr (.inr (.inr k))) =
        (1 / 2 : ℝ) • quaternionEmbedding (quaternionUnit k) := by
  constructor
  · rw [quaternionProbe, (signedBasis_colors (R := ℝ) k).1]
    ext i <;> (try fin_cases k) <;> (try fin_cases i) <;>
      norm_num [quaternionProjector, quaternionPart, quaternionEmbedding,
        quaternionUnit, u, ZornVectorMatrix.V, ZornVectorMatrix.smul,
        ZornVec3.basis]
  · rw [quaternionProbe, (signedBasis_colors (R := ℝ) k).2]
    ext i <;> (try fin_cases k) <;> (try fin_cases i) <;>
      norm_num [quaternionProjector, quaternionPart, quaternionEmbedding,
        quaternionUnit, uStar, ZornVectorMatrix.U, ZornVectorMatrix.neg,
        ZornVectorMatrix.smul, ZornVec3.basis]

/-- The full unnormalized 8-by-8 sum with both basis probes projected onto
the quaternion image. The existing regular-action operator carries the state. -/
def quaternionAssociatorGram : LinearMap.BilinForm ℝ Z :=
  ∑ i : BasisIndex, ∑ j : BasisIndex,
    coefficientPairing.compl₁₂
      (leftRightCommutator (R := ℝ) (quaternionProbe i) (quaternionProbe j))
      (leftRightCommutator (R := ℝ) (quaternionProbe i) (quaternionProbe j))

theorem quaternionAssociatorGram_apply (X Y : Z) :
    quaternionAssociatorGram X Y =
      ∑ i : BasisIndex, ∑ j : BasisIndex,
        coefficientPairing
          (_root_.associator X (quaternionProbe i) (quaternionProbe j))
          (_root_.associator Y (quaternionProbe i) (quaternionProbe j)) := by
  simp only [quaternionAssociatorGram, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.compl₁₂_apply, leftRightCommutator_apply_first]

theorem quaternionAssociatorGram_symm (X Y : Z) :
    quaternionAssociatorGram X Y = quaternionAssociatorGram Y X := by
  rw [quaternionAssociatorGram_apply, quaternionAssociatorGram_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact coefficientPairing_symm _ _

theorem quaternionAssociatorGram_isSymm : quaternionAssociatorGram.IsSymm :=
  ⟨quaternionAssociatorGram_symm⟩

theorem quaternionAssociatorGram_nonneg (X : Z) :
    0 ≤ quaternionAssociatorGram X X := by
  rw [quaternionAssociatorGram_apply]
  exact Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => coefficientPairing_nonneg _

theorem quaternionAssociatorGram_zero_iff_probes (X : Z) :
    quaternionAssociatorGram X X = 0 ↔
      ∀ i j : BasisIndex,
        _root_.associator X (quaternionProbe i) (quaternionProbe j) = 0 := by
  rw [quaternionAssociatorGram_apply]
  constructor
  · intro h i j
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => Finset.sum_nonneg
        (fun _ _ => coefficientPairing_nonneg _))).mp h i (Finset.mem_univ i)
    have hij := (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ => coefficientPairing_nonneg _)).mp hi j (Finset.mem_univ j)
    exact (coefficientPairing_zero_iff _).mp hij
  · intro h
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    rw [h i j]
    simp only [map_zero, LinearMap.zero_apply]

private theorem associator_smul_probes (X Y W : Z) (r s : ℝ) :
    _root_.associator X (r • Y) (s • W) =
      (r * s) • _root_.associator X Y W := by
  simp only [_root_.associator_apply, _root_.smul_mul_assoc,
    _root_.mul_smul_comm, _root_.smul_smul, ← _root_.smul_sub, mul_comm r s]

/-- Exact kernel: projection of the two probe arguments makes every ordinary
quaternion state invisible, and the actual ordered `i,j` defect detects all
four complementary coordinates. No generic kernel hypothesis is used. -/
theorem quaternionAssociatorGram_zero_iff_mem_range (X : Z) :
    quaternionAssociatorGram X X = 0 ↔ X ∈ quaternionEmbedding.range := by
  constructor
  · intro h
    apply (associator_quaternion_i_j_zero_iff X).mp
    have hij := (quaternionAssociatorGram_zero_iff_probes X).mp h
      (.inr (.inr (.inl 0))) (.inr (.inr (.inl 1)))
    rw [(quaternionProbe_colors 0).1, (quaternionProbe_colors 1).1,
      associator_smul_probes] at hij
    exact (smul_eq_zero.mp hij).resolve_left (by norm_num)
  · intro h
    obtain ⟨q, rfl⟩ := LinearMap.mem_range.mp h
    apply (quaternionAssociatorGram_zero_iff_probes _).mpr
    intro i j
    change _root_.associator (quaternionEmbedding q)
      (quaternionEmbedding (quaternionPart (signedBasis (R := ℝ) i)))
      (quaternionEmbedding (quaternionPart (signedBasis (R := ℝ) j))) = 0
    exact associator_quaternion_triple q _ _

theorem quaternionAssociatorGram_zero_iff_projector (X : Z) :
    quaternionAssociatorGram X X = 0 ↔ quaternionProjector X = X :=
  (quaternionAssociatorGram_zero_iff_mem_range X).trans
    (quaternionProjector_eq_self_iff X).symm

theorem quaternionAssociatorGram_left_kernel_iff_mem_range (X : Z) :
    (∀ Y : Z, quaternionAssociatorGram X Y = 0) ↔
      X ∈ quaternionEmbedding.range := by
  constructor
  · intro h
    exact (quaternionAssociatorGram_zero_iff_mem_range X).mp (h X)
  · intro h Y
    have hX := (quaternionAssociatorGram_zero_iff_probes X).mp
      ((quaternionAssociatorGram_zero_iff_mem_range X).mpr h)
    rw [quaternionAssociatorGram_apply]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    rw [hX i j]
    simp only [map_zero, LinearMap.zero_apply]

theorem quaternionAssociatorGram_pos_of_not_mem_range {X : Z}
    (hX : X ∉ quaternionEmbedding.range) :
    0 < quaternionAssociatorGram X X := by
  apply lt_of_le_of_ne (quaternionAssociatorGram_nonneg X)
  intro h
  exact hX ((quaternionAssociatorGram_zero_iff_mem_range X).mp h.symm)

theorem quaternionAssociatorGram_embedding_zero (q : Quaternion ℝ) :
    quaternionAssociatorGram (quaternionEmbedding q) (quaternionEmbedding q) = 0 :=
  (quaternionAssociatorGram_zero_iff_mem_range _).mpr
    (LinearMap.mem_range_self quaternionEmbedding q)

/-- A concrete state outside the quaternion image has strictly positive
projected-probe Gram value. -/
theorem quaternionAssociatorGram_ell_pos :
    0 < quaternionAssociatorGram ell ell := by
  apply quaternionAssociatorGram_pos_of_not_mem_range
  intro h
  obtain ⟨q, hq⟩ := LinearMap.mem_range.mp h
  have ha := congrArg ZornVectorMatrix.a hq
  have hb := congrArg ZornVectorMatrix.b hq
  norm_num [quaternionEmbedding, ell, ZornVectorMatrix.diagonal] at ha hb
  linarith

end InfoGeometry.Algebra.ZornQuaternionAssociatorGram

end
