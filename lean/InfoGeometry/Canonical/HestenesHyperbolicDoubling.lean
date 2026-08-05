import Mathlib.Algebra.Quaternion
import InfoGeometry.Canonical.AlbertCayleyDickson

/-!
# Hyperbolic quaternion doubling

This owner records the constructive crossing laws for the `γ = 1` Albert
doubling of the real quaternion algebra.  The doubled carrier is deliberately
not given an associative algebra instance: the product is the explicit
Cayley--Dickson product from `AlbertStep.mul`.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesHyperbolicDoubling

open InfoGeometry.Canonical.AlbertCayleyDickson

abbrev QuaternionDouble := AlbertStep ℝ (Quaternion ℝ) (1 : ℝ)

def quaternionDoubleAdd (x y : QuaternionDouble) : QuaternionDouble :=
  ⟨x.p + y.p, x.q + y.q⟩

def quaternionDoubleNeg (x : QuaternionDouble) : QuaternionDouble :=
  ⟨-x.p, -x.q⟩

def quaternionDoubleSmul (r : ℝ) (x : QuaternionDouble) : QuaternionDouble :=
  ⟨r • x.p, r • x.q⟩

instance : Add QuaternionDouble := ⟨quaternionDoubleAdd⟩

instance : Neg QuaternionDouble := ⟨quaternionDoubleNeg⟩

instance : SMul ℝ QuaternionDouble := ⟨quaternionDoubleSmul⟩

@[simp] theorem quaternionDoubleAdd_p (x y : QuaternionDouble) :
    (x + y).p = x.p + y.p := rfl

@[simp] theorem quaternionDoubleAdd_q (x y : QuaternionDouble) :
    (x + y).q = x.q + y.q := rfl

@[simp] theorem quaternionDoubleSmul_p (r : ℝ) (x : QuaternionDouble) :
    (r • x).p = r • x.p := rfl

@[simp] theorem quaternionDoubleSmul_q (r : ℝ) (x : QuaternionDouble) :
    (r • x).q = r • x.q := rfl

instance : AddCommGroup QuaternionDouble where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc x y z := by
    apply AlbertStep.ext
    · change (x.p + y.p) + z.p = x.p + (y.p + z.p)
      exact add_assoc _ _ _
    · change (x.q + y.q) + z.q = x.q + (y.q + z.q)
      exact add_assoc _ _ _
  zero_add x := by
    apply AlbertStep.ext
    · change (0 : Quaternion ℝ) + x.p = x.p
      exact zero_add _
    · change (0 : Quaternion ℝ) + x.q = x.q
      exact zero_add _
  add_zero x := by
    apply AlbertStep.ext
    · change x.p + (0 : Quaternion ℝ) = x.p
      exact add_zero _
    · change x.q + (0 : Quaternion ℝ) = x.q
      exact add_zero _
  neg_add_cancel x := by
    apply AlbertStep.ext
    · change -x.p + x.p = 0
      exact neg_add_cancel _
    · change -x.q + x.q = 0
      exact neg_add_cancel _
  add_comm x y := by
    apply AlbertStep.ext
    · change x.p + y.p = y.p + x.p
      exact add_comm _ _
    · change x.q + y.q = y.q + x.q
      exact add_comm _ _

instance : Module ℝ QuaternionDouble where
  one_smul x := by
    apply AlbertStep.ext
    · change (1 : ℝ) • x.p = x.p
      exact one_smul _ _
    · change (1 : ℝ) • x.q = x.q
      exact one_smul _ _
  mul_smul r s x := by
    apply AlbertStep.ext
    · change (r * s) • x.p = r • s • x.p
      rw [mul_smul]
    · change (r * s) • x.q = r • s • x.q
      rw [mul_smul]
  smul_zero r := by
    apply AlbertStep.ext
    · change r • (0 : Quaternion ℝ) = 0
      apply QuaternionAlgebra.ext <;> simp
    · change r • (0 : Quaternion ℝ) = 0
      apply QuaternionAlgebra.ext <;> simp
  smul_add r x y := by
    apply AlbertStep.ext
    · change r • (x.p + y.p) = r • x.p + r • y.p
      exact smul_add _ _ _
    · change r • (x.q + y.q) = r • x.q + r • y.q
      exact smul_add _ _ _
  add_smul r s x := by
    apply AlbertStep.ext
    · change (r + s) • x.p = r • x.p + s • x.p
      exact (add_smul r s x.p : (r + s) • x.p = r • x.p + s • x.p)
    · change (r + s) • x.q = r • x.q + s • x.q
      exact (add_smul r s x.q : (r + s) • x.q = r • x.q + s • x.q)
  zero_smul x := by
    apply AlbertStep.ext
    · change (0 : ℝ) • x.p = 0
      exact (zero_smul ℝ x.p : (0 : ℝ) • x.p = 0)
    · change (0 : ℝ) • x.q = 0
      exact (zero_smul ℝ x.q : (0 : ℝ) • x.q = 0)

def quaternionEmbed (a : Quaternion ℝ) : QuaternionDouble :=
  ⟨a, 0⟩

def doublingUnit : QuaternionDouble :=
  ⟨0, 1⟩

def doubledPart (a : Quaternion ℝ) : QuaternionDouble :=
  ⟨0, a⟩

def quaternionI : Quaternion ℝ :=
  ⟨0, 1, 0, 0⟩

def quaternionJ : Quaternion ℝ :=
  ⟨0, 0, 1, 0⟩

def quaternionK : Quaternion ℝ :=
  ⟨0, 0, 0, 1⟩

@[simp] theorem quaternionEmbed_p (a : Quaternion ℝ) :
    (quaternionEmbed a).p = a := rfl

@[simp] theorem quaternionEmbed_q (a : Quaternion ℝ) :
    (quaternionEmbed a).q = 0 := rfl

@[simp] theorem doubledPart_p (a : Quaternion ℝ) :
    (doubledPart a).p = 0 := rfl

@[simp] theorem doubledPart_q (a : Quaternion ℝ) :
    (doubledPart a).q = a := rfl

@[simp] theorem doublingUnit_p :
    doublingUnit.p = 0 := rfl

@[simp] theorem doublingUnit_q :
    doublingUnit.q = 1 := rfl

theorem doubled_decomposition (x : QuaternionDouble) :
    x = ⟨x.p, x.q⟩ := by
  rfl

theorem quaternionEmbed_mul (a b : Quaternion ℝ) :
    AlbertStep.mul (quaternionEmbed a) (quaternionEmbed b) =
      quaternionEmbed (a * b) := by
  ext <;> simp [quaternionEmbed, AlbertStep.mul]

theorem quaternionI_mul_quaternionJ :
    quaternionI * quaternionJ = quaternionK := by
  ext <;>
    norm_num [quaternionI, quaternionJ, quaternionK,
      QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
      QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul]

theorem quaternionJ_mul_quaternionI :
    quaternionJ * quaternionI = -quaternionK := by
  ext <;>
    norm_num [quaternionI, quaternionJ, quaternionK,
      QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
      QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul]

theorem doublingUnit_sq :
    AlbertStep.mul doublingUnit doublingUnit =
      AlbertStep.oneElem := by
  ext <;> simp [doublingUnit, AlbertStep.mul, AlbertStep.oneElem]

theorem doublingUnit_ne_zero :
    doublingUnit ≠ (0 : QuaternionDouble) := by
  intro h
  have hq := congrArg AlbertStep.q h
  simp [doublingUnit] at hq

theorem doublingUnit_mul_quaternionEmbed (a : Quaternion ℝ) :
    AlbertStep.mul doublingUnit (quaternionEmbed a) =
      doubledPart (star a) := by
  ext <;> simp [doublingUnit, quaternionEmbed, doubledPart, AlbertStep.mul]

theorem quaternionEmbed_mul_doublingUnit (a : Quaternion ℝ) :
    AlbertStep.mul (quaternionEmbed a) doublingUnit =
      doubledPart a := by
  ext <;> simp [doublingUnit, quaternionEmbed, doubledPart, AlbertStep.mul]

theorem doublingUnit_mul_doubledPart (a : Quaternion ℝ) :
    AlbertStep.mul doublingUnit (doubledPart a) =
      quaternionEmbed (star a) := by
  ext <;> simp [doublingUnit, doubledPart, quaternionEmbed, AlbertStep.mul]

theorem doubledPart_mul_doublingUnit (a : Quaternion ℝ) :
    AlbertStep.mul (doubledPart a) doublingUnit =
      quaternionEmbed a := by
  ext <;> simp [doublingUnit, doubledPart, quaternionEmbed, AlbertStep.mul]

theorem doubledPart_mul_quaternionEmbed (a b : Quaternion ℝ) :
    AlbertStep.mul (doubledPart a) (quaternionEmbed b) =
      doubledPart (a * star b) := by
  ext <;> simp [doubledPart, quaternionEmbed, AlbertStep.mul]

theorem quaternionEmbed_mul_doubledPart (a b : Quaternion ℝ) :
    AlbertStep.mul (quaternionEmbed a) (doubledPart b) =
      doubledPart (b * a) := by
  ext <;> simp [doubledPart, quaternionEmbed, AlbertStep.mul]

theorem doubledPart_mul_doubledPart (a b : Quaternion ℝ) :
    AlbertStep.mul (doubledPart a) (doubledPart b) =
      quaternionEmbed (star b * a) := by
  ext <;> simp [doubledPart, quaternionEmbed, AlbertStep.mul]

/-- The split quadratic norm on the real hyperbolic doubling. -/
def splitNorm (x : QuaternionDouble) : ℝ :=
  Quaternion.normSq x.p - Quaternion.normSq x.q

@[simp] theorem splitNorm_zero :
    splitNorm (0 : QuaternionDouble) = 0 := by
  simp [splitNorm]

@[simp] theorem splitNorm_quaternionEmbed (a : Quaternion ℝ) :
    splitNorm (quaternionEmbed a) = Quaternion.normSq a := by
  simp [splitNorm, quaternionEmbed]

@[simp] theorem splitNorm_doubledPart (a : Quaternion ℝ) :
    splitNorm (doubledPart a) = -Quaternion.normSq a := by
  simp [splitNorm, doubledPart]

@[simp] theorem splitNorm_doublingUnit :
    splitNorm doublingUnit = -1 := by
  simp [splitNorm, doublingUnit, Quaternion.normSq_def']

theorem splitNorm_mul (x y : QuaternionDouble) :
    splitNorm (AlbertStep.mul x y) = splitNorm x * splitNorm y := by
  cases x with
  | mk xp xq =>
    cases y with
    | mk yp yq =>
      simp [splitNorm, AlbertStep.mul, Quaternion.normSq_def',
        QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
        QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul]
      ring

theorem quaternionDouble_mul_add (x y z : QuaternionDouble) :
    AlbertStep.mul x (y + z) =
      AlbertStep.mul x y + AlbertStep.mul x z := by
  cases x with
  | mk xp xq =>
    cases y with
    | mk yp yq =>
      cases z with
      | mk zp zq =>
        apply AlbertStep.ext
        · simp [AlbertStep.mul, add_mul, mul_add, smul_add] <;> abel
        · simp [AlbertStep.mul, add_mul, mul_add, smul_add] <;> abel

theorem quaternionDouble_add_mul (x y z : QuaternionDouble) :
    AlbertStep.mul (x + y) z =
      AlbertStep.mul x z + AlbertStep.mul y z := by
  cases x with
  | mk xp xq =>
    cases y with
    | mk yp yq =>
      cases z with
      | mk zp zq =>
        apply AlbertStep.ext
        · simp [AlbertStep.mul, add_mul, mul_add, smul_add] <;> abel
        · simp [AlbertStep.mul, add_mul, mul_add, smul_add] <;> abel

theorem left_alternative (x y : QuaternionDouble) :
    AlbertStep.mul (AlbertStep.mul x x) y =
      AlbertStep.mul x (AlbertStep.mul x y) := by
  cases x with
  | mk a b =>
    cases y with
    | mk c d =>
      have hs : a + star a = (2 * a.re : Quaternion ℝ) := by
        simpa using (Quaternion.self_add_star a)
      have hbs : b * (a + star a) = (a + star a) * b := by
        rw [hs]
        simpa [two_mul] using
          (QuaternionAlgebra.coe_commutes (2 * a.re) b).symm
      have hsb : (a + star a) * star d = star d * (a + star a) := by
        rw [hs]
        simpa [two_mul] using
          (QuaternionAlgebra.coe_commutes (2 * a.re) (star d))
      have hsc : (a + star a) * star c = star c * (a + star a) := by
        rw [hs]
        simpa [two_mul] using
          (QuaternionAlgebra.coe_commutes (2 * a.re) (star c))
      have hba : b * a + b * star a = b * (a + star a) :=
        (mul_add b a (star a)).symm
      have hbb : star b * b =
          (algebraMap ℝ (Quaternion ℝ) (Quaternion.normSq b)) :=
        Quaternion.star_mul_self b
      have hbn : b * star b =
          (algebraMap ℝ (Quaternion ℝ) (Quaternion.normSq b)) :=
        Quaternion.self_mul_star b
      have hnorm_c :
          (algebraMap ℝ (Quaternion ℝ) (Quaternion.normSq b)) * c =
            c * (algebraMap ℝ (Quaternion ℝ) (Quaternion.normSq b)) := by
        exact QuaternionAlgebra.coe_commutes _ _
      have hnorm_d :
          (algebraMap ℝ (Quaternion ℝ) (Quaternion.normSq b)) * d =
            d * (algebraMap ℝ (Quaternion ℝ) (Quaternion.normSq b)) := by
        exact QuaternionAlgebra.coe_commutes _ _
      apply AlbertStep.ext
      · simp only [AlbertStep.mul]
        simp only [one_smul, star_add, star_mul]
        simp only [star_star]
        rw [hba, hbs, ← mul_assoc, ← hsb]
        rw [hbb]
        rw [add_mul (star a * star d) (c * star b) b]
        rw [mul_assoc c (star b) b, hbb]
        rw [add_mul (a * a)
          (algebraMap ℝ (Quaternion ℝ) (Quaternion.normSq b)) c]
        rw [hnorm_c]
        noncomm_ring
      · simp only [AlbertStep.mul]
        simp only [one_smul, star_add, star_mul]
        simp only [star_star]
        rw [hba]
        rw [mul_assoc b (a + star a) (star c), hsc]
        rw [hbb]
        rw [mul_add b (star c * star a) (star b * d)]
        rw [← mul_assoc b (star b) d, hbn]
        rw [hnorm_d]
        noncomm_ring

theorem quaternionI_add_doublingUnit_sq :
    AlbertStep.mul (quaternionEmbed quaternionI + doublingUnit)
        (quaternionEmbed quaternionI + doublingUnit) = 0 := by
  have hI : quaternionI * quaternionI = -1 := by
    ext <;> norm_num [quaternionI, QuaternionAlgebra.re_mul,
      QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
      QuaternionAlgebra.imK_mul]
  rw [quaternionDouble_add_mul]
  rw [quaternionDouble_mul_add
    (quaternionEmbed quaternionI) (quaternionEmbed quaternionI) doublingUnit]
  rw [quaternionDouble_mul_add
    doublingUnit (quaternionEmbed quaternionI) doublingUnit]
  rw [quaternionEmbed_mul, quaternionEmbed_mul_doublingUnit,
    doublingUnit_mul_quaternionEmbed, doublingUnit_sq, hI]
  apply AlbertStep.ext
  · simp [quaternionI, quaternionEmbed, doubledPart, AlbertStep.oneElem]
  · apply QuaternionAlgebra.ext <;>
      simp [quaternionI, quaternionEmbed, doubledPart, AlbertStep.oneElem]

@[simp] theorem splitNorm_quaternionI_add_doublingUnit :
    splitNorm (quaternionEmbed quaternionI + doublingUnit) = 0 := by
  simp [splitNorm, quaternionEmbed, doublingUnit, quaternionI,
    Quaternion.normSq_def']

@[simp] theorem conjugate_quaternionEmbed (a : Quaternion ℝ) :
    AlbertStep.conj (quaternionEmbed a) = quaternionEmbed (star a) := by
  ext <;> simp [AlbertStep.conj, quaternionEmbed]

@[simp] theorem conjugate_doublingUnit :
    AlbertStep.conj doublingUnit = ⟨0, -1⟩ := by
  ext <;> simp [AlbertStep.conj, doublingUnit]

@[simp] theorem conjugate_doubledPart (a : Quaternion ℝ) :
    AlbertStep.conj (doubledPart a) = doubledPart (-a) := by
  ext <;> simp [AlbertStep.conj, doubledPart]

set_option maxHeartbeats 1000000 in
theorem conjugate_mul (x y : QuaternionDouble) :
    AlbertStep.conj (AlbertStep.mul x y) =
      AlbertStep.mul (AlbertStep.conj y) (AlbertStep.conj x) := by
  cases x with
  | mk xp xq =>
    cases y with
    | mk yp yq =>
      ext <;>
        simp [AlbertStep.conj, AlbertStep.mul, star_mul, add_mul, mul_add] <;>
        noncomm_ring

theorem conjugate_injective :
    Function.Injective (AlbertStep.conj : QuaternionDouble → QuaternionDouble) := by
  intro x y h
  have h' := congrArg AlbertStep.conj h
  apply AlbertStep.ext
  · have hp := congrArg AlbertStep.p h'
    simpa [AlbertStep.conj] using hp
  · have hq := congrArg AlbertStep.q h'
    simpa [AlbertStep.conj] using hq

theorem right_alternative (x y : QuaternionDouble) :
    AlbertStep.mul (AlbertStep.mul x y) y =
      AlbertStep.mul x (AlbertStep.mul y y) := by
  apply conjugate_injective
  rw [conjugate_mul, conjugate_mul, conjugate_mul, conjugate_mul]
  exact (left_alternative (AlbertStep.conj y) (AlbertStep.conj x)).symm

theorem quaternion_crossing_law (a : Quaternion ℝ) :
    AlbertStep.mul doublingUnit (quaternionEmbed a) =
      AlbertStep.mul (quaternionEmbed (star a)) doublingUnit := by
  rw [doublingUnit_mul_quaternionEmbed, quaternionEmbed_mul_doublingUnit]

theorem doubledPart_injective :
    Function.Injective doubledPart := by
  intro a b h
  exact congrArg AlbertStep.q h

theorem quaternionEmbed_injective :
    Function.Injective quaternionEmbed := by
  intro a b h
  exact congrArg AlbertStep.p h

theorem quaternionK_ne_neg : quaternionK ≠ -quaternionK := by
  intro h
  have hk := congrArg QuaternionAlgebra.imK h
  norm_num [quaternionK] at hk

theorem doubling_associator_nonzero :
    AlbertStep.mul
        (AlbertStep.mul (quaternionEmbed quaternionI) (quaternionEmbed quaternionJ))
        doublingUnit ≠
      AlbertStep.mul (quaternionEmbed quaternionI)
        (AlbertStep.mul (quaternionEmbed quaternionJ) doublingUnit) := by
  rw [quaternionEmbed_mul, quaternionEmbed_mul_doublingUnit,
    quaternionEmbed_mul_doublingUnit, quaternionEmbed_mul_doubledPart,
    quaternionI_mul_quaternionJ,
    quaternionJ_mul_quaternionI]
  intro h
  apply quaternionK_ne_neg
  exact doubledPart_injective h

end InfoGeometry.Canonical.HestenesHyperbolicDoubling
