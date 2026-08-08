import proofs.ClPlus14DualProduct
import proofs.ZornCore

/-!
# Quaternionic split doubling to the canonical real Zorn carrier

The signs are fixed by the multiplication theorem below.  No algebraic
structure is inferred from dimension alone.
-/

noncomputable section
namespace HestenesSplitOctonionZornBridge

open HestenesHyperbolicDoubling

abbrev SplitDouble := HestenesHyperbolicDoubling.Carrier
abbrev HRot := Quaternion ℝ
abbrev Zorn := ZornCore.Zorn
abbrev Vec3 := ZornCore.Vec3

def imagVec (q : HRot) : Vec3 := ![q.imI, q.imJ, q.imK]

def quaternionOf (r : ℝ) (v : Vec3) : HRot :=
  ⟨r, v 0, v 1, v 2⟩

/-- Coordinate map
`(a,b) ↦ [[a₀+b₀, -Im(a)+Im(b)], [Im(a)+Im(b), a₀-b₀]]`. -/
def doubleToZorn (x : SplitDouble) : Zorn where
  a := x.1.re + x.2.re
  u := -imagVec x.1 + imagVec x.2
  v := imagVec x.1 + imagVec x.2
  b := x.1.re - x.2.re

def zornToDouble (X : Zorn) : SplitDouble :=
  (quaternionOf ((X.a + X.b) / 2) ((X.v - X.u) / 2),
   quaternionOf ((X.a - X.b) / 2) ((X.u + X.v) / 2))

theorem zornToDouble_doubleToZorn (x : SplitDouble) :
    zornToDouble (doubleToZorn x) = x := by
  rcases x with ⟨p, q⟩
  apply Prod.ext <;> apply QuaternionAlgebra.ext <;>
    simp [zornToDouble, doubleToZorn, quaternionOf, imagVec] <;> ring

theorem doubleToZorn_zornToDouble (X : Zorn) :
    doubleToZorn (zornToDouble X) = X := by
  apply ZornCore.Zorn.ext'
  · simp [doubleToZorn, zornToDouble, quaternionOf, imagVec]
    ring
  · funext i
    fin_cases i <;> simp [doubleToZorn, zornToDouble, quaternionOf, imagVec] <;> ring
  · funext i
    fin_cases i <;> simp [doubleToZorn, zornToDouble, quaternionOf, imagVec] <;> ring
  · simp [doubleToZorn, zornToDouble, quaternionOf, imagVec]
    ring

def splitDoubleZornEquiv : SplitDouble ≃ Zorn where
  toFun := doubleToZorn
  invFun := zornToDouble
  left_inv := zornToDouble_doubleToZorn
  right_inv := doubleToZorn_zornToDouble

theorem doubleToZorn_add (x y : SplitDouble) :
    doubleToZorn (x + y) = doubleToZorn x + doubleToZorn y := by
  apply ZornCore.Zorn.ext'
  · simp [doubleToZorn]; ring
  · funext i; fin_cases i <;> simp [doubleToZorn, imagVec] <;> ring
  · funext i; fin_cases i <;> simp [doubleToZorn, imagVec] <;> ring
  · simp [doubleToZorn]; ring

theorem doubleToZorn_smul (r : ℝ) (x : SplitDouble) :
    doubleToZorn (r • x) = r • doubleToZorn x := by
  apply ZornCore.Zorn.ext'
  · simp [doubleToZorn]; ring
  · funext i; fin_cases i <;> simp [doubleToZorn, imagVec] <;> ring
  · funext i; fin_cases i <;> simp [doubleToZorn, imagVec] <;> ring
  · simp [doubleToZorn]; ring

set_option maxHeartbeats 1000000 in
/-- The quaternionic split Cayley--Dickson table is exactly the canonical
real Zorn multiplication table. -/
theorem doubleToZorn_mul (x y : SplitDouble) :
    doubleToZorn (x * y) = doubleToZorn x * doubleToZorn y := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  apply ZornCore.Zorn.ext'
  · simp [doubleToZorn, imagVec, ZornCore.dot, ZornCore.cross,
      Fin.sum_univ_three, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]
    ring
  · funext i
    fin_cases i <;>
      simp [doubleToZorn, imagVec, ZornCore.dot, ZornCore.cross,
        Fin.sum_univ_three, Quaternion.re_mul, Quaternion.imI_mul,
        Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring
  · funext i
    fin_cases i <;>
      simp [doubleToZorn, imagVec, ZornCore.dot, ZornCore.cross,
        Fin.sum_univ_three, Quaternion.re_mul, Quaternion.imI_mul,
        Quaternion.imJ_mul, Quaternion.imK_mul] <;> ring
  · simp [doubleToZorn, imagVec, ZornCore.dot, ZornCore.cross,
      Fin.sum_univ_three, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul]
    ring

theorem clPlus_splitProduct_toZorn (x y : ClPlus14DualProduct.EvenAlgebra) :
    doubleToZorn
        (ClPlus14DualProduct.clPlusDoubleLinearEquiv
          (ClPlus14DualProduct.splitProduct x y)) =
      doubleToZorn (ClPlus14DualProduct.clPlusDoubleLinearEquiv x) *
        doubleToZorn (ClPlus14DualProduct.clPlusDoubleLinearEquiv y) := by
  rw [ClPlus14DualProduct.splitProduct_map, doubleToZorn_mul]

theorem full_split_octonion_transport_packet :
    Function.Bijective doubleToZorn ∧
      (∀ x y, doubleToZorn (x * y) = doubleToZorn x * doubleToZorn y) := by
  exact ⟨splitDoubleZornEquiv.bijective, doubleToZorn_mul⟩

end HestenesSplitOctonionZornBridge
end noncomputable section
