import InfoGeometry.Canonical.HestenesHyperbolicDoubling

/-!
# Two products on the same eight-dimensional real carrier

`QuaternionDouble` carries both the central associative doubling product and
the conjugation-twisted Albert product.  This owner records the distinction
constructively; it does not identify the two products or install a second
algebra instance.
-/

noncomputable section

namespace InfoGeometry.Canonical.ClPlus14DualProduct

open InfoGeometry.Canonical.AlbertCayleyDickson
open InfoGeometry.Canonical.HestenesHyperbolicDoubling

abbrev Carrier := QuaternionDouble

def centralMul (x y : Carrier) : Carrier :=
  ⟨x.p * y.p + x.q * y.q,
    x.p * y.q + x.q * y.p⟩

def twistedMul (x y : Carrier) : Carrier :=
  AlbertStep.mul x y

theorem centralMul_assoc (x y z : Carrier) :
    centralMul (centralMul x y) z = centralMul x (centralMul y z) := by
  ext <;> simp [centralMul] <;> noncomm_ring

theorem centralMul_one_left (x : Carrier) :
    centralMul (AlbertStep.oneElem) x = x := by
  ext <;> simp [centralMul, AlbertStep.oneElem]

theorem centralMul_one_right (x : Carrier) :
    centralMul x (AlbertStep.oneElem) = x := by
  ext <;> simp [centralMul, AlbertStep.oneElem]

theorem centralMul_doublingUnit_mul_quaternionEmbed (a : Quaternion ℝ) :
    centralMul doublingUnit (quaternionEmbed a) = doubledPart a := by
  ext <;> simp [centralMul, doublingUnit, quaternionEmbed, doubledPart]

theorem centralMul_doublingUnit_sq :
    centralMul doublingUnit doublingUnit = AlbertStep.oneElem := by
  ext <;> simp [centralMul, doublingUnit, AlbertStep.oneElem]

theorem twistedMul_doublingUnit_mul_quaternionEmbed (a : Quaternion ℝ) :
    twistedMul doublingUnit (quaternionEmbed a) = doubledPart (star a) := by
  exact doublingUnit_mul_quaternionEmbed a

theorem quaternionI_ne_neg : quaternionI ≠ -quaternionI := by
  intro h
  have hi := congrArg QuaternionAlgebra.imI h
  norm_num [quaternionI] at hi

theorem centralMul_ne_twistedMul :
    centralMul doublingUnit (quaternionEmbed quaternionI) ≠
      twistedMul doublingUnit (quaternionEmbed quaternionI) := by
  rw [centralMul_doublingUnit_mul_quaternionEmbed,
    twistedMul_doublingUnit_mul_quaternionEmbed]
  have hstar : star quaternionI = -quaternionI := by
    ext <;>
      simp [Quaternion.instStar,
        QuaternionAlgebra.instStarQuaternionAlgebra, quaternionI]
  rw [hstar]
  intro h
  exact quaternionI_ne_neg (doubledPart_injective h)

theorem products_are_distinct :
    centralMul ≠ twistedMul := by
  intro h
  have hpoint := congrFun (congrFun h doublingUnit) (quaternionEmbed quaternionI)
  exact centralMul_ne_twistedMul hpoint

end InfoGeometry.Canonical.ClPlus14DualProduct
