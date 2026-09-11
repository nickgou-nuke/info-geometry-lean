import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import InfoGeometry.Canonical.CliffordParityBridge
import InfoGeometry.Canonical.HestenesBivectorCarrier

namespace InfoGeometry.Canonical.HestenesTransportedOddHodge

open CliffordAlgebra
open InfoGeometry.Canonical.CliffordParity
open HasVolumeElement
open InfoGeometry.Canonical.HestenesBivectorCarrier

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M) [HasVolumeElement R M Q] [HasSpacetimeBasis Q]

/-- The transported odd Hodge star maps the odd subalgebra to itself.
    It is defined as R_{gamma_0} ∘ star ∘ R_{gamma_0}^{-1}.
    We implement this assuming Q(gamma_0) = 1, so gamma_0^{-1} = gamma_0. -/
noncomputable def transportedOddHodge (h_time : Q (HasSpacetimeBasis.gamma Q 0) = 1) : evenOdd Q 1 →ₗ[R] evenOdd Q 1 where
  toFun x := ⟨ι Q (HasSpacetimeBasis.gamma Q 0) * CliffordAlgebra.reverse (x.val) * ι Q (HasSpacetimeBasis.gamma Q 0), by
    have h_rev : CliffordAlgebra.reverse (x.val) ∈ evenOdd Q 1 := by
      rw [CliffordAlgebra.reverse_mem_evenOdd_iff]
      exact x.prop
    have h1 := SetLike.mul_mem_graded (ι_mem_evenOdd_one Q (HasSpacetimeBasis.gamma Q 0)) h_rev
    have h2 := SetLike.mul_mem_graded h1 (ι_mem_evenOdd_one Q (HasSpacetimeBasis.gamma Q 0))
    rwa [add_assoc, ←add_assoc (1 : ZMod 2) 1 1, show (1 : ZMod 2) + 1 = 0 from rfl, zero_add] at h2⟩
  map_add' x y := Subtype.ext (by simp [mul_add, add_mul])
  map_smul' c x := Subtype.ext (by simp [Algebra.smul_mul_assoc, Algebra.mul_smul_comm])

/-- The transported odd Hodge star squares to +1 on the odd subalgebra. -/
theorem transportedOddHodge_sq (h_time : Q (HasSpacetimeBasis.gamma Q 0) = 1) (x : evenOdd Q 1) :
    transportedOddHodge R M Q h_time (transportedOddHodge R M Q h_time x) = x := by
  ext
  dsimp [transportedOddHodge]
  have hrev : ∀ a b : CliffordAlgebra Q, reverse (a * b) = reverse b * reverse a := reverse.map_mul
  have hrev_gamma : reverse (ι Q (HasSpacetimeBasis.gamma Q 0)) = ι Q (HasSpacetimeBasis.gamma Q 0) := reverse_ι _
  rw [hrev, hrev, hrev_gamma, reverse_reverse]
  have hq : ι Q (HasSpacetimeBasis.gamma Q 0) * ι Q (HasSpacetimeBasis.gamma Q 0) = 1 := by
    rw [ι_sq_scalar, h_time, RingHom.map_one]
  simp only [← mul_assoc]
  rw [hq, one_mul, mul_assoc, hq, mul_one]

/-- The transported odd Hodge star maps self-adjoint elements to self-adjoint elements. -/
theorem transportedOddHodge_selfAdjoint (h_time : Q (HasSpacetimeBasis.gamma Q 0) = 1) (y : evenOdd Q 1) (hy : CliffordAlgebra.reverse y.val = y.val) :
    CliffordAlgebra.reverse (transportedOddHodge R M Q h_time y).val = (transportedOddHodge R M Q h_time y).val := by
  dsimp [transportedOddHodge]
  have hrev : ∀ a b : CliffordAlgebra Q, reverse (a * b) = reverse b * reverse a := reverse.map_mul
  have hrev_gamma : reverse (ι Q (HasSpacetimeBasis.gamma Q 0)) = ι Q (HasSpacetimeBasis.gamma Q 0) := reverse_ι _
  rw [hrev, hrev, hrev_gamma, reverse_reverse, hy]
  simp only [← mul_assoc]

/-- The transported odd Hodge star maps skew-adjoint elements to skew-adjoint elements. -/
theorem transportedOddHodge_skewAdjoint (h_time : Q (HasSpacetimeBasis.gamma Q 0) = 1) (y : evenOdd Q 1) (hy : CliffordAlgebra.reverse y.val = -y.val) :
    CliffordAlgebra.reverse (transportedOddHodge R M Q h_time y).val = -(transportedOddHodge R M Q h_time y).val := by
  dsimp [transportedOddHodge]
  have hrev : ∀ a b : CliffordAlgebra Q, reverse (a * b) = reverse b * reverse a := reverse.map_mul
  have hrev_gamma : reverse (ι Q (HasSpacetimeBasis.gamma Q 0)) = ι Q (HasSpacetimeBasis.gamma Q 0) := reverse_ι _
  rw [hrev, hrev, hrev_gamma, reverse_reverse, hy, mul_neg, neg_mul]
  simp only [← mul_assoc, neg_neg]

end InfoGeometry.Canonical.HestenesTransportedOddHodge
