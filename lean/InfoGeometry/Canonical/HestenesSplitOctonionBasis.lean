import InfoGeometry.Canonical.HestenesHyperbolicDoubling
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

namespace InfoGeometry.Canonical.HestenesSplitOctonionBasis

open InfoGeometry.Canonical.HestenesHyperbolicDoubling
open InfoGeometry.Canonical.AlbertCayleyDickson

abbrev Carrier := QuaternionDouble

/-!
The eight coordinate directions of the split Cayley--Dickson carrier.  The
native `Module.Basis` below is obtained from the explicit coordinate
equivalence; the labelled map is retained as the computational interface.
-/
def sageBasisVector : Fin 8 → Carrier :=
  ![ quaternionEmbed 1
   , quaternionEmbed quaternionI
   , quaternionEmbed quaternionJ
   , quaternionEmbed quaternionK
   , doublingUnit
   , doubledPart quaternionI
   , doubledPart quaternionJ
   , doubledPart quaternionK ]

noncomputable def coordinateEquiv : Carrier ≃ₗ[ℝ] Fin 8 → ℝ where
  toFun x := ![x.p.re, x.p.imI, x.p.imJ, x.p.imK,
    x.q.re, x.q.imI, x.q.imJ, x.q.imK]
  invFun v :=
    ⟨⟨v 0, v 1, v 2, v 3⟩, ⟨v 4, v 5, v 6, v 7⟩⟩
  left_inv := by
    intro x
    cases x with
    | mk p q =>
      cases p with
      | mk pre pi pj pk =>
        cases q with
        | mk qre qi qj qk =>
          rfl
  right_inv := by
    intro v
    funext i
    fin_cases i <;> rfl
  map_add' := by
    intro x y
    funext i
    fin_cases i <;> simp
  map_smul' := by
    intro a x
    funext i
    fin_cases i <;> simp

noncomputable def sageBasis : Module.Basis (Fin 8) ℝ Carrier :=
  Module.Basis.ofEquivFun coordinateEquiv

@[simp] theorem sageBasis_apply (i : Fin 8) :
    sageBasis i = sageBasisVector i := by
  fin_cases i <;>
    simp [sageBasis, Module.Basis.coe_ofEquivFun, coordinateEquiv,
      sageBasisVector, quaternionEmbed, doubledPart, doublingUnit,
      quaternionI, quaternionJ, quaternionK] <;>
    constructor <;>
      apply QuaternionAlgebra.ext <;>
      norm_num

@[simp] theorem sageBasisVector_zero :
    sageBasisVector 0 = quaternionEmbed 1 := by
  rfl

@[simp] theorem sageBasisVector_one :
    sageBasisVector 1 = quaternionEmbed quaternionI := by
  rfl

@[simp] theorem sageBasisVector_two :
    sageBasisVector 2 = quaternionEmbed quaternionJ := by
  rfl

@[simp] theorem sageBasisVector_three :
    sageBasisVector 3 = quaternionEmbed quaternionK := by
  rfl

@[simp] theorem sageBasisVector_four :
    sageBasisVector 4 = doublingUnit := by
  rfl

@[simp] theorem sageBasisVector_five :
    sageBasisVector 5 = doubledPart quaternionI := by
  rfl

@[simp] theorem sageBasisVector_six :
    sageBasisVector 6 = doubledPart quaternionJ := by
  rfl

@[simp] theorem sageBasisVector_seven :
    sageBasisVector 7 = doubledPart quaternionK := by
  rfl

theorem sageBasisVector_injective :
    Function.Injective sageBasisVector := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals
    have hp := congrArg (fun x : Carrier => x.p.re) h
    have hpi := congrArg (fun x : Carrier => x.p.imI) h
    have hpj := congrArg (fun x : Carrier => x.p.imJ) h
    have hpk := congrArg (fun x : Carrier => x.p.imK) h
    have hq := congrArg (fun x : Carrier => x.q) h
    have hqr := congrArg QuaternionAlgebra.re hq
    have hqi := congrArg QuaternionAlgebra.imI hq
    have hqj := congrArg QuaternionAlgebra.imJ hq
    all_goals try norm_num [sageBasisVector, quaternionEmbed, doubledPart,
      doublingUnit, quaternionI, quaternionJ, quaternionK] at hp
    all_goals try norm_num [sageBasisVector, quaternionEmbed, doubledPart,
      doublingUnit, quaternionI, quaternionJ, quaternionK] at hpi
    all_goals try norm_num [sageBasisVector, quaternionEmbed, doubledPart,
      doublingUnit, quaternionI, quaternionJ, quaternionK] at hpj
    all_goals try norm_num [sageBasisVector, quaternionEmbed, doubledPart,
      doublingUnit, quaternionI, quaternionJ, quaternionK] at hpk
    all_goals try norm_num [sageBasisVector, quaternionEmbed, doubledPart,
      doublingUnit, quaternionI, quaternionJ, quaternionK] at hqr
    all_goals try norm_num [sageBasisVector, quaternionEmbed, doubledPart,
      doublingUnit, quaternionI, quaternionJ, quaternionK] at hqi
    all_goals try norm_num [sageBasisVector, quaternionEmbed, doubledPart,
      doublingUnit, quaternionI, quaternionJ, quaternionK] at hqj

theorem doublingUnit_mul_quaternionI_basis :
    AlbertStep.mul doublingUnit (sageBasisVector 1) =
      doubledPart (star quaternionI) := by
  simpa [sageBasisVector] using doublingUnit_mul_quaternionEmbed quaternionI

theorem doublingUnit_mul_quaternionJ_basis :
    AlbertStep.mul doublingUnit (sageBasisVector 2) =
      doubledPart (star quaternionJ) := by
  simpa [sageBasisVector] using doublingUnit_mul_quaternionEmbed quaternionJ

theorem doublingUnit_mul_quaternionK_basis :
    AlbertStep.mul doublingUnit (sageBasisVector 3) =
      doubledPart (star quaternionK) := by
  simpa [sageBasisVector] using doublingUnit_mul_quaternionEmbed quaternionK

theorem quaternionI_basis_mul_doublingUnit :
    AlbertStep.mul (sageBasisVector 1) doublingUnit = sageBasisVector 5 := by
  simpa [sageBasisVector] using quaternionEmbed_mul_doublingUnit quaternionI

theorem quaternionJ_basis_mul_doublingUnit :
    AlbertStep.mul (sageBasisVector 2) doublingUnit = sageBasisVector 6 := by
  simpa [sageBasisVector] using quaternionEmbed_mul_doublingUnit quaternionJ

theorem quaternionK_basis_mul_doublingUnit :
    AlbertStep.mul (sageBasisVector 3) doublingUnit = sageBasisVector 7 := by
  simpa [sageBasisVector] using quaternionEmbed_mul_doublingUnit quaternionK

theorem sageBasisVector_one_mul_two :
    AlbertStep.mul (sageBasisVector 1) (sageBasisVector 2) = sageBasisVector 3 := by
  calc
    AlbertStep.mul (sageBasisVector 1) (sageBasisVector 2) =
        quaternionEmbed (quaternionI * quaternionJ) := by
      simpa [sageBasisVector] using quaternionEmbed_mul quaternionI quaternionJ
    _ = sageBasisVector 3 := by
      rw [quaternionI_mul_quaternionJ]
      rfl

theorem sageBasisVector_two_mul_one :
    AlbertStep.mul (sageBasisVector 2) (sageBasisVector 1) =
      quaternionEmbed (-quaternionK) := by
  calc
    AlbertStep.mul (sageBasisVector 2) (sageBasisVector 1) =
        quaternionEmbed (quaternionJ * quaternionI) := by
      simpa [sageBasisVector] using quaternionEmbed_mul quaternionJ quaternionI
    _ = quaternionEmbed (-quaternionK) := by rw [quaternionJ_mul_quaternionI]

theorem sageBasisVector_four_sq :
    AlbertStep.mul (sageBasisVector 4) (sageBasisVector 4) =
      sageBasisVector 0 := by
  simpa [sageBasisVector, quaternionEmbed] using doublingUnit_sq

end InfoGeometry.Canonical.HestenesSplitOctonionBasis
