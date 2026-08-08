import InfoGeometry.Canonical.TensorColimitExpectation
import InfoGeometry.Canonical.Cl11MarkovJonesCompatibleFunctionalFamily
import InfoGeometry.Clifford.Cl11TensorTowerLimit

/-!
# Algebraic tensor-inductive-limit property for the `Cl(1,1)` tower

The concrete direct-limit carrier already owned by
`Cl11TensorTowerLimit` is packaged as the repository's
`TensorInductiveLimit`.  The final functional remains conditional: an
extending linear functional must be supplied before stage trace recovery can
be stated.  No completed UHF algebra or global KMS state is postulated here.
-/

noncomputable section

namespace InfoGeometry.Canonical.Cl11TensorInductiveLimitWitness

open InfoGeometry.Canonical.TensorColimitExpectation
open InfoGeometry.Canonical.Cl11MarkovJonesCompatibleFunctionalFamily
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Clifford.Cl11TensorTowerLimit

abbrev Stage (n : ℕ) : Type := MatStage n
abbrev Limit : Type := InfoGeometry.Clifford.Cl11TensorTowerLimit.Limit

noncomputable def ofStageAlgHom (n : ℕ) :
    Stage n →ₐ[ℝ] Limit where
  toFun := ofStage n
  map_one' := map_one (ofStage n)
  map_mul' A B := map_mul (ofStage n) A B
  map_zero' := map_zero (ofStage n)
  map_add' A B := map_add (ofStage n) A B
  commutes' r := by
    change ofStage n (algebraMap ℝ (Stage n) r) = realAlgebraMap r
    exact (realAlgebraMap_stage n r).symm

noncomputable def cl11TensorInductiveLimit :
    TensorInductiveLimit
      (R := ℝ) (A := Stage) (fun n => stageEmbed n) where
  AInf := Limit
  instSemiring := inferInstance
  instAlgebra := inferInstance
  inj := ofStageAlgHom
  inj_compat := by
    intro n A
    exact ofStage_apply_bond n A

theorem cl11_limit_functional_recovers_trace
    (Ω : cl11TensorInductiveLimit.LimitFunctional)
    (hΩ : cl11TensorInductiveLimit.ExtendsFamily
      cl11CompatibleFunctionalFamily Ω)
    (n : ℕ) (A : Stage n) :
    Ω (cl11TensorInductiveLimit.inj n A) =
      cl11CompatibleFunctionalFamily n A := by
  exact TensorInductiveLimit.limit_functional_recovers_stage
    cl11TensorInductiveLimit cl11CompatibleFunctionalFamily Ω hΩ n A

theorem cl11_limit_functional_recovers_normalized_trace
    (Ω : cl11TensorInductiveLimit.LimitFunctional)
    (hΩ : cl11TensorInductiveLimit.ExtendsFamily
      cl11CompatibleFunctionalFamily Ω)
    (n : ℕ) (A : Stage n) :
    Ω (cl11TensorInductiveLimit.inj n A) = normalizedTrace n A := by
  rw [cl11_limit_functional_recovers_trace Ω hΩ n A]
  rfl

end InfoGeometry.Canonical.Cl11TensorInductiveLimitWitness

end
