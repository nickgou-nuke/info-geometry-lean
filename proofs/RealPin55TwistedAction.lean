import proofs.RealPin55Core
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-! # Twisted vector action of the full real `Pin(5,5)` core -/

noncomputable section
namespace RealPin55TwistedAction

open Clifford55
open RealPin55Core

/-- Faithfulness of the universal Clifford vector inclusion in characteristic
different from two.  The proof uses Mathlib's equivalence with the exterior
algebra and its explicit left inverse on degree one. -/
theorem iota55_injective : Function.Injective ι55 := by
  intro x y h
  apply (ExteriorAlgebra.ι_leftInverse (R := ℝ) (M := V55)).injective
  have h' := congrArg (CliffordAlgebra.equivExterior Q55) h
  simpa [CliffordAlgebra.equivExterior, CliffordAlgebra.changeForm_ι] using h'

/-- Every signature-correct Pin generator is a Lipschitz generator, hence the
whole generated subgroup lies in Mathlib's Lipschitz group. -/
theorem fullPin55_le_lipschitz : FullPin55 ≤ LipschitzGroup55 := by
  rw [FullPin55, LipschitzGroup55, lipschitzGroup, Subgroup.closure_le]
  intro u hu
  rcases hu with ⟨v, _hv, huv⟩
  apply Subgroup.subset_closure
  change (u : Cl55) ∈ Set.range ι55
  exact ⟨v, huv.symm⟩

theorem twisted_clifford_mem_range (g : FullPin55) (v : V55) :
    CliffordAlgebra.involute (g.1 : Cl55) * ι55 v *
        ((g.1⁻¹ : Cl55ˣ) : Cl55) ∈ LinearMap.range ι55 :=
  lipschitzGroup.involute_act_ι_mem_range_ι
    (fullPin55_le_lipschitz g.2) v

/-- The unique vector represented by twisted Clifford conjugation. -/
def twistedVector (g : FullPin55) (v : V55) : V55 :=
  Classical.choose (twisted_clifford_mem_range g v)

theorem iota_twistedVector (g : FullPin55) (v : V55) :
    ι55 (twistedVector g v) =
      CliffordAlgebra.involute (g.1 : Cl55) * ι55 v *
        ((g.1⁻¹ : Cl55ˣ) : Cl55) :=
  Classical.choose_spec (twisted_clifford_mem_range g v)

/-- Twisted conjugation is linear on the real vector carrier. -/
def twistedVectorLinear (g : FullPin55) : V55 →ₗ[ℝ] V55 where
  toFun := twistedVector g
  map_add' v w := by
    apply iota55_injective
    rw [map_add, iota_twistedVector, iota_twistedVector,
      iota_twistedVector, map_add]
    noncomm_ring
  map_smul' c v := by
    apply iota55_injective
    rw [map_smul, iota_twistedVector, iota_twistedVector, map_smul]
    simp only [RingHom.id_apply, Algebra.smul_def]
    calc
      CliffordAlgebra.involute (g.1 : Cl55) *
            ((algebraMap ℝ Cl55) c * ι55 v) * ((g.1⁻¹ : Cl55ˣ) : Cl55) =
          (((CliffordAlgebra.involute (g.1 : Cl55) *
            (algebraMap ℝ Cl55) c) * ι55 v) *
              ((g.1⁻¹ : Cl55ˣ) : Cl55)) := by rw [← mul_assoc]
      _ = ((((algebraMap ℝ Cl55) c *
            CliffordAlgebra.involute (g.1 : Cl55)) * ι55 v) *
              ((g.1⁻¹ : Cl55ˣ) : Cl55)) := by
            rw [Algebra.commutes c (CliffordAlgebra.involute (g.1 : Cl55))]
      _ = (algebraMap ℝ Cl55) c *
          (CliffordAlgebra.involute (g.1 : Cl55) * ι55 v *
            ((g.1⁻¹ : Cl55ˣ) : Cl55)) := by simp [mul_assoc]

@[simp] theorem twistedVector_one (v : V55) :
    twistedVector (1 : FullPin55) v = v := by
  apply iota55_injective
  rw [iota_twistedVector]
  simp

theorem twistedVector_mul (g h : FullPin55) (v : V55) :
    twistedVector (g * h) v = twistedVector g (twistedVector h v) := by
  apply iota55_injective
  rw [iota_twistedVector, iota_twistedVector, iota_twistedVector]
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
  noncomm_ring

theorem twistedVectorLinear_mul (g h : FullPin55) :
    twistedVectorLinear (g * h) =
      (twistedVectorLinear g).comp (twistedVectorLinear h) := by
  apply LinearMap.ext
  intro v
  exact twistedVector_mul g h v

/-- Every twisted vector action is invertible; the inverse is the action of
the inverse Pin word. -/
def twistedVectorEquiv (g : FullPin55) : V55 ≃ₗ[ℝ] V55 where
  toLinearMap := twistedVectorLinear g
  invFun := twistedVectorLinear g⁻¹
  left_inv v := by
    have h := twistedVector_mul g⁻¹ g v
    change twistedVector g⁻¹ (twistedVector g v) = v
    simpa using h.symm
  right_inv v := by
    have h := twistedVector_mul g g⁻¹ v
    change twistedVector g (twistedVector g⁻¹ v) = v
    simpa using h.symm

@[simp] theorem twistedVectorEquiv_apply (g : FullPin55) (v : V55) :
    twistedVectorEquiv g v = twistedVector g v := rfl

/-- The signature-correct Pin core acts natively by real linear
automorphisms of the ten-dimensional vector carrier. -/
def fullPinVectorRepresentation : FullPin55 →* (V55 ≃ₗ[ℝ] V55) where
  toFun := twistedVectorEquiv
  map_one' := by
    apply LinearEquiv.ext
    intro v
    exact twistedVector_one v
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    exact twistedVector_mul g h v

theorem fullPinVectorRepresentation_apply (g : FullPin55) (v : V55) :
    fullPinVectorRepresentation g v = twistedVector g v := rfl

end RealPin55TwistedAction
end noncomputable section
