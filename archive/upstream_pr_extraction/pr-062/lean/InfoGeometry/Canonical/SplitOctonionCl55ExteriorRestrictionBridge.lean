import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic
import InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
import InfoGeometry.Clifford.Clifford55
import InfoGeometry.Clifford.Cl55ThreeColorChiralGenerators

/-!
# Three-mode exterior restriction inside the `Cl(5,5)` exterior shadow

The three-dimensional Hestenes/exterior carrier embeds into the first three
positive Witt coordinates of the five-mode exterior carrier.  The embedding is
split by an explicit coordinate projection, so the induced exterior-algebra
map is injective by Mathlib's native retraction theorem.

This is a carrier-level cross-tower bridge.  It does not identify the
nonassociative split-octonion product with Clifford multiplication, nor does it
assert an exceptional Lie-algebra representation on the five-mode carrier.
-/

noncomputable section

namespace InfoGeometry.Canonical.SplitOctonionCl55ExteriorRestrictionBridge

open InfoGeometry.Canonical.SplitOctonionExterior3HodgeDiracBridge
open InfoGeometry.Clifford.Clifford55

abbrev V5 := Fin 5 → ℝ
abbrev Exterior5 := ExteriorAlgebra ℝ V55

def embedV5 (v : V3) : V5 :=
  fun j => if h : j.val < 3 then v ⟨j.val, h⟩ else 0

def projectV3 (w : V5) : V3 :=
  fun i => w (Fin.castAdd 2 i)

def basisVector3 (i : Fin 3) : V3 :=
  fun j => if j = i then 1 else 0

def threeToFive : V3 →ₗ[ℝ] V55 where
  toFun v := (embedV5 v, fun j => -embedV5 v j)
  map_add' v w := by
    apply Prod.ext
    · funext j
      by_cases h : j.val < 3
      · simp [embedV5, h, add_comm]
      · simp [embedV5, h]
    · funext j
      by_cases h : j.val < 3
      · simp [embedV5, h, add_comm]
      · simp [embedV5, h]
  map_smul' c v := by
    ext j <;> simp [embedV5]

def fiveToThree : V55 →ₗ[ℝ] V3 where
  toFun z := projectV3 z.1
  map_add' z w := by
    ext i
    rfl
  map_smul' c z := by
    ext i
    rfl

theorem fiveToThree_threeToFive :
    fiveToThree.comp threeToFive = LinearMap.id := by
  apply LinearMap.ext
  intro v
  ext i
  simp [fiveToThree, projectV3, threeToFive, embedV5]

theorem embedV5_basisVector3 (i : Fin 3) :
    embedV5 (basisVector3 i) =
      fun j => if j = Fin.castAdd 2 i then 1 else 0 := by
  classical
  funext j
  by_cases hij : j = Fin.castAdd 2 i
  · subst j
    simp [embedV5, basisVector3]
  · by_cases hlt : j.val < 3
    · have hneq : (⟨j.val, hlt⟩ : Fin 3) ≠ i := by
        intro h
        have hv : j.val = i.val := congrArg Fin.val h
        exact hij (Fin.ext (by simpa using hv))
      simp [embedV5, basisVector3, hlt, hneq, hij]
    · simp [embedV5, basisVector3, hlt, hij]

theorem threeToFive_basisVector3 (i : Fin 3) :
    threeToFive (basisVector3 i) = nbar_pair (Fin.castAdd 2 i) := by
  classical
  rw [show threeToFive (basisVector3 i) =
      (embedV5 (basisVector3 i), fun j => -embedV5 (basisVector3 i) j) by rfl]
  rw [embedV5_basisVector3]
  apply Prod.ext <;> funext j <;>
    simp [nbar_pair, e_pos, f_neg]

noncomputable def exterior3ToExterior5 : Exterior3 →ₐ[ℝ] Exterior5 :=
  ExteriorAlgebra.map threeToFive

theorem exterior3ToExterior5_injective :
    Function.Injective exterior3ToExterior5 := by
  apply ExteriorAlgebra.map_injective
  exact ⟨fiveToThree, fiveToThree_threeToFive⟩

@[simp] theorem exterior3ToExterior5_generator (v : V3) :
    exterior3ToExterior5 (ExteriorAlgebra.ι ℝ v) =
      ExteriorAlgebra.ι ℝ (threeToFive v) := by
  simp [exterior3ToExterior5]

@[simp] theorem exterior3ToExterior5_mul (x y : Exterior3) :
    exterior3ToExterior5 (x * y) =
      exterior3ToExterior5 x * exterior3ToExterior5 y := by
  exact map_mul (exterior3ToExterior5) x y

@[simp] theorem exterior3ToExterior5_one :
    exterior3ToExterior5 (1 : Exterior3) = 1 := by
  exact map_one (exterior3ToExterior5)

noncomputable def exterior3ToCl55Carrier :
    Exterior3 →ₗ[ℝ] Cl55 :=
  cl55ExteriorEquiv.symm.toLinearMap.comp
    exterior3ToExterior5.toLinearMap

theorem exterior3ToCl55Carrier_injective :
    Function.Injective exterior3ToCl55Carrier := by
  intro x y h
  apply exterior3ToExterior5_injective
  have h' := congrArg cl55ExteriorEquiv h
  simpa [exterior3ToCl55Carrier] using h'

theorem exterior3ToCl55Carrier_generator (v : V3) :
    exterior3ToCl55Carrier (ExteriorAlgebra.ι ℝ v) =
      ι55 (threeToFive v) := by
  apply cl55ExteriorEquiv.injective
  simp [exterior3ToCl55Carrier, cl55ExteriorEquiv_ι]

theorem exterior3ToCl55Carrier_basis_generator (i : Fin 3) :
    exterior3ToCl55Carrier (ExteriorAlgebra.ι ℝ (basisVector3 i)) =
      (2 : ℝ) • chiralPlus55 i := by
  rw [exterior3ToCl55Carrier_generator, threeToFive_basisVector3]
  change ι55 (nbar_pair (Fin.castAdd 2 i)) =
    (2 : ℝ) • ((1 / 2 : ℝ) • ι55 (nbar_pair (Fin.castAdd 2 i)))
  rw [smul_smul]
  norm_num

theorem exterior3ToExterior5_retraction_on_generators (v : V3) :
    ExteriorAlgebra.map fiveToThree
        (exterior3ToExterior5 (ExteriorAlgebra.ι ℝ v)) =
      ExteriorAlgebra.ι ℝ v := by
  rw [exterior3ToExterior5_generator, ExteriorAlgebra.map_apply_ι]
  have h := congrArg (fun F : V3 →ₗ[ℝ] V3 => F v) fiveToThree_threeToFive
  rw [show fiveToThree (threeToFive v) = v by simpa using h]

end InfoGeometry.Canonical.SplitOctonionCl55ExteriorRestrictionBridge
