import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dimension.Constructions
import proofs.V55Fin10Coordinates

/-! # PBW basis and dimension of the real split Clifford algebra `Cl(5,5)` -/

noncomputable section
namespace Clifford55PBWFinrank

open scoped DirectSum

open Clifford55
open V55Fin10Coordinates

/-- The dependent union of fixed-cardinality subsets of `Fin 10` is the
type of all finite subsets. -/
def sigmaPowersetCardFin10Equiv :
    (Σ n : ℕ, Set.powersetCard (Fin 10) n) ≃ Finset (Fin 10) where
  toFun x := x.2.1
  invFun s := ⟨s.card, ⟨s, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨n, s, hs⟩
    subst n
    rfl
  right_inv s := rfl

/-- The exterior-algebra basis obtained by joining the native bases of all
homogeneous exterior powers of the fixed `(5,5)` coordinate basis. -/
def exteriorAlgebraV55Basis :
    Module.Basis (Finset (Fin 10)) ℝ (ExteriorAlgebra ℝ V55) := by
  let homogeneousBasis :
      Module.Basis (Σ n : ℕ, Set.powersetCard (Fin 10) n) ℝ
        (⨁ n : ℕ, ExteriorAlgebra.exteriorPower ℝ n V55) :=
    DFinsupp.basis (fun n => fin10Basis55.exteriorPower n)
  let transported := homogeneousBasis.map
    (DirectSum.decomposeLinearEquiv
      (fun n : ℕ => ExteriorAlgebra.exteriorPower ℝ n V55)).symm
  exact transported.reindex sigmaPowersetCardFin10Equiv

/-- The full exterior algebra on the ten-dimensional real `(5,5)` carrier
has dimension `2^10 = 1024`. -/
theorem exteriorAlgebra_v55_finrank :
    Module.finrank ℝ (ExteriorAlgebra ℝ V55) = 1024 := by
  rw [Module.finrank_eq_card_basis exteriorAlgebraV55Basis]
  rw [Fintype.card_finset, Fintype.card_fin]
  norm_num

/-- The native PBW basis of `Cl(5,5)`, transported from the exterior algebra
through Mathlib's characteristic-not-two PBW equivalence. -/
def cliffordAlgebra55Basis :
    Module.Basis (Finset (Fin 10)) ℝ Cl55 :=
  exteriorAlgebraV55Basis.map
    (CliffordAlgebra.equivExterior Q55).symm

/-- Native PBW dimension of the real split Clifford algebra `Cl(5,5)`. -/
theorem cliffordAlgebra55_finrank :
    Module.finrank ℝ Cl55 = 1024 := by
  rw [LinearEquiv.finrank_eq (CliffordAlgebra.equivExterior Q55)]
  exact exteriorAlgebra_v55_finrank

/-- The PBW basis supplies the finite-dimensional instance used by the exact
kernel calculation. -/
noncomputable instance : FiniteDimensional ℝ Cl55 :=
  cliffordAlgebra55Basis.finiteDimensional_of_finite

end Clifford55PBWFinrank
end noncomputable section
