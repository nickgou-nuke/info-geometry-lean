import InfoGeometry.Algebra.SupergradedBracket
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.BottPeriodicity
import InfoGeometry.Clifford.CartanInstance
import InfoGeometry.Clifford.SplitQ11ChiralDecomposition

/-!
# InfoGeometry.Clifford.BottSupergradedCartanBridge

A theorem-safe bridge for the combined lane the user described:

* split Bott periodicity on `Cl(n,n)`;
* supergraded bracket transport along the Bott step;
* chiral split decomposition in `Cl(1,1)`;
* involutive Cartan decomposition on the matrix tower.

Nothing here asserts a new completion theorem.  It only packages the owned
finite algebraic surfaces so they can be read together.
-/

set_option autoImplicit false

noncomputable section

open scoped Matrix

namespace InfoGeometry.Clifford.BottSupergradedCartanBridge

open InfoGeometry.Algebra.SupergradedBracket
open InfoGeometry.Clifford.BottPeriodicity
open InfoGeometry.Clifford.CartanInstance
open InfoGeometry.Clifford.SplitQ11ChiralDecomposition
open InfoGeometry.Clifford.SplitQ11PhaseFlip

/-- The split Bott step preserves parity-controlled superbrackets. -/
theorem splitBottStep_superBracket_map
    (n : ℕ) (px py : Bool)
    (a b : SplitBottClifford (n + 1)) :
    splitBottStep n (superBracket px py a b) =
      superBracket px py (splitBottStep n a) (splitBottStep n b) := by
  exact map_superBracket (splitBottStep n).toRingHom px py a b

/-- The owner `Cl(n+1,n+1)` step enjoys the same superbracket transport. -/
theorem clsplit_succ_equiv_superBracket_map
    (n : ℕ) (px py : Bool)
    (a b : SplitBottClifford (n + 1)) :
    InfoGeometry.CliffordTower.clsplit_succ_equiv n (superBracket px py a b) =
      superBracket px py (InfoGeometry.CliffordTower.clsplit_succ_equiv n a)
        (InfoGeometry.CliffordTower.clsplit_succ_equiv n b) := by
  simpa [InfoGeometry.Clifford.BottPeriodicity.splitBottStep_eq_clsplit_succ_equiv] using
    (splitBottStep_superBracket_map (n := n) (px := px) (py := py) (a := a) (b := b))

/-- The split Bott step, chiral split, and Cartan involution can be read together. -/
theorem supergraded_bott_chiral_cartan_packet
    (n : ℕ) (px py : Bool) (a b : SplitBottClifford (n + 1))
    (x : InfoGeometry.Clifford.SplitQ11PhaseFlip.Alg)
    (J1 : Matrix (Fin 2) (Fin 2) ℝ) (hJ1_sq : J1 * J1 = 1) (hJ1t : J1ᵀ = J1) :
    (splitBottStep n (superBracket px py a b) =
      superBracket px py (splitBottStep n a) (splitBottStep n b)) ∧
    (InfoGeometry.Clifford.SplitQ11ChiralDecomposition.splitQ11ChiralProjectorPair.PL * x +
      InfoGeometry.Clifford.SplitQ11ChiralDecomposition.splitQ11ChiralProjectorPair.PR * x = x) ∧
    (InfoGeometry.Cartan.IsCartanInvolution
      ((InfoGeometry.Clifford.CartanInstance.C (J1 := J1) (n := n) hJ1_sq hJ1t).toLinearMap)) := by
  exact ⟨splitBottStep_superBracket_map (n := n) (px := px) (py := py) (a := a) (b := b),
    splitQ11_chiral_pair_decomposition x,
    C_isCartanInvolution (J1 := J1) (n := n) hJ1_sq hJ1t⟩

end InfoGeometry.Clifford.BottSupergradedCartanBridge
