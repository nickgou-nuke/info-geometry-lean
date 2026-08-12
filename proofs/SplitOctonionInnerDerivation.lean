import InfoGeometry.Algebra.AlternativeDerivations
import proofs.SplitOctonionAlternativity
import proofs.SplitOctonionDerivationSpace
set_option maxHeartbeats 1000000

open SplitOctonion

namespace SplitOctonionInnerDerivation

/-- The Associator measures the failure of associativity -/
def associator (x y z : SplitOct) : SplitOct :=
  (x * y) * z - x * (y * z)

/-- The Standard Inner Derivation Operator for Alternative Algebras
    D_{x,y}(z) = [[x,y], z] - 3(x,y,z) -/
def innerDeriv (x y z : SplitOct) : SplitOct :=
  bracket (bracket x y) z - (3 : ℝ) • associator x y z

private theorem splitOct_left_alternative (a b : SplitOct) :
    (a * a) * b = a * (a * b) :=
  (left_alternative a b).symm

private theorem splitOct_right_alternative (a b : SplitOct) :
    (b * a) * a = b * (a * a) :=
  right_alternative b a

theorem innerDeriv_eq_stanDerMap (x y z : SplitOct) :
    innerDeriv x y z = InfoGeometry.Algebra.stanDerMap (R := ℝ) x y z := by
  rw [InfoGeometry.Algebra.stanDerMap_apply_normal_form
    splitOct_left_alternative splitOct_right_alternative]
  unfold innerDeriv SplitOctonion.bracket associator
  rw [associator_apply]
  congr 1
  exact Nat.cast_smul_eq_nsmul ℝ 3 _

/-- The standard inner derivation obeys the Leibniz rule. -/
theorem innerDeriv_is_derivation (x y u v : SplitOct) :
    innerDeriv x y (u * v) =
      innerDeriv x y u * v + u * innerDeriv x y v := by
  simpa only [innerDeriv_eq_stanDerMap] using
    InfoGeometry.Algebra.stanDerMap_isLeibniz
      (R := ℝ) splitOct_left_alternative splitOct_right_alternative x y u v

/-- The standard inner derivation as a real-linear map. -/
def innerDerivLinearMap (x y : SplitOct) : SplitOct →ₗ[ℝ] SplitOct where
  toFun z := innerDeriv x y z
  map_add' u v := by
    simpa only [innerDeriv_eq_stanDerMap] using
      (InfoGeometry.Algebra.stanDerMap (R := ℝ) x y).map_add u v
  map_smul' c u := by
    simpa only [innerDeriv_eq_stanDerMap, RingHom.id_apply] using
      (InfoGeometry.Algebra.stanDerMap (R := ℝ) x y).map_smul c u

/-- Inner Derivation as a formal OctDerivation Lie Algebra element -/
def mkInnerDeriv (x y : SplitOct) : OctDerivation where
  toLinearMap := innerDerivLinearMap x y
  leibniz' := innerDeriv_is_derivation x y

theorem OctDerivation.map_bracket (D : OctDerivation) (x y : SplitOct) :
    D.toLinearMap (SplitOctonion.bracket x y) =
      SplitOctonion.bracket (D.toLinearMap x) y +
        SplitOctonion.bracket x (D.toLinearMap y) := by
  unfold SplitOctonion.bracket
  rw [map_sub, D.leibniz', D.leibniz']
  noncomm_ring

theorem OctDerivation.map_associator (D : OctDerivation) (x y z : SplitOct) :
    D.toLinearMap (associator x y z) =
      associator (D.toLinearMap x) y z +
        associator x (D.toLinearMap y) z +
          associator x y (D.toLinearMap z) := by
  unfold associator
  rw [map_sub, D.leibniz', D.leibniz', D.leibniz', D.leibniz']
  noncomm_ring

theorem OctDerivation.map_innerDeriv (D : OctDerivation) (x y z : SplitOct) :
    D.toLinearMap (innerDeriv x y z) =
      innerDeriv (D.toLinearMap x) y z +
        innerDeriv x (D.toLinearMap y) z +
          innerDeriv x y (D.toLinearMap z) := by
  unfold innerDeriv
  rw [map_sub, D.toLinearMap.map_smul]
  rw [OctDerivation.map_bracket D (bracket x y) z]
  rw [OctDerivation.map_bracket D x y]
  rw [OctDerivation.map_associator D x y z]
  have hleft (a b c : SplitOct) :
      bracket (a + b) c = bracket a c + bracket b c := by
    unfold SplitOctonion.bracket
    simp only [add_mul, mul_add]
    abel
  rw [hleft]
  simp only [smul_add]
  abel

theorem bracket_mkInnerDeriv (D : OctDerivation) (x y : SplitOct) :
    ⁅D, mkInnerDeriv x y⁆ =
      mkInnerDeriv (D.toLinearMap x) y +
        mkInnerDeriv x (D.toLinearMap y) := by
  apply OctDerivation.ext_lin
  apply LinearMap.ext
  intro z
  change D.toLinearMap (innerDeriv x y z) -
      innerDeriv x y (D.toLinearMap z) = _
  rw [OctDerivation.map_innerDeriv D x y z]
  change _ = innerDeriv (D.toLinearMap x) y z + innerDeriv x (D.toLinearMap y) z
  abel

theorem bracket_mkInnerDeriv_mkInnerDeriv (x y u v : SplitOct) :
    ⁅mkInnerDeriv x y, mkInnerDeriv u v⁆ =
      mkInnerDeriv (innerDeriv x y u) v +
        mkInnerDeriv u (innerDeriv x y v) := by
  simpa only [mkInnerDeriv] using
    bracket_mkInnerDeriv (mkInnerDeriv x y) u v

end SplitOctonionInnerDerivation
