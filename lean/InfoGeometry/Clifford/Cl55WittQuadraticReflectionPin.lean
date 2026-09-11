import InfoGeometry.Clifford.Cl55WittQuadraticReflection
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Clifford.Cl55WittPinAction

namespace InfoGeometry.Clifford.Clifford55

/-!
# Clifford twisted action of a native negative reflection

The native Pin group in this split realization contains the normalized
negative-norm vector generators.  This file identifies their twisted action
with the quadratic reflection already defined through `Q55`; it does not
assert Cartan--Dieudonné generation or surjectivity of the Pin action.
-/

theorem negativeVector_triple_product
    (v x : V55) (hv : Q55 v = -1) :
    ι55 v * ι55 x * ι55 v =
      algebraMap ℝ Cl55 (QuadraticMap.polar (⇑Q55) x v) * ι55 v +
        ι55 x := by
  have hsq : ι55 v * ι55 v = (-1 : Cl55) := by
    rw [CliffordAlgebra.ι_sq_scalar, hv]
    simp
  have hpolar :
      ι55 v * ι55 x + ι55 x * ι55 v =
        algebraMap ℝ Cl55 (QuadraticMap.polar (⇑Q55) x v) := by
    simpa [add_comm] using
      (CliffordAlgebra.ι_mul_ι_add_swap (Q := Q55) x v)
  have hleft :
      ι55 v * ι55 x =
        algebraMap ℝ Cl55 (QuadraticMap.polar (⇑Q55) x v) -
          ι55 x * ι55 v := by
    exact eq_sub_of_add_eq hpolar
  rw [hleft, sub_mul, mul_assoc, hsq]
  simp

theorem pinTwistedAdj_eq_quadraticReflection
    (g : Pin55) (v : V55)
    (hcoe : (pinToUnits g : Cl55) = ι55 v)
    (hv : Q55 v = -1) (x : V55) :
    pinTwistedAdj g x =
      ι55 (quadraticReflection v (by simp [hv]) x) := by
  have hsq : ι55 v * ι55 v = (-1 : Cl55) := by
    rw [CliffordAlgebra.ι_sq_scalar, hv]
    simp
  have hinv : (↑((pinToUnits g)⁻¹) : Cl55) = -ι55 v := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hcoe]
    calc
      ι55 v * -ι55 v = -(ι55 v * ι55 v) := by rw [mul_neg]
      _ = 1 := by rw [hsq]; simp
  have hinvol :
      CliffordAlgebra.involute (pinToUnits g : Cl55) = -ι55 v := by
    rw [hcoe, CliffordAlgebra.involute_ι]
  have hpolar :
      ι55 v * ι55 x + ι55 x * ι55 v =
        algebraMap ℝ Cl55 (QuadraticMap.polar (⇑Q55) x v) := by
    simpa [add_comm] using
      (CliffordAlgebra.ι_mul_ι_add_swap (Q := Q55) x v)
  have hleft :
      ι55 v * ι55 x =
        algebraMap ℝ Cl55 (QuadraticMap.polar (⇑Q55) x v) -
          ι55 x * ι55 v := by
    exact eq_sub_of_add_eq hpolar
  have hprod := negativeVector_triple_product v x hv
  rw [pinTwistedAdj, hinvol, hinv]
  have hnegprod :
      -ι55 v * ι55 x * -ι55 v = ι55 v * ι55 x * ι55 v := by
    noncomm_ring
  rw [hnegprod]
  rw [quadraticReflection_apply]
  rw [map_sub, map_smul]
  have hdiv :
      QuadraticMap.polar (⇑Q55) x v / Q55 v =
        -QuadraticMap.polar (⇑Q55) x v := by
    rw [hv]
    ring
  rw [hdiv]
  simp only [Algebra.smul_def, map_neg]
  rw [show ι55 v * ι55 x * ι55 v =
      algebraMap ℝ Cl55 (QuadraticMap.polar (⇑Q55) x v) * ι55 v +
        ι55 x by exact hprod]
  noncomm_ring

theorem fNegPin_twistedAction_eq_quadraticReflection (i : Fin 5) (x : V55) :
    pinTwistedAdj (fNegPin i) x =
      ι55 (quadraticReflection (f_neg i) (by
        rw [Q55_f_neg]
        norm_num) x) := by
  apply pinTwistedAdj_eq_quadraticReflection (fNegPin i) (f_neg i) ?_ (Q55_f_neg i)
  change (pinToUnits
      ⟨ι55 (f_neg i), f_neg_mem_pinGroup i⟩ : Cl55ˣ) = ι55 (f_neg i)
  rw [pinToUnits_f_neg, fNegUnit_coe]

theorem pinTwistedActionEquiv_eq_quadraticReflection
    (g : Pin55) (v : V55)
    (hcoe : (pinToUnits g : Cl55) = ι55 v)
    (hv : Q55 v = -1) :
    pinTwistedActionEquiv g = quadraticReflection v (by simp [hv]) := by
  apply LinearEquiv.ext
  intro x
  apply ι55_injective
  change ι55 (pinTwistedAction g x) =
    ι55 (quadraticReflection v (by simp [hv]) x)
  rw [pinTwistedAction_apply_ι]
  exact pinTwistedAdj_eq_quadraticReflection g v hcoe hv x

end InfoGeometry.Clifford.Clifford55
