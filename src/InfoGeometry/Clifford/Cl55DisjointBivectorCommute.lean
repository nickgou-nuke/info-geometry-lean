import InfoGeometry.Clifford.Cl55OperatorZ2Grading
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-! The first concrete commuting bivector cell in the Cl(5,5) carrier.

The result is deliberately stated for two explicit disjoint planes.  It uses
only the native distinct-axis anticommutation theorem; no maximal-torus
interpretation is included.
-/

noncomputable section

namespace InfoGeometry.Clifford.Clifford55

def disjointBivector55 (i j : Fin 5) : Cl55 :=
  hyperbolicAxis55 i * hyperbolicAxis55 j

theorem disjointBivector55_01_23_commute :
    disjointBivector55 0 1 * disjointBivector55 2 3 =
      disjointBivector55 2 3 * disjointBivector55 0 1 := by
  unfold disjointBivector55
  have h02 := hyperbolicAxis55_anticommute_distinct (i := (0 : Fin 5))
    (j := (2 : Fin 5)) (by decide)
  have h03 := hyperbolicAxis55_anticommute_distinct (i := (0 : Fin 5))
    (j := (3 : Fin 5)) (by decide)
  have h12 := hyperbolicAxis55_anticommute_distinct (i := (1 : Fin 5))
    (j := (2 : Fin 5)) (by decide)
  have h13 := hyperbolicAxis55_anticommute_distinct (i := (1 : Fin 5))
    (j := (3 : Fin 5)) (by decide)
  have h02' : hyperbolicAxis55 0 * hyperbolicAxis55 2 =
      -(hyperbolicAxis55 2 * hyperbolicAxis55 0) :=
    eq_neg_of_add_eq_zero_left h02
  have h03' : hyperbolicAxis55 0 * hyperbolicAxis55 3 =
      -(hyperbolicAxis55 3 * hyperbolicAxis55 0) :=
    eq_neg_of_add_eq_zero_left h03
  have h12' : hyperbolicAxis55 1 * hyperbolicAxis55 2 =
      -(hyperbolicAxis55 2 * hyperbolicAxis55 1) :=
    eq_neg_of_add_eq_zero_left h12
  have h13' : hyperbolicAxis55 1 * hyperbolicAxis55 3 =
      -(hyperbolicAxis55 3 * hyperbolicAxis55 1) :=
    eq_neg_of_add_eq_zero_left h13
  calc
    (hyperbolicAxis55 0 * hyperbolicAxis55 1) *
        (hyperbolicAxis55 2 * hyperbolicAxis55 3) =
        hyperbolicAxis55 0 * (hyperbolicAxis55 1 *
          hyperbolicAxis55 2) * hyperbolicAxis55 3 := by
            simp [mul_assoc]
    _ = hyperbolicAxis55 0 * (-(hyperbolicAxis55 2 *
          hyperbolicAxis55 1)) * hyperbolicAxis55 3 := by rw [h12']
    _ = -(hyperbolicAxis55 0 * hyperbolicAxis55 2) *
          (hyperbolicAxis55 1 * hyperbolicAxis55 3) := by noncomm_ring
    _ = -(-(hyperbolicAxis55 2 * hyperbolicAxis55 0)) *
          (hyperbolicAxis55 1 * hyperbolicAxis55 3) := by rw [h02']
    _ = hyperbolicAxis55 2 * hyperbolicAxis55 0 *
          (hyperbolicAxis55 1 * hyperbolicAxis55 3) := by noncomm_ring
    _ = hyperbolicAxis55 2 * hyperbolicAxis55 0 *
          (-(hyperbolicAxis55 3 * hyperbolicAxis55 1)) := by rw [h13']
    _ = -(hyperbolicAxis55 2 * hyperbolicAxis55 0 *
          hyperbolicAxis55 3) * hyperbolicAxis55 1 := by noncomm_ring
    _ = -(hyperbolicAxis55 2 * (hyperbolicAxis55 0 *
          hyperbolicAxis55 3)) * hyperbolicAxis55 1 := by
            simp [mul_assoc]
    _ = -(hyperbolicAxis55 2 * (-(hyperbolicAxis55 3 *
          hyperbolicAxis55 0))) * hyperbolicAxis55 1 := by rw [h03']
    _ = (hyperbolicAxis55 2 * hyperbolicAxis55 3) *
          (hyperbolicAxis55 0 * hyperbolicAxis55 1) := by noncomm_ring

theorem disjointBivector55_commute_of_pairwise_distinct
    {i j k l : Fin 5}
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    disjointBivector55 i j * disjointBivector55 k l =
      disjointBivector55 k l * disjointBivector55 i j := by
  unfold disjointBivector55
  have hik' := hyperbolicAxis55_anticommute_distinct hik
  have hil' := hyperbolicAxis55_anticommute_distinct hil
  have hjk' := hyperbolicAxis55_anticommute_distinct hjk
  have hjl' := hyperbolicAxis55_anticommute_distinct hjl
  have hik'' : hyperbolicAxis55 i * hyperbolicAxis55 k =
      -(hyperbolicAxis55 k * hyperbolicAxis55 i) :=
    eq_neg_of_add_eq_zero_left hik'
  have hil'' : hyperbolicAxis55 i * hyperbolicAxis55 l =
      -(hyperbolicAxis55 l * hyperbolicAxis55 i) :=
    eq_neg_of_add_eq_zero_left hil'
  have hjk'' : hyperbolicAxis55 j * hyperbolicAxis55 k =
      -(hyperbolicAxis55 k * hyperbolicAxis55 j) :=
    eq_neg_of_add_eq_zero_left hjk'
  have hjl'' : hyperbolicAxis55 j * hyperbolicAxis55 l =
      -(hyperbolicAxis55 l * hyperbolicAxis55 j) :=
    eq_neg_of_add_eq_zero_left hjl'
  calc
    (hyperbolicAxis55 i * hyperbolicAxis55 j) *
        (hyperbolicAxis55 k * hyperbolicAxis55 l) =
        hyperbolicAxis55 i * (hyperbolicAxis55 j *
          hyperbolicAxis55 k) * hyperbolicAxis55 l := by simp [mul_assoc]
    _ = hyperbolicAxis55 i * (-(hyperbolicAxis55 k *
          hyperbolicAxis55 j)) * hyperbolicAxis55 l := by rw [hjk'']
    _ = -(hyperbolicAxis55 i * hyperbolicAxis55 k) *
          (hyperbolicAxis55 j * hyperbolicAxis55 l) := by noncomm_ring
    _ = -(-(hyperbolicAxis55 k * hyperbolicAxis55 i)) *
          (hyperbolicAxis55 j * hyperbolicAxis55 l) := by rw [hik'']
    _ = hyperbolicAxis55 k * hyperbolicAxis55 i *
          (hyperbolicAxis55 j * hyperbolicAxis55 l) := by noncomm_ring
    _ = hyperbolicAxis55 k * hyperbolicAxis55 i *
          (-(hyperbolicAxis55 l * hyperbolicAxis55 j)) := by rw [hjl'']
    _ = -(hyperbolicAxis55 k * hyperbolicAxis55 i *
          hyperbolicAxis55 l) * hyperbolicAxis55 j := by noncomm_ring
    _ = -(hyperbolicAxis55 k * (-(hyperbolicAxis55 l *
          hyperbolicAxis55 i))) * hyperbolicAxis55 j := by
            rw [show hyperbolicAxis55 k * hyperbolicAxis55 i *
              hyperbolicAxis55 l = hyperbolicAxis55 k *
              (hyperbolicAxis55 i * hyperbolicAxis55 l) by simp [mul_assoc]]
            rw [hil'']
    _ = (hyperbolicAxis55 k * hyperbolicAxis55 l) *
          (hyperbolicAxis55 i * hyperbolicAxis55 j) := by noncomm_ring

theorem disjointBivector55_01_23_sq :
    disjointBivector55 0 1 * disjointBivector55 0 1 = -(1 : Cl55) := by
  unfold disjointBivector55
  have h01 := hyperbolicAxis55_anticommute_distinct
    (i := (0 : Fin 5)) (j := (1 : Fin 5)) (by decide)
  have h01' : hyperbolicAxis55 1 * hyperbolicAxis55 0 =
      -(hyperbolicAxis55 0 * hyperbolicAxis55 1) :=
    eq_neg_of_add_eq_zero_right h01
  calc
    (hyperbolicAxis55 0 * hyperbolicAxis55 1) *
        (hyperbolicAxis55 0 * hyperbolicAxis55 1) =
        hyperbolicAxis55 0 * (-(hyperbolicAxis55 0 *
          hyperbolicAxis55 1)) * hyperbolicAxis55 1 := by
            rw [← h01']
            simp [mul_assoc]
    _ = -(hyperbolicAxis55 0 * hyperbolicAxis55 0) *
          (hyperbolicAxis55 1 * hyperbolicAxis55 1) := by noncomm_ring
    _ = -(1 : Cl55) := by rw [hyperbolicAxis55_sq 0, hyperbolicAxis55_sq 1]; simp

theorem disjointBivector55_23_sq :
    disjointBivector55 2 3 * disjointBivector55 2 3 = -(1 : Cl55) := by
  unfold disjointBivector55
  have h23 := hyperbolicAxis55_anticommute_distinct
    (i := (2 : Fin 5)) (j := (3 : Fin 5)) (by decide)
  have h23' : hyperbolicAxis55 3 * hyperbolicAxis55 2 =
      -(hyperbolicAxis55 2 * hyperbolicAxis55 3) :=
    eq_neg_of_add_eq_zero_right h23
  calc
    (hyperbolicAxis55 2 * hyperbolicAxis55 3) *
        (hyperbolicAxis55 2 * hyperbolicAxis55 3) =
        hyperbolicAxis55 2 * (-(hyperbolicAxis55 2 *
          hyperbolicAxis55 3)) * hyperbolicAxis55 3 := by
            rw [← h23']
            simp [mul_assoc]
    _ = -(hyperbolicAxis55 2 * hyperbolicAxis55 2) *
          (hyperbolicAxis55 3 * hyperbolicAxis55 3) := by noncomm_ring
    _ = -(1 : Cl55) := by rw [hyperbolicAxis55_sq 2, hyperbolicAxis55_sq 3]; simp

end InfoGeometry.Clifford.Clifford55
