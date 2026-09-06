import InfoGeometry.Clifford.Cl55SpinOperatorAutomorphism
import InfoGeometry.Physics.SplitCliffordAlgebras

/-!
# CAR generators inside `Cl(5,5)` and their Spin transport

The null pairs already owned by `Clifford55` give five genuine CAR pairs in
the noncommutative Clifford algebra.  This file records the pair relations
and the fact that the `Spin(5,5)` inner-conjugation automorphism transports
them without replacing the Clifford carrier by matrices.
-/

namespace InfoGeometry.Clifford.Clifford55

open SplitClifford

noncomputable def annihilation55 (i : Fin 5) : Cl55 :=
  (1 / 2 : ℝ) • ι55 (n_pair i)

noncomputable def creation55 (i : Fin 5) : Cl55 :=
  (1 / 2 : ℝ) • ι55 (nbar_pair i)

@[simp] theorem annihilation55_sq (i : Fin 5) :
    annihilation55 i * annihilation55 i = 0 := by
  change ((1 / 2 : ℝ) • ι55 (n_pair i)) *
    ((1 / 2 : ℝ) • ι55 (n_pair i)) = 0
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, n_pair_sq_zero]
  norm_num

@[simp] theorem creation55_sq (i : Fin 5) :
    creation55 i * creation55 i = 0 := by
  change ((1 / 2 : ℝ) • ι55 (nbar_pair i)) *
    ((1 / 2 : ℝ) • ι55 (nbar_pair i)) = 0
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, nbar_pair_sq_zero]
  norm_num

theorem annihilation55_creation55_anticommutator (i : Fin 5) :
    annihilation55 i * creation55 i +
        creation55 i * annihilation55 i = 1 := by
  change ((1 / 2 : ℝ) • ι55 (n_pair i)) *
      ((1 / 2 : ℝ) • ι55 (nbar_pair i)) +
    ((1 / 2 : ℝ) • ι55 (nbar_pair i)) *
      ((1 / 2 : ℝ) • ι55 (n_pair i)) = 1
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [← smul_add, n_dot_nbar_clifford]
  rw [Algebra.smul_def]
  have hfour : (4 : Cl55) = algebraMap ℝ Cl55 (4 : ℝ) := by
    simpa using (map_ofNat (algebraMap ℝ Cl55) 4).symm
  rw [hfour, ← map_mul]
  norm_num

theorem annihilation55_anticommutator (i j : Fin 5) :
    annihilation55 i * annihilation55 j +
        annihilation55 j * annihilation55 i = 0 := by
  simp only [annihilation55]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [← smul_add]
  rw [CliffordAlgebra.ι_mul_ι_add_swap]
  have hzero : QuadraticMap.polar Q55 (n_pair i) (n_pair j) = 0 := by
    classical
    fin_cases i <;> fin_cases j <;>
      simp [QuadraticMap.polar, Q55_apply, n_pair, e_pos, f_neg,
        Fin.sum_univ_succ]
  rw [hzero]
  simp

theorem creation55_anticommutator (i j : Fin 5) :
    creation55 i * creation55 j +
        creation55 j * creation55 i = 0 := by
  simp only [creation55]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [← smul_add]
  rw [CliffordAlgebra.ι_mul_ι_add_swap]
  have hzero : QuadraticMap.polar Q55 (nbar_pair i) (nbar_pair j) = 0 := by
    classical
    fin_cases i <;> fin_cases j <;>
      simp [QuadraticMap.polar, Q55_apply, nbar_pair, e_pos, f_neg,
        Fin.sum_univ_succ] <;> try ring
  rw [hzero]
  simp

theorem annihilation55_creation55_anticommutator_eq (i j : Fin 5) :
    annihilation55 i * creation55 j +
        creation55 j * annihilation55 i =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simpa using annihilation55_creation55_anticommutator i
  · simp only [annihilation55, creation55]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [← smul_add]
    rw [CliffordAlgebra.ι_mul_ι_add_swap]
    have hzero :
        QuadraticMap.polar Q55 (n_pair i) (nbar_pair j) = 0 := by
      classical
      fin_cases i <;> fin_cases j <;>
        simp_all [QuadraticMap.polar, Q55_apply, n_pair, nbar_pair, e_pos,
          f_neg, Fin.sum_univ_succ]
    rw [hzero]
    simp [hij]

noncomputable def carPair55 (i : Fin 5) : CARPair Cl55 where
  ann := annihilation55 i
  cre := creation55 i
  ann_sq := annihilation55_sq i
  cre_sq := creation55_sq i
  anti := annihilation55_creation55_anticommutator i

theorem spinCliffordRingEquiv_annihilation55_sq (g : Spin55) (i : Fin 5) :
    spinCliffordRingEquiv g (annihilation55 i) *
        spinCliffordRingEquiv g (annihilation55 i) = 0 := by
  simpa only [map_mul, map_zero] using
    congrArg (spinCliffordRingEquiv g) (annihilation55_sq i)

theorem spinCliffordRingEquiv_creation55_sq (g : Spin55) (i : Fin 5) :
    spinCliffordRingEquiv g (creation55 i) *
        spinCliffordRingEquiv g (creation55 i) = 0 := by
  simpa only [map_mul, map_zero] using
    congrArg (spinCliffordRingEquiv g) (creation55_sq i)

theorem spinCliffordRingEquiv_car_anticommutator (g : Spin55) (i : Fin 5) :
    spinCliffordRingEquiv g (annihilation55 i) *
        spinCliffordRingEquiv g (creation55 i) +
      spinCliffordRingEquiv g (creation55 i) *
        spinCliffordRingEquiv g (annihilation55 i) = 1 := by
  simpa only [map_mul, map_add, map_one] using
    congrArg (spinCliffordRingEquiv g)
    (annihilation55_creation55_anticommutator i)

theorem spinCliffordRingEquiv_annihilation55_anticommutator
    (g : Spin55) (i j : Fin 5) :
    spinCliffordRingEquiv g (annihilation55 i) *
          spinCliffordRingEquiv g (annihilation55 j) +
        spinCliffordRingEquiv g (annihilation55 j) *
          spinCliffordRingEquiv g (annihilation55 i) = 0 := by
  simpa only [map_mul, map_add, map_zero] using
    congrArg (spinCliffordRingEquiv g)
      (annihilation55_anticommutator i j)

theorem spinCliffordRingEquiv_creation55_anticommutator
    (g : Spin55) (i j : Fin 5) :
    spinCliffordRingEquiv g (creation55 i) *
          spinCliffordRingEquiv g (creation55 j) +
        spinCliffordRingEquiv g (creation55 j) *
          spinCliffordRingEquiv g (creation55 i) = 0 := by
  simpa only [map_mul, map_add, map_zero] using
    congrArg (spinCliffordRingEquiv g)
      (creation55_anticommutator i j)

theorem spinCliffordRingEquiv_annihilation55_creation55_anticommutator_eq
    (g : Spin55) (i j : Fin 5) :
    spinCliffordRingEquiv g (annihilation55 i) *
          spinCliffordRingEquiv g (creation55 j) +
        spinCliffordRingEquiv g (creation55 j) *
          spinCliffordRingEquiv g (annihilation55 i) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simpa using spinCliffordRingEquiv_car_anticommutator g i
  · simpa only [map_mul, map_add, map_zero, map_one, if_neg hij] using
      congrArg (spinCliffordRingEquiv g)
        (annihilation55_creation55_anticommutator_eq i j)

noncomputable def mixedGenerator55 (i j : Fin 5) : Cl55 :=
  creation55 i * annihilation55 j -
    (if i = j then (1 / 2 : ℝ) • (1 : Cl55) else 0)

private theorem creation55_annihilation55_raw_commutator_creation
    (i j k : Fin 5) :
    creation55 i * annihilation55 j * creation55 k -
        creation55 k * (creation55 i * annihilation55 j) =
      if j = k then creation55 i else 0 := by
  by_cases hjk : j = k
  · subst k
    have hcar : annihilation55 j * creation55 j +
        creation55 j * annihilation55 j = 1 :=
      annihilation55_creation55_anticommutator j
    have hcc : creation55 j * creation55 i =
        -(creation55 i * creation55 j) := by
      exact eq_neg_of_add_eq_zero_right (creation55_anticommutator i j)
    have hac : annihilation55 j * creation55 j =
        1 - creation55 j * annihilation55 j :=
      eq_sub_of_add_eq hcar
    rw [if_pos (rfl : j = j)]
    calc
      creation55 i * annihilation55 j * creation55 j -
          creation55 j * (creation55 i * annihilation55 j) =
        creation55 i * (annihilation55 j * creation55 j) -
          (creation55 j * creation55 i) * annihilation55 j := by
            noncomm_ring
      _ = creation55 i * (1 - creation55 j * annihilation55 j) -
          (-(creation55 i * creation55 j)) * annihilation55 j := by
            rw [hac, hcc]
      _ = creation55 i := by noncomm_ring
  · have hcar : annihilation55 j * creation55 k +
        creation55 k * annihilation55 j = 0 := by
      simpa [if_neg hjk] using
        annihilation55_creation55_anticommutator_eq j k
    have hcc : creation55 k * creation55 i =
        -(creation55 i * creation55 k) := by
      exact eq_neg_of_add_eq_zero_right (creation55_anticommutator i k)
    have hac : annihilation55 j * creation55 k =
        -(creation55 k * annihilation55 j) :=
      eq_neg_of_add_eq_zero_left hcar
    simp only [if_neg hjk]
    calc
      creation55 i * annihilation55 j * creation55 k -
          creation55 k * (creation55 i * annihilation55 j) =
        creation55 i * (annihilation55 j * creation55 k) -
          (creation55 k * creation55 i) * annihilation55 j := by
            noncomm_ring
      _ = creation55 i * (-(creation55 k * annihilation55 j)) -
          (-(creation55 i * creation55 k)) * annihilation55 j := by
            rw [hac, hcc]
      _ = 0 := by noncomm_ring

theorem mixedGenerator55_commutator_creation
    (i j k : Fin 5) :
    mixedGenerator55 i j * creation55 k -
        creation55 k * mixedGenerator55 i j =
      if j = k then creation55 i else 0 := by
  simpa [mixedGenerator55, sub_mul, mul_sub] using
    creation55_annihilation55_raw_commutator_creation i j k

private theorem creation55_annihilation55_raw_commutator_annihilation
    (i j k : Fin 5) :
    creation55 i * annihilation55 j * annihilation55 k -
        annihilation55 k * (creation55 i * annihilation55 j) =
      if i = k then -(annihilation55 j) else 0 := by
  by_cases hik : i = k
  · subst k
    have hcar : annihilation55 i * creation55 i +
        creation55 i * annihilation55 i = 1 :=
      annihilation55_creation55_anticommutator i
    have haa : annihilation55 j * annihilation55 i =
        -(annihilation55 i * annihilation55 j) := by
      exact eq_neg_of_add_eq_zero_left (annihilation55_anticommutator j i)
    have hac : annihilation55 i * creation55 i =
        1 - creation55 i * annihilation55 i :=
      eq_sub_of_add_eq hcar
    rw [if_pos (rfl : i = i)]
    calc
      creation55 i * annihilation55 j * annihilation55 i -
          annihilation55 i * (creation55 i * annihilation55 j) =
        creation55 i * (annihilation55 j * annihilation55 i) -
          (annihilation55 i * creation55 i) * annihilation55 j := by
            noncomm_ring
      _ = creation55 i * (annihilation55 j * annihilation55 i) -
          (1 - creation55 i * annihilation55 i) * annihilation55 j := by
            rw [hac]
      _ = -(annihilation55 j) := by
        rw [haa]
        noncomm_ring
  · have hcar : annihilation55 k * creation55 i +
        creation55 i * annihilation55 k = 0 := by
      simpa [if_neg (Ne.symm hik)] using
        annihilation55_creation55_anticommutator_eq k i
    have haa : annihilation55 j * annihilation55 k =
        -(annihilation55 k * annihilation55 j) := by
      exact eq_neg_of_add_eq_zero_left (annihilation55_anticommutator j k)
    have hac : annihilation55 k * creation55 i =
        -(creation55 i * annihilation55 k) :=
      eq_neg_of_add_eq_zero_left hcar
    simp only [if_neg hik]
    calc
      creation55 i * annihilation55 j * annihilation55 k -
          annihilation55 k * (creation55 i * annihilation55 j) =
        creation55 i * (annihilation55 j * annihilation55 k) -
          (annihilation55 k * creation55 i) * annihilation55 j := by
            noncomm_ring
      _ = creation55 i * (annihilation55 j * annihilation55 k) -
          (-(creation55 i * annihilation55 k)) * annihilation55 j := by
            rw [hac]
      _ = 0 := by
        rw [haa]
        noncomm_ring

theorem mixedGenerator55_commutator_annihilation
    (i j k : Fin 5) :
    mixedGenerator55 i j * annihilation55 k -
        annihilation55 k * mixedGenerator55 i j =
      if i = k then -(annihilation55 j) else 0 := by
  simpa [mixedGenerator55, sub_mul, mul_sub] using
    creation55_annihilation55_raw_commutator_annihilation i j k

private theorem commutator_mul_right55 (X Y Z : Cl55) :
    X * (Y * Z) - (Y * Z) * X =
      (X * Y - Y * X) * Z + Y * (X * Z - Z * X) := by
  noncomm_ring

theorem mixedGenerator55_commutator_mixedGenerator
    (i j k l : Fin 5) :
    mixedGenerator55 i j * mixedGenerator55 k l -
        mixedGenerator55 k l * mixedGenerator55 i j =
      (if j = k then mixedGenerator55 i l else 0) -
        (if i = l then mixedGenerator55 k j else 0) := by
  have hcentral : ∀ (r : ℝ) (x : Cl55),
      (r • (1 : Cl55)) * x = x * (r • (1 : Cl55)) := by
    intro r x
    simpa [Algebra.smul_def] using (Algebra.commutes r x)
  unfold mixedGenerator55
  calc
    (creation55 i * annihilation55 j -
          (if i = j then (1 / 2 : ℝ) • (1 : Cl55) else 0)) *
        (creation55 k * annihilation55 l -
          (if k = l then (1 / 2 : ℝ) • (1 : Cl55) else 0)) -
      (creation55 k * annihilation55 l -
          (if k = l then (1 / 2 : ℝ) • (1 : Cl55) else 0)) *
        (creation55 i * annihilation55 j -
          (if i = j then (1 / 2 : ℝ) • (1 : Cl55) else 0)) =
        (creation55 i * annihilation55 j) *
            (creation55 k * annihilation55 l) -
          (creation55 k * annihilation55 l) *
            (creation55 i * annihilation55 j) := by
          by_cases hij : i = j <;> by_cases hkl : k = l <;>
            simp [hij, hkl, mul_sub, sub_mul, Algebra.smul_def,
              Algebra.commutes]
            <;> noncomm_ring
    _ = ((creation55 i * annihilation55 j) * creation55 k -
          creation55 k * (creation55 i * annihilation55 j)) *
            annihilation55 l +
        creation55 k * ((creation55 i * annihilation55 j) *
          annihilation55 l - annihilation55 l *
            (creation55 i * annihilation55 j)) := by
          exact commutator_mul_right55
            (creation55 i * annihilation55 j) (creation55 k) (annihilation55 l)
    _ = (if j = k then creation55 i else 0) * annihilation55 l +
        creation55 k * (if i = l then -(annihilation55 j) else 0) := by
          rw [creation55_annihilation55_raw_commutator_creation,
            creation55_annihilation55_raw_commutator_annihilation]
    _ = (if j = k then
          (creation55 i * annihilation55 l -
            (if i = l then (1 / 2 : ℝ) • (1 : Cl55) else 0)) else 0) -
        (if i = l then
          (creation55 k * annihilation55 j -
            (if k = j then (1 / 2 : ℝ) • (1 : Cl55) else 0)) else 0) := by
          by_cases hjk : j = k <;> by_cases hil : i = l <;>
            simp_all [eq_comm]
            <;> noncomm_ring

noncomputable def spinTransportedMixedGenerator55
    (g : Spin55) (i j : Fin 5) : Cl55 :=
  spinCliffordRingEquiv g (mixedGenerator55 i j)

theorem spinTransportedMixedGenerator55_commutator_mixedGenerator
    (g : Spin55) (i j k l : Fin 5) :
    spinTransportedMixedGenerator55 g i j *
          spinTransportedMixedGenerator55 g k l -
        spinTransportedMixedGenerator55 g k l *
          spinTransportedMixedGenerator55 g i j =
      (if j = k then spinTransportedMixedGenerator55 g i l else 0) -
        (if i = l then spinTransportedMixedGenerator55 g k j else 0) := by
  by_cases hjk : j = k <;> by_cases hil : i = l
  · subst k
    subst l
    simpa only [spinTransportedMixedGenerator55, map_mul, map_sub, map_zero,
      if_pos rfl] using
      congrArg (spinCliffordRingEquiv g)
        (mixedGenerator55_commutator_mixedGenerator i j j i)
  · subst k
    simpa only [spinTransportedMixedGenerator55, map_mul, map_sub, map_zero,
      if_pos rfl, if_neg hil] using
      congrArg (spinCliffordRingEquiv g)
        (mixedGenerator55_commutator_mixedGenerator i j j l)
  · subst l
    simpa only [spinTransportedMixedGenerator55, map_mul, map_sub, map_zero,
      if_neg hjk, if_pos rfl] using
      congrArg (spinCliffordRingEquiv g)
        (mixedGenerator55_commutator_mixedGenerator i j k i)
  · simpa only [spinTransportedMixedGenerator55, map_mul, map_sub, map_zero,
      if_neg hjk, if_neg hil] using
      congrArg (spinCliffordRingEquiv g)
        (mixedGenerator55_commutator_mixedGenerator i j k l)

/-! ### The quadratic number operator and its CAR derivation -/

noncomputable def numberOperator55 : Cl55 :=
  ∑ i : Fin 5, creation55 i * annihilation55 i

private theorem numberOperator55_summand_commutator_creation
    (i j : Fin 5) :
    creation55 i * annihilation55 i * creation55 j -
        creation55 j * (creation55 i * annihilation55 i) =
      if i = j then creation55 j else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    have hcar : annihilation55 i * creation55 i +
        creation55 i * annihilation55 i = 1 :=
      annihilation55_creation55_anticommutator i
    have hac : annihilation55 i * creation55 i =
        1 - creation55 i * annihilation55 i :=
      eq_sub_of_add_eq hcar
    calc
      creation55 i * annihilation55 i * creation55 i -
          creation55 i * (creation55 i * annihilation55 i) =
        creation55 i * (annihilation55 i * creation55 i) -
          (creation55 i * creation55 i) * annihilation55 i := by
            noncomm_ring
      _ = creation55 i * (1 - creation55 i * annihilation55 i) -
          0 * annihilation55 i := by
            rw [hac, creation55_sq]
      _ = creation55 i := by
        simp [mul_sub, ← mul_assoc, creation55_sq]
  · have hcar : annihilation55 i * creation55 j +
        creation55 j * annihilation55 i = 0 := by
      simpa [if_neg hij] using
        annihilation55_creation55_anticommutator_eq i j
    have hac : annihilation55 i * creation55 j =
        -(creation55 j * annihilation55 i) :=
      eq_neg_of_add_eq_zero_left hcar
    have hcc : creation55 j * creation55 i =
        -(creation55 i * creation55 j) := by
      exact eq_neg_of_add_eq_zero_right (creation55_anticommutator i j)
    rw [if_neg hij]
    calc
      creation55 i * annihilation55 i * creation55 j -
          creation55 j * (creation55 i * annihilation55 i) =
        creation55 i * (annihilation55 i * creation55 j) -
          (creation55 j * creation55 i) * annihilation55 i := by
            noncomm_ring
      _ = creation55 i * (-(creation55 j * annihilation55 i)) -
          (-(creation55 i * creation55 j)) * annihilation55 i := by
            rw [hac, hcc]
      _ = 0 := by noncomm_ring

private theorem numberOperator55_summand_commutator_annihilation
    (i j : Fin 5) :
    creation55 i * annihilation55 i * annihilation55 j -
        annihilation55 j * (creation55 i * annihilation55 i) =
      if i = j then -(annihilation55 j) else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    have hcar : annihilation55 i * creation55 i +
        creation55 i * annihilation55 i = 1 :=
      annihilation55_creation55_anticommutator i
    have hca : annihilation55 i * creation55 i =
        1 - creation55 i * annihilation55 i :=
      eq_sub_of_add_eq hcar
    calc
      creation55 i * annihilation55 i * annihilation55 i -
          annihilation55 i * (creation55 i * annihilation55 i) =
        creation55 i * (annihilation55 i * annihilation55 i) -
          (annihilation55 i * creation55 i) * annihilation55 i := by
            noncomm_ring
      _ = creation55 i * 0 -
          (1 - creation55 i * annihilation55 i) * annihilation55 i := by
            rw [annihilation55_sq, hca]
      _ = -(annihilation55 i) := by
        rw [sub_mul, mul_zero, one_mul]
        have hzero : creation55 i * annihilation55 i * annihilation55 i = 0 := by
          calc
            creation55 i * annihilation55 i * annihilation55 i =
                creation55 i * (annihilation55 i * annihilation55 i) := by
                  noncomm_ring
            _ = 0 := by rw [annihilation55_sq, mul_zero]
        rw [hzero]
        simp
  · have hcar : annihilation55 j * creation55 i +
        creation55 i * annihilation55 j = 0 := by
      simpa [if_neg (Ne.symm hij)] using
        annihilation55_creation55_anticommutator_eq j i
    have hac : annihilation55 j * creation55 i =
        -(creation55 i * annihilation55 j) :=
      eq_neg_of_add_eq_zero_left hcar
    have haa : annihilation55 i * annihilation55 j =
        -(annihilation55 j * annihilation55 i) := by
      exact eq_neg_of_add_eq_zero_left (annihilation55_anticommutator i j)
    rw [if_neg hij]
    calc
      creation55 i * annihilation55 i * annihilation55 j -
          annihilation55 j * (creation55 i * annihilation55 i) =
        creation55 i * (annihilation55 i * annihilation55 j) -
          (annihilation55 j * creation55 i) * annihilation55 i := by
            noncomm_ring
      _ = creation55 i * (-(annihilation55 j * annihilation55 i)) -
          (-(creation55 i * annihilation55 j)) * annihilation55 i := by
            rw [haa, hac]
      _ = 0 := by noncomm_ring

theorem numberOperator55_commutator_creation (j : Fin 5) :
    numberOperator55 * creation55 j - creation55 j * numberOperator55 =
      creation55 j := by
  calc
    numberOperator55 * creation55 j - creation55 j * numberOperator55 =
        ∑ i : Fin 5, (creation55 i * annihilation55 i * creation55 j -
          creation55 j * (creation55 i * annihilation55 i)) := by
            simp only [numberOperator55, Finset.sum_mul, Finset.mul_sum,
              Finset.sum_sub_distrib]
    _ = ∑ i : Fin 5, if i = j then creation55 j else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact numberOperator55_summand_commutator_creation i j
    _ = creation55 j := by simp

theorem numberOperator55_commutator_annihilation (j : Fin 5) :
    numberOperator55 * annihilation55 j -
        annihilation55 j * numberOperator55 = -(annihilation55 j) := by
  calc
    numberOperator55 * annihilation55 j -
        annihilation55 j * numberOperator55 =
        ∑ i : Fin 5, (creation55 i * annihilation55 i * annihilation55 j -
          annihilation55 j * (creation55 i * annihilation55 i)) := by
            simp only [numberOperator55, Finset.sum_mul, Finset.mul_sum,
              Finset.sum_sub_distrib]
    _ = ∑ i : Fin 5, if i = j then -(annihilation55 j) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact numberOperator55_summand_commutator_annihilation i j
    _ = -(annihilation55 j) := by simp

noncomputable def spinTransportedNumberOperator55 (g : Spin55) : Cl55 :=
  spinCliffordRingEquiv g numberOperator55

theorem spinTransportedNumberOperator55_commutator_creation
    (g : Spin55) (j : Fin 5) :
    spinTransportedNumberOperator55 g *
          spinCliffordRingEquiv g (creation55 j) -
        spinCliffordRingEquiv g (creation55 j) *
          spinTransportedNumberOperator55 g =
      spinCliffordRingEquiv g (creation55 j) := by
  simpa only [spinTransportedNumberOperator55, map_mul, map_sub] using
    congrArg (spinCliffordRingEquiv g)
      (numberOperator55_commutator_creation j)

theorem spinTransportedNumberOperator55_commutator_annihilation
    (g : Spin55) (j : Fin 5) :
    spinTransportedNumberOperator55 g *
          spinCliffordRingEquiv g (annihilation55 j) -
        spinCliffordRingEquiv g (annihilation55 j) *
          spinTransportedNumberOperator55 g =
      -(spinCliffordRingEquiv g (annihilation55 j)) := by
  simpa only [spinTransportedNumberOperator55, map_mul, map_sub, map_neg] using
    congrArg (spinCliffordRingEquiv g)
      (numberOperator55_commutator_annihilation j)

noncomputable def spinTransportedCARPair55 (g : Spin55) (i : Fin 5) :
    CARPair Cl55 where
  ann := spinCliffordRingEquiv g (annihilation55 i)
  cre := spinCliffordRingEquiv g (creation55 i)
  ann_sq := spinCliffordRingEquiv_annihilation55_sq g i
  cre_sq := spinCliffordRingEquiv_creation55_sq g i
  anti := spinCliffordRingEquiv_car_anticommutator g i

end InfoGeometry.Clifford.Clifford55
