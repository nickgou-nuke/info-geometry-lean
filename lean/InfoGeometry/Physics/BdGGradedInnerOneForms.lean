import InfoGeometry.Physics.ConnesDifferentialInnerFluctuations
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.Physics

variable {A : Type*} [Ring A] [StarRing A]

def IsEven (M : BdGBlock A) : Prop :=
  M * chiralGrading = chiralGrading * M

def IsOdd (M : BdGBlock A) : Prop :=
  M * chiralGrading + chiralGrading * M = 0

theorem diagonal_isEven {M : BdGBlock A} (hM : BdGIsDiagonal M) :
    IsEven M := by
  rcases hM with ⟨h01, h10⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [IsEven, chiralGrading, Matrix.mul_apply, Fin.sum_univ_two, h01, h10]

theorem offDiagonal_isOdd {M : BdGBlock A} (hM : BdGIsOffDiagonal M) :
    IsOdd M := by
  exact offDiagonal_anticommutes_chiral M hM

theorem odd_add_odd {M N : BdGBlock A}
    (hM : IsOdd M) (hN : IsOdd N) : IsOdd (M + N) := by
  dsimp [IsOdd] at hM hN ⊢
  rw [add_mul, mul_add]
  calc
    M * chiralGrading + N * chiralGrading +
        (chiralGrading * M + chiralGrading * N) =
        (M * chiralGrading + chiralGrading * M) +
          (N * chiralGrading + chiralGrading * N) := by abel
    _ = 0 := by rw [hM, hN, add_zero]

theorem odd_neg {M : BdGBlock A} (hM : IsOdd M) : IsOdd (-M) := by
  dsimp [IsOdd] at hM ⊢
  simpa [add_comm] using congrArg Neg.neg hM

theorem odd_sub_odd {M N : BdGBlock A}
    (hM : IsOdd M) (hN : IsOdd N) : IsOdd (M - N) := by
  simpa [sub_eq_add_neg] using odd_add_odd hM (odd_neg hN)

theorem odd_mul_even_isOdd {M N : BdGBlock A}
    (hM : IsOdd M) (hN : IsEven N) : IsOdd (M * N) := by
  dsimp [IsEven, IsOdd] at hM hN ⊢
  have hM' : chiralGrading * M = -(M * chiralGrading) :=
    eq_neg_of_add_eq_zero_right hM
  have hN' : chiralGrading * N = N * chiralGrading := hN.symm
  calc
    M * N * chiralGrading + chiralGrading * (M * N) =
        M * (N * chiralGrading) + (chiralGrading * M) * N := by
          noncomm_ring
    _ = M * (N * chiralGrading) + (-(M * chiralGrading)) * N := by
          rw [hM']
    _ = 0 := by rw [← hN']; noncomm_ring

theorem even_mul_odd_isOdd {M N : BdGBlock A}
    (hM : IsEven M) (hN : IsOdd N) : IsOdd (M * N) := by
  have hM' : chiralGrading * M = M * chiralGrading := hM.symm
  have hN' : N * chiralGrading = -(chiralGrading * N) :=
    eq_neg_of_add_eq_zero_left hN
  calc
    M * N * chiralGrading + chiralGrading * (M * N) =
        M * (N * chiralGrading) + (chiralGrading * M) * N := by
          noncomm_ring
    _ = M * (-(chiralGrading * N)) + (chiralGrading * M) * N := by
          rw [hN']
    _ = 0 := by rw [hM']; noncomm_ring

theorem diagonal_mul_offDiagonal {M N : BdGBlock A}
    (hM : BdGIsDiagonal M) (hN : BdGIsOffDiagonal N) :
    IsOdd (M * N) := by
  exact even_mul_odd_isOdd (diagonal_isEven hM) (offDiagonal_isOdd hN)

theorem commutator_odd_even_isOdd {D a : BdGBlock A}
    (hD : IsOdd D) (ha : IsEven a) :
    IsOdd (connesDifferential D a) := by
  dsimp [connesDifferential]
  apply odd_sub_odd
  · exact odd_mul_even_isOdd hD ha
  · exact even_mul_odd_isOdd ha hD

theorem commutator_odd_even_is_odd {D a : BdGBlock A}
    (hD : IsOdd D) (ha : IsEven a) :
    IsOdd (connesDifferential D a) :=
  commutator_odd_even_isOdd hD ha

def representedOneForm (n : ℕ) (D : BdGBlock A)
    (a b : Fin n → BdGBlock A) : BdGBlock A :=
  ∑ i, a i * connesDifferential D (b i)

theorem odd_sum {ι : Type*} (s : Finset ι) (f : ι → BdGBlock A)
    (hf : ∀ i ∈ s, IsOdd (f i)) : IsOdd (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [IsOdd]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      apply odd_add_odd
      · exact hf i (Finset.mem_insert_self i s)
      · apply ih
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)

theorem representedOneForm_isOdd
    {n : ℕ} {D : BdGBlock A} (hD : IsOdd D)
    (a b : Fin n → BdGBlock A)
    (ha : ∀ i, IsEven (a i)) (hb : ∀ i, IsEven (b i)) :
    IsOdd (representedOneForm n D a b) := by
  classical
  apply odd_sum Finset.univ
  intro i hi
  exact even_mul_odd_isOdd (ha i)
    (commutator_odd_even_isOdd hD (hb i))

theorem fluctuatedDirac_isOdd
    {n : ℕ} {D : BdGBlock A} (hD : IsOdd D)
    (a b : Fin n → BdGBlock A)
    (ha : ∀ i, IsEven (a i)) (hb : ∀ i, IsEven (b i)) :
    IsOdd (D + representedOneForm n D a b) := by
  exact odd_add_odd hD (representedOneForm_isOdd hD a b ha hb)

theorem fluctuatedDirac_star_eq_self
    {D A₁ : BdGBlock A}
    (hD : star D = D) (hA : star A₁ = A₁) :
    star (D + A₁) = D + A₁ := by
  simp [hD, hA]

end InfoGeometry.Physics
