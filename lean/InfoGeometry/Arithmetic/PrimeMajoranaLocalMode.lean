import Mathlib.Tactic


noncomputable section

namespace InfoGeometry.Arithmetic.PrimeMajoranaLocalMode

abbrev LocalFock : Type :=
  ℝ × ℝ

def vacuum : LocalFock :=
  (1, 0)

def occupied : LocalFock :=
  (0, 1)

abbrev LocalEnd : Type :=
  LocalFock →ₗ[ℝ] LocalFock

def epsilon : LocalFock →ₗ[ℝ] LocalFock where
  toFun := fun x => (0, x.1)
  map_add' := by
    intro x y
    ext <;> simp
  map_smul' := by
    intro a x
    ext <;> simp

def iota : LocalFock →ₗ[ℝ] LocalFock where
  toFun := fun x => (x.2, 0)
  map_add' := by
    intro x y
    ext <;> simp
  map_smul' := by
    intro a x
    ext <;> simp

def numberOp : LocalFock →ₗ[ℝ] LocalFock :=
  epsilon.comp iota

def cMajorana : LocalFock →ₗ[ℝ] LocalFock :=
  epsilon + iota

def dMajorana : LocalFock →ₗ[ℝ] LocalFock :=
  epsilon - iota

def parityOp : LocalEnd :=
  cMajorana.comp dMajorana

def anticommutator
    (A B : LocalEnd) : LocalEnd :=
  A.comp B + B.comp A

theorem epsilon_sq :
    epsilon.comp epsilon = 0 := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [epsilon]

theorem iota_sq :
    iota.comp iota = 0 := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [iota]

theorem iota_epsilon_anticomm :
    iota.comp epsilon + epsilon.comp iota = 1 := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [epsilon, iota]

theorem epsilon_iota_anticomm :
    epsilon.comp iota + iota.comp epsilon = 1 := by
  rw [add_comm]
  exact iota_epsilon_anticomm

theorem epsilon_iota_anticomm' :
    anticommutator epsilon iota = 1 := by
  simpa [anticommutator] using epsilon_iota_anticomm

theorem iota_epsilon_anticomm' :
    anticommutator iota epsilon = 1 := by
  simpa [anticommutator] using iota_epsilon_anticomm

theorem cMajorana_sq :
    cMajorana.comp cMajorana = 1 := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [cMajorana, epsilon, iota]

theorem cMajorana_cMajorana_anticomm :
    anticommutator cMajorana cMajorana = (2 : ℝ) • (1 : LocalEnd) := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [anticommutator, cMajorana, epsilon, iota]
  · ring_nf
  · ring_nf

theorem dMajorana_sq :
    dMajorana.comp dMajorana = -1 := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [dMajorana, epsilon, iota]

theorem dMajorana_dMajorana_anticomm :
    anticommutator dMajorana dMajorana = -((2 : ℝ) • (1 : LocalEnd)) := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [anticommutator, dMajorana, epsilon, iota]
  · ring_nf
  · ring_nf

theorem cMajorana_dMajorana_anticomm :
    cMajorana.comp dMajorana + dMajorana.comp cMajorana = 0 := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [cMajorana, dMajorana, epsilon, iota]

theorem dMajorana_cMajorana_anticomm :
    dMajorana.comp cMajorana + cMajorana.comp dMajorana = 0 := by
  rw [add_comm]
  exact cMajorana_dMajorana_anticomm

theorem numberOp_apply
    (x : LocalFock) :
    numberOp x = (0, x.2) := by
  rcases x with ⟨x0, x1⟩
  ext <;> simp [numberOp, epsilon, iota]

theorem numberOp_sq :
    numberOp.comp numberOp = numberOp := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, numberOp_apply, numberOp_apply]

@[simp] theorem numberOp_vacuum :
    numberOp vacuum = 0 := by
  rw [numberOp_apply]
  rfl

@[simp] theorem numberOp_occupied :
    numberOp occupied = occupied := by
  rw [numberOp_apply]
  rfl

theorem parityOp_apply
    (x : LocalFock) :
    parityOp x = (x.1, -x.2) := by
  rcases x with ⟨x0, x1⟩
  ext <;> simp [parityOp, cMajorana, dMajorana, epsilon, iota]

theorem parityOp_eq_one_sub_two_numberOp :
    parityOp = 1 - (2 : ℝ) • numberOp := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [parityOp_apply, numberOp_apply]
  ring

theorem parityOp_conj_cMajorana :
    parityOp.comp (cMajorana.comp parityOp) = -cMajorana := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [parityOp, cMajorana, dMajorana, epsilon, iota]

theorem parityOp_conj_dMajorana :
    parityOp.comp (dMajorana.comp parityOp) = -dMajorana := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [parityOp, cMajorana, dMajorana, epsilon, iota]

@[simp]
theorem parityOp_vacuum :
    parityOp vacuum = vacuum := by
  ext <;> simp [parityOp_apply, vacuum]

@[simp]
theorem parityOp_occupied :
    parityOp occupied = -occupied := by
  ext <;> simp [parityOp_apply, occupied]

@[simp]
theorem cMajorana_vacuum :
    cMajorana vacuum = occupied := by
  ext <;> simp [cMajorana, epsilon, iota, vacuum, occupied]

@[simp]
theorem cMajorana_occupied :
    cMajorana occupied = vacuum := by
  ext <;> simp [cMajorana, epsilon, iota, vacuum, occupied]

@[simp]
theorem dMajorana_vacuum :
    dMajorana vacuum = occupied := by
  ext <;> simp [dMajorana, epsilon, iota, vacuum, occupied]

@[simp]
theorem dMajorana_occupied :
    dMajorana occupied = -vacuum := by
  ext <;> simp [dMajorana, epsilon, iota, vacuum, occupied]

theorem parityOp_sq :
    parityOp.comp parityOp = (1 : LocalEnd) := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [parityOp, cMajorana, dMajorana, epsilon, iota]

theorem parityOp_cMajorana_anticomm :
    parityOp.comp cMajorana + cMajorana.comp parityOp = 0 := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [parityOp, cMajorana, dMajorana, epsilon, iota]

theorem parityOp_dMajorana_anticomm :
    parityOp.comp dMajorana + dMajorana.comp parityOp = 0 := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [parityOp, cMajorana, dMajorana, epsilon, iota]

theorem parityOp_cMajorana_apply
    (x : LocalFock) :
    parityOp (cMajorana x) = -cMajorana (parityOp x) := by
  have h :=
    congrArg (fun T : LocalEnd => T x) parityOp_cMajorana_anticomm
  have h0 : parityOp (cMajorana x) + cMajorana (parityOp x) = 0 := by
    simpa [LinearMap.add_apply] using h
  exact (eq_neg_iff_add_eq_zero).2 h0

theorem parityOp_dMajorana_apply
    (x : LocalFock) :
    parityOp (dMajorana x) = -dMajorana (parityOp x) := by
  have h :=
    congrArg (fun T : LocalEnd => T x) parityOp_dMajorana_anticomm
  have h0 : parityOp (dMajorana x) + dMajorana (parityOp x) = 0 := by
    simpa [LinearMap.add_apply] using h
  exact (eq_neg_iff_add_eq_zero).2 h0

end InfoGeometry.Arithmetic.PrimeMajoranaLocalMode
