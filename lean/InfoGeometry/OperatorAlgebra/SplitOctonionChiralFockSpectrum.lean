import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.CliffordCARFockParity
import InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR
import InfoGeometry.OperatorAlgebra.SplitCliffordRealForms

noncomputable section

/-!
# Three-mode chiral/Fock spectrum

The six null chiral directions have the finite three-mode occupation shadow
`Fin 3 → Bool`.  This owner records only the kernel-checkable spectral data:
the degree multiplicities `1 + 3 + 3 + 1`, complement reflection, and the
centered degree charge.  It does not identify this finite label set with a
Hilbert-space eigenbasis or assert a Tomita/BKM theorem.
-/

namespace InfoGeometry.OperatorAlgebra.SplitOctonionChiralFockSpectrum

open InfoGeometry.OperatorAlgebra.CliffordSplitOctonionCAR

abbrev Occupation3 :=
  InfoGeometry.OperatorAlgebra.CliffordCARFockParity.Occupation 3

def degree (w : Occupation3) : ℕ :=
  InfoGeometry.OperatorAlgebra.CliffordCARFockParity.fermionNumber w

def reflected (w : Occupation3) : Occupation3 :=
  InfoGeometry.OperatorAlgebra.SplitCliffordRealForms.Occupation.complement w

@[simp] theorem total_states : Fintype.card Occupation3 = 8 := by
  decide

@[simp] theorem degree_reflected (w : Occupation3) :
    degree (reflected w) = 3 - degree w := by
  revert w
  decide

@[simp] theorem degree_le_three (w : Occupation3) : degree w ≤ 3 := by
  revert w
  decide

@[simp] theorem degree_zero_card :
    Fintype.card {w : Occupation3 // degree w = 0} = 1 := by
  decide

@[simp] theorem degree_one_card :
    Fintype.card {w : Occupation3 // degree w = 1} = 3 := by
  decide

@[simp] theorem degree_two_card :
    Fintype.card {w : Occupation3 // degree w = 2} = 3 := by
  decide

@[simp] theorem degree_three_card :
    Fintype.card {w : Occupation3 // degree w = 3} = 1 := by
  decide

def centeredDegree (w : Occupation3) : ℚ :=
  (degree w : ℚ) - 3 / 2

@[simp] theorem centeredDegree_reflected (w : Occupation3) :
    centeredDegree (reflected w) = -centeredDegree w := by
  rw [centeredDegree, centeredDegree, degree_reflected]
  rw [Nat.cast_sub (degree_le_three w)]
  norm_num
  ring

def parity (w : Occupation3) : ℤ :=
  if Even (degree w) then 1 else -1

@[simp] theorem parity_sq (w : Occupation3) : parity w * parity w = 1 := by
  by_cases h : Even (degree w) <;> simp [parity, h]

@[simp] theorem parity_reflected (w : Occupation3) :
    parity (reflected w) = -parity w := by
  revert w
  decide

/-! ### Associative CAR realization of the three-mode spectral shadow -/

/-- The first three annihilation modes in the verified `Cl(4,4)` CAR algebra.

This is deliberately a Clifford realization.  It is not an identification of
raw split-octonion left multiplication with an associative CAR algebra. -/
noncomputable def annihilation (i : Fin 3) : Cl44 :=
  a i.castSucc

/-- The corresponding three creation modes. -/
noncomputable def creation (i : Fin 3) : Cl44 :=
  aDag i.castSucc

@[simp] theorem annihilation_sq (i : Fin 3) :
    annihilation i * annihilation i = 0 := by
  exact a_sq_zero i.castSucc

@[simp] theorem creation_sq (i : Fin 3) :
    creation i * creation i = 0 := by
  exact aDag_sq_zero i.castSucc

theorem annihilation_anticomm (i j : Fin 3) :
    annihilation i * annihilation j + annihilation j * annihilation i = 0 := by
  exact a_a_anticomm i.castSucc j.castSucc

theorem creation_anticomm (i j : Fin 3) :
    creation i * creation j + creation j * creation i = 0 := by
  exact aDag_aDag_anticomm i.castSucc j.castSucc

theorem car_pairing (i j : Fin 3) :
    annihilation i * creation j + creation j * annihilation i =
      if i = j then (1 : Cl44) else 0 := by
  by_cases h : i = j
  · subst j
    simpa [annihilation, creation] using car_identity i.castSucc i.castSucc
  · simpa [annihilation, creation, h] using
      car_identity i.castSucc j.castSucc

/-! These finite occupation labels are spectral data, not an asserted
operator eigenbasis.  The distinction is intentional until a concrete Fock
module and inner product are supplied. -/

def parityBit (w : Occupation3) : ZMod 2 :=
  if Even (degree w) then 0 else 1

@[simp] theorem parityBit_reflected (w : Occupation3) :
    parityBit (reflected w) = 1 - parityBit w := by
  revert w
  native_decide

theorem even_sector_card :
    Fintype.card {w : Occupation3 // Even (degree w)} = 4 := by
  decide

theorem odd_sector_card :
    Fintype.card {w : Occupation3 // ¬ Even (degree w)} = 4 := by
  decide

/-! ### Diagonal occupation operator -/

abbrev Function3 :=
  InfoGeometry.OperatorAlgebra.SplitCliffordRealForms.OccupationFunction 3

/-- Diagonal number operator on the finite occupation-function carrier. -/
def numberOperator : Function3 →ₗ[ℝ] Function3 where
  toFun f := fun w => (degree w : ℝ) * f w
  map_add' f g := by
    funext w
    simp [mul_add]
  map_smul' c f := by
    funext w
    simp [mul_assoc, mul_comm, mul_left_comm]

/-- Complement/reflection operator on occupation functions. -/
def reflectionOperator : Function3 →ₗ[ℝ] Function3 :=
  (InfoGeometry.OperatorAlgebra.SplitCliffordRealForms.occupationComplementClosure 3).theta

/-- Coordinate delta mode at an occupation state. -/
def deltaMode (w : Occupation3) : Function3 := fun x => if x = w then 1 else 0

@[simp] theorem numberOperator_deltaMode (w : Occupation3) :
    numberOperator (deltaMode w) = (degree w : ℝ) • deltaMode w := by
  funext x
  by_cases h : x = w <;> simp [numberOperator, deltaMode, h]

@[simp] theorem reflectionOperator_deltaMode (w : Occupation3) :
    reflectionOperator (deltaMode w) = deltaMode (reflected w) := by
  funext x
  change deltaMode w (reflected x) = deltaMode (reflected w) x
  by_cases h : reflected x = w
  · have hx : x = reflected w := by
      have h' := congrArg reflected h
      have hxx : reflected (reflected x) = x := by
        simpa [reflected] using
          InfoGeometry.OperatorAlgebra.SplitCliffordRealForms.Occupation.complement_involutive x
      exact hxx.symm.trans h'
    have hrr : reflected (reflected w) = w := by
      simpa [reflected] using
        InfoGeometry.OperatorAlgebra.SplitCliffordRealForms.Occupation.complement_involutive w
    simp [deltaMode, h, hx, hrr]
  · have hx : x ≠ reflected w := by
      intro hx
      apply h
      rw [hx]
      simpa [reflected] using
        InfoGeometry.OperatorAlgebra.SplitCliffordRealForms.Occupation.complement_involutive w
    simp [deltaMode, h, hx]

theorem numberOperator_reflection (f : Function3) :
    numberOperator (reflectionOperator f) =
      (3 : ℝ) • reflectionOperator f - reflectionOperator (numberOperator f) := by
  funext w
  change (degree w : ℝ) * f (reflected w) =
    3 * f (reflected w) - (degree (reflected w) : ℝ) * f (reflected w)
  rw [degree_reflected, Nat.cast_sub (degree_le_three w)]
  ring

/-! ### Reflection, chirality, and the induced complex structure -/

def paritySign (w : Occupation3) : ℝ :=
  parity w

/-- Fermion parity, viewed as a diagonal linear operator. -/
def chiralityOperator : Function3 →ₗ[ℝ] Function3 where
  toFun f := fun w => paritySign w * f w
  map_add' f g := by
    funext w
    simp [paritySign, mul_add]
  map_smul' c f := by
    funext w
    change paritySign w * (c * f w) = c * (paritySign w * f w)
    simp [mul_assoc, mul_comm, mul_left_comm]

@[simp] theorem paritySign_sq (w : Occupation3) :
    paritySign w * paritySign w = 1 := by
  change (parity w : ℝ) * (parity w : ℝ) = 1
  exact_mod_cast parity_sq w

@[simp] theorem paritySign_reflected (w : Occupation3) :
    paritySign (reflected w) = -paritySign w := by
  change (parity (reflected w) : ℝ) = -(parity w : ℝ)
  rw [parity_reflected]
  norm_num

@[simp] theorem reflectionOperator_sq :
    reflectionOperator.comp reflectionOperator = LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext w
  change f (reflected (reflected w)) = f w
  rw [show reflected (reflected w) = w by
    simpa [reflected] using
      InfoGeometry.OperatorAlgebra.SplitCliffordRealForms.Occupation.complement_involutive w]

@[simp] theorem chiralityOperator_sq :
    chiralityOperator.comp chiralityOperator = LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext w
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  change paritySign w * (paritySign w * f w) = f w
  rw [← mul_assoc, paritySign_sq, one_mul]

theorem reflection_chirality_anticommute :
    reflectionOperator.comp chiralityOperator =
      -(chiralityOperator.comp reflectionOperator) := by
  apply LinearMap.ext
  intro f
  funext w
  simp only [LinearMap.comp_apply, LinearMap.neg_apply]
  change paritySign (reflected w) * f (reflected w) =
    -(paritySign w * f (reflected w))
  rw [paritySign_reflected]
  ring

theorem numberOperator_reflection_conjugate :
    reflectionOperator.comp (numberOperator.comp reflectionOperator) =
      (3 : ℝ) • LinearMap.id - numberOperator := by
  apply LinearMap.ext
  intro f
  funext w
  change (degree (reflected w) : ℝ) * f (reflected (reflected w)) =
    3 * f w - (degree w : ℝ) * f w
  rw [show reflected (reflected w) = w by
    simpa [reflected] using
      InfoGeometry.OperatorAlgebra.SplitCliffordRealForms.Occupation.complement_involutive w]
  rw [degree_reflected, Nat.cast_sub (degree_le_three w)]
  ring

/-- Centered occupation charge `Q = N - 3/2`. -/
def centeredNumberOperator : Function3 →ₗ[ℝ] Function3 :=
  numberOperator - (3 / 2 : ℝ) • LinearMap.id

theorem centeredNumberOperator_reflection (f : Function3) :
    centeredNumberOperator (reflectionOperator f) =
      -reflectionOperator (centeredNumberOperator f) := by
  funext w
  change (degree w : ℝ) * f (reflected w) - (3 / 2 : ℝ) * f (reflected w) =
    -((degree (reflected w) : ℝ) * f (reflected w) -
      (3 / 2 : ℝ) * f (reflected w))
  rw [degree_reflected, Nat.cast_sub (degree_le_three w)]
  ring

def complexStructureOperator : Function3 →ₗ[ℝ] Function3 :=
  chiralityOperator.comp reflectionOperator

@[simp] theorem complexStructureOperator_sq :
    complexStructureOperator.comp complexStructureOperator =
      -(LinearMap.id : Function3 →ₗ[ℝ] Function3) := by
  apply LinearMap.ext
  intro f
  funext w
  unfold complexStructureOperator
  unfold chiralityOperator reflectionOperator
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply]
  change paritySign w *
      (paritySign (reflected w) * f (reflected (reflected w))) = -f w
  rw [show reflected (reflected w) = w by
    simpa [reflected] using
      InfoGeometry.OperatorAlgebra.SplitCliffordRealForms.Occupation.complement_involutive w]
  rw [paritySign_reflected]
  calc
    paritySign w * (-paritySign w * f w) =
        -(paritySign w * (paritySign w * f w)) := by ring
    _ = -f w := by rw [← mul_assoc, paritySign_sq, one_mul]

end InfoGeometry.OperatorAlgebra.SplitOctonionChiralFockSpectrum
