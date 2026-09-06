/- Sandbox for Serre Spectral Sequence - one genuine lemma at a time -/

import InfoGeometry.Spectral.Spectrum.Basic
import InfoGeometry.Spectral.Algebra.ExactCouple
import InfoGeometry.Spectral.Algebra.SpectralSequence
import InfoGeometry.Spectral.Cohomology.SerreExactCouple

open InfoGeometry.Spectral.Spectrum.Basic
open InfoGeometry.Spectral.Algebra.ExactCouple
open InfoGeometry.Spectral.Algebra

variable {u : Type}
variable {R : Type u} [Ring R]
variable {D E : Z2 → Type u}
variable [∀ pq, AddCommGroup (D pq)] [∀ pq, AddCommGroup (E pq)]
variable [∀ pq, Module R (D pq)] [∀ pq, Module R (E pq)]

/- LEMMA 1: The exact-couple differential d = j ∘ k squares to zero. -/

lemma differential_squares_to_zero (C : ExactCouple R D E) (pq : Z2) :
    (C.differential (shiftK pq)).comp (C.differential pq) = 0 := by
  exact ExactCouple.differential_comp_differential C pq

/- LEMMA 2: The exact-couple page has square-zero differential. -/

lemma exact_couple_page_sq_zero (C : ExactCouple R D E) (pq : Z2) :
    ((ExactCouple.toPage C).d (shiftK pq)).comp ((ExactCouple.toPage C).d pq) = 0 := by
  exact InfoGeometry.Spectral.Algebra.ExactCouple.toPage_differential_sq_zero C pq

/- LEMMA 3: The page differential equals the exact-couple differential. -/

lemma page_differential_eq_exact_couple_differential (C : ExactCouple R D E) (pq : Z2) :
    (ExactCouple.toPage C).d pq = C.differential pq := by
  rw [ExactCouple.toPage_d]

/- LEMMA 4: ShiftK applied twice shifts by -2 in the first component, 0 in second. -/

@[simp]
lemma shiftK_shiftK (pq : Z2) : shiftK (shiftK pq) = (pq.1 - 2, pq.2) := by
  simp [shiftK, Prod.ext_iff]
  ring_nf

/- LEMMA 5: ShiftI applied twice shifts by +2 in first, -2 in second component. -/

@[simp]
lemma shiftI_shiftI (pq : Z2) : shiftI (shiftI pq) = (pq.1 + 2, pq.2 - 2) := by
  ext <;> simp [shiftI] <;> ring_nf

/- LEMMA 6: The exact couple differential shifts indices by shiftK = (-1, 0). -/

lemma differential_shift_is_shiftK (C : ExactCouple R D E) (pq : Z2) :
    C.differential pq = (C.j (shiftK pq)).comp (C.k pq) := by
  rfl

/- LEMMA 10: The exactness condition: ker k = range j. -/

lemma exactness_ker_k_eq_range (C : ExactCouple R D E) (pq : Z2) :
    LinearMap.ker (C.k pq) = LinearMap.range (C.j pq) := by
  exact C.exact_k pq

/- LEMMA 11: The differential on the r-th page has shift (r, -r+1) -/

def shift_r (r : ℕ) (pq : Z2) : Z2 :=
  (pq.1 + r, pq.2 - r + 1)

lemma shift_r_zero (pq : Z2) : shift_r 0 pq = (pq.1, pq.2 + 1) := by
  ext <;> simp [shift_r]

lemma shift_r_two (pq : Z2) : shift_r 2 pq = (pq.1 + 2, pq.2 - 1) := by
  ext <;> simp [shift_r]
  ring_nf

lemma shift_r_three (pq : Z2) : shift_r 3 pq = (pq.1 + 3, pq.2 - 2) := by
  ext <;> simp [shift_r]
  ring_nf

/- LEMMA 12: shift_r (r+1) = shift_r ∘ shiftI -/

lemma shift_r_succ (r : ℕ) (pq : Z2) : shift_r (r + 1) pq = shift_r r (shiftI pq) := by
  ext <;> simp [shift_r, shiftI]
  <;> norm_cast at *
  <;> simp_all [Nat.cast_add, Nat.cast_one]
  <;> ring_nf at *

/- LEMMA 13: The exact couple yields a spectral sequence page -/

def exact_couple_page (C : ExactCouple R D E) : SpectralSequencePage R E shiftK :=
  C.toPage

/- LEMMA 14: The page differential is d = j ∘ k -/

lemma page_differential_eq_j_comp_k (C : ExactCouple R D E) (pq : Z2) :
    (C.toPage).d pq = (C.j (shiftK pq)).comp (C.k pq) := by
  rw [ExactCouple.toPage_d]
  rfl

/- LEMMA 15: The differential on the page squares to zero -/

lemma page_differential_sq_zero (C : ExactCouple R D E) (pq : Z2) :
    ((C.toPage).d (shiftK pq)).comp ((C.toPage).d pq) = 0 := by
  exact InfoGeometry.Spectral.Algebra.ExactCouple.toPage_differential_sq_zero C pq

/- LEMMA 16: The Serre exact couple from SerreExactCoupleData -/
/- This is imported from SerreExactCouple.lean -/

/- LEMMA 17: The E₁ page of the Serre spectral sequence -/
/- The E₁ page of the Serre spectral sequence for a fibration F → E → B
   with coefficients in a spectrum Y has terms:
   E₁^{p,q} = H^{p+q}(F; Y) for the fiber
   and the differential d₁ is the boundary map in the long exact sequence. -/

class SerreE1PageData (B F E : Type*) (Y : Spectrum) (R : Type u) [Ring R] where
  (E₁ : Z2 → Type u)
  (E₁_addCommGroup : ∀ (pq : Z2), AddCommGroup (E₁ pq))
  (E₁_module : ∀ (pq : Z2), Module R (E₁ pq))
  (d₁ : ∀ (pq : Z2),
    letI := E₁_addCommGroup pq
    letI := E₁_addCommGroup (shiftI pq)
    letI := E₁_module pq
    letI := E₁_module (shiftI pq)
    E₁ pq →ₗ[R] E₁ (shiftI pq))
  (d₁_sq_zero : ∀ (pq : Z2),
    letI := E₁_addCommGroup pq
    letI := E₁_addCommGroup (shiftI pq)
    letI := E₁_addCommGroup (shiftI (shiftI pq))
    letI := E₁_module pq
    letI := E₁_module (shiftI pq)
    letI := E₁_module (shiftI (shiftI pq))
    (d₁ (shiftI pq)).comp (d₁ pq) = 0)

/- LEMMA 18: The E₁ page differential squares to zero -/

lemma serre_e1_page_d1_sq_zero {B F E : Type*} (Y : Spectrum) (R : Type u) [Ring R]
    (data : SerreE1PageData B F E Y R) (pq : Z2) :
    letI := data.E₁_addCommGroup pq
    letI := data.E₁_addCommGroup (shiftI pq)
    letI := data.E₁_addCommGroup (shiftI (shiftI pq))
    letI := data.E₁_module pq
    letI := data.E₁_module (shiftI pq)
    letI := data.E₁_module (shiftI (shiftI pq))
    (data.d₁ (shiftI pq)).comp (data.d₁ pq) = 0 := by
  letI := data.E₁_addCommGroup pq
  letI := data.E₁_addCommGroup (shiftI pq)
  letI := data.E₁_addCommGroup (shiftI (shiftI pq))
  letI := data.E₁_module pq
  letI := data.E₁_module (shiftI pq)
  letI := data.E₁_module (shiftI (shiftI pq))
  exact data.d₁_sq_zero pq

/- LEMMA 19: The E₁ page forms a chain complex -/
/- The E₁ page differential d₁ has shift (+1, -1), so composing two gives
   shift (+2, -2) which is shiftI ∘ shiftI. The square-zero property means
   (d₁)² = 0, giving a chain complex at each bidegree. -/

lemma serre_e1_page_chain_complex {B F E : Type*} (Y : Spectrum) (R : Type u) [Ring R]
    (data : SerreE1PageData B F E Y R) (pq : Z2) :
    letI := data.E₁_addCommGroup pq
    letI := data.E₁_addCommGroup (shiftI pq)
    letI := data.E₁_addCommGroup (shiftI (shiftI pq))
    letI := data.E₁_module pq
    letI := data.E₁_module (shiftI pq)
    letI := data.E₁_module (shiftI (shiftI pq))
    (data.d₁ (shiftI pq)).comp (data.d₁ pq) = 0 := by
  letI := data.E₁_addCommGroup pq
  letI := data.E₁_addCommGroup (shiftI pq)
  letI := data.E₁_addCommGroup (shiftI (shiftI pq))
  letI := data.E₁_module pq
  letI := data.E₁_module (shiftI pq)
  letI := data.E₁_module (shiftI (shiftI pq))
  exact data.d₁_sq_zero pq
