import Mathlib
import proofs.KleinSixStateBundle

/-!
# Reciprocal affine Klein action and its torus shadow

The universal reciprocal cover is `ℝ²`.  Its glide is the half-period
translation followed by transverse reflection.  Squaring it gives the full
longitudinal translation.  Passing coordinatewise to `AddCircle (2π)` turns
the glide into an involution on the Brillouin torus.

The orbit-space Klein bottle is not defined in this file; this owner supplies
the action and the cover-to-torus compatibility needed for that quotient.
-/

noncomputable section

namespace KleinBrillouinBase

abbrev Cover := ℝ × ℝ

def tx (k : Cover) : Cover := (k.1 + 2 * Real.pi, k.2)
def ty (k : Cover) : Cover := (k.1, k.2 + 2 * Real.pi)
def tyInv (k : Cover) : Cover := (k.1, k.2 - 2 * Real.pi)

/-- Lifted glide `(kx,ky) ↦ (kx+π,-ky)`. -/
def glide (k : Cover) : Cover := (k.1 + Real.pi, -k.2)
def glideInv (k : Cover) : Cover := (k.1 - Real.pi, -k.2)

theorem glide_sq (k : Cover) : glide (glide k) = tx k := by
  apply Prod.ext <;> simp [glide, tx] <;> ring

theorem glide_left_inverse (k : Cover) : glideInv (glide k) = k := by
  apply Prod.ext <;> simp [glide, glideInv]

theorem glide_right_inverse (k : Cover) : glide (glideInv k) = k := by
  apply Prod.ext <;> simp [glide, glideInv]

/-- The glide reverses the transverse reciprocal translation. -/
theorem glide_conj_ty (k : Cover) :
    glide (ty (glideInv k)) = tyInv k := by
  apply Prod.ext <;> simp [glide, glideInv, ty, tyInv] <;> ring

/-! ## Brillouin torus -/

abbrev MomentumCircle := AddCircle (2 * Real.pi)
abbrev BrillouinTorus := MomentumCircle × MomentumCircle

def coverToTorus (k : Cover) : BrillouinTorus := (k.1, k.2)

/-- Induced glide after quotienting by both reciprocal periods. -/
def torusGlide (k : BrillouinTorus) : BrillouinTorus :=
  (k.1 + (Real.pi : MomentumCircle), -k.2)

theorem two_pi_eq_zero :
    (((2 * Real.pi : ℝ) : MomentumCircle)) = 0 :=
  AddCircle.coe_period _

theorem pi_add_pi_eq_zero :
    (Real.pi : MomentumCircle) + (Real.pi : MomentumCircle) = 0 := by
  rw [← AddCircle.coe_add]
  convert two_pi_eq_zero using 1
  ring_nf

theorem pi_ne_zero : (Real.pi : MomentumCircle) ≠ 0 := by
  intro h
  rw [AddCircle.coe_eq_zero_iff (2 * Real.pi)] at h
  obtain ⟨n, hn⟩ := h
  have hp : (Real.pi : ℝ) > 0 := Real.pi_pos
  rw [zsmul_eq_mul] at hn
  have hn' : (2 * (n : ℝ) - 1) * Real.pi = 0 := by
    calc
      (2 * (n : ℝ) - 1) * Real.pi =
          (n : ℝ) * (2 * Real.pi) - Real.pi := by ring
      _ = 0 := by rw [hn]; ring
  have hz : (2 : ℤ) * n - 1 = 0 := by
    exact_mod_cast (mul_eq_zero.mp hn').resolve_right (ne_of_gt hp)
  omega

theorem torusGlide_ne_self (k : BrillouinTorus) : torusGlide k ≠ k := by
  intro h
  have hfst := congrArg Prod.fst h
  change k.1 + (Real.pi : MomentumCircle) = k.1 at hfst
  have : (Real.pi : MomentumCircle) = 0 := by
    exact add_left_cancel (show k.1 + (Real.pi : MomentumCircle) =
      k.1 + 0 by simpa using hfst)
  exact pi_ne_zero this

theorem torusGlide_involutive : Function.Involutive torusGlide := by
  intro k
  apply Prod.ext
  · change (k.1 + (Real.pi : MomentumCircle)) + Real.pi = k.1
    rw [add_assoc, pi_add_pi_eq_zero, add_zero]
  · simp [torusGlide]

/-- The affine glide descends to the torus involution. -/
theorem coverToTorus_glide (k : Cover) :
    coverToTorus (glide k) = torusGlide (coverToTorus k) := by
  apply Prod.ext <;> simp [coverToTorus, glide, torusGlide, AddCircle.coe_add]

/-- Full reciprocal translations disappear under the torus projection. -/
theorem coverToTorus_tx (k : Cover) : coverToTorus (tx k) = coverToTorus k := by
  apply Prod.ext
  · change ((k.1 + 2 * Real.pi : ℝ) : MomentumCircle) = (k.1 : MomentumCircle)
    rw [AddCircle.coe_add, two_pi_eq_zero, add_zero]
  · rfl

theorem coverToTorus_ty (k : Cover) : coverToTorus (ty k) = coverToTorus k := by
  apply Prod.ext
  · rfl
  · change ((k.2 + 2 * Real.pi : ℝ) : MomentumCircle) = (k.2 : MomentumCircle)
    rw [AddCircle.coe_add, two_pi_eq_zero, add_zero]

/-- Cover and quotient-level statements packaged without asserting that the
final orbit space has already been constructed. -/
theorem affine_to_torus_klein_packet (k : Cover) :
    glide (glide k) = tx k ∧
    glide (ty (glideInv k)) = tyInv k ∧
    torusGlide (torusGlide (coverToTorus k)) = coverToTorus k ∧
    coverToTorus (glide k) = torusGlide (coverToTorus k) := by
  exact ⟨glide_sq k, glide_conj_ty k,
    torusGlide_involutive (coverToTorus k), coverToTorus_glide k⟩

end KleinBrillouinBase

end noncomputable section
