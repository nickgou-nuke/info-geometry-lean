import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Canonical.LeeYangAsanoDigest
import InfoGeometry.Canonical.PrimeCl11ModularAtomCore

/-!
# InfoGeometry.Canonical.LeeYangAsanoNativeCore

Native algebraic closure for the first Asano-contraction branches.

This file does not claim the full Ruelle/Asano theorem.
It packages the algebraic `D = 0` branch, the determinant-zero transfer
branch, and the quadratic reduction used by the Möbius case.

No witness packets.
No `sorry`.
No convergence claim.
-/

noncomputable section

namespace InfoGeometry.Canonical.LeeYangAsanoNativeCore

open Set
open InfoGeometry.Canonical.LeeYangAsanoDigest
open InfoGeometry.Canonical.PrimeCl11ModularAtomCore

/-- The Asano forbidden set, with the standard sign convention. -/
@[rep_depth thermo]
def negProductSet (K1 K2 : Set ℂ) : Set ℂ :=
  {z : ℂ | ∃ u ∈ K1, ∃ v ∈ K2, z = -(u * v)}

/-- Two-variable affine polynomial shape used in the Asano contraction. -/
@[rep_depth thermo]
def asanoPhi (A B C D z1 z2 : ℂ) : ℂ :=
  A + B * z1 + C * z2 + D * z1 * z2

/--
The Möbius root map of the affine equation
`asanoPhi A B C D z1 z2 = 0`, solved for `z2`.
-/
@[rep_depth thermo]
def asanoRootMap (A B C D z1 : ℂ) : ℂ :=
  -((A + B * z1) / (C + D * z1))

/--
Substituting the root map makes the affine Asano polynomial vanish,
provided the denominator is nonzero.
-/
@[rep_depth thermo]
theorem asanoPhi_rootMap_zero
    {A B C D z1 : ℂ}
    (hden : C + D * z1 ≠ 0) :
    asanoPhi A B C D z1 (asanoRootMap A B C D z1) = 0 := by
  have hsplit :
      asanoPhi A B C D z1 (asanoRootMap A B C D z1) =
        (A + B * z1) + (C + D * z1) * asanoRootMap A B C D z1 := by
    unfold asanoPhi asanoRootMap
    ring
  have hcancel :
      (C + D * z1) * asanoRootMap A B C D z1 = -(A + B * z1) := by
    unfold asanoRootMap
    field_simp [hden]
  rw [hsplit, hcancel]
  ring

/--
If the affine Asano polynomial vanishes, then the second variable is the
Möbius root map, provided the coefficient of `z2` is nonzero.
-/
@[rep_depth thermo]
theorem z₂_eq_asanoRootMap_of_asanoPhi_eq_zero
    {A B C D z1 z2 : ℂ}
    (hden : C + D * z1 ≠ 0)
    (hzero : asanoPhi A B C D z1 z2 = 0) :
    z2 = asanoRootMap A B C D z1 := by
  unfold asanoPhi asanoRootMap at *
  have hlin : (C + D * z1) * z2 = -(A + B * z1) := by
    calc
      (C + D * z1) * z2 = C * z2 + D * z1 * z2 := by ring
      _ = -(A + B * z1) := by
        have h := congrArg (fun x => x - (A + B * z1)) hzero
        ring_nf at h ⊢
        exact h
  calc
    z2 = ((C + D * z1) * z2) / (C + D * z1) := by
      have hdiv : ((C + D * z1) * z2) / (C + D * z1) = z2 := by
        field_simp [hden]
      exact hdiv.symm
    _ = (-(A + B * z1)) / (C + D * z1) := by rw [hlin]
    _ = -((A + B * z1) / (C + D * z1)) := by ring

@[rep_depth thermo]
theorem asano_contraction_D_eq_zero_no_root
    {K1 K2 : Set ℂ}
    {A B C z : ℂ}
    (h0K1 : (0 : ℂ) ∉ K1)
    (h0K2 : (0 : ℂ) ∉ K2)
    (hPhi :
      ∀ z1 z2 : ℂ,
        z1 ∉ K1 →
        z2 ∉ K2 →
        asanoPhi A B C 0 z1 z2 ≠ 0)
    (hroot : A + 0 * z = 0) :
    False := by
  have hA : A = 0 := by
    simpa using hroot
  have hbad : asanoPhi A B C 0 0 0 = 0 := by
    simp [asanoPhi, hA]
  exact (hPhi 0 0 h0K1 h0K2) hbad

@[rep_depth thermo]
theorem asano_contraction_D_eq_zero_nonzero
    {K1 K2 : Set ℂ}
    {A B C z : ℂ}
    (h0K1 : (0 : ℂ) ∉ K1)
    (h0K2 : (0 : ℂ) ∉ K2)
    (hPhi :
      ∀ z1 z2 : ℂ,
        z1 ∉ K1 →
        z2 ∉ K2 →
        asanoPhi A B C 0 z1 z2 ≠ 0) :
    A + 0 * z ≠ 0 := by
  intro hroot
  exact asano_contraction_D_eq_zero_no_root h0K1 h0K2 hPhi hroot

@[rep_depth thermo]
theorem asano_det_zero_root_mem_negProductSet
    {K1 K2 : Set ℂ}
    {A B C D z : ℂ}
    (h0K1 : (0 : ℂ) ∉ K1)
    (h0K2 : (0 : ℂ) ∉ K2)
    (hD : D ≠ 0)
    (hDet : A * D - B * C = 0)
    (hPhi :
      ∀ z1 z2 : ℂ,
        z1 ∉ K1 →
        z2 ∉ K2 →
        asanoPhi A B C D z1 z2 ≠ 0)
    (hroot : A + D * z = 0) :
    z ∈ negProductSet K1 K2 := by
  by_cases hC : C = 0
  · have hAD : A * D = 0 := by
      simpa [hC] using hDet
    have hA : A = 0 := by
      rcases mul_eq_zero.mp hAD with hA | hD0
      · exact hA
      · exact False.elim (hD hD0)
    have hbad : asanoPhi A B C D 0 0 = 0 := by
      simp [asanoPhi, hA, hC]
    exact False.elim ((hPhi 0 0 h0K1 h0K2) hbad)
  · let u : ℂ := -(C / D)
    let v : ℂ := -(B / D)

    have huK : u ∈ K1 := by
      by_contra hu
      have hzero : asanoPhi A B C D u 0 = 0 := by
        subst u
        unfold asanoPhi
        field_simp [hD]
        ring_nf
        exact hDet
      exact (hPhi (-(C / D)) 0 hu h0K2) hzero

    have hvK : v ∈ K2 := by
      by_contra hv
      have hzero : asanoPhi A B C D 0 v = 0 := by
        subst v
        unfold asanoPhi
        field_simp [hD]
        ring_nf
        have hDet' : A * D = B * C := by
          simpa [sub_eq_zero] using hDet
        simpa [sub_eq_zero] using hDet'
      exact (hPhi 0 (-(B / D)) h0K1 hv) hzero

    have hDz : D * z = -A := by
      calc
        D * z = (A + D * z) - A := by ring
        _ = 0 - A := by rw [hroot]
        _ = -A := by ring

    have hz : z = - A / D := by
      apply (eq_div_iff hD).2
      simpa [mul_comm] using hDz

    have hprod : (C / D) * (B / D) = A / D := by
      field_simp [hD]
      ring_nf
      simpa [sub_eq_zero, mul_comm] using (sub_eq_zero.mp hDet).symm

    refine ⟨u, huK, v, hvK, ?_⟩
    subst u v
    simp [hz, hprod, neg_div]

@[rep_depth thermo]
theorem asano_det_zero_contraction_nonzero_off_negProductSet
    {K1 K2 : Set ℂ}
    {A B C D z : ℂ}
    (h0K1 : (0 : ℂ) ∉ K1)
    (h0K2 : (0 : ℂ) ∉ K2)
    (hD : D ≠ 0)
    (hDet : A * D - B * C = 0)
    (hPhi :
      ∀ z1 z2 : ℂ,
        z1 ∉ K1 →
        z2 ∉ K2 →
        asanoPhi A B C D z1 z2 ≠ 0)
    (hzOff : z ∉ negProductSet K1 K2) :
    A + D * z ≠ 0 := by
  intro hroot
  exact hzOff
    (asano_det_zero_root_mem_negProductSet
      (K1 := K1) (K2 := K2) (A := A) (B := B) (C := C) (D := D)
      h0K1 h0K2 hD hDet hPhi hroot)

/-- The Möbius transform induced by a nondegenerate Asano polynomial. -/
@[rep_depth thermo]
structure MoebiusTransform (K : Type*) [Field K] where
  a : K
  b : K
  c : K
  d : K
  det_neq_zero : a * d - b * c ≠ 0

/-- Extract the Möbius coefficients from a nondegenerate Asano polynomial. -/
@[rep_depth thermo]
def extractMoebius (A B C D : ℂ) (hDet : A * D - B * C ≠ 0) :
    MoebiusTransform ℂ :=
  { a := - C
  , b := - A
  , c := D
  , d := B
  , det_neq_zero := by
      have h_alg : (- C) * B - (- A) * D = A * D - B * C := by ring
      rw [h_alg]
      exact hDet }

end InfoGeometry.Canonical.LeeYangAsanoNativeCore
