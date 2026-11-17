/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.ChiralProjectorFromInvolution

/-!
# Ginsparg–Wilson algebra from two chiral involutions

This module works in an associative real algebra, including native matrix and
linear-endomorphism algebras. Multiplication order is retained throughout.

For a chiral involution `gamma`, the normalized Ginsparg–Wilson defect is
`gamma * D + D * gamma - D * gamma * D`. Its vanishing is equivalent to the
involution law for `gamma * (1 - D)`. Conversely, two involutions `gamma` and
`epsilon` construct `D = 1 - gamma * epsilon` satisfying that relation. The
existing `ChiralInvolution` owner supplies both pairs of half-projectors; the
new bridge proves their ordered intertwining and native linear-range mapping.

The normalization is dimensionless: here `D` corresponds to `a * D_phys`.
In the overlap convention `a * D_phys = 1 + gamma * sign(H_W)`, the second
involution is `epsilon = -sign(H_W)` and the modified chirality is `epsilon`.

No Wilson lattice operator, spectral sign, admissibility/locality estimate,
fermion measure, anomaly cancellation, refinement limit, reflection positivity,
or interacting continuum theory is constructed by this algebraic result.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.GinspargWilson

variable {Op : Type*} [Ring Op] [Algebra ℝ Op]

/-- Ordered defect of the dimensionless Ginsparg–Wilson relation. -/
def gwDefect (gamma : ChiralInvolution Op) (D : Op) : Op :=
  gamma.chi * D + D * gamma.chi - D * gamma.chi * D

/-- The chirality modified by a dimensionless Dirac operator. -/
def modifiedChirality (gamma : ChiralInvolution Op) (D : Op) : Op :=
  gamma.chi * (1 - D)

/-- The algebraic overlap operator constructed from two involutions. -/
def overlapDirac (gamma epsilon : ChiralInvolution Op) : Op :=
  1 - gamma.chi * epsilon.chi

theorem gwDefect_eq_zero_iff (gamma : ChiralInvolution Op) (D : Op) :
    gwDefect gamma D = 0 ↔
      gamma.chi * D + D * gamma.chi = D * gamma.chi * D := by
  exact sub_eq_zero

/-- The same defect measures failure of the two-chirality intertwining law. -/
theorem dirac_modified_defect (gamma : ChiralInvolution Op) (D : Op) :
    D * modifiedChirality gamma D + gamma.chi * D = gwDefect gamma D := by
  unfold modifiedChirality gwDefect
  noncomm_ring

/-- Exact square defect, before assuming the Ginsparg–Wilson relation. -/
theorem modifiedChirality_sq (gamma : ChiralInvolution Op) (D : Op) :
    modifiedChirality gamma D * modifiedChirality gamma D =
      1 - gamma.chi * gwDefect gamma D := by
  unfold modifiedChirality gwDefect
  calc
    (gamma.chi * (1 - D)) * (gamma.chi * (1 - D)) =
        gamma.chi * gamma.chi -
          gamma.chi * (gamma.chi * D + D * gamma.chi - D * gamma.chi * D) := by
            noncomm_ring
    _ = 1 - gamma.chi *
        (gamma.chi * D + D * gamma.chi - D * gamma.chi * D) := by
          rw [gamma.chi_sq]

/-- Modified chirality is an involution exactly when the GW defect vanishes. -/
theorem modifiedChirality_sq_eq_one_iff (gamma : ChiralInvolution Op) (D : Op) :
    modifiedChirality gamma D * modifiedChirality gamma D = 1 ↔
      gwDefect gamma D = 0 := by
  rw [modifiedChirality_sq]
  constructor
  · intro h
    have hzero : gamma.chi * gwDefect gamma D = 0 := by
      calc
        gamma.chi * gwDefect gamma D =
            1 - (1 - gamma.chi * gwDefect gamma D) := by abel
        _ = 0 := by rw [h, sub_self]
    calc
      gwDefect gamma D = gamma.chi * (gamma.chi * gwDefect gamma D) := by
        rw [← mul_assoc, gamma.chi_sq, one_mul]
      _ = 0 := by rw [hzero, mul_zero]
  · intro h
    rw [h, mul_zero, sub_zero]

/-- Reuse the existing projector owner for a GW-modified involution. -/
def modifiedInvolution (gamma : ChiralInvolution Op) (D : Op)
    (hD : gwDefect gamma D = 0) : ChiralInvolution Op where
  chi := modifiedChirality gamma D
  chi_sq := (modifiedChirality_sq_eq_one_iff gamma D).2 hD

/-- Reconstructing the Dirac operator from its modified chirality is exact. -/
theorem one_sub_chi_mul_modifiedChirality (gamma : ChiralInvolution Op) (D : Op) :
    1 - gamma.chi * modifiedChirality gamma D = D := by
  unfold modifiedChirality
  rw [← mul_assoc, gamma.chi_sq, one_mul]
  abel

/-- For the constructed overlap operator, modified chirality is the second input. -/
theorem modifiedChirality_overlapDirac (gamma epsilon : ChiralInvolution Op) :
    modifiedChirality gamma (overlapDirac gamma epsilon) = epsilon.chi := by
  unfold modifiedChirality overlapDirac
  calc
    gamma.chi * (1 - (1 - gamma.chi * epsilon.chi)) =
        gamma.chi * (gamma.chi * epsilon.chi) := by noncomm_ring
    _ = epsilon.chi := by rw [← mul_assoc, gamma.chi_sq, one_mul]

/-- Two involutions construct a GW solution; GW is not an input field. -/
theorem overlapDirac_gwDefect_eq_zero (gamma epsilon : ChiralInvolution Op) :
    gwDefect gamma (overlapDirac gamma epsilon) = 0 := by
  apply (modifiedChirality_sq_eq_one_iff gamma (overlapDirac gamma epsilon)).1
  simpa only [modifiedChirality_overlapDirac] using epsilon.chi_sq

theorem overlapDirac_ginspargWilson (gamma epsilon : ChiralInvolution Op) :
    gamma.chi * overlapDirac gamma epsilon +
        overlapDirac gamma epsilon * gamma.chi =
      overlapDirac gamma epsilon * gamma.chi * overlapDirac gamma epsilon := by
  exact (gwDefect_eq_zero_iff gamma (overlapDirac gamma epsilon)).1
    (overlapDirac_gwDefect_eq_zero gamma epsilon)

/-- GW implies intertwining between the two distinct chirality operators. -/
theorem dirac_modified_intertwining (gamma : ChiralInvolution Op) (D : Op)
    (hD : gwDefect gamma D = 0) :
    D * modifiedChirality gamma D = -(gamma.chi * D) := by
  apply add_eq_zero_iff_eq_neg.mp
  rw [dirac_modified_defect, hD]

theorem overlapDirac_intertwining (gamma epsilon : ChiralInvolution Op) :
    overlapDirac gamma epsilon * epsilon.chi =
      -(gamma.chi * overlapDirac gamma epsilon) := by
  simpa only [modifiedChirality_overlapDirac] using
    dirac_modified_intertwining gamma (overlapDirac gamma epsilon)
      (overlapDirac_gwDefect_eq_zero gamma epsilon)

/-! ## Intertwining the existing half-projectors -/

/-- Two-chirality intertwining exchanges the positive and negative projectors. -/
theorem dirac_mul_Pleft_of_intertwining (gamma epsilon : ChiralInvolution Op)
    (D : Op) (hD : D * epsilon.chi = -(gamma.chi * D)) :
    D * epsilon.Pleft = gamma.Pright * D := by
  simp only [ChiralInvolution.Pleft, ChiralInvolution.Pright,
    mul_smul_comm, smul_mul_assoc, mul_add, sub_mul, mul_one, one_mul]
  rw [hD, sub_eq_add_neg]

theorem dirac_mul_Pright_of_intertwining (gamma epsilon : ChiralInvolution Op)
    (D : Op) (hD : D * epsilon.chi = -(gamma.chi * D)) :
    D * epsilon.Pright = gamma.Pleft * D := by
  simp only [ChiralInvolution.Pleft, ChiralInvolution.Pright,
    mul_smul_comm, smul_mul_assoc, mul_sub, add_mul, mul_one, one_mul,
    hD, sub_neg_eq_add]

theorem dirac_mul_modified_Pleft (gamma : ChiralInvolution Op) (D : Op)
    (hD : gwDefect gamma D = 0) :
    D * (modifiedInvolution gamma D hD).Pleft = gamma.Pright * D := by
  exact dirac_mul_Pleft_of_intertwining gamma (modifiedInvolution gamma D hD) D
    (dirac_modified_intertwining gamma D hD)

theorem dirac_mul_modified_Pright (gamma : ChiralInvolution Op) (D : Op)
    (hD : gwDefect gamma D = 0) :
    D * (modifiedInvolution gamma D hD).Pright = gamma.Pleft * D := by
  exact dirac_mul_Pright_of_intertwining gamma (modifiedInvolution gamma D hD) D
    (dirac_modified_intertwining gamma D hD)

theorem overlapDirac_mul_Pleft (gamma epsilon : ChiralInvolution Op) :
    overlapDirac gamma epsilon * epsilon.Pleft =
      gamma.Pright * overlapDirac gamma epsilon := by
  exact dirac_mul_Pleft_of_intertwining gamma epsilon (overlapDirac gamma epsilon)
    (overlapDirac_intertwining gamma epsilon)

theorem overlapDirac_mul_Pright (gamma epsilon : ChiralInvolution Op) :
    overlapDirac gamma epsilon * epsilon.Pright =
      gamma.Pleft * overlapDirac gamma epsilon := by
  exact dirac_mul_Pright_of_intertwining gamma epsilon (overlapDirac gamma epsilon)
    (overlapDirac_intertwining gamma epsilon)

/-! ## Native linear-operator range transport -/

section LinearMaps

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The constructed operator maps the modified positive sector into the negative sector. -/
theorem overlapDirac_maps_left_range
    (gamma epsilon : ChiralInvolution (Module.End ℝ V)) :
    Set.MapsTo (overlapDirac gamma epsilon)
      (LinearMap.range epsilon.Pleft) (LinearMap.range gamma.Pright) := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  refine ⟨overlapDirac gamma epsilon y, ?_⟩
  exact (LinearMap.congr_fun (overlapDirac_mul_Pleft gamma epsilon) y).symm

/-- The constructed operator maps the modified negative sector into the positive sector. -/
theorem overlapDirac_maps_right_range
    (gamma epsilon : ChiralInvolution (Module.End ℝ V)) :
    Set.MapsTo (overlapDirac gamma epsilon)
      (LinearMap.range epsilon.Pright) (LinearMap.range gamma.Pleft) := by
  intro x hx
  rcases hx with ⟨y, rfl⟩
  refine ⟨overlapDirac gamma epsilon y, ?_⟩
  exact (LinearMap.congr_fun (overlapDirac_mul_Pright gamma epsilon) y).symm

end LinearMaps

/-! ## Optional adjoint hypotheses, kept separate from the GW algebra -/

section Star

variable [StarRing Op]

/-- Self-adjoint involutions give the usual gamma-Hermiticity identity. -/
theorem star_overlapDirac (gamma epsilon : ChiralInvolution Op)
    (hgamma : star gamma.chi = gamma.chi)
    (hepsilon : star epsilon.chi = epsilon.chi) :
    star (overlapDirac gamma epsilon) =
      gamma.chi * overlapDirac gamma epsilon * gamma.chi := by
  unfold overlapDirac
  rw [star_sub, star_one, star_mul, hepsilon, hgamma]
  calc
    1 - epsilon.chi * gamma.chi =
        gamma.chi * gamma.chi -
          (gamma.chi * gamma.chi) * (epsilon.chi * gamma.chi) := by
            rw [gamma.chi_sq, one_mul]
    _ = gamma.chi * (1 - gamma.chi * epsilon.chi) * gamma.chi := by
      noncomm_ring

/-- Gamma-Hermiticity makes modified chirality self-adjoint. -/
theorem star_modifiedChirality (gamma : ChiralInvolution Op) (D : Op)
    (hgamma : star gamma.chi = gamma.chi)
    (hD : star D = gamma.chi * D * gamma.chi) :
    star (modifiedChirality gamma D) = modifiedChirality gamma D := by
  calc
    star (modifiedChirality gamma D) =
        (1 - gamma.chi * D * gamma.chi) * gamma.chi := by
          simp only [modifiedChirality, star_mul, star_sub, star_one, hgamma, hD]
    _ = gamma.chi - (gamma.chi * D) * (gamma.chi * gamma.chi) := by
      noncomm_ring
    _ = modifiedChirality gamma D := by
      rw [gamma.chi_sq, mul_one]
      simp only [modifiedChirality, mul_sub, mul_one]

end Star

end InfoGeometry.OperatorAlgebra.GinspargWilson
