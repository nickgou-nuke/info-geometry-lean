/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic

/-!
# De Broglie–Daviau Real Photon-Proca and Torsion-Scalar Fusion (`[CommRing R]`)

Formalizes Section 5 (Eqs. 68–80) of Claude Daviau (2001), *"Vers une mecanique quantique sans
nombre complexe"*, Ann. Fond. Louis de Broglie 26 (n deg special), 149-171, over an arbitrary
commutative ring `[CommRing R]` (without requiring `√(-1)` or division by `2` in the core
polynomial theorem).

Using `halfMass` (representing `m / 2` in Daviau Eqs. 69-70) and `photonMass := 2 * halfMass`,
we prove that under:
- Daviau's motion-lock hypothesis `(∂_μ a_j) b_k = a_j (∂_μ b_k)` (Eq. 68),
- the left-chiral first-order spinor equations for `(a₁, a₂, a₃, a₄)` with mass `halfMass` (Eq. 69),
- the right-chiral first-order spinor equations for `(b₁, b₂, b₃, b₄)` with mass `halfMass` (Eq. 70),
the real composite bilinears `(A_μ, F_{μν}, s, p, B_μ)` (Eqs. 71-72, 78-79) satisfy both:
1. Maxwell–Proca system (Eqs. 73-74): `F_{μν} = ∂_μ A_ν - ∂_ν A_μ`, `∂_μ F^{μν} = -m² A^ν`,
   `∂_μ A^μ = 0`, and the Bianchi identity `∂_ρ F_{μν} + ∂_μ F_{νρ} + ∂_ν F_{ρμ} = 0`.
2. Non-Maxwellian torsion-scalar system (Eq. 80): `∂_μ p = 0`, `∂_μ s = -m B_μ`, `∂_μ B^μ = m s`.
-/

namespace InfoGeometry.Clifford.DeBroglieDaviauPhotonProcaFusion

/-- First-order 1-jet data for the twin chiral spinors `(a₁..a₄, b₁..b₄)`, their spacetime
derivatives `(∂_μ a_j, ∂_μ b_k)`, and the constituent spinor half-mass `halfMass` (`m / 2`). -/
structure FusionJetData (R : Type*) where
  a : Fin 4 → R
  b : Fin 4 → R
  da : Fin 4 → Fin 4 → R
  db : Fin 4 → Fin 4 → R
  halfMass : R

section CommRingFusion

variable {R : Type*} [CommRing R] (D : FusionJetData R)

/-- Photon mass `m = 2 * halfMass`. -/
def photonMass : R := 2 * D.halfMass

/-- Daviau Eq. (68): 64 motion-lock bilinear constraints `(∂_μ a_j) b_k = a_j (∂_μ b_k)`. -/
def IsMotionLocked : Prop :=
  ∀ μ j k : Fin 4, D.da μ j * D.b k = D.a j * D.db μ k

/-- Daviau Eq. (69): left-chiral spinor equation with half-mass `m / 2 = D.halfMass`. -/
def SatisfiesLeftChiralEq : Prop :=
  D.halfMass * D.a 0 + D.da 0 1 + D.da 1 3 + D.da 2 0 + D.da 3 1 = 0 ∧
  D.halfMass * D.a 1 - D.da 0 0 - D.da 1 2 - D.da 2 1 + D.da 3 0 = 0 ∧
  D.halfMass * D.a 2 - D.da 0 3 - D.da 1 1 + D.da 2 2 + D.da 3 3 = 0 ∧
  D.halfMass * D.a 3 + D.da 0 2 + D.da 1 0 - D.da 2 3 + D.da 3 2 = 0

/-- Daviau Eq. (70): right-chiral spinor equation with half-mass `m / 2 = D.halfMass`. -/
def SatisfiesRightChiralEq : Prop :=
  -D.halfMass * D.b 0 + D.db 0 1 - D.db 1 3 - D.db 2 0 - D.db 3 1 = 0 ∧
  -D.halfMass * D.b 1 - D.db 0 0 + D.db 1 2 + D.db 2 1 - D.db 3 0 = 0 ∧
  -D.halfMass * D.b 2 - D.db 0 3 + D.db 1 1 - D.db 2 2 - D.db 3 3 = 0 ∧
  -D.halfMass * D.b 3 + D.db 0 2 - D.db 1 0 + D.db 2 3 - D.db 3 2 = 0

/-- Product-rule derivative `∂_μ(a_j b_k) = (∂_μ a_j) b_k + a_j (∂_μ b_k)` at indices `(j, k)`. -/
def dProd (μ j k : Fin 4) : R :=
  D.da μ j * D.b k + D.a j * D.db μ k

/-- Real electromagnetic potential covector `A_μ` (Daviau Eq. 71). -/
def photonA : Fin 4 → R
  | ⟨0, _⟩ => D.a 0 * D.b 2 + D.a 1 * D.b 3 - D.a 2 * D.b 0 - D.a 3 * D.b 1
  | ⟨1, _⟩ => D.a 0 * D.b 0 + D.a 1 * D.b 1 - D.a 2 * D.b 2 - D.a 3 * D.b 3
  | ⟨2, _⟩ => -D.a 0 * D.b 3 - D.a 1 * D.b 2 - D.a 2 * D.b 1 - D.a 3 * D.b 0
  | ⟨3, _⟩ => D.a 0 * D.b 2 - D.a 1 * D.b 3 + D.a 2 * D.b 0 - D.a 3 * D.b 1

/-- Partial derivative `∂_μ A_ν` via Leibniz rule. -/
def dPhotonA (μ ν : Fin 4) : R :=
  match ν with
  | ⟨0, _⟩ => dProd D μ 0 2 + dProd D μ 1 3 - dProd D μ 2 0 - dProd D μ 3 1
  | ⟨1, _⟩ => dProd D μ 0 0 + dProd D μ 1 1 - dProd D μ 2 2 - dProd D μ 3 3
  | ⟨2, _⟩ => -dProd D μ 0 3 - dProd D μ 1 2 - dProd D μ 2 1 - dProd D μ 3 0
  | ⟨3, _⟩ => dProd D μ 0 2 - dProd D μ 1 3 + dProd D μ 2 0 - dProd D μ 3 1

/-- Unscaled antisymmetric bilinear kernel `f_{μν}` of `F_{μν} = m f_{μν}` (Daviau Eq. 72). -/
def photonFBase (μ ν : Fin 4) : R :=
  if μ = 0 then
    if ν = 1 then -D.a 0 * D.b 1 + D.a 1 * D.b 0 - D.a 2 * D.b 3 + D.a 3 * D.b 2
    else if ν = 2 then D.a 0 * D.b 2 - D.a 1 * D.b 3 - D.a 2 * D.b 0 + D.a 3 * D.b 1
    else if ν = 3 then D.a 0 * D.b 3 + D.a 1 * D.b 2 - D.a 2 * D.b 1 - D.a 3 * D.b 0
    else 0
  else if μ = 1 then
    if ν = 0 then -(-D.a 0 * D.b 1 + D.a 1 * D.b 0 - D.a 2 * D.b 3 + D.a 3 * D.b 2)
    else if ν = 2 then D.a 0 * D.b 0 - D.a 1 * D.b 1 - D.a 2 * D.b 2 + D.a 3 * D.b 3
    else if ν = 3 then -(-D.a 0 * D.b 1 - D.a 1 * D.b 0 + D.a 2 * D.b 3 + D.a 3 * D.b 2)
    else 0
  else if μ = 2 then
    if ν = 0 then -(D.a 0 * D.b 2 - D.a 1 * D.b 3 - D.a 2 * D.b 0 + D.a 3 * D.b 1)
    else if ν = 1 then -(D.a 0 * D.b 0 - D.a 1 * D.b 1 - D.a 2 * D.b 2 + D.a 3 * D.b 3)
    else if ν = 3 then -D.a 0 * D.b 2 - D.a 1 * D.b 3 - D.a 2 * D.b 0 - D.a 3 * D.b 1
    else 0
  else
    if ν = 0 then -(D.a 0 * D.b 3 + D.a 1 * D.b 2 - D.a 2 * D.b 1 - D.a 3 * D.b 0)
    else if ν = 1 then -D.a 0 * D.b 1 - D.a 1 * D.b 0 + D.a 2 * D.b 3 + D.a 3 * D.b 2
    else if ν = 2 then -(-D.a 0 * D.b 2 - D.a 1 * D.b 3 - D.a 2 * D.b 0 - D.a 3 * D.b 1)
    else 0

/-- Partial derivative `∂_ρ f_{μν}` via Leibniz rule. -/
def dPhotonFBase (ρ μ ν : Fin 4) : R :=
  if μ = 0 then
    if ν = 1 then -dProd D ρ 0 1 + dProd D ρ 1 0 - dProd D ρ 2 3 + dProd D ρ 3 2
    else if ν = 2 then dProd D ρ 0 2 - dProd D ρ 1 3 - dProd D ρ 2 0 + dProd D ρ 3 1
    else if ν = 3 then dProd D ρ 0 3 + dProd D ρ 1 2 - dProd D ρ 2 1 - dProd D ρ 3 0
    else 0
  else if μ = 1 then
    if ν = 0 then -(-dProd D ρ 0 1 + dProd D ρ 1 0 - dProd D ρ 2 3 + dProd D ρ 3 2)
    else if ν = 2 then dProd D ρ 0 0 - dProd D ρ 1 1 - dProd D ρ 2 2 + dProd D ρ 3 3
    else if ν = 3 then -(-dProd D ρ 0 1 - dProd D ρ 1 0 + dProd D ρ 2 3 + dProd D ρ 3 2)
    else 0
  else if μ = 2 then
    if ν = 0 then -(dProd D ρ 0 2 - dProd D ρ 1 3 - dProd D ρ 2 0 + dProd D ρ 3 1)
    else if ν = 1 then -(dProd D ρ 0 0 - dProd D ρ 1 1 - dProd D ρ 2 2 + dProd D ρ 3 3)
    else if ν = 3 then -dProd D ρ 0 2 - dProd D ρ 1 3 - dProd D ρ 2 0 - dProd D ρ 3 1
    else 0
  else
    if ν = 0 then -(dProd D ρ 0 3 + dProd D ρ 1 2 - dProd D ρ 2 1 - dProd D ρ 3 0)
    else if ν = 1 then -dProd D ρ 0 1 - dProd D ρ 1 0 + dProd D ρ 2 3 + dProd D ρ 3 2
    else if ν = 2 then -(-dProd D ρ 0 2 - dProd D ρ 1 3 - dProd D ρ 2 0 - dProd D ρ 3 1)
    else 0

/-- Real electromagnetic field tensor `F_{μν} = m f_{μν}` (Daviau Eq. 72). -/
def photonF (μ ν : Fin 4) : R := photonMass D * photonFBase D μ ν

/-- Partial derivative `∂_ρ F_{μν} = m ∂_ρ f_{μν}`. -/
def dPhotonF (ρ μ ν : Fin 4) : R := photonMass D * dPhotonFBase D ρ μ ν

/-- Non-Maxwellian scalar `s` (Daviau Eq. 78). -/
def fusionScalarS : R :=
  D.a 0 * D.b 0 + D.a 1 * D.b 1 + D.a 2 * D.b 2 + D.a 3 * D.b 3

/-- Non-Maxwellian pseudoscalar `p` (Daviau Eq. 78). -/
def fusionPseudoscalarP : R :=
  D.a 0 * D.b 3 - D.a 1 * D.b 2 + D.a 2 * D.b 1 - D.a 3 * D.b 0

/-- Non-Maxwellian axial torsion pseudovector `B_μ` (Daviau Eq. 79). -/
def fusionAxialB : Fin 4 → R
  | ⟨0, _⟩ => D.a 0 * D.b 1 - D.a 1 * D.b 0 - D.a 2 * D.b 3 + D.a 3 * D.b 2
  | ⟨1, _⟩ => D.a 0 * D.b 3 - D.a 1 * D.b 2 - D.a 2 * D.b 1 + D.a 3 * D.b 0
  | ⟨2, _⟩ => D.a 0 * D.b 0 - D.a 1 * D.b 1 + D.a 2 * D.b 2 - D.a 3 * D.b 3
  | ⟨3, _⟩ => D.a 0 * D.b 1 + D.a 1 * D.b 0 + D.a 2 * D.b 3 + D.a 3 * D.b 2

def dFusionS (μ : Fin 4) : R :=
  dProd D μ 0 0 + dProd D μ 1 1 + dProd D μ 2 2 + dProd D μ 3 3

def dFusionP (μ : Fin 4) : R :=
  dProd D μ 0 3 - dProd D μ 1 2 + dProd D μ 2 1 - dProd D μ 3 0

def dFusionB (μ ν : Fin 4) : R :=
  match ν with
  | ⟨0, _⟩ => dProd D μ 0 1 - dProd D μ 1 0 - dProd D μ 2 3 + dProd D μ 3 2
  | ⟨1, _⟩ => dProd D μ 0 3 - dProd D μ 1 2 - dProd D μ 2 1 + dProd D μ 3 0
  | ⟨2, _⟩ => dProd D μ 0 0 - dProd D μ 1 1 + dProd D μ 2 2 - dProd D μ 3 3
  | ⟨3, _⟩ => dProd D μ 0 1 + dProd D μ 1 0 + dProd D μ 2 3 + dProd D μ 3 2

theorem photonF_antisymm (μ ν : Fin 4) : photonF D μ ν = -photonF D ν μ := by
  fin_cases μ <;> fin_cases ν <;> simp [photonF, photonFBase] <;> ring

private lemma eq73a_01 (h68 : IsMotionLocked D) (h69 : SatisfiesLeftChiralEq D)
    (h70 : SatisfiesRightChiralEq D) :
    photonF D 0 1 = dPhotonA D 0 1 - dPhotonA D 1 0 := by
  rcases h69 with ⟨hl0, hl1, hl2, hl3⟩; rcases h70 with ⟨hr0, hr1, hr2, hr3⟩
  have h : photonF D 0 1 - (dPhotonA D 0 1 - dPhotonA D 1 0) = 0 := by
    dsimp [photonF, photonMass, dPhotonA, dProd]; simp [photonFBase]
    have e01 := h68 2 0 1; have e10 := h68 2 1 0; have e23 := h68 2 2 3; have e32 := h68 2 3 2
    have f00 := h68 3 0 0; have f11 := h68 3 1 1; have f22 := h68 3 2 2; have f33 := h68 3 3 3
    linear_combination -1 * (hl0 * D.b 1) + 1 * (hl1 * D.b 0) + -1 * (hl2 * D.b 3) +
      1 * (hl3 * D.b 2) + 1 * (D.a 0 * hr1) + -1 * (D.a 1 * hr0) + 1 * (D.a 2 * hr3) +
      -1 * (D.a 3 * hr2) + e01 + e10 + e23 + e32 - f00 + f11 - f22 + f33
  exact sub_eq_zero.mp h

private lemma eq73a_02 (h68 : IsMotionLocked D) (h69 : SatisfiesLeftChiralEq D)
    (h70 : SatisfiesRightChiralEq D) :
    photonF D 0 2 = dPhotonA D 0 2 - dPhotonA D 2 0 := by
  rcases h69 with ⟨hl0, hl1, hl2, hl3⟩; rcases h70 with ⟨hr0, hr1, hr2, hr3⟩
  have h : photonF D 0 2 - (dPhotonA D 0 2 - dPhotonA D 2 0) = 0 := by
    dsimp [photonF, photonMass, dPhotonA, dProd]; simp [photonFBase]
    have e01 := h68 1 0 1; have e10 := h68 1 1 0; have e23 := h68 1 2 3; have e32 := h68 1 3 2
    have f03 := h68 3 0 3; have f12 := h68 3 1 2; have f21 := h68 3 2 1; have f30 := h68 3 3 0
    linear_combination 1 * (hl0 * D.b 2) - 1 * (hl1 * D.b 3) - 1 * (hl2 * D.b 0) +
      1 * (hl3 * D.b 1) - 1 * (D.a 0 * hr2) + 1 * (D.a 1 * hr3) + 1 * (D.a 2 * hr0) -
      1 * (D.a 3 * hr1) - e01 - e10 - e23 - e32 + f03 - f12 - f21 + f30
  exact sub_eq_zero.mp h

private lemma eq73a_03 (h68 : IsMotionLocked D) (h69 : SatisfiesLeftChiralEq D)
    (h70 : SatisfiesRightChiralEq D) :
    photonF D 0 3 = dPhotonA D 0 3 - dPhotonA D 3 0 := by
  rcases h69 with ⟨hl0, hl1, hl2, hl3⟩; rcases h70 with ⟨hr0, hr1, hr2, hr3⟩
  have h : photonF D 0 3 - (dPhotonA D 0 3 - dPhotonA D 3 0) = 0 := by
    dsimp [photonF, photonMass, dPhotonA, dProd]; simp [photonFBase]
    have e00 := h68 1 0 0; have e11 := h68 1 1 1; have e22 := h68 1 2 2; have e33 := h68 1 3 3
    have f03 := h68 2 0 3; have f12 := h68 2 1 2; have f21 := h68 2 2 1; have f30 := h68 2 3 0
    linear_combination 1 * (hl0 * D.b 3) + 1 * (hl1 * D.b 2) - 1 * (hl2 * D.b 1) -
      1 * (hl3 * D.b 0) - 1 * (D.a 0 * hr3) - 1 * (D.a 1 * hr2) + 1 * (D.a 2 * hr1) +
      1 * (D.a 3 * hr0) + e00 - e11 + e22 - e33 - f03 + f12 + f21 - f30
  exact sub_eq_zero.mp h

private lemma eq73a_12 (h68 : IsMotionLocked D) (h69 : SatisfiesLeftChiralEq D)
    (h70 : SatisfiesRightChiralEq D) :
    photonF D 1 2 = dPhotonA D 1 2 - dPhotonA D 2 1 := by
  rcases h69 with ⟨hl0, hl1, hl2, hl3⟩; rcases h70 with ⟨hr0, hr1, hr2, hr3⟩
  have h : photonF D 1 2 - (dPhotonA D 1 2 - dPhotonA D 2 1) = 0 := by
    dsimp [photonF, photonMass, dPhotonA, dProd]; simp [photonFBase]
    have g10 := h68 0 1 0; have g23 := h68 0 2 3
    have e03 := h68 1 0 3; have e12 := h68 1 1 2; have e21 := h68 1 2 1; have e30 := h68 1 3 0
    have f00 := h68 2 0 0; have f11 := h68 2 1 1; have f22 := h68 2 2 2; have f33 := h68 2 3 3
    have k10 := h68 3 1 0; have k23 := h68 3 2 3
    linear_combination 2 * (hl0 * D.b 0) + 2 * (hl3 * D.b 3) + 2 * (D.a 1 * hr1) +
      2 * (D.a 2 * hr2) - 2 * g10 - 2 * g23 - e03 + e12 + e21 - e30 -
      f00 + f11 - f22 + f33 - 2 * k10 - 2 * k23
  exact sub_eq_zero.mp h

private lemma eq73a_23 (h68 : IsMotionLocked D) (h69 : SatisfiesLeftChiralEq D)
    (h70 : SatisfiesRightChiralEq D) :
    photonF D 2 3 = dPhotonA D 2 3 - dPhotonA D 3 2 := by
  rcases h69 with ⟨hl0, hl1, hl2, hl3⟩; rcases h70 with ⟨hr0, hr1, hr2, hr3⟩
  have h : photonF D 2 3 - (dPhotonA D 2 3 - dPhotonA D 3 2) = 0 := by
    dsimp [photonF, photonMass, dPhotonA, dProd]; simp [photonFBase]
    have g03 := h68 0 0 3; have g12 := h68 0 1 2; have g21 := h68 0 2 1; have g30 := h68 0 3 0
    have e01 := h68 1 0 1; have e10 := h68 1 1 0; have e23 := h68 1 2 3; have e32 := h68 1 3 2
    linear_combination -1 * (hl0 * D.b 2) - 1 * (hl1 * D.b 3) - 1 * (hl2 * D.b 0) -
      1 * (hl3 * D.b 1) + 1 * (D.a 0 * hr2) + 1 * (D.a 1 * hr3) + 1 * (D.a 2 * hr0) +
      1 * (D.a 3 * hr1) - g03 + g12 + g21 - g30 + e01 - e10 - e23 + e32
  exact sub_eq_zero.mp h

private lemma eq73a_31 (h68 : IsMotionLocked D) (h69 : SatisfiesLeftChiralEq D)
    (h70 : SatisfiesRightChiralEq D) :
    photonF D 3 1 = dPhotonA D 3 1 - dPhotonA D 1 3 := by
  rcases h69 with ⟨hl0, hl1, hl2, hl3⟩; rcases h70 with ⟨hr0, hr1, hr2, hr3⟩
  have h : photonF D 3 1 - (dPhotonA D 3 1 - dPhotonA D 1 3) = 0 := by
    dsimp [photonF, photonMass, dPhotonA, dProd]; simp [photonFBase]
    have g00 := h68 0 0 0; have g11 := h68 0 1 1; have g22 := h68 0 2 2; have g33 := h68 0 3 3
    have e01 := h68 2 0 1; have e10 := h68 2 1 0; have e23 := h68 2 2 3; have e32 := h68 2 3 2
    linear_combination -1 * (hl0 * D.b 1) - 1 * (hl1 * D.b 0) + 1 * (hl2 * D.b 3) +
      1 * (hl3 * D.b 2) + 1 * (D.a 0 * hr1) + 1 * (D.a 1 * hr0) - 1 * (D.a 2 * hr3) -
      1 * (D.a 3 * hr2) - g00 + g11 - g22 + g33 + e01 - e10 - e23 + e32
  exact sub_eq_zero.mp h

/-- Daviau Eq. (73a): `F_{μν} = ∂_μ A_ν - ∂_ν A_μ` for all `μ, ν : Fin 4`. -/
theorem eq73a_field_strength (h68 : IsMotionLocked D) (h69 : SatisfiesLeftChiralEq D)
    (h70 : SatisfiesRightChiralEq D) (μ ν : Fin 4) :
    photonF D μ ν = dPhotonA D μ ν - dPhotonA D ν μ := by
  fin_cases μ <;> fin_cases ν
  · simp [photonF, photonFBase]
  · exact eq73a_01 D h68 h69 h70
  · exact eq73a_02 D h68 h69 h70
  · exact eq73a_03 D h68 h69 h70
  · change photonF D 1 0 = dPhotonA D 1 0 - dPhotonA D 0 1
    rw [photonF_antisymm, eq73a_01 D h68 h69 h70]; ring
  · simp [photonF, photonFBase]
  · exact eq73a_12 D h68 h69 h70
  · change photonF D 1 3 = dPhotonA D 1 3 - dPhotonA D 3 1
    rw [photonF_antisymm, eq73a_31 D h68 h69 h70]; ring
  · change photonF D 2 0 = dPhotonA D 2 0 - dPhotonA D 0 2
    rw [photonF_antisymm, eq73a_02 D h68 h69 h70]; ring
  · change photonF D 2 1 = dPhotonA D 2 1 - dPhotonA D 1 2
    rw [photonF_antisymm, eq73a_12 D h68 h69 h70]; ring
  · simp [photonF, photonFBase]
  · exact eq73a_23 D h68 h69 h70
  · change photonF D 3 0 = dPhotonA D 3 0 - dPhotonA D 0 3
    rw [photonF_antisymm, eq73a_03 D h68 h69 h70]; ring
  · exact eq73a_31 D h68 h69 h70
  · change photonF D 3 2 = dPhotonA D 3 2 - dPhotonA D 2 3
    rw [photonF_antisymm, eq73a_23 D h68 h69 h70]; ring
  · simp [photonF, photonFBase]

private lemma eq73b_base_0 (h68 : IsMotionLocked D) (h69 : SatisfiesLeftChiralEq D)
    (h70 : SatisfiesRightChiralEq D) :
    (dPhotonFBase D 0 0 0 - dPhotonFBase D 1 1 0 - dPhotonFBase D 2 2 0 - dPhotonFBase D 3 3 0) +
      photonMass D * photonA D 0 = 0 := by
  rcases h69 with ⟨hl0, hl1, hl2, hl3⟩; rcases h70 with ⟨hr0, hr1, hr2, hr3⟩
  simp [dPhotonFBase]; dsimp [photonMass, photonA, dProd]
  have g03 := h68 0 0 3; have g12 := h68 0 1 2; have g21 := h68 0 2 1; have g30 := h68 0 3 0
  linear_combination 1 * (hl0 * D.b 2) + 1 * (hl1 * D.b 3) - 1 * (hl2 * D.b 0) -
    1 * (hl3 * D.b 1) - 1 * (D.a 0 * hr2) - 1 * (D.a 1 * hr3) + 1 * (D.a 2 * hr0) +
    1 * (D.a 3 * hr1) + g03 - g12 + g21 - g30

private lemma eq73b_base_1 (h68 : IsMotionLocked D) (h69 : SatisfiesLeftChiralEq D)
    (h70 : SatisfiesRightChiralEq D) :
    (dPhotonFBase D 0 0 1 - dPhotonFBase D 1 1 1 - dPhotonFBase D 2 2 1 - dPhotonFBase D 3 3 1) +
      photonMass D * photonA D 1 = 0 := by
  rcases h69 with ⟨hl0, hl1, hl2, hl3⟩; rcases h70 with ⟨hr0, hr1, hr2, hr3⟩
  simp [dPhotonFBase]; dsimp [photonMass, photonA, dProd]
  have g01 := h68 0 0 1; have g10 := h68 0 1 0; have g23 := h68 0 2 3; have g32 := h68 0 3 2
  have e03 := h68 1 0 3; have e12 := h68 1 1 2
  have f00 := h68 2 0 0; have f11 := h68 2 1 1; have f22 := h68 2 2 2; have f33 := h68 2 3 3
  have k01 := h68 3 0 1; have k10 := h68 3 1 0; have k23 := h68 3 2 3; have k32 := h68 3 3 2
  linear_combination -2 * (hl2 * D.b 2) - 2 * (hl3 * D.b 3) - 2 * (D.a 0 * hr0) -
    2 * (D.a 1 * hr1) - g01 + g10 + g23 - g32 + 2 * e03 - 2 * e12 +
    f00 - f11 + f22 - f33 + k01 + k10 + k23 + k32

private lemma eq73b_base_2 (h68 : IsMotionLocked D) (h69 : SatisfiesLeftChiralEq D)
    (h70 : SatisfiesRightChiralEq D) :
    (dPhotonFBase D 0 0 2 - dPhotonFBase D 1 1 2 - dPhotonFBase D 2 2 2 - dPhotonFBase D 3 3 2) +
      photonMass D * photonA D 2 = 0 := by
  rcases h69 with ⟨hl0, hl1, hl2, hl3⟩; rcases h70 with ⟨hr0, hr1, hr2, hr3⟩
  simp [dPhotonFBase]; dsimp [photonMass, photonA, dProd]
  have f03 := h68 2 0 3; have f12 := h68 2 1 2; have f21 := h68 2 2 1; have f30 := h68 2 3 0
  linear_combination -1 * (hl0 * D.b 3) - 1 * (hl1 * D.b 2) - 1 * (hl2 * D.b 1) -
    1 * (hl3 * D.b 0) + 1 * (D.a 0 * hr3) + 1 * (D.a 1 * hr2) + 1 * (D.a 2 * hr1) +
    1 * (D.a 3 * hr0) + f03 - f12 + f21 - f30

private lemma eq73b_base_3 (h68 : IsMotionLocked D) (h69 : SatisfiesLeftChiralEq D)
    (h70 : SatisfiesRightChiralEq D) :
    (dPhotonFBase D 0 0 3 - dPhotonFBase D 1 1 3 - dPhotonFBase D 2 2 3 - dPhotonFBase D 3 3 3) +
      photonMass D * photonA D 3 = 0 := by
  rcases h69 with ⟨hl0, hl1, hl2, hl3⟩; rcases h70 with ⟨hr0, hr1, hr2, hr3⟩
  simp [dPhotonFBase]; dsimp [photonMass, photonA, dProd]
  have k03 := h68 3 0 3; have k12 := h68 3 1 2; have k21 := h68 3 2 1; have k30 := h68 3 3 0
  linear_combination 1 * (hl0 * D.b 2) - 1 * (hl1 * D.b 3) + 1 * (hl2 * D.b 0) -
    1 * (hl3 * D.b 1) - 1 * (D.a 0 * hr2) + 1 * (D.a 1 * hr3) - 1 * (D.a 2 * hr0) +
    1 * (D.a 3 * hr1) + k03 - k12 + k21 - k30

/-- Daviau Eq. (73b): Maxwell–Proca divergence `∂_μ F^{μν} = -m² A^ν` (covariant form
`∑_μ g^{μμ} ∂_μ F_{μν} = -m² A_ν`) for all `ν : Fin 4`. -/
theorem eq73b_proca (h68 : IsMotionLocked D) (h69 : SatisfiesLeftChiralEq D)
    (h70 : SatisfiesRightChiralEq D) (ν : Fin 4) :
    dPhotonF D 0 0 ν - dPhotonF D 1 1 ν - dPhotonF D 2 2 ν - dPhotonF D 3 3 ν =
      -(photonMass D ^ 2) * photonA D ν := by
  have hb :
      (dPhotonFBase D 0 0 ν - dPhotonFBase D 1 1 ν - dPhotonFBase D 2 2 ν - dPhotonFBase D 3 3 ν) +
        photonMass D * photonA D ν = 0 := by
    fin_cases ν
    · exact eq73b_base_0 D h68 h69 h70
    · exact eq73b_base_1 D h68 h69 h70
    · exact eq73b_base_2 D h68 h69 h70
    · exact eq73b_base_3 D h68 h69 h70
  have hmul : photonMass D *
      ((dPhotonFBase D 0 0 ν - dPhotonFBase D 1 1 ν - dPhotonFBase D 2 2 ν - dPhotonFBase D 3 3 ν) +
        photonMass D * photonA D ν) = 0 := by rw [hb, mul_zero]
  dsimp [dPhotonF]
  linear_combination hmul

/-- Daviau Eq. (74a): Lorenz gauge condition `∂_μ A^μ = ∂₀ A₀ - ∂₁ A₁ - ∂₂ A₂ - ∂₃ A₃ = 0`. -/
theorem eq74a_lorenz_gauge (h69 : SatisfiesLeftChiralEq D) (h70 : SatisfiesRightChiralEq D) :
    dPhotonA D 0 0 - dPhotonA D 1 1 - dPhotonA D 2 2 - dPhotonA D 3 3 = 0 := by
  rcases h69 with ⟨hl0, hl1, hl2, hl3⟩; rcases h70 with ⟨hr0, hr1, hr2, hr3⟩
  dsimp [dPhotonA, dProd]
  linear_combination 1 * (hl0 * D.b 3) - 1 * (hl1 * D.b 2) + 1 * (hl2 * D.b 1) -
    1 * (hl3 * D.b 0) + 1 * (D.a 0 * hr3) - 1 * (D.a 1 * hr2) + 1 * (D.a 2 * hr1) -
    1 * (D.a 3 * hr0)

private lemma eq74b_base_012 (h68 : IsMotionLocked D) (h69 : SatisfiesLeftChiralEq D)
    (h70 : SatisfiesRightChiralEq D) :
    dPhotonFBase D 0 1 2 + dPhotonFBase D 1 2 0 + dPhotonFBase D 2 0 1 = 0 := by
  rcases h69 with ⟨hl0, hl1, hl2, hl3⟩; rcases h70 with ⟨hr0, hr1, hr2, hr3⟩
  simp [dPhotonFBase]; dsimp [dProd]
  have k00 := h68 3 0 0; have k11 := h68 3 1 1; have k22 := h68 3 2 2; have k33 := h68 3 3 3
  linear_combination -1 * (hl0 * D.b 1) - 1 * (hl1 * D.b 0) - 1 * (hl2 * D.b 3) -
    1 * (hl3 * D.b 2) - 1 * (D.a 0 * hr1) - 1 * (D.a 1 * hr0) - 1 * (D.a 2 * hr3) -
    1 * (D.a 3 * hr2) + k00 + k11 + k22 + k33

private lemma eq74b_base_013 (h68 : IsMotionLocked D) (h69 : SatisfiesLeftChiralEq D)
    (h70 : SatisfiesRightChiralEq D) :
    dPhotonFBase D 0 1 3 + dPhotonFBase D 1 3 0 + dPhotonFBase D 3 0 1 = 0 := by
  rcases h69 with ⟨hl0, hl1, hl2, hl3⟩; rcases h70 with ⟨hr0, hr1, hr2, hr3⟩
  simp [dPhotonFBase]; dsimp [dProd]
  have g01 := h68 0 0 1; have g10 := h68 0 1 0; have g23 := h68 0 2 3; have g32 := h68 0 3 2
  have e03 := h68 1 0 3; have e12 := h68 1 1 2; have e21 := h68 1 2 1; have e30 := h68 1 3 0
  have f00 := h68 2 0 0; have f22 := h68 2 2 2
  have k01 := h68 3 0 1; have k10 := h68 3 1 0; have k23 := h68 3 2 3; have k32 := h68 3 3 2
  linear_combination 2 * (hl0 * D.b 0) + 2 * (hl2 * D.b 2) + 2 * (D.a 0 * hr0) +
    2 * (D.a 2 * hr2) + g01 - g10 - g23 + g32 - e03 + e12 + e21 - e30 -
    2 * f00 - 2 * f22 - k01 - k10 - k23 - k32

private lemma eq74b_base_023 (h68 : IsMotionLocked D) (h69 : SatisfiesLeftChiralEq D)
    (h70 : SatisfiesRightChiralEq D) :
    dPhotonFBase D 0 2 3 + dPhotonFBase D 2 3 0 + dPhotonFBase D 3 0 2 = 0 := by
  rcases h69 with ⟨hl0, hl1, hl2, hl3⟩; rcases h70 with ⟨hr0, hr1, hr2, hr3⟩
  simp [dPhotonFBase]; dsimp [dProd]
  have e00 := h68 1 0 0; have e11 := h68 1 1 1; have e22 := h68 1 2 2; have e33 := h68 1 3 3
  linear_combination -1 * (hl0 * D.b 3) + 1 * (hl1 * D.b 2) + 1 * (hl2 * D.b 1) -
    1 * (hl3 * D.b 0) - 1 * (D.a 0 * hr3) + 1 * (D.a 1 * hr2) + 1 * (D.a 2 * hr1) -
    1 * (D.a 3 * hr0) + e00 + e11 + e22 + e33

private lemma eq74b_base_123 (h68 : IsMotionLocked D) (h69 : SatisfiesLeftChiralEq D)
    (h70 : SatisfiesRightChiralEq D) :
    dPhotonFBase D 1 2 3 + dPhotonFBase D 2 3 1 + dPhotonFBase D 3 1 2 = 0 := by
  rcases h69 with ⟨hl0, hl1, hl2, hl3⟩; rcases h70 with ⟨hr0, hr1, hr2, hr3⟩
  simp [dPhotonFBase]; dsimp [dProd]
  have g00 := h68 0 0 0; have g11 := h68 0 1 1; have g22 := h68 0 2 2; have g33 := h68 0 3 3
  linear_combination -1 * (hl0 * D.b 1) + 1 * (hl1 * D.b 0) + 1 * (hl2 * D.b 3) -
    1 * (hl3 * D.b 2) - 1 * (D.a 0 * hr1) + 1 * (D.a 1 * hr0) + 1 * (D.a 2 * hr3) -
    1 * (D.a 3 * hr2) + g00 + g11 + g22 + g33

private lemma dPhotonFBase_antisymm (ρ μ ν : Fin 4) :
    dPhotonFBase D ρ μ ν = -dPhotonFBase D ρ ν μ := by
  fin_cases μ <;> fin_cases ν <;> (simp [dPhotonFBase]; try ring)

private lemma dPhotonFBase_diag (ρ μ : Fin 4) :
    dPhotonFBase D ρ μ μ = 0 := by
  fin_cases μ <;> simp [dPhotonFBase]

private lemma bianchi_cyclic {ρ μ ν : Fin 4}
    (h : dPhotonFBase D ρ μ ν + dPhotonFBase D μ ν ρ + dPhotonFBase D ν ρ μ = 0) :
    dPhotonFBase D μ ν ρ + dPhotonFBase D ν ρ μ + dPhotonFBase D ρ μ ν = 0 := by
  linear_combination h

private lemma bianchi_swap {ρ μ ν : Fin 4}
    (h : dPhotonFBase D ρ μ ν + dPhotonFBase D μ ν ρ + dPhotonFBase D ν ρ μ = 0) :
    dPhotonFBase D ρ ν μ + dPhotonFBase D ν μ ρ + dPhotonFBase D μ ρ ν = 0 := by
  rw [dPhotonFBase_antisymm D ρ ν μ, dPhotonFBase_antisymm D ν μ ρ,
    dPhotonFBase_antisymm D μ ρ ν]
  linear_combination -h

private lemma bianchi_eq12 (ρ ν : Fin 4) :
    dPhotonFBase D ρ ρ ν + dPhotonFBase D ρ ν ρ + dPhotonFBase D ν ρ ρ = 0 := by
  rw [dPhotonFBase_diag D ν ρ, dPhotonFBase_antisymm D ρ ν ρ]
  ring

private lemma bianchi_eq13 (ρ μ : Fin 4) :
    dPhotonFBase D ρ μ ρ + dPhotonFBase D μ ρ ρ + dPhotonFBase D ρ ρ μ = 0 := by
  rw [dPhotonFBase_diag D μ ρ, dPhotonFBase_antisymm D ρ μ ρ]
  ring

private lemma bianchi_eq23 (ρ μ : Fin 4) :
    dPhotonFBase D ρ μ μ + dPhotonFBase D μ μ ρ + dPhotonFBase D μ ρ μ = 0 := by
  rw [dPhotonFBase_diag D ρ μ, dPhotonFBase_antisymm D μ μ ρ]
  ring

/-- Daviau Eq. (74b): Homogeneous Maxwell Bianchi identity `∂_ρ F_{μν} + ∂_μ F_{νρ} + ∂_ν F_{ρμ} = 0`
for all `ρ, μ, ν : Fin 4`. -/
theorem eq74b_bianchi (h68 : IsMotionLocked D) (h69 : SatisfiesLeftChiralEq D)
    (h70 : SatisfiesRightChiralEq D) (ρ μ ν : Fin 4) :
    dPhotonF D ρ μ ν + dPhotonF D μ ν ρ + dPhotonF D ν ρ μ = 0 := by
  have hb : dPhotonFBase D ρ μ ν + dPhotonFBase D μ ν ρ + dPhotonFBase D ν ρ μ = 0 := by
    have h012 := eq74b_base_012 D h68 h69 h70
    have h013 := eq74b_base_013 D h68 h69 h70
    have h023 := eq74b_base_023 D h68 h69 h70
    have h123 := eq74b_base_123 D h68 h69 h70
    fin_cases ρ <;> fin_cases μ <;> fin_cases ν
    · exact bianchi_eq12 D 0 0
    · exact bianchi_eq12 D 0 1
    · exact bianchi_eq12 D 0 2
    · exact bianchi_eq12 D 0 3
    · exact bianchi_eq13 D 0 1
    · exact bianchi_eq23 D 0 1
    · exact h012
    · exact h013
    · exact bianchi_eq13 D 0 2
    · exact bianchi_swap D h012
    · exact bianchi_eq23 D 0 2
    · exact h023
    · exact bianchi_eq13 D 0 3
    · exact bianchi_swap D h013
    · exact bianchi_swap D h023
    · exact bianchi_eq23 D 0 3
    · exact bianchi_eq23 D 1 0
    · exact bianchi_eq13 D 1 0
    · exact bianchi_cyclic D (bianchi_cyclic D (bianchi_swap D h012))
    · exact bianchi_cyclic D (bianchi_cyclic D (bianchi_swap D h013))
    · exact bianchi_eq12 D 1 0
    · exact bianchi_eq12 D 1 1
    · exact bianchi_eq12 D 1 2
    · exact bianchi_eq12 D 1 3
    · exact bianchi_cyclic D h012
    · exact bianchi_eq13 D 1 2
    · exact bianchi_eq23 D 1 2
    · exact h123
    · exact bianchi_cyclic D h013
    · exact bianchi_eq13 D 1 3
    · exact bianchi_swap D h123
    · exact bianchi_eq23 D 1 3
    · exact bianchi_eq23 D 2 0
    · exact bianchi_cyclic D (bianchi_cyclic D h012)
    · exact bianchi_eq13 D 2 0
    · exact bianchi_cyclic D (bianchi_cyclic D (bianchi_swap D h023))
    · exact bianchi_cyclic D (bianchi_swap D h012)
    · exact bianchi_eq23 D 2 1
    · exact bianchi_eq13 D 2 1
    · exact bianchi_cyclic D (bianchi_cyclic D (bianchi_swap D h123))
    · exact bianchi_eq12 D 2 0
    · exact bianchi_eq12 D 2 1
    · exact bianchi_eq12 D 2 2
    · exact bianchi_eq12 D 2 3
    · exact bianchi_cyclic D h023
    · exact bianchi_cyclic D h123
    · exact bianchi_eq13 D 2 3
    · exact bianchi_eq23 D 2 3
    · exact bianchi_eq23 D 3 0
    · exact bianchi_cyclic D (bianchi_cyclic D h013)
    · exact bianchi_cyclic D (bianchi_cyclic D h023)
    · exact bianchi_eq13 D 3 0
    · exact bianchi_cyclic D (bianchi_swap D h013)
    · exact bianchi_eq23 D 3 1
    · exact bianchi_cyclic D (bianchi_cyclic D h123)
    · exact bianchi_eq13 D 3 1
    · exact bianchi_cyclic D (bianchi_swap D h023)
    · exact bianchi_cyclic D (bianchi_swap D h123)
    · exact bianchi_eq23 D 3 2
    · exact bianchi_eq13 D 3 2
    · exact bianchi_eq12 D 3 0
    · exact bianchi_eq12 D 3 1
    · exact bianchi_eq12 D 3 2
    · exact bianchi_eq12 D 3 3
  dsimp [dPhotonF]
  rw [← mul_add, ← mul_add, hb, mul_zero]

/-- Daviau Eq. (80a): pseudoscalar gradient vanishes, `∂_μ p = 0` for all `μ : Fin 4`. -/
theorem eq80a_pseudoscalar_const (h68 : IsMotionLocked D) (h69 : SatisfiesLeftChiralEq D)
    (h70 : SatisfiesRightChiralEq D) (μ : Fin 4) :
    dFusionP D μ = 0 := by
  rcases h69 with ⟨hl0, hl1, hl2, hl3⟩; rcases h70 with ⟨hr0, hr1, hr2, hr3⟩
  fin_cases μ <;> dsimp [dFusionP, dProd]
  · have e01 := h68 1 0 1; have e10 := h68 1 1 0; have e23 := h68 1 2 3; have e32 := h68 1 3 2
    have f02 := h68 2 0 2; have f13 := h68 2 1 3; have f20 := h68 2 2 0; have f31 := h68 2 3 1
    have k03 := h68 3 0 3; have k12 := h68 3 1 2; have k21 := h68 3 2 1; have k30 := h68 3 3 0
    linear_combination -1 * (hl0 * D.b 2) - 1 * (hl1 * D.b 3) + 1 * (hl2 * D.b 0) +
      1 * (hl3 * D.b 1) - 1 * (D.a 0 * hr2) - 1 * (D.a 1 * hr3) + 1 * (D.a 2 * hr0) +
      1 * (D.a 3 * hr1) - e01 + e10 - e23 + e32 + f02 - f13 - f20 + f31 +
      k03 + k12 - k21 - k30
  · have g01 := h68 0 0 1; have g10 := h68 0 1 0
    have e03 := h68 1 0 3; have e12 := h68 1 1 2; have e21 := h68 1 2 1; have e30 := h68 1 3 0
    have f00 := h68 2 0 0; have f11 := h68 2 1 1
    have k01 := h68 3 0 1; have k10 := h68 3 1 0
    linear_combination -2 * (hl0 * D.b 0) - 2 * (hl1 * D.b 1) - 2 * (D.a 0 * hr0) -
      2 * (D.a 1 * hr1) - 2 * g01 + 2 * g10 + e03 - e12 - e21 + e30 +
      2 * f00 - 2 * f11 + 2 * k01 + 2 * k10
  · have g02 := h68 0 0 2; have g13 := h68 0 1 3; have g20 := h68 0 2 0; have g31 := h68 0 3 1
    have e00 := h68 1 0 0; have e11 := h68 1 1 1; have e22 := h68 1 2 2; have e33 := h68 1 3 3
    have k02 := h68 3 0 2; have k13 := h68 3 1 3; have k20 := h68 3 2 0; have k31 := h68 3 3 1
    linear_combination 1 * (hl0 * D.b 3) + 1 * (hl1 * D.b 2) + 1 * (hl2 * D.b 1) +
      1 * (hl3 * D.b 0) + 1 * (D.a 0 * hr3) + 1 * (D.a 1 * hr2) + 1 * (D.a 2 * hr1) +
      1 * (D.a 3 * hr0) + g02 - g13 - g20 + g31 - e00 + e11 + e22 - e33 -
      k02 - k13 - k20 - k31
  · have g03 := h68 0 0 3; have g12 := h68 0 1 2; have g21 := h68 0 2 1; have g30 := h68 0 3 0
    have e01 := h68 1 0 1; have e10 := h68 1 1 0; have e23 := h68 1 2 3; have e32 := h68 1 3 2
    have f02 := h68 2 0 2; have f13 := h68 2 1 3; have f20 := h68 2 2 0; have f31 := h68 2 3 1
    linear_combination -1 * (hl0 * D.b 2) + 1 * (hl1 * D.b 3) - 1 * (hl2 * D.b 0) +
      1 * (hl3 * D.b 1) - 1 * (D.a 0 * hr2) + 1 * (D.a 1 * hr3) - 1 * (D.a 2 * hr0) +
      1 * (D.a 3 * hr1) + g03 + g12 - g21 - g30 - e01 - e10 + e23 + e32 +
      f02 + f13 + f20 + f31

/-- Daviau Eq. (80b): scalar gradient `∂_μ s = -m B_μ` for all `μ : Fin 4`. -/
theorem eq80b_scalar_grad (h68 : IsMotionLocked D) (h69 : SatisfiesLeftChiralEq D)
    (h70 : SatisfiesRightChiralEq D) (μ : Fin 4) :
    dFusionS D μ = -photonMass D * fusionAxialB D μ := by
  rcases h69 with ⟨hl0, hl1, hl2, hl3⟩; rcases h70 with ⟨hr0, hr1, hr2, hr3⟩
  have h : dFusionS D μ + photonMass D * fusionAxialB D μ = 0 := by
    fin_cases μ <;> dsimp [dFusionS, photonMass, fusionAxialB, dProd]
    · have e02 := h68 1 0 2; have e13 := h68 1 1 3; have e20 := h68 1 2 0; have e31 := h68 1 3 1
      have f01 := h68 2 0 1; have f10 := h68 2 1 0; have f23 := h68 2 2 3; have f32 := h68 2 3 2
      have k00 := h68 3 0 0; have k11 := h68 3 1 1; have k22 := h68 3 2 2; have k33 := h68 3 3 3
      linear_combination 1 * (hl0 * D.b 1) - 1 * (hl1 * D.b 0) - 1 * (hl2 * D.b 3) +
        1 * (hl3 * D.b 2) - 1 * (D.a 0 * hr1) + 1 * (D.a 1 * hr0) + 1 * (D.a 2 * hr3) -
        1 * (D.a 3 * hr2) - e02 - e13 - e20 - e31 - f01 - f10 + f23 + f32 +
        k00 - k11 - k22 + k33
    · have g02 := h68 0 0 2; have g13 := h68 0 1 3; have g20 := h68 0 2 0; have g31 := h68 0 3 1
      have f03 := h68 2 0 3; have f12 := h68 2 1 2; have f21 := h68 2 2 1; have f30 := h68 2 3 0
      have k02 := h68 3 0 2; have k13 := h68 3 1 3; have k20 := h68 3 2 0; have k31 := h68 3 3 1
      linear_combination 1 * (hl0 * D.b 3) - 1 * (hl1 * D.b 2) - 1 * (hl2 * D.b 1) +
        1 * (hl3 * D.b 0) - 1 * (D.a 0 * hr3) + 1 * (D.a 1 * hr2) + 1 * (D.a 2 * hr1) -
        1 * (D.a 3 * hr0) - g02 - g13 - g20 - g31 - f03 - f12 + f21 + f30 +
        k02 - k13 - k20 + k31
    · have g01 := h68 0 0 1; have g23 := h68 0 2 3
      have e03 := h68 1 0 3; have e21 := h68 1 2 1
      have f00 := h68 2 0 0; have f11 := h68 2 1 1; have f22 := h68 2 2 2; have f33 := h68 2 3 3
      have k01 := h68 3 0 1; have k23 := h68 3 2 3
      linear_combination -2 * (hl1 * D.b 1) - 2 * (hl3 * D.b 3) - 2 * (D.a 0 * hr0) -
        2 * (D.a 2 * hr2) - 2 * g01 + 2 * g23 + 2 * e03 - 2 * e21 +
        f00 - f11 + f22 - f33 + 2 * k01 + 2 * k23
    · have g00 := h68 0 0 0; have g11 := h68 0 1 1; have g22 := h68 0 2 2; have g33 := h68 0 3 3
      have e02 := h68 1 0 2; have e13 := h68 1 1 3; have e20 := h68 1 2 0; have e31 := h68 1 3 1
      have f01 := h68 2 0 1; have f10 := h68 2 1 0; have f23 := h68 2 2 3; have f32 := h68 2 3 2
      linear_combination 1 * (hl0 * D.b 1) + 1 * (hl1 * D.b 0) + 1 * (hl2 * D.b 3) +
        1 * (hl3 * D.b 2) - 1 * (D.a 0 * hr1) - 1 * (D.a 1 * hr0) - 1 * (D.a 2 * hr3) -
        1 * (D.a 3 * hr2) + g00 - g11 - g22 + g33 - e02 + e13 + e20 - e31 -
        f01 + f10 - f23 + f32
  rw [neg_mul]
  exact eq_neg_of_add_eq_zero_left h

/-- Daviau Eq. (80c): axial divergence `∂_μ B^μ = m s`. -/
theorem eq80c_axial_div (h68 : IsMotionLocked D) (h69 : SatisfiesLeftChiralEq D) :
    dFusionB D 0 0 - dFusionB D 1 1 - dFusionB D 2 2 - dFusionB D 3 3 =
      photonMass D * fusionScalarS D := by
  rcases h69 with ⟨hl0, hl1, hl2, hl3⟩
  have h : (dFusionB D 0 0 - dFusionB D 1 1 - dFusionB D 2 2 - dFusionB D 3 3) -
      photonMass D * fusionScalarS D = 0 := by
    dsimp [dFusionB, photonMass, fusionScalarS, dProd]
    have g01 := h68 0 0 1; have g10 := h68 0 1 0; have g23 := h68 0 2 3; have g32 := h68 0 3 2
    have e03 := h68 1 0 3; have e12 := h68 1 1 2; have e21 := h68 1 2 1; have e30 := h68 1 3 0
    have f00 := h68 2 0 0; have f11 := h68 2 1 1; have f22 := h68 2 2 2; have f33 := h68 2 3 3
    have k01 := h68 3 0 1; have k10 := h68 3 1 0; have k23 := h68 3 2 3; have k32 := h68 3 3 2
    linear_combination -2 * (hl0 * D.b 0) - 2 * (hl1 * D.b 1) - 2 * (hl2 * D.b 2) -
      2 * (hl3 * D.b 3) - g01 + g10 + g23 - g32 + e03 - e12 - e21 + e30 +
      f00 - f11 + f22 - f33 + k01 + k10 + k23 + k32
  exact sub_eq_zero.mp h

/-- **Theorem 4 (`deBroglie_daviau_real_photon_proca_fusion`)**:
Purely polynomial identity over any `[CommRing R]`: motion lock (Eq. 68) and twin chiral
first-order spinor systems (Eqs. 69–70) imply all Maxwell–Proca equations (Eqs. 73–74) and all
non-Maxwellian torsion-scalar equations (Eq. 80). -/
theorem deBroglie_daviau_real_photon_proca_fusion
    (h68 : IsMotionLocked D) (h69 : SatisfiesLeftChiralEq D)
    (h70 : SatisfiesRightChiralEq D) :
    (∀ μ ν : Fin 4, photonF D μ ν = dPhotonA D μ ν - dPhotonA D ν μ) ∧
    (∀ ν : Fin 4, dPhotonF D 0 0 ν - dPhotonF D 1 1 ν - dPhotonF D 2 2 ν - dPhotonF D 3 3 ν =
      -(photonMass D ^ 2) * photonA D ν) ∧
    (dPhotonA D 0 0 - dPhotonA D 1 1 - dPhotonA D 2 2 - dPhotonA D 3 3 = 0) ∧
    (∀ ρ μ ν : Fin 4, dPhotonF D ρ μ ν + dPhotonF D μ ν ρ + dPhotonF D ν ρ μ = 0) ∧
    (∀ μ : Fin 4, dFusionP D μ = 0) ∧
    (∀ μ : Fin 4, dFusionS D μ = -photonMass D * fusionAxialB D μ) ∧
    (dFusionB D 0 0 - dFusionB D 1 1 - dFusionB D 2 2 - dFusionB D 3 3 =
      photonMass D * fusionScalarS D) :=
  ⟨eq73a_field_strength D h68 h69 h70,
   eq73b_proca D h68 h69 h70,
   eq74a_lorenz_gauge D h69 h70,
   eq74b_bianchi D h68 h69 h70,
   eq80a_pseudoscalar_const D h68 h69 h70,
   eq80b_scalar_grad D h68 h69 h70,
   eq80c_axial_div D h68 h69⟩

/-- Field corollary matching Daviau's explicit `m / 2` half-mass parameter when `[Field R] [CharZero R]`. -/
theorem deBroglie_daviau_real_photon_proca_fusion_halfMass
    {F : Type*} [Field F] [CharZero F]
    (a b : Fin 4 → F) (da db : Fin 4 → Fin 4 → F) (m : F)
    (h68 : IsMotionLocked ⟨a, b, da, db, m / 2⟩)
    (h69 : SatisfiesLeftChiralEq ⟨a, b, da, db, m / 2⟩)
    (h70 : SatisfiesRightChiralEq ⟨a, b, da, db, m / 2⟩) :
    (∀ μ ν : Fin 4, photonF ⟨a, b, da, db, m / 2⟩ μ ν =
      dPhotonA ⟨a, b, da, db, m / 2⟩ μ ν - dPhotonA ⟨a, b, da, db, m / 2⟩ ν μ) ∧
    (∀ ν : Fin 4, dPhotonF ⟨a, b, da, db, m / 2⟩ 0 0 ν -
        dPhotonF ⟨a, b, da, db, m / 2⟩ 1 1 ν -
        dPhotonF ⟨a, b, da, db, m / 2⟩ 2 2 ν -
        dPhotonF ⟨a, b, da, db, m / 2⟩ 3 3 ν =
      -(m ^ 2) * photonA ⟨a, b, da, db, m / 2⟩ ν) ∧
    (dPhotonA ⟨a, b, da, db, m / 2⟩ 0 0 - dPhotonA ⟨a, b, da, db, m / 2⟩ 1 1 -
        dPhotonA ⟨a, b, da, db, m / 2⟩ 2 2 - dPhotonA ⟨a, b, da, db, m / 2⟩ 3 3 = 0) ∧
    (∀ ρ μ ν : Fin 4, dPhotonF ⟨a, b, da, db, m / 2⟩ ρ μ ν +
        dPhotonF ⟨a, b, da, db, m / 2⟩ μ ν ρ +
        dPhotonF ⟨a, b, da, db, m / 2⟩ ν ρ μ = 0) ∧
    (∀ μ : Fin 4, dFusionP ⟨a, b, da, db, m / 2⟩ μ = 0) ∧
    (∀ μ : Fin 4, dFusionS ⟨a, b, da, db, m / 2⟩ μ =
      -m * fusionAxialB ⟨a, b, da, db, m / 2⟩ μ) ∧
    (dFusionB ⟨a, b, da, db, m / 2⟩ 0 0 - dFusionB ⟨a, b, da, db, m / 2⟩ 1 1 -
        dFusionB ⟨a, b, da, db, m / 2⟩ 2 2 - dFusionB ⟨a, b, da, db, m / 2⟩ 3 3 =
      m * fusionScalarS ⟨a, b, da, db, m / 2⟩) := by
  have h := deBroglie_daviau_real_photon_proca_fusion ⟨a, b, da, db, m / 2⟩ h68 h69 h70
  have hm : photonMass ⟨a, b, da, db, m / 2⟩ = m := by
    dsimp [photonMass]; ring
  simpa [hm] using h

/-- Concrete nontrivial witness showing `IsMotionLocked`, `SatisfiesLeftChiralEq`, and
`SatisfiesRightChiralEq` are simultaneously satisfiable for any `μ : R` with nonvanishing `A₁ = 1`,
`s = 1`, `B₂ = 1`, and `F₁₂ = 2 μ`. -/
def nontrivialFusionWitness (μ : R) : FusionJetData R where
  a := ![1, 0, 0, 0]
  b := ![1, 0, 0, 0]
  da := fun ν j => if ν = 2 ∧ j = 0 then -μ else 0
  db := fun ν k => if ν = 2 ∧ k = 0 then -μ else 0
  halfMass := μ

theorem nontrivial_fusion_jet_witness (μ : R) :
    IsMotionLocked (nontrivialFusionWitness μ) ∧
    SatisfiesLeftChiralEq (nontrivialFusionWitness μ) ∧
    SatisfiesRightChiralEq (nontrivialFusionWitness μ) ∧
    photonA (nontrivialFusionWitness μ) 1 = 1 ∧
    fusionScalarS (nontrivialFusionWitness μ) = 1 ∧
    fusionAxialB (nontrivialFusionWitness μ) 2 = 1 ∧
    photonF (nontrivialFusionWitness μ) 1 2 = 2 * μ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ν j k
    fin_cases ν <;> fin_cases j <;> fin_cases k <;> simp [nontrivialFusionWitness]
  · simp [SatisfiesLeftChiralEq, nontrivialFusionWitness]
  · simp [SatisfiesRightChiralEq, nontrivialFusionWitness]
  · simp [photonA, nontrivialFusionWitness]
  · simp [fusionScalarS, nontrivialFusionWitness]
  · simp [fusionAxialB, nontrivialFusionWitness]
  · dsimp [photonF, photonMass]; simp [photonFBase, nontrivialFusionWitness]

end CommRingFusion

/-- Explicit zero-parameter witness proving `FusionJetData R` is inhabited for any `[CommRing R]`. -/
def fusionWitnessZero {R : Type*} [CommRing R] : FusionJetData R :=
  nontrivialFusionWitness 0

instance {R : Type*} [CommRing R] : Inhabited (FusionJetData R) :=
  ⟨fusionWitnessZero⟩

end InfoGeometry.Clifford.DeBroglieDaviauPhotonProcaFusion
