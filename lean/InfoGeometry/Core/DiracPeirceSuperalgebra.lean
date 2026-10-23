/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Core.DiracSuperalgebra

/-!
# Peirce projections and the odd supercharge of a square-zero MP pair

This owner completes the finite `Z₂`-graded picture of a square-zero
Moore--Penrose pair `(a, m)` over an arbitrary involutive ring.  The global
involution `J`, the active support `Delta = P₊ + P₋`, and the normalized
supercharge `Q = a + m` are owned by `InfoGeometry.Core.DiracSuperalgebra`.

Here we add:

* the odd supercharge intertwines the two supports, `Q P₊ = P₋ Q` and
  `Q P₋ = P₊ Q`;
* `Q Delta = Delta Q = Q` (so the imported cube identity gives `Q^3 = Q`);
* the even and odd active Peirce projections, together with the forward
  parity implications `E₀(X) = X -> [Gamma, X] = 0` and
  `E₁(X) = X -> {Gamma, X} = 0`;
* the odd anticommutator `D_Q(X) = Q X + X Q`, its values on the two
  generators and on `Q` itself, and the explicit repeated-anticommutator
  correction: `D_Q(D_Q(P₊)) = 2 Delta`, while `[Delta, P₊] = 0`.

The converse parity implications are deliberately not asserted.  The harmonic
block `P₀ X P₀` commutes with `Gamma` and also anticommutes with it, so in a
ring with `2`-torsion the equations `[Gamma, X] = 0` and `{Gamma, X} = 0` do
not determine the Peirce block without extra hypotheses.  The parity-alternating
graded superderivation is owned separately by
`InfoGeometry.Canonical.ChiralSuperderivationColimit`.
-/

namespace InfoGeometry.Core.DiracPeirceSuperalgebra

open InfoGeometry.Singular.MoorePenrose
open InfoGeometry.Core.DiracSuperalgebra

variable {R : Type*} [Ring R] [StarRing R]
variable {a m : R}

/-- The even active Peirce component
`P₊ X P₊ + P₋ X P₋ + P₀ X P₀`. -/
def evenPeircePart (a m x : R) : R :=
  exactSupport a m * x * exactSupport a m +
    coexactSupport a m * x * coexactSupport a m +
    harmonicSupport a m * x * harmonicSupport a m

/-- The odd active Peirce component `P₊ X P₋ + P₋ X P₊`. -/
def oddPeircePart (a m x : R) : R :=
  exactSupport a m * x * coexactSupport a m +
    coexactSupport a m * x * exactSupport a m

/-- The odd anticommutator `D_Q(X) = Q X + X Q` with the normalized
supercharge `Q = a + m`.  This is the odd-parity branch of the
parity-alternating superderivation; it is not a derivation on its own. -/
def diracAnticommutator (a m x : R) : R :=
  normalizedDirac a m * x + x * normalizedDirac a m

/-- The chiral grading annihilates the harmonic complement on the left. -/
theorem chiralSupport_mul_harmonicSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    chiralSupport a m * harmonicSupport a m = 0 := by
  unfold chiralSupport
  rw [sub_mul, h.exactSupport_mul_harmonicSupport ha,
    h.coexactSupport_mul_harmonicSupport ha, sub_self]

/-- The harmonic complement annihilates the chiral grading on the left. -/
theorem harmonicSupport_mul_chiralSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    harmonicSupport a m * chiralSupport a m = 0 := by
  unfold chiralSupport
  rw [mul_sub, h.harmonicSupport_mul_exactSupport ha,
    h.harmonicSupport_mul_coexactSupport ha, sub_self]

/-! ## Generator actions -/

/-- The exact support absorbs the forward arrow. -/
theorem exactSupport_mul_self (h : IsMoorePenroseInverse a m) :
    exactSupport a m * a = a :=
  h.aba_eq_a

/-- The forward arrow is absorbed by the coexact support. -/
theorem self_mul_coexactSupport (h : IsMoorePenroseInverse a m) :
    a * coexactSupport a m = a := by
  unfold coexactSupport
  rw [← mul_assoc, h.aba_eq_a]

omit [StarRing R] in
/-- The forward arrow annihilates the exact support. -/
theorem self_mul_exactSupport (ha : a * a = 0) :
    a * exactSupport a m = 0 := by
  unfold exactSupport
  rw [← mul_assoc, ha, zero_mul]

omit [StarRing R] in
/-- The coexact support annihilates the forward arrow. -/
theorem coexactSupport_mul_self (ha : a * a = 0) :
    coexactSupport a m * a = 0 := by
  unfold coexactSupport
  rw [mul_assoc, ha, mul_zero]

/-- The coexact support absorbs the reverse arrow. -/
theorem coexactSupport_mul_inverse (h : IsMoorePenroseInverse a m) :
    coexactSupport a m * m = m :=
  h.bab_eq_b

/-- The reverse arrow is absorbed by the exact support. -/
theorem inverse_mul_exactSupport (h : IsMoorePenroseInverse a m) :
    m * exactSupport a m = m := by
  unfold exactSupport
  rw [← mul_assoc, h.bab_eq_b]

/-- The reverse arrow annihilates the coexact support. -/
theorem inverse_mul_coexactSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    m * coexactSupport a m = 0 := by
  unfold coexactSupport
  rw [← mul_assoc, h.inverse_sq_eq_zero ha, zero_mul]

/-- The exact support annihilates the reverse arrow. -/
theorem exactSupport_mul_inverse (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    exactSupport a m * m = 0 := by
  unfold exactSupport
  rw [mul_assoc, h.inverse_sq_eq_zero ha, mul_zero]

/-! ## The supercharge intertwines the two supports -/

/-- `Q P₊ = P₋ Q`. -/
theorem normalizedDirac_mul_exactSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    normalizedDirac a m * exactSupport a m = m := by
  unfold normalizedDirac exactSupport
  rw [add_mul, ← mul_assoc, ha, zero_mul, zero_add, ← mul_assoc, h.bab_eq_b]

/-- `Q P₋ = P₊ Q`. -/
theorem normalizedDirac_mul_coexactSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    normalizedDirac a m * coexactSupport a m = a := by
  unfold normalizedDirac coexactSupport
  rw [add_mul, ← mul_assoc, h.aba_eq_a, ← mul_assoc,
    h.inverse_sq_eq_zero ha, zero_mul, add_zero]

/-- `P₊ Q = a`. -/
theorem exactSupport_mul_normalizedDirac (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    exactSupport a m * normalizedDirac a m = a := by
  unfold normalizedDirac exactSupport
  rw [mul_add, h.aba_eq_a, mul_assoc, h.inverse_sq_eq_zero ha, mul_zero,
    add_zero]

/-- `P₋ Q = m`. -/
theorem coexactSupport_mul_normalizedDirac (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    coexactSupport a m * normalizedDirac a m = m := by
  unfold normalizedDirac coexactSupport
  rw [mul_add, mul_assoc, ha, mul_zero, zero_add, h.bab_eq_b]

/-- The supercharge intertwines the exact support with the coexact support. -/
theorem normalizedDirac_intertwines_exactSupport
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    normalizedDirac a m * exactSupport a m =
      coexactSupport a m * normalizedDirac a m := by
  rw [normalizedDirac_mul_exactSupport h ha,
    coexactSupport_mul_normalizedDirac h ha]

/-- The supercharge intertwines the coexact support with the exact support. -/
theorem normalizedDirac_intertwines_coexactSupport
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    normalizedDirac a m * coexactSupport a m =
      exactSupport a m * normalizedDirac a m := by
  rw [normalizedDirac_mul_coexactSupport h ha,
    exactSupport_mul_normalizedDirac h ha]

/-! ## Centrality of the active support -/

/-- The active support is absorbed by the supercharge on the right. -/
theorem normalizedDirac_mul_activeSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    normalizedDirac a m * activeSupport a m = normalizedDirac a m := by
  unfold activeSupport
  rw [mul_add, normalizedDirac_mul_exactSupport h ha,
    normalizedDirac_mul_coexactSupport h ha, add_comm]
  rfl

/-- The active support is absorbed by the supercharge on the left. -/
theorem activeSupport_mul_normalizedDirac (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    activeSupport a m * normalizedDirac a m = normalizedDirac a m := by
  unfold activeSupport
  rw [add_mul, exactSupport_mul_normalizedDirac h ha,
    coexactSupport_mul_normalizedDirac h ha]
  rfl

/-- The active support commutes with the supercharge. -/
theorem activeSupport_commute_normalizedDirac
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    activeSupport a m * normalizedDirac a m =
      normalizedDirac a m * activeSupport a m := by
  rw [activeSupport_mul_normalizedDirac h ha,
    normalizedDirac_mul_activeSupport h ha]

/-- The active support is fixed on the right by the chiral grading. -/
theorem activeSupport_mul_chiralSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    activeSupport a m * chiralSupport a m = chiralSupport a m := by
  unfold activeSupport
  rw [add_mul, h.exactSupport_mul_chiralSupport ha,
    h.coexactSupport_mul_chiralSupport ha]
  unfold chiralSupport
  abel

/-- The active support is fixed on the left by the chiral grading. -/
theorem chiralSupport_mul_activeSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    chiralSupport a m * activeSupport a m = chiralSupport a m := by
  unfold activeSupport
  rw [mul_add, h.chiralSupport_mul_exactSupport ha,
    h.chiralSupport_mul_coexactSupport ha]
  unfold chiralSupport
  abel

/-- The active support annihilates the harmonic complement. -/
theorem activeSupport_mul_harmonicSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    activeSupport a m * harmonicSupport a m = 0 := by
  unfold activeSupport
  rw [add_mul, h.exactSupport_mul_harmonicSupport ha,
    h.coexactSupport_mul_harmonicSupport ha, add_zero]

/-- The harmonic complement annihilates the active support. -/
theorem harmonicSupport_mul_activeSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    harmonicSupport a m * activeSupport a m = 0 := by
  unfold activeSupport
  rw [mul_add, h.harmonicSupport_mul_exactSupport ha,
    h.harmonicSupport_mul_coexactSupport ha, add_zero]

/-- The active support commutes with the chiral grading. -/
theorem activeSupport_commute_chiralSupport
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    activeSupport a m * chiralSupport a m =
      chiralSupport a m * activeSupport a m := by
  rw [activeSupport_mul_chiralSupport h ha,
    chiralSupport_mul_activeSupport h ha]

/-- The active support times the global involution is the chiral grading. -/
theorem activeSupport_mul_superInvolution
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    activeSupport a m * superInvolution a m = chiralSupport a m := by
  unfold superInvolution
  rw [mul_add, activeSupport_mul_chiralSupport h ha,
    activeSupport_mul_harmonicSupport h ha, add_zero]

/-- The global involution times the active support is the chiral grading. -/
theorem superInvolution_mul_activeSupport
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    superInvolution a m * activeSupport a m = chiralSupport a m := by
  unfold superInvolution
  rw [add_mul, chiralSupport_mul_activeSupport h ha,
    harmonicSupport_mul_activeSupport h ha, add_zero]

/-- The active support commutes with the global involution. -/
theorem activeSupport_commute_superInvolution
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    activeSupport a m * superInvolution a m =
      superInvolution a m * activeSupport a m := by
  rw [activeSupport_mul_superInvolution h ha,
    superInvolution_mul_activeSupport h ha]

/-! ## The global involution on the Peirce supports -/

/-- The global involution acts as `+1` on the exact support. -/
theorem superInvolution_mul_exactSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    superInvolution a m * exactSupport a m = exactSupport a m := by
  unfold superInvolution
  rw [add_mul, h.chiralSupport_mul_exactSupport ha,
    h.harmonicSupport_mul_exactSupport ha, add_zero]

/-- The global involution acts as `-1` on the coexact support. -/
theorem superInvolution_mul_coexactSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    superInvolution a m * coexactSupport a m = -coexactSupport a m := by
  unfold superInvolution
  rw [add_mul, h.chiralSupport_mul_coexactSupport ha,
    h.harmonicSupport_mul_coexactSupport ha, add_zero]

/-- The global involution acts as `+1` on the harmonic complement. -/
theorem superInvolution_mul_harmonicSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    superInvolution a m * harmonicSupport a m = harmonicSupport a m := by
  unfold superInvolution
  rw [add_mul, chiralSupport_mul_harmonicSupport h ha,
    h.harmonicSupport_idem ha, zero_add]

/-- The exact support is fixed on the right by the global involution. -/
theorem exactSupport_mul_superInvolution (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    exactSupport a m * superInvolution a m = exactSupport a m := by
  unfold superInvolution
  rw [mul_add, h.exactSupport_mul_chiralSupport ha,
    h.exactSupport_mul_harmonicSupport ha, add_zero]

/-- The coexact support is negated on the right by the global involution. -/
theorem coexactSupport_mul_superInvolution (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    coexactSupport a m * superInvolution a m = -coexactSupport a m := by
  unfold superInvolution
  rw [mul_add, h.coexactSupport_mul_chiralSupport ha,
    h.coexactSupport_mul_harmonicSupport ha, add_zero]

/-- The harmonic complement is fixed on the right by the global involution. -/
theorem harmonicSupport_mul_superInvolution (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    harmonicSupport a m * superInvolution a m = harmonicSupport a m := by
  unfold superInvolution
  rw [mul_add, harmonicSupport_mul_chiralSupport h ha,
    h.harmonicSupport_idem ha, zero_add]

omit [StarRing R] in
/-- The global involution is the reflection in the coexact support. -/
theorem superInvolution_eq_one_sub_two_smul_coexactSupport :
    superInvolution a m = 1 - 2 • coexactSupport a m := by
  unfold superInvolution chiralSupport harmonicSupport
  rw [two_nsmul]
  abel

/-- The global involution is self-adjoint. -/
theorem superInvolution_star (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    star (superInvolution a m) = superInvolution a m := by
  have hH := h.harmonic_isStarProjection ha
  unfold superInvolution chiralSupport harmonicSupport exactSupport coexactSupport
  rw [star_add, star_sub, h.ab_adj_eq, h.ba_adj_eq,
    hH.isSelfAdjoint.star_eq]

/-! ## Parity of the active Peirce components -/

/-- The chiral grading commutes with the even active Peirce part. -/
theorem evenPeircePart_chiralSupport_commute
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) (x : R) :
    chiralSupport a m * evenPeircePart a m x =
      evenPeircePart a m x * chiralSupport a m := by
  unfold evenPeircePart
  calc
    chiralSupport a m * (exactSupport a m * x * exactSupport a m +
        coexactSupport a m * x * coexactSupport a m +
        harmonicSupport a m * x * harmonicSupport a m) =
      (chiralSupport a m * exactSupport a m) * x * exactSupport a m +
        (chiralSupport a m * coexactSupport a m) * x * coexactSupport a m +
        (chiralSupport a m * harmonicSupport a m) * x * harmonicSupport a m := by
          noncomm_ring
    _ = exactSupport a m * x * exactSupport a m -
        coexactSupport a m * x * coexactSupport a m := by
          rw [h.chiralSupport_mul_exactSupport ha,
            h.chiralSupport_mul_coexactSupport ha,
            chiralSupport_mul_harmonicSupport h ha]
          noncomm_ring
    _ = (exactSupport a m * x) * (exactSupport a m * chiralSupport a m) +
        (coexactSupport a m * x) * (coexactSupport a m * chiralSupport a m) +
        (harmonicSupport a m * x) * (harmonicSupport a m * chiralSupport a m) := by
          rw [h.exactSupport_mul_chiralSupport ha,
            h.coexactSupport_mul_chiralSupport ha,
            harmonicSupport_mul_chiralSupport h ha]
          noncomm_ring
    _ = (exactSupport a m * x * exactSupport a m +
        coexactSupport a m * x * coexactSupport a m +
        harmonicSupport a m * x * harmonicSupport a m) * chiralSupport a m := by
          noncomm_ring

/-- The chiral grading anticommutes with the odd active Peirce part. -/
theorem oddPeircePart_chiralSupport_anticommute
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) (x : R) :
    chiralSupport a m * oddPeircePart a m x =
      -(oddPeircePart a m x * chiralSupport a m) := by
  unfold oddPeircePart
  calc
    chiralSupport a m * (exactSupport a m * x * coexactSupport a m +
        coexactSupport a m * x * exactSupport a m) =
      (chiralSupport a m * exactSupport a m) * x * coexactSupport a m +
        (chiralSupport a m * coexactSupport a m) * x * exactSupport a m := by
          noncomm_ring
    _ = exactSupport a m * x * coexactSupport a m -
        coexactSupport a m * x * exactSupport a m := by
          rw [h.chiralSupport_mul_exactSupport ha,
            h.chiralSupport_mul_coexactSupport ha]
          noncomm_ring
    _ = -((exactSupport a m * x) * (coexactSupport a m * chiralSupport a m) +
        (coexactSupport a m * x) * (exactSupport a m * chiralSupport a m)) := by
          rw [h.exactSupport_mul_chiralSupport ha,
            h.coexactSupport_mul_chiralSupport ha]
          noncomm_ring
    _ = -( (exactSupport a m * x * coexactSupport a m +
        coexactSupport a m * x * exactSupport a m) * chiralSupport a m) := by
          noncomm_ring

/-- An element equal to its even active Peirce part commutes with the grading. -/
theorem chiralSupport_commute_of_evenPeircePart_eq_self
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) {x : R}
    (hx : evenPeircePart a m x = x) :
    chiralSupport a m * x = x * chiralSupport a m := by
  have h0 := evenPeircePart_chiralSupport_commute h ha x
  rwa [hx] at h0

/-- An element equal to its odd active Peirce part anticommutes with the
grading. -/
theorem chiralSupport_anticommute_of_oddPeircePart_eq_self
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) {x : R}
    (hx : oddPeircePart a m x = x) :
    chiralSupport a m * x = -(x * chiralSupport a m) := by
  have h0 := oddPeircePart_chiralSupport_anticommute h ha x
  rwa [hx] at h0

/-- The active support commutes with the even active Peirce part.  This is the
centrality of `Delta = Q^2` on the even part of the active Peirce algebra. -/
theorem activeSupport_commute_evenPeircePart
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) (x : R) :
    activeSupport a m * evenPeircePart a m x =
      evenPeircePart a m x * activeSupport a m := by
  have hz : coexactSupport a m * exactSupport a m = 0 :=
    InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse.coexactSupport_mul_exactSupport ha
  have hpp : (exactSupport a m + coexactSupport a m) *
      (exactSupport a m * x * exactSupport a m) =
        exactSupport a m * x * exactSupport a m := by
    calc
      (exactSupport a m + coexactSupport a m) *
          (exactSupport a m * x * exactSupport a m) =
        (exactSupport a m * exactSupport a m) * x * exactSupport a m +
          (coexactSupport a m * exactSupport a m) * x * exactSupport a m := by
            noncomm_ring
      _ = exactSupport a m * x * exactSupport a m := by
        rw [h.exactSupport_idem, hz]
        noncomm_ring
  have hqq : (exactSupport a m + coexactSupport a m) *
      (coexactSupport a m * x * coexactSupport a m) =
        coexactSupport a m * x * coexactSupport a m := by
    calc
      (exactSupport a m + coexactSupport a m) *
          (coexactSupport a m * x * coexactSupport a m) =
        (exactSupport a m * coexactSupport a m) * x * coexactSupport a m +
          (coexactSupport a m * coexactSupport a m) * x * coexactSupport a m := by
            noncomm_ring
      _ = coexactSupport a m * x * coexactSupport a m := by
        rw [h.exactSupport_mul_coexactSupport ha, h.coexactSupport_idem]
        noncomm_ring
  have hrr : (exactSupport a m + coexactSupport a m) *
      (harmonicSupport a m * x * harmonicSupport a m) = 0 := by
    calc
      (exactSupport a m + coexactSupport a m) *
          (harmonicSupport a m * x * harmonicSupport a m) =
        (exactSupport a m * harmonicSupport a m) * x * harmonicSupport a m +
          (coexactSupport a m * harmonicSupport a m) * x * harmonicSupport a m := by
            noncomm_ring
      _ = 0 := by
        rw [h.exactSupport_mul_harmonicSupport ha,
          h.coexactSupport_mul_harmonicSupport ha]
        noncomm_ring
  have hpp' : (exactSupport a m * x * exactSupport a m) *
      (exactSupport a m + coexactSupport a m) =
        exactSupport a m * x * exactSupport a m := by
    calc
      (exactSupport a m * x * exactSupport a m) *
          (exactSupport a m + coexactSupport a m) =
        exactSupport a m * x * (exactSupport a m * exactSupport a m) +
          exactSupport a m * x * (exactSupport a m * coexactSupport a m) := by
            noncomm_ring
      _ = exactSupport a m * x * exactSupport a m := by
        rw [h.exactSupport_idem, h.exactSupport_mul_coexactSupport ha]
        noncomm_ring
  have hqq' : (coexactSupport a m * x * coexactSupport a m) *
      (exactSupport a m + coexactSupport a m) =
        coexactSupport a m * x * coexactSupport a m := by
    calc
      (coexactSupport a m * x * coexactSupport a m) *
          (exactSupport a m + coexactSupport a m) =
        coexactSupport a m * x * (coexactSupport a m * exactSupport a m) +
          coexactSupport a m * x * (coexactSupport a m * coexactSupport a m) := by
            noncomm_ring
      _ = coexactSupport a m * x * coexactSupport a m := by
        rw [hz, h.coexactSupport_idem]
        noncomm_ring
  have hrr' : (harmonicSupport a m * x * harmonicSupport a m) *
      (exactSupport a m + coexactSupport a m) = 0 := by
    calc
      (harmonicSupport a m * x * harmonicSupport a m) *
          (exactSupport a m + coexactSupport a m) =
        harmonicSupport a m * x * (harmonicSupport a m * exactSupport a m) +
          harmonicSupport a m * x * (harmonicSupport a m * coexactSupport a m) := by
            noncomm_ring
      _ = 0 := by
        rw [h.harmonicSupport_mul_exactSupport ha,
          h.harmonicSupport_mul_coexactSupport ha]
        noncomm_ring
  unfold evenPeircePart activeSupport
  calc
    (exactSupport a m + coexactSupport a m) *
        (exactSupport a m * x * exactSupport a m +
          coexactSupport a m * x * coexactSupport a m +
          harmonicSupport a m * x * harmonicSupport a m) =
      (exactSupport a m + coexactSupport a m) *
          (exactSupport a m * x * exactSupport a m) +
        (exactSupport a m + coexactSupport a m) *
          (coexactSupport a m * x * coexactSupport a m) +
        (exactSupport a m + coexactSupport a m) *
          (harmonicSupport a m * x * harmonicSupport a m) := by
            noncomm_ring
    _ = exactSupport a m * x * exactSupport a m +
        coexactSupport a m * x * coexactSupport a m := by
          rw [hpp, hqq, hrr]
          abel
    _ = (exactSupport a m * x * exactSupport a m) *
          (exactSupport a m + coexactSupport a m) +
        (coexactSupport a m * x * coexactSupport a m) *
          (exactSupport a m + coexactSupport a m) +
        (harmonicSupport a m * x * harmonicSupport a m) *
          (exactSupport a m + coexactSupport a m) := by
          rw [hpp', hqq', hrr']
          abel
    _ = (exactSupport a m * x * exactSupport a m +
          coexactSupport a m * x * coexactSupport a m +
          harmonicSupport a m * x * harmonicSupport a m) *
        (exactSupport a m + coexactSupport a m) := by
          noncomm_ring

/-- The active support commutes with the odd active Peirce part.  This is the
centrality of `Delta = Q^2` on the odd part of the active Peirce algebra. -/
theorem activeSupport_commute_oddPeircePart
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) (x : R) :
    activeSupport a m * oddPeircePart a m x =
      oddPeircePart a m x * activeSupport a m := by
  have hz : coexactSupport a m * exactSupport a m = 0 :=
    InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse.coexactSupport_mul_exactSupport ha
  have h1 : (exactSupport a m + coexactSupport a m) *
      (exactSupport a m * x * coexactSupport a m) =
        exactSupport a m * x * coexactSupport a m := by
    calc
      (exactSupport a m + coexactSupport a m) *
          (exactSupport a m * x * coexactSupport a m) =
        (exactSupport a m * exactSupport a m) * x * coexactSupport a m +
          (coexactSupport a m * exactSupport a m) * x * coexactSupport a m := by
            noncomm_ring
      _ = exactSupport a m * x * coexactSupport a m := by
        rw [h.exactSupport_idem, hz]
        noncomm_ring
  have h2 : (exactSupport a m + coexactSupport a m) *
      (coexactSupport a m * x * exactSupport a m) =
        coexactSupport a m * x * exactSupport a m := by
    calc
      (exactSupport a m + coexactSupport a m) *
          (coexactSupport a m * x * exactSupport a m) =
        (exactSupport a m * coexactSupport a m) * x * exactSupport a m +
          (coexactSupport a m * coexactSupport a m) * x * exactSupport a m := by
            noncomm_ring
      _ = coexactSupport a m * x * exactSupport a m := by
        rw [h.exactSupport_mul_coexactSupport ha, h.coexactSupport_idem]
        noncomm_ring
  have h1' : (exactSupport a m * x * coexactSupport a m) *
      (exactSupport a m + coexactSupport a m) =
        exactSupport a m * x * coexactSupport a m := by
    calc
      (exactSupport a m * x * coexactSupport a m) *
          (exactSupport a m + coexactSupport a m) =
        exactSupport a m * x * (coexactSupport a m * exactSupport a m) +
          exactSupport a m * x * (coexactSupport a m * coexactSupport a m) := by
            noncomm_ring
      _ = exactSupport a m * x * coexactSupport a m := by
        rw [hz, h.coexactSupport_idem]
        noncomm_ring
  have h2' : (coexactSupport a m * x * exactSupport a m) *
      (exactSupport a m + coexactSupport a m) =
        coexactSupport a m * x * exactSupport a m := by
    calc
      (coexactSupport a m * x * exactSupport a m) *
          (exactSupport a m + coexactSupport a m) =
        coexactSupport a m * x * (exactSupport a m * exactSupport a m) +
          coexactSupport a m * x * (exactSupport a m * coexactSupport a m) := by
            noncomm_ring
      _ = coexactSupport a m * x * exactSupport a m := by
        rw [h.exactSupport_idem, h.exactSupport_mul_coexactSupport ha]
        noncomm_ring
  unfold oddPeircePart activeSupport
  calc
    (exactSupport a m + coexactSupport a m) *
        (exactSupport a m * x * coexactSupport a m +
          coexactSupport a m * x * exactSupport a m) =
      (exactSupport a m + coexactSupport a m) *
          (exactSupport a m * x * coexactSupport a m) +
        (exactSupport a m + coexactSupport a m) *
          (coexactSupport a m * x * exactSupport a m) := by
            noncomm_ring
    _ = exactSupport a m * x * coexactSupport a m +
        coexactSupport a m * x * exactSupport a m := by
          rw [h1, h2]
    _ = (exactSupport a m * x * coexactSupport a m) *
          (exactSupport a m + coexactSupport a m) +
        (coexactSupport a m * x * exactSupport a m) *
          (exactSupport a m + coexactSupport a m) := by
          rw [h1', h2']
    _ = (exactSupport a m * x * coexactSupport a m +
          coexactSupport a m * x * exactSupport a m) *
        (exactSupport a m + coexactSupport a m) := by
          noncomm_ring

/-- The supercharge has no even active component. -/
theorem evenPeircePart_normalizedDirac (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    evenPeircePart a m (normalizedDirac a m) = 0 := by
  have h1 : exactSupport a m * normalizedDirac a m *
      exactSupport a m = 0 := by
    rw [exactSupport_mul_normalizedDirac h ha, self_mul_exactSupport ha]
  have h2 : coexactSupport a m * normalizedDirac a m *
      coexactSupport a m = 0 := by
    rw [coexactSupport_mul_normalizedDirac h ha, inverse_mul_coexactSupport h ha]
  have h3 : harmonicSupport a m * normalizedDirac a m *
      harmonicSupport a m = 0 := by
    rw [h.harmonicSupport_mul_normalizedDirac ha, zero_mul]
  unfold evenPeircePart
  rw [h1, h2, h3, add_zero, add_zero]

/-- The supercharge is its own odd active component. -/
theorem oddPeircePart_normalizedDirac (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    oddPeircePart a m (normalizedDirac a m) = normalizedDirac a m := by
  have h1 : exactSupport a m * normalizedDirac a m *
      coexactSupport a m = a := by
    rw [exactSupport_mul_normalizedDirac h ha, self_mul_coexactSupport h]
  have h2 : coexactSupport a m * normalizedDirac a m *
      exactSupport a m = m := by
    rw [coexactSupport_mul_normalizedDirac h ha, inverse_mul_exactSupport h]
  unfold oddPeircePart
  rw [h1, h2]
  rfl

/-! ## The odd anticommutator and its correction term -/

omit [StarRing R] in
/-- The odd anticommutator sends the forward arrow to the active support. -/
theorem diracAnticommutator_forward (ha : a * a = 0) :
    diracAnticommutator a m a = activeSupport a m := by
  unfold diracAnticommutator activeSupport normalizedDirac exactSupport
    coexactSupport
  noncomm_ring [ha]

/-- The odd anticommutator sends the reverse arrow to the active support. -/
theorem diracAnticommutator_inverse (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    diracAnticommutator a m m = activeSupport a m := by
  unfold diracAnticommutator activeSupport normalizedDirac exactSupport
    coexactSupport
  noncomm_ring [h.inverse_sq_eq_zero ha]

/-- The odd anticommutator sends the supercharge to twice the active support. -/
theorem diracAnticommutator_normalizedDirac (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    diracAnticommutator a m (normalizedDirac a m) = 2 • activeSupport a m := by
  have hsq := h.normalizedDirac_sq_support ha
  unfold diracAnticommutator
  rw [hsq, two_nsmul]
  rfl

/-- On the exact support the odd anticommutator returns the reverse arrow. -/
theorem diracAnticommutator_exactSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    diracAnticommutator a m (exactSupport a m) = normalizedDirac a m := by
  unfold diracAnticommutator
  rw [normalizedDirac_mul_exactSupport h ha, exactSupport_mul_normalizedDirac h ha,
    add_comm]
  rfl

/- The same odd anticommutator value holds on the coexact support. -/
theorem diracAnticommutator_coexactSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    diracAnticommutator a m (coexactSupport a m) = normalizedDirac a m := by
  unfold diracAnticommutator
  rw [normalizedDirac_mul_coexactSupport h ha,
    coexactSupport_mul_normalizedDirac h ha]
  rfl

/- The harmonic complement is invisible to the odd anticommutator. -/
theorem diracAnticommutator_harmonicSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    diracAnticommutator a m (harmonicSupport a m) = 0 := by
  unfold diracAnticommutator
  rw [h.normalizedDirac_mul_harmonicSupport ha,
    h.harmonicSupport_mul_normalizedDirac ha, add_zero]

/- On the active support, the odd anticommutator doubles the supercharge. -/
theorem diracAnticommutator_activeSupport (h : IsMoorePenroseInverse a m)
    (ha : a * a = 0) :
    diracAnticommutator a m (activeSupport a m) =
      2 • normalizedDirac a m := by
  unfold activeSupport
  unfold diracAnticommutator
  rw [mul_add, add_mul, normalizedDirac_mul_exactSupport h ha,
    normalizedDirac_mul_coexactSupport h ha,
    exactSupport_mul_normalizedDirac h ha,
    coexactSupport_mul_normalizedDirac h ha]
  simp only [normalizedDirac, two_nsmul]
  abel

/-- Repeating the *odd* anticommutator without flipping parity gives `2 Delta`
on the exact support.  This is the correction term that distinguishes the
parity-alternating superderivation from a fixed-bracket derivation. -/
theorem diracAnticommutator_sq_exactSupport
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    diracAnticommutator a m (diracAnticommutator a m (exactSupport a m)) =
      2 • activeSupport a m := by
  rw [diracAnticommutator_exactSupport h ha, diracAnticommutator_normalizedDirac h ha]

/-- The active support nevertheless commutes with the exact support, so the
repeated odd anticommutator is not the commutator with `Delta`. -/
theorem activeSupport_commutator_exactSupport
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    activeSupport a m * exactSupport a m -
      exactSupport a m * activeSupport a m = 0 := by
  unfold activeSupport
  rw [add_mul, mul_add, h.exactSupport_idem,
    InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse.coexactSupport_mul_exactSupport ha,
    h.exactSupport_mul_coexactSupport ha]
  abel

/-! ## Conjugation form of the global parity law -/

/-- Conjugation by the global parity involution flips the odd supercharge.

This is the multiplicative form of
`superInvolution * normalizedDirac + normalizedDirac * superInvolution = 0`,
using the already-proved involution square. -/
theorem superInvolution_conjugates_normalizedDirac
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    superInvolution a m * normalizedDirac a m * superInvolution a m =
      -normalizedDirac a m := by
  have h_anti := superInvolution_anticommute_normalizedDirac h ha
  have h_left : superInvolution a m * normalizedDirac a m =
      -(normalizedDirac a m * superInvolution a m) := by
    rw [add_eq_zero_iff_eq_neg] at h_anti
    exact h_anti
  calc
    superInvolution a m * normalizedDirac a m * superInvolution a m =
        (-(normalizedDirac a m * superInvolution a m)) *
          superInvolution a m := by rw [h_left]
    _ = -(normalizedDirac a m *
        (superInvolution a m * superInvolution a m)) := by
          noncomm_ring
    _ = -normalizedDirac a m := by
      rw [superInvolution_sq h ha, mul_one]

/- The global chiral involution preserves the active support. -/
theorem superInvolution_conjugates_activeSupport
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    superInvolution a m * activeSupport a m * superInvolution a m =
      activeSupport a m := by
  have hch' : chiralSupport a m * chiralSupport a m =
      activeSupport a m := by
    simpa [activeSupport] using h.chiralSupport_sq_support ha
  have hchH := chiralSupport_mul_harmonicSupport h ha
  have hHactive := harmonicSupport_mul_activeSupport h ha
  unfold superInvolution
  calc
    (chiralSupport a m + harmonicSupport a m) * activeSupport a m *
        (chiralSupport a m + harmonicSupport a m) =
      chiralSupport a m * activeSupport a m * chiralSupport a m +
        chiralSupport a m * activeSupport a m * harmonicSupport a m +
        harmonicSupport a m * activeSupport a m * chiralSupport a m +
        harmonicSupport a m * activeSupport a m * harmonicSupport a m := by
          noncomm_ring
    _ = activeSupport a m := by
      have h₁ : chiralSupport a m * activeSupport a m =
          chiralSupport a m := chiralSupport_mul_activeSupport h ha
      simp only [h₁, hch', hchH, hHactive, zero_mul, add_zero]

/- The symmetric Majorana reflection preserves the active support. -/
theorem globalMajoranaReflection_conjugates_activeSupport
    (h : IsMoorePenroseInverse a m) (ha : a * a = 0) :
    globalMajoranaReflection a m * activeSupport a m *
        globalMajoranaReflection a m = activeSupport a m := by
  have hq := h.normalizedDirac_sq_support ha
  have hqH := h.normalizedDirac_mul_harmonicSupport ha
  have hQactive := normalizedDirac_mul_activeSupport h ha
  have hHactive := harmonicSupport_mul_activeSupport h ha
  have hactiveH := activeSupport_mul_harmonicSupport h ha
  unfold globalMajoranaReflection
  calc
    (majoranaPlus a m + harmonicSupport a m) * activeSupport a m *
        (majoranaPlus a m + harmonicSupport a m) =
      majoranaPlus a m * activeSupport a m * majoranaPlus a m +
        majoranaPlus a m * activeSupport a m * harmonicSupport a m +
        harmonicSupport a m * activeSupport a m * majoranaPlus a m +
        harmonicSupport a m * activeSupport a m * harmonicSupport a m := by
          noncomm_ring
    _ = activeSupport a m := by
      have h₁ : majoranaPlus a m * activeSupport a m *
          majoranaPlus a m = activeSupport a m := by
        rw [show majoranaPlus a m = normalizedDirac a m by rfl,
          hQactive]
        simpa [activeSupport] using hq
      have h₂ : majoranaPlus a m * activeSupport a m *
          harmonicSupport a m = 0 := by
        rw [show majoranaPlus a m = normalizedDirac a m by rfl,
          hQactive, hqH]
      have h₃ : harmonicSupport a m * activeSupport a m *
          majoranaPlus a m = 0 := by
        rw [hHactive, zero_mul]
      have h₄ : harmonicSupport a m * activeSupport a m *
          harmonicSupport a m = 0 := by
        rw [hHactive, zero_mul]
      rw [h₁, h₂, h₃, h₄]
      simp only [add_zero]

end InfoGeometry.Core.DiracPeirceSuperalgebra
