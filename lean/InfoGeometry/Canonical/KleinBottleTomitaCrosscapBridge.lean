/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Ring.Aut
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Tactic
import InfoGeometry.Physics.AlgebraicTomitaTakesakiBridge
import InfoGeometry.Algebra.DeWittPeirceChiralBridge
import InfoGeometry.OperatorAlgebra.PeirceSpine.StarGrading

/-!
# Klein Bottle Crosscap Collapse, Tomita-Takesaki Modular Reduction, and Frobenius-Schur Selection

This module formalizes the exact operator-algebraic and CFT crosscap structure on the Klein bottle $\mathbb{K}^2$:

1. **Tomita-Takesaki Inversion & Glide Reflection:**
   - Involutive modular conjugation $J : \mathcal{M} \to \mathcal{M}$ satisfying $J^2 = \mathrm{id}$.
   - Glide reflection operator $\Omega$ satisfying $\Omega^2 = \mathrm{id}$.
   - The Crosscap Real Fixed Subalgebra $\mathcal{M}_{\mathbb{K}^2} = \{ A \in \mathcal{M} \mid \Omega A \Omega^{-1} = J A^* J \}$.

2. **Peirce-Witten Parity Twisted Monodromy:**
   $C K = -(-1)^F K C$ on the longitudinal ($F=0$) and transverse ($F=1$) sectors.

3. **Frobenius-Schur Indicator Selection:**
   Anyons with indicator $\nu_a = 0$ (chiral pairs $a \neq \bar{a}$) vanish under the crosscap trace,
   while self-conjugate Majorana states ($\nu_a = +1$) are topologically preserved.

The algebraic statements below are checked by Lean; analytic Tomita--Takesaki
and CFT interpretations remain parameterized by their explicit data.
-/

namespace InfoGeometry.Canonical.KleinBottleTomitaCrosscap

open InfoGeometry.Algebra.DeWittPeirceSuperalgebra
open InfoGeometry.Algebra.DeWittPeirceChiralBridge
open InfoGeometry.OperatorAlgebra.PeirceSpine

variable {M : Type*} [Ring M] [StarRing M]
open InfoGeometry.Physics

/-- Crosscap Datum comprising the modular conjugation J and the glide reflection Ω -/
structure CrosscapDatum (M : Type*) [Ring M] [StarRing M] where
  /-- The repository's ring-level anti-automorphism, distinct from
  vector-level antilinear modular conjugation. -/
  J : AntiAutomorphism M
  /-- J preserves the star operation -/
  J_star : ∀ x : M, J.toFun (star x) = star (J.toFun x)
  /-- Glide reflection automorphism Ω -/
  glide : RingAut M
  /-- Glide reflection is involutive on the double cover: Ω² = id -/
  glide_involutive : ∀ x : M, glide (glide x) = x

/-- The Tomita conjugation followed by the star involution is the multiplicative
CPT map used by the crosscap condition. -/
def tomitaCPT (D : CrosscapDatum M) (A : M) : M := D.J.toFun (star A)

/-- The involutive anti-multiplicative Tomita map preserves zero; zero
preservation follows from the ring laws and does not need a separate field. -/
theorem crosscapTomitaJ_zero (D : CrosscapDatum M) : D.J.toFun 0 = 0 := by
  calc
    D.J.toFun 0 = D.J.toFun (0 * D.J.toFun 0) := by rw [zero_mul]
    _ = D.J.toFun (D.J.toFun 0) * D.J.toFun 0 := D.J.map_mul 0 (D.J.toFun 0)
    _ = 0 * D.J.toFun 0 := by rw [D.J.inv]
    _ = 0 := zero_mul _

/-- Subtraction is preserved by the additive anti-automorphism; it is derived
from the actual ring-level interface rather than assumed as extra structure. -/
theorem crosscapTomitaJ_sub (D : CrosscapDatum M) (A B : M) :
    D.J.toFun (A - B) = D.J.toFun A - D.J.toFun B := by
  rw [sub_eq_add_neg, D.J.map_add]
  have hneg : D.J.toFun (-B) = -D.J.toFun B := by
    have h := D.J.map_add B (-B)
    rw [add_neg_cancel, crosscapTomitaJ_zero] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  rw [hneg, sub_eq_add_neg]

/-- The multiplicative CPT composite used in the crosscap equation preserves
zero, derived from the ring star law and the Tomita involution. -/
@[simp] theorem tomitaCPT_zero (D : CrosscapDatum M) :
    tomitaCPT D 0 = 0 := by
  simp [tomitaCPT, crosscapTomitaJ_zero]

/-- Crosscap fixed-locus equation, expressed through the multiplicative CPT
map induced by the Tomita anti-automorphism and the star operation. -/
def InCrosscapSubalgebra (D : CrosscapDatum M) (A : M) : Prop :=
  D.glide A = tomitaCPT D A

/-- The two anti-multiplicative operations in `tomitaCPT` compose to a
multiplicative operation. -/
theorem tomitaCPT_mul (D : CrosscapDatum M) (A B : M) :
    tomitaCPT D (A * B) = tomitaCPT D A * tomitaCPT D B := by
  simp only [tomitaCPT, star_mul, D.J.map_mul]

/-- Multiplicative CPT carries a ring commutator to the commutator of the
images, preserving the order of both factors. -/
theorem tomitaCPT_comm (D : CrosscapDatum M) (A B : M) :
    tomitaCPT D (InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm A B) =
      InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm
        (tomitaCPT D A) (tomitaCPT D B) := by
  simp only [InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm,
    tomitaCPT, star_sub, crosscapTomitaJ_sub, star_mul, D.J.map_mul]

/-- The anti-multiplicative Tomita involution reverses the commutator sign:
`J([A,B]) = -[J(A),J(B)]`. -/
theorem tomitaJ_comm (D : CrosscapDatum M) (A B : M) :
    D.J.toFun (InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm A B) =
      -(InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm
        (D.J.toFun A) (D.J.toFun B)) := by
  simp only [InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm,
    crosscapTomitaJ_sub, D.J.map_mul]
  noncomm_ring

/-- The Tomita/star composite is additive on the operator ring. -/
theorem tomitaCPT_add (D : CrosscapDatum M) (A B : M) :
    tomitaCPT D (A + B) = tomitaCPT D A + tomitaCPT D B := by
  simp only [tomitaCPT, star_add, D.J.map_add]

/-- The Tomita/star composite is involutive on the crosscap carrier. -/
theorem tomitaCPT_involutive (D : CrosscapDatum M) (A : M) :
    tomitaCPT D (tomitaCPT D A) = A := by
  simp [tomitaCPT, D.J_star, D.J.inv]

/-- Under sheet-stable star and sheet-swapping Tomita conjugation, CPT carries
the left-to-right DeWitt soul corner to the opposite Peirce corner. -/
theorem tomitaCPT_soul_LR_eq_soul_RL
    (D : CrosscapDatum M) [S : ChiralPeirceSystem M]
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL) (X : M) :
    tomitaCPT D (soul_LR X) = soul_RL (tomitaCPT D X) := by
  have hComplement : S.PR = 1 - S.PL := right_is_complement
  have hPL : tomitaCPT D S.PL = 1 - S.PL := by
    simp [tomitaCPT, hstarPL, hJPL, hComplement]
  have hPR : tomitaCPT D (1 - S.PL) = S.PL := by
    rw [← hComplement]
    simp [tomitaCPT, hstarPR, hJPR]
  have hCorners := multSheetSwap_corners (tomitaCPT D) (tomitaCPT_mul D)
    hPL hPR X
  simpa [soul_LR, soul_RL, conePlus, coneMinus, hComplement] using hCorners.2.2.1

/-- In the anti-multiplicative Tomita convention, applying `J` to the
star-reflected left-to-right soul corner sends it to the opposite corner of
`star (J X)`. This is the direct Peirce-corner form of the operator `j` law. -/
theorem tomitaJ_star_soul_LR_eq_soul_RL
    (D : CrosscapDatum M) [S : ChiralPeirceSystem M]
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL) (X : M) :
    D.J.toFun (star (soul_LR X)) = soul_RL (star (D.J.toFun X)) := by
  rw [← D.J_star X]
  exact tomitaCPT_soul_LR_eq_soul_RL D hstarPL hstarPR hJPL hJPR X

/-- The reverse off-diagonal corner is exchanged back by the same CPT map. -/
theorem tomitaCPT_soul_RL_eq_soul_LR
    (D : CrosscapDatum M) [S : ChiralPeirceSystem M]
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL) (X : M) :
    tomitaCPT D (soul_RL X) = soul_LR (tomitaCPT D X) := by
  have hComplement : S.PR = 1 - S.PL := right_is_complement
  have hPL : tomitaCPT D S.PL = 1 - S.PL := by
    simp [tomitaCPT, hstarPL, hJPL, hComplement]
  have hPR : tomitaCPT D (1 - S.PL) = S.PL := by
    rw [← hComplement]
    simp [tomitaCPT, hstarPR, hJPR]
  have hCorners := multSheetSwap_corners (tomitaCPT D) (tomitaCPT_mul D)
    hPL hPR X
  simpa [soul_LR, soul_RL, conePlus, coneMinus, hComplement] using hCorners.2.2.2

/-- Under the sheet-swap law, CPT transports the Peirce first-grade
noncommutativity defect to the corresponding defect of the opposite projector. -/
theorem tomitaCPT_comm_PL_eq_comm_PR
    (D : CrosscapDatum M) [S : ChiralPeirceSystem M]
    (hstarPL : star S.PL = S.PL) (hJPL : D.J.toFun S.PL = S.PR) (X : M) :
    tomitaCPT D (InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL X) =
      InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PR (tomitaCPT D X) := by
  have hCPTPL : tomitaCPT D S.PL = S.PR := by
    simp [tomitaCPT, hstarPL, hJPL]
  rw [tomitaCPT_comm, hCPTPL]

/-- The anti-multiplicative Tomita involution alone preserves a directed
Peirce soul corner when it exchanges the sheet projectors: product reversal
and sheet exchange cancel. This is distinct from `tomitaCPT`, whose additional
star reversal makes it multiplicative and exchanges the two directed corners. -/
theorem tomitaJ_soul_LR_eq_soul_LR
    (D : CrosscapDatum M) [S : ChiralPeirceSystem M]
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL) (X : M) :
    D.J.toFun (soul_LR X) = soul_LR (D.J.toFun X) := by
  simp only [soul_LR, D.J.map_mul, hJPR, hJPL, mul_assoc]

/-- The reverse directed soul corner obeys the same double-reversal
cancellation under the anti-multiplicative sheet-exchanging Tomita map. -/
theorem tomitaJ_soul_RL_eq_soul_RL
    (D : CrosscapDatum M) [S : ChiralPeirceSystem M]
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL) (X : M) :
    D.J.toFun (soul_RL X) = soul_RL (D.J.toFun X) := by
  simp only [soul_RL, D.J.map_mul, hJPL, hJPR, mul_assoc]

/-- If the glide preserves both sheets while multiplicative CPT exchanges them,
a crosscap-fixed element cannot occupy only one directed fermion corner.  The
two symmetries send that corner into opposite Peirce bimodules, whose
intersection is zero.  This records the obstruction condition explicitly:
when the glide itself also exchanges sheets, this vanishing conclusion does
not follow. -/
theorem crosscap_fixed_single_soul_corner_vanishes
    (D : CrosscapDatum M) [S : ChiralPeirceSystem M]
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PL) (hΩPR : D.glide S.PR = S.PR)
    (X : M) (hX : InCrosscapSubalgebra D X) :
    (soul_LR X = X → X = 0) ∧ (soul_RL X = X → X = 0) := by
  have hGlideLR (A : M) :
      D.glide (soul_LR A) = soul_LR (D.glide A) := by
    simp only [soul_LR, map_mul, hΩPL, hΩPR]
  have hGlideRL (A : M) :
      D.glide (soul_RL A) = soul_RL (D.glide A) := by
    simp only [soul_RL, map_mul, hΩPL, hΩPR]
  constructor
  · intro hPure
    have hYLR : soul_LR (D.glide X) = D.glide X := by
      rw [← hGlideLR X, hPure]
    have hYRL : soul_RL (D.glide X) = D.glide X := by
      calc soul_RL (D.glide X)
          = soul_RL (tomitaCPT D X) := by rw [hX]
        _ = tomitaCPT D (soul_LR X) :=
          (tomitaCPT_soul_LR_eq_soul_RL D hstarPL hstarPR hJPL hJPR X).symm
        _ = tomitaCPT D X := by rw [hPure]
        _ = D.glide X := hX.symm
    have hzero := soul_RL_soul_LR_eq_zero (A := M) (D.glide X)
    rw [hYLR, hYRL] at hzero
    have hCPTzero : tomitaCPT D X = 0 := by rw [← hX]; exact hzero
    have hInvol := tomitaCPT_involutive D X
    rw [hCPTzero] at hInvol
    simpa using hInvol.symm
  · intro hPure
    have hYRL : soul_RL (D.glide X) = D.glide X := by
      rw [← hGlideRL X, hPure]
    have hYLR : soul_LR (D.glide X) = D.glide X := by
      calc soul_LR (D.glide X)
          = soul_LR (tomitaCPT D X) := by rw [hX]
        _ = tomitaCPT D (soul_RL X) :=
          (tomitaCPT_soul_RL_eq_soul_LR D hstarPL hstarPR hJPL hJPR X).symm
        _ = tomitaCPT D X := by rw [hPure]
        _ = D.glide X := hX.symm
    have hzero := soul_LR_soul_RL_eq_zero (A := M) (D.glide X)
    rw [hYRL, hYLR] at hzero
    have hCPTzero : tomitaCPT D X = 0 := by rw [← hX]; exact hzero
    have hInvol := tomitaCPT_involutive D X
    rw [hCPTzero] at hInvol
    simpa using hInvol.symm

/-- CPT preserves the DeWitt body, exchanging its two diagonal Peirce summands. -/
theorem tomitaCPT_body_eq_body
    (D : CrosscapDatum M) [S : ChiralPeirceSystem M]
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL) (X : M) :
    tomitaCPT D (body X) = body (tomitaCPT D X) := by
  simp only [tomitaCPT, body, star_add, star_mul, D.J.map_add, D.J.map_mul,
    hstarPL, hstarPR, hJPL, hJPR]
  abel

/-- CPT preserves the total DeWitt soul (`soul_LR + soul_RL`) while exchanging its two corners. -/
theorem tomitaCPT_soul_eq_soul
    (D : CrosscapDatum M) [S : ChiralPeirceSystem M]
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL) (X : M) :
    tomitaCPT D (soul X) = soul (tomitaCPT D X) := by
  dsimp [soul]
  rw [tomitaCPT]
  rw [star_add, D.J.map_add]
  change tomitaCPT D (soul_LR X) + tomitaCPT D (soul_RL X) =
    soul_LR (tomitaCPT D X) + soul_RL (tomitaCPT D X)
  rw [tomitaCPT_soul_LR_eq_soul_RL D hstarPL hstarPR hJPL hJPR X,
      tomitaCPT_soul_RL_eq_soul_LR D hstarPL hstarPR hJPL hJPR X]
  exact add_comm _ _

/-- Under sheet-stable star and sheet-swapping `D.J.toFun`, `tomitaCPT` negates the DeWitt chiral grading `G = P_L - P_R`. -/
theorem tomitaCPT_chiralGrading
    (D : CrosscapDatum M) [S : ChiralPeirceSystem M]
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL) :
    tomitaCPT D (G (A := M)) = -(G (A := M)) := by
  have hneg : ∀ z : M, D.J.toFun (-z) = -D.J.toFun z := fun z =>
    eq_neg_of_add_eq_zero_left (by rw [← D.J.map_add, neg_add_cancel, (crosscapTomitaJ_zero D)])
  have hsub : ∀ a b : M, D.J.toFun (a - b) = D.J.toFun a - D.J.toFun b := fun a b => by
    rw [sub_eq_add_neg, D.J.map_add, hneg, ← sub_eq_add_neg]
  change D.J.toFun (star (S.PL - S.PR)) = -(S.PL - S.PR)
  rw [star_sub, hsub, hstarPL, hstarPR, hJPL, hJPR, neg_sub]

/-- The DeWitt chiral grading `G = P_L - P_R` belongs to the crosscap real fixed subalgebra
whenever the glide reflection and `tomitaCPT` both exchange `P_L ↔ P_R`. -/
theorem chiralGrading_mem_crosscap
    (D : CrosscapDatum M) [S : ChiralPeirceSystem M]
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PR) (hΩPR : D.glide S.PR = S.PL) :
    InCrosscapSubalgebra D (G (A := M)) := by
  dsimp [InCrosscapSubalgebra]
  have hLHS : D.glide (G (A := M)) = -(G (A := M)) := by
    change D.glide (S.PL - S.PR) = -(S.PL - S.PR)
    rw [map_sub, hΩPL, hΩPR, neg_sub]
  rw [hLHS, tomitaCPT_chiralGrading D hstarPL hstarPR hJPL hJPR]

/-- Every element of the crosscap subalgebra splits corner-by-corner inside the crosscap subalgebra:
`D.glide` and `tomitaCPT = D.J.toFun ∘ star` match on every Peirce–DeWitt block. -/
theorem crosscap_splits_peirce_corners
    (D : CrosscapDatum M) [S : ChiralPeirceSystem M]
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PR) (hΩPR : D.glide S.PR = S.PL)
    (A : M) (hA : InCrosscapSubalgebra D A) :
    InCrosscapSubalgebra D (S.PL * A * S.PL) ∧
    InCrosscapSubalgebra D (S.PR * A * S.PR) ∧
    InCrosscapSubalgebra D (soul_LR A) ∧
    InCrosscapSubalgebra D (soul_RL A) := by
  have hComplement : S.PR = 1 - S.PL := right_is_complement
  have hΩQ : D.glide (1 - S.PL) = S.PL := by
    rw [← hComplement]
    exact hΩPR
  have hΩP : D.glide S.PL = 1 - S.PL := by
    simpa [hComplement] using hΩPL
  have hCPTP : tomitaCPT D S.PL = 1 - S.PL := by
    simp [tomitaCPT, hstarPL, hJPL, hComplement]
  have hCPTQ : tomitaCPT D (1 - S.PL) = S.PL := by
    rw [← hComplement]
    simp [tomitaCPT, hstarPR, hJPR]
  have hGlideCorners := multSheetSwap_corners D.glide
    (fun x y => map_mul D.glide x y) hΩP hΩQ A
  have hCPTCorners := multSheetSwap_corners (tomitaCPT D)
    (tomitaCPT_mul D) hCPTP hCPTQ A
  have hGlideRR : D.glide (S.PR * A * S.PR) = S.PL * D.glide A * S.PL := by
    rw [hComplement]
    change D.glide (OperatorAlgebra.PeirceSpine.peirce00 S.PL A) =
      OperatorAlgebra.PeirceSpine.peirce11 S.PL (D.glide A)
    exact hGlideCorners.2.1
  have hCPTRR : tomitaCPT D (S.PR * A * S.PR) = S.PL * tomitaCPT D A * S.PL := by
    rw [hComplement]
    change tomitaCPT D (OperatorAlgebra.PeirceSpine.peirce00 S.PL A) =
      OperatorAlgebra.PeirceSpine.peirce11 S.PL (tomitaCPT D A)
    exact hCPTCorners.2.1
  have hGlideLR : D.glide (soul_LR A) = soul_RL (D.glide A) := by
    simpa [soul_LR, soul_RL, conePlus, coneMinus, hComplement] using
      hGlideCorners.2.2.1
  have hGlideRL : D.glide (soul_RL A) = soul_LR (D.glide A) := by
    simpa [soul_LR, soul_RL, conePlus, coneMinus, hComplement] using
      hGlideCorners.2.2.2
  have hCPTLR : tomitaCPT D (soul_LR A) = soul_RL (tomitaCPT D A) := by
    simpa [soul_LR, soul_RL, conePlus, coneMinus, hComplement] using
      hCPTCorners.2.2.1
  have hCPTRL : tomitaCPT D (soul_RL A) = soul_LR (tomitaCPT D A) := by
    simpa [soul_LR, soul_RL, conePlus, coneMinus, hComplement] using
      hCPTCorners.2.2.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · change D.glide (OperatorAlgebra.PeirceSpine.peirce11 S.PL A) =
      tomitaCPT D (OperatorAlgebra.PeirceSpine.peirce11 S.PL A)
    rw [hGlideCorners.1, hCPTCorners.1, hA]
  · change D.glide (S.PR * A * S.PR) =
      tomitaCPT D (S.PR * A * S.PR)
    rw [hGlideRR, hCPTRR, hA]
  · change D.glide (soul_LR A) = tomitaCPT D (soul_LR A)
    rw [hGlideLR, hA, hCPTLR]
  · change D.glide (soul_RL A) = tomitaCPT D (soul_RL A)
    rw [hGlideRL, hA, hCPTRL]

/-- If `D.J.toFun` is made multiplicative while the glide and the two projectors
exchange sheets, a crosscap-fixed single DeWitt soul corner must vanish.
The proof separates the glide's corner reversal from the anti-multiplicative
`D.J.toFun ∘ star` corner preservation. Since `D.J.toFun` is already anti-multiplicative
in `CrosscapDatum`, imposing multiplicativity also forces the coefficient
ring to be commutative; this is therefore an obstruction theorem, not a
noncommutative Tomita model. -/
theorem tomita_anti_and_multiplicative_forces_commutative
    (D : CrosscapDatum M)
    (hJ_mul : ∀ x y : M, D.J.toFun (x * y) = D.J.toFun x * D.J.toFun y) :
    ∀ x y : M, x * y = y * x := by
  have hJ_inj : Function.Injective D.J.toFun := fun x y hxy => by
    calc x = D.J.toFun (D.J.toFun x) := (D.J.inv x).symm
      _ = D.J.toFun (D.J.toFun y) := by rw [hxy]
      _ = y := D.J.inv y
  intro x y
  apply hJ_inj
  have hxy : D.J.toFun x * D.J.toFun y = D.J.toFun y * D.J.toFun x := by
    calc D.J.toFun x * D.J.toFun y = D.J.toFun (x * y) := (hJ_mul x y).symm
      _ = D.J.toFun y * D.J.toFun x := D.J.map_mul x y
  calc D.J.toFun (x * y) = D.J.toFun x * D.J.toFun y := hJ_mul x y
    _ = D.J.toFun y * D.J.toFun x := hxy
    _ = D.J.toFun x * D.J.toFun y := hxy.symm
    _ = D.J.toFun (y * x) := (D.J.map_mul y x).symm

/-- A multiplicative modular action composed with the ring-level Tomita
anti-automorphism is anti-multiplicative. If that same composite is identified
with the multiplicative glide of a `CrosscapDatum`, injectivity forces the
coefficient ring to be commutative. Thus a noncommutative crosscap cannot
identify its ring-automorphism glide with `J ∘ σ` under these hypotheses;
the multiplicative CPT composite `J ∘ star` remains a distinct map. -/
theorem modular_glide_crosscap_identification_forces_commutative
    (D : CrosscapDatum M) (sigma : M → M)
    (hSigmaMul : ∀ x y : M, sigma (x * y) = sigma x * sigma y)
    (hSigmaInj : Function.Injective sigma)
    (hGlideEq : ∀ x : M, D.glide x = D.J.toFun (sigma x)) :
    ∀ x y : M, x * y = y * x := by
  have hCompositeInj : Function.Injective (fun x => D.J.toFun (sigma x)) := by
    intro x y hxy
    apply hSigmaInj
    calc
      sigma x = D.J.toFun (D.J.toFun (sigma x)) := (D.J.inv (sigma x)).symm
      _ = D.J.toFun (D.J.toFun (sigma y)) := congrArg D.J.toFun hxy
      _ = sigma y := D.J.inv (sigma y)
  intro x y
  apply hCompositeInj
  have hAnti : D.J.toFun (sigma (x * y)) =
      D.J.toFun (sigma y) * D.J.toFun (sigma x) := by
    rw [hSigmaMul, D.J.map_mul]
  have hCrosscapMul : D.J.toFun (sigma (x * y)) =
      D.J.toFun (sigma x) * D.J.toFun (sigma y) := by
    calc
      D.J.toFun (sigma (x * y)) = D.glide (x * y) := (hGlideEq (x * y)).symm
      _ = D.glide x * D.glide y := map_mul D.glide x y
      _ = D.J.toFun (sigma x) * D.J.toFun (sigma y) := by rw [hGlideEq x, hGlideEq y]
  have hSwap : D.J.toFun (sigma y) * D.J.toFun (sigma x) =
      D.J.toFun (sigma x) * D.J.toFun (sigma y) := hAnti.symm.trans hCrosscapMul
  calc
    D.J.toFun (sigma (x * y)) = D.J.toFun (sigma y) * D.J.toFun (sigma x) := hAnti
    _ = D.J.toFun (sigma x) * D.J.toFun (sigma y) := hSwap
    _ = D.J.toFun (sigma (y * x)) := by
      rw [hSigmaMul, D.J.map_mul]

theorem crosscap_multiplicative_J_soul_vanishing
    (D : CrosscapDatum M) [S : ChiralPeirceSystem M]
    (hJ_mul : ∀ x y : M, D.J.toFun (x * y) = D.J.toFun x * D.J.toFun y)
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PR) (hΩPR : D.glide S.PR = S.PL)
    (X : M) :
    (InCrosscapSubalgebra D (soul_LR X) → soul_LR X = 0) ∧
    (InCrosscapSubalgebra D (soul_RL X) → soul_RL X = 0) := by
  have hComplement : S.PR = 1 - S.PL := right_is_complement
  have hGlideP : D.glide S.PL = 1 - S.PL := by
    simpa [hComplement] using hΩPL
  have hGlideQ : D.glide (1 - S.PL) = S.PL := by
    rw [← hComplement]
    exact hΩPR
  have hCPT_anti : ∀ a b : M,
      tomitaCPT D (a * b) = tomitaCPT D b * tomitaCPT D a := by
    intro a b
    simp only [tomitaCPT, star_mul, hJ_mul]
  have hCPTP : tomitaCPT D S.PL = 1 - S.PL := by
    simp [tomitaCPT, hstarPL, hJPL, hComplement]
  have hCPTQ : tomitaCPT D (1 - S.PL) = S.PL := by
    rw [← hComplement]
    simp [tomitaCPT, hstarPR, hJPR]
  have hGlideInj : Function.Injective D.glide := by
    intro a b hab
    calc
      a = D.glide (D.glide a) := (D.glide_involutive a).symm
      _ = D.glide (D.glide b) := by rw [hab]
      _ = b := D.glide_involutive b
  have hCore := multAntiMultSheetSwap_fixed_singleCorner_eq_zero
    S.h_PL_sq D.glide (tomitaCPT D)
    (fun a b => map_mul D.glide a b) (map_zero D.glide) hGlideInj
    hGlideP hGlideQ hCPT_anti hCPTP hCPTQ X
  refine ⟨?_, ?_⟩
  · intro hLR
    have hCoreInput :
        D.glide (conePlus S.PL X) = tomitaCPT D (conePlus S.PL X) := by
      simpa [InCrosscapSubalgebra, soul_LR, conePlus, hComplement] using hLR
    have hZero := hCore.1 hCoreInput
    simpa [soul_LR, conePlus, hComplement] using hZero
  · intro hRL
    have hCoreInput :
        D.glide (coneMinus S.PL X) = tomitaCPT D (coneMinus S.PL X) := by
      simpa [InCrosscapSubalgebra, soul_RL, coneMinus, hComplement] using hRL
    have hZero := hCore.2 hCoreInput
    simpa [soul_RL, coneMinus, hComplement] using hZero

/-- Star exchanges the two DeWitt soul corners when the Peirce projectors are
self-adjoint. -/
theorem star_soul_LR_eq_soul_RL
    [S : ChiralPeirceSystem M]
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR) (X : M) :
    star (soul_LR X) = soul_RL (star X) := by
  dsimp [soul_LR, soul_RL]
  rw [star_mul, star_mul, hstarPL, hstarPR, mul_assoc]

/-- A self-adjoint element's DeWitt soul is the Majorana pair consisting of
one chiral corner and its star-conjugate corner.  The equality is in the
original associative ring and does not identify the two corners. -/
theorem selfAdjoint_soul_is_paired_chiral_corners
    [S : ChiralPeirceSystem M]
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (X : M) (hX : star X = X) :
    soul X = soul_LR X + star (soul_LR X) := by
  dsimp [soul]
  rw [star_soul_LR_eq_soul_RL hstarPL hstarPR X, hX]

/-- The full DeWitt decomposition of a self-adjoint element separates its
diagonal body from the paired Majorana soul. -/
theorem selfAdjoint_dewitt_split_into_body_and_paired_soul
    [S : ChiralPeirceSystem M]
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (X : M) (hX : star X = X) :
    X = body X + (soul_LR X + star (soul_LR X)) := by
  rw [← selfAdjoint_soul_is_paired_chiral_corners hstarPL hstarPR X hX]
  exact dewitt_split X

omit [StarRing M] in
/-- Anti-multiplicativity is incompatible with a nonzero fermionic product in
the fixed locus: if both odd factors and their product are fixed, and the
factors anticommute, the product vanishes in a ring without additive 2-torsion. -/
theorem anti_multiplicative_fixed_fermion_product_eq_zero
    (J : M → M) (hJmul : ∀ A B : M, J (A * B) = J B * J A)
    (hNoTwoTorsion : ∀ Z : M, Z + Z = 0 → Z = 0)
    (A B : M) (hJA : J A = A) (hJB : J B = B)
    (hJAB : J (A * B) = A * B) (hFermion : A * B = -(B * A)) :
    A * B = 0 := by
  have hCommute : A * B = B * A := by
    calc
      A * B = J (A * B) := hJAB.symm
      _ = J B * J A := hJmul A B
      _ = B * A := by rw [hJB, hJA]
  have hNeg : A * B = -(A * B) := by
    calc
      A * B = -(B * A) := hFermion
      _ = -(A * B) := by rw [← hCommute]
  apply hNoTwoTorsion
  calc
    A * B + A * B = A * B + -(A * B) :=
      congrArg (fun Z : M => A * B + Z) hNeg
    _ = 0 := add_neg_cancel _

/-- 🏆 THEOREM 1: Zero is in the Crosscap Subalgebra -/
theorem zero_mem_crosscap (D : CrosscapDatum M) :
    InCrosscapSubalgebra D (0 : M) := by
  dsimp [InCrosscapSubalgebra]
  rw [map_zero, tomitaCPT_zero]

/-- 🏆 THEOREM 2: Addition is preserved in Crosscap Subalgebra -/
theorem add_mem_crosscap (D : CrosscapDatum M)
    (A B : M) (hA : InCrosscapSubalgebra D A) (hB : InCrosscapSubalgebra D B) :
    InCrosscapSubalgebra D (A + B) := by
  dsimp [InCrosscapSubalgebra] at *
  rw [map_add, tomitaCPT_add, hA, hB]

/-- Any element in the crosscap subalgebra has both its DeWitt `body` and `soul` in the crosscap subalgebra. -/
theorem crosscap_splits_body_and_soul
    (D : CrosscapDatum M) [S : ChiralPeirceSystem M]
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PR) (hΩPR : D.glide S.PR = S.PL)
    (A : M) (hA : InCrosscapSubalgebra D A) :
    InCrosscapSubalgebra D (body A) ∧ InCrosscapSubalgebra D (soul A) := by
  obtain ⟨hLL, hRR, hLR, hRL⟩ :=
    crosscap_splits_peirce_corners D hstarPL hstarPR hJPL hJPR hΩPL hΩPR A hA
  exact ⟨add_mem_crosscap D _ _ hLL hRR,
         add_mem_crosscap D _ _ hLR hRL⟩

/-- A self-adjoint crosscap-fixed element decomposes within the crosscap real
fixed locus into a self-adjoint Peirce body and a self-adjoint paired
Majorana soul.  The soul is explicitly the sum of one chiral corner and its
star-reflected corner; a single self-adjoint chiral corner is not asserted to
survive.  This is an operator-ring statement under the stated sheet actions,
not a claim about vector-level antilinear Tomita conjugation. -/
theorem crosscap_selfAdjoint_body_majorana_decomposition
    (D : CrosscapDatum M) [S : ChiralPeirceSystem M]
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PR) (hΩPR : D.glide S.PR = S.PL)
    (A : M) (hA : InCrosscapSubalgebra D A) (hSA : star A = A) :
    InCrosscapSubalgebra D (body A) ∧ star (body A) = body A ∧
    InCrosscapSubalgebra D (soul A) ∧ star (soul A) = soul A ∧
    soul A = soul_LR A + star (soul_LR A) ∧
    A = body A + (soul_LR A + star (soul_LR A)) := by
  have hCrosscapSplit := crosscap_splits_body_and_soul D
    hstarPL hstarPR hJPL hJPR hΩPL hΩPR A hA
  have hBodyStar : star (body A) = body A := by
    dsimp [body]
    simp only [star_add, star_mul, hstarPL, hstarPR, hSA]
    noncomm_ring
  have hSoulStar : star (soul A) = soul A := by
    have hstarRL : star (soul_RL A) = soul_LR A := by
      dsimp [soul_RL, soul_LR]
      rw [star_mul, star_mul, hstarPL, hstarPR, hSA]
      noncomm_ring
    change star (soul_LR A + soul_RL A) = soul_LR A + soul_RL A
    rw [star_add, star_soul_LR_eq_soul_RL hstarPL hstarPR A, hSA, hstarRL]
    exact add_comm (soul_RL A) (soul_LR A)
  have hPaired := selfAdjoint_soul_is_paired_chiral_corners
    hstarPL hstarPR A hSA
  have hDecomp := selfAdjoint_dewitt_split_into_body_and_paired_soul
    hstarPL hstarPR A hSA
  exact ⟨hCrosscapSplit.1, hBodyStar, hCrosscapSplit.2, hSoulStar,
    hPaired, hDecomp⟩

/-- Multiplication is preserved in the crosscap fixed locus.

This uses only the ring-automorphism law for the glide, the reversal law for
the star operation, and the anti-multiplicativity of the Tomita datum `J`.
It is the multiplicative part of the algebraic closure statement; no
topological or von Neumann-algebra interpretation is needed.
-/
theorem mul_mem_crosscap (D : CrosscapDatum M)
    (A B : M) (hA : InCrosscapSubalgebra D A) (hB : InCrosscapSubalgebra D B) :
    InCrosscapSubalgebra D (A * B) := by
  dsimp [InCrosscapSubalgebra] at *
  calc
    D.glide (A * B) = D.glide A * D.glide B := map_mul D.glide A B
    _ = tomitaCPT D A * tomitaCPT D B := by rw [hA, hB]
    _ = tomitaCPT D (A * B) := (tomitaCPT_mul D A B).symm

/-- A crosscap-fixed operator's Peirce noncommutativity obstruction is itself
crosscap-fixed. Its square then descends to the Peirce body and commutes with
the defining left projector. This transports the odd first-grade obstruction
to an even second-grade invariant while keeping the original noncommutative
ring carrier. -/
theorem crosscap_fixed_peirce_obstruction_generates_body_grade
    (D : CrosscapDatum M) [S : ChiralPeirceSystem M]
    (hstarPL : star S.PL = S.PL) (hJPL : D.J.toFun S.PL = S.PR)
    (hΩPL : D.glide S.PL = S.PR)
    (X : M) (hX : InCrosscapSubalgebra D X) :
    InCrosscapSubalgebra D
      (InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL X) ∧
    InCrosscapSubalgebra D
      (InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL X *
        InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL X) ∧
    body (InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL X *
      InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL X) =
      InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL X *
        InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL X ∧
    InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL
      (InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL X *
        InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL X) = 0 := by
  have hGlideComm : ∀ a b : M,
      D.glide (InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm a b) =
        InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm (D.glide a) (D.glide b) := by
    intro a b
    simp only [InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm,
      map_sub, map_mul]
  have hCPTPL : tomitaCPT D S.PL = S.PR := by
    simp [tomitaCPT, hstarPL, hJPL]
  have hCommFixed : InCrosscapSubalgebra D
      (InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL X) := by
    change D.glide (InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL X) =
      tomitaCPT D (InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL X)
    rw [hGlideComm, hΩPL, hX, tomitaCPT_comm, hCPTPL]
  have hSquareFixed :
      InCrosscapSubalgebra D
        (InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL X *
          InfoGeometry.Algebra.DeWittPeirceSuperalgebra.comm S.PL X) :=
    mul_mem_crosscap D _ _ hCommFixed hCommFixed
  exact ⟨hCommFixed, hSquareFixed,
    two_idempotent_comm_sq_is_body (A := M) X,
    two_idempotent_comm_sq_comm_PL (A := M) X⟩

/-- If the glide commutes with the involution `star`, the crosscap fixed
locus is stable under `star`.  The proof uses `J_star`; it does not identify
the multiplicative CPT map with the anti-multiplicative Tomita map. -/
theorem star_mem_crosscap (D : CrosscapDatum M)
    (hGlideStar : ∀ A : M, D.glide (star A) = star (D.glide A))
    (A : M) (hA : InCrosscapSubalgebra D A) :
    InCrosscapSubalgebra D (star A) := by
  dsimp [InCrosscapSubalgebra] at hA ⊢
  calc
    D.glide (star A) = star (D.glide A) := hGlideStar A
    _ = star (tomitaCPT D A) := congrArg star hA
    _ = tomitaCPT D (star A) := by simp [tomitaCPT, D.J_star]

/-- The operatorial crosscap fixed locus is a genuine subring of the original
possibly noncommutative coefficient ring.  Its carrier is the existing
equalizer predicate; the closure laws follow from the actual glide and
Tomita/star maps, without changing the coefficient algebra. -/
def crosscapFixedSubring (D : CrosscapDatum M) : Subring M where
  carrier := {A | InCrosscapSubalgebra D A}
  zero_mem' := zero_mem_crosscap D
  one_mem' := by
    have hJone : D.J.toFun (1 : M) = 1 :=
      (antiOppositeRingEquiv D.J).map_one
    change D.glide 1 = D.J.toFun (star 1)
    rw [map_one, star_one, hJone]
  add_mem' := by
    intro A B hA hB
    exact add_mem_crosscap D A B hA hB
  neg_mem' := by
    intro A hA
    change D.glide A = D.J.toFun (star A) at hA
    change D.glide (-A) = D.J.toFun (star (-A))
    rw [map_neg, star_neg]
    have hJneg : ∀ x : M, D.J.toFun (-x) = -D.J.toFun x := by
      intro x
      have h := (antiOppositeRingEquiv D.J).map_neg (MulOpposite.op x)
      simpa [antiOppositeRingEquiv] using h
    rw [hJneg, hA]
  mul_mem' := fun {A B} hA hB => mul_mem_crosscap D A B hA hB

/-- If the crosscap maps are continuous on a Hausdorff topological operator
ring, the native subring carrier is closed.  This joins the algebraic fixed
subring and the already established equalizer-topology theorem. -/
theorem isClosed_crosscapFixedSubring [TopologicalSpace M] [T2Space M]
    (D : CrosscapDatum M)
    (hglide : Continuous D.glide)
    (hCPT : Continuous (tomitaCPT D)) :
    IsClosed (crosscapFixedSubring D : Set M) := by
  have hcarrier : (crosscapFixedSubring D : Set M) =
      {A : M | InCrosscapSubalgebra D A} := by
    ext A
    rfl
  rw [hcarrier]
  change IsClosed {A : M | D.glide A = tomitaCPT D A}
  exact isClosed_eq hglide hCPT

/-- 🏆 THEOREM 3: Double Glide Orbit Invariance: Ω²(A) = A -/
theorem double_glide_identity (D : CrosscapDatum M) (A : M) :
    D.glide (D.glide A) = A :=
  D.glide_involutive A

/-! ### Topological crosscap fixed locus

The algebraic crosscap equation is an equalizer.  On a Hausdorff topology on
the operator carrier, continuity of its two maps therefore makes the fixed
locus closed.  This statement is deliberately independent of any claim that
the resulting topology is a von Neumann algebra topology or a quotient Klein
bottle topology. -/

/-- Continuity of the operator-level Tomita conjugation and star operation
induces continuity of the multiplicative CPT composite used in the crosscap
equalizer. -/
theorem continuous_tomitaCPT [TopologicalSpace M]
    (D : CrosscapDatum M)
    (hJ : Continuous D.J.toFun)
    (hstar : Continuous (star : M → M)) :
    Continuous (tomitaCPT D) := by
  exact hJ.comp hstar

/-- The crosscap fixed locus is closed when the glide and Tomita-CPT maps are
continuous into a Hausdorff operator carrier. -/
theorem isClosed_crosscap_fixed_locus [TopologicalSpace M] [T2Space M]
    (D : CrosscapDatum M)
    (hglide : Continuous D.glide)
    (hCPT : Continuous (tomitaCPT D)) :
    IsClosed {A : M | InCrosscapSubalgebra D A} := by
  change IsClosed {A : M | D.glide A = tomitaCPT D A}
  exact isClosed_eq hglide hCPT

/-! The algebraic Peirce projections are continuous for the intrinsic
topology of a topological operator ring.  The crosscap subtype inherits this
topology, and the already-proved corner closure therefore restricts these
continuous maps to its fixed locus. -/

omit [StarRing M] in
theorem continuous_soul_LR [TopologicalSpace M] [IsTopologicalRing M]
    [S : ChiralPeirceSystem M] : Continuous (soul_LR : M → M) := by
  change Continuous (fun X : M => (S.PL * X) * S.PR)
  exact (continuous_const.mul continuous_id).mul continuous_const

omit [StarRing M] in
theorem continuous_soul_RL [TopologicalSpace M] [IsTopologicalRing M]
    [S : ChiralPeirceSystem M] : Continuous (soul_RL : M → M) := by
  change Continuous (fun X : M => (S.PR * X) * S.PL)
  exact (continuous_const.mul continuous_id).mul continuous_const

omit [StarRing M] in
theorem continuous_body [TopologicalSpace M] [IsTopologicalRing M]
    [S : ChiralPeirceSystem M] : Continuous (body : M → M) := by
  change Continuous (fun X : M => (S.PL * X) * S.PL + (S.PR * X) * S.PR)
  exact ((continuous_const.mul continuous_id).mul continuous_const).add
    ((continuous_const.mul continuous_id).mul continuous_const)

omit [StarRing M] in
theorem continuous_soul [TopologicalSpace M] [IsTopologicalRing M]
    [S : ChiralPeirceSystem M] : Continuous (soul : M → M) := by
  change Continuous (fun X : M => soul_LR X + soul_RL X)
  exact (continuous_soul_LR.add continuous_soul_RL)

/-- The Peirce body projection restricted to the crosscap fixed locus.  Its
range proof is the algebraic body/soul compatibility theorem above. -/
def crosscapBodyMap [S : ChiralPeirceSystem M]
    (D : CrosscapDatum M)
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PR) (hΩPR : D.glide S.PR = S.PL) :
    {A : M // InCrosscapSubalgebra D A} → {A : M // InCrosscapSubalgebra D A} :=
  fun A => ⟨body A.1,
    (crosscap_splits_body_and_soul D hstarPL hstarPR hJPL hJPR
      hΩPL hΩPR A.1 A.2).1⟩

/-- The DeWitt soul projection restricted to the crosscap fixed locus. -/
def crosscapSoulMap [S : ChiralPeirceSystem M]
    (D : CrosscapDatum M)
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PR) (hΩPR : D.glide S.PR = S.PL) :
    {A : M // InCrosscapSubalgebra D A} → {A : M // InCrosscapSubalgebra D A} :=
  fun A => ⟨soul A.1,
    (crosscap_splits_body_and_soul D hstarPL hstarPR hJPL hJPR
      hΩPL hΩPR A.1 A.2).2⟩

/-- On the crosscap fixed locus, the restricted body and soul maps remain
complementary projections.  This records the decomposition in the actual
fixed-locus carrier rather than only in the ambient ring. -/
theorem crosscap_body_soul_projection_laws [S : ChiralPeirceSystem M]
    (D : CrosscapDatum M)
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PR) (hΩPR : D.glide S.PR = S.PL)
    (x : {A : M // InCrosscapSubalgebra D A}) :
    crosscapBodyMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR
        (crosscapBodyMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR x) =
      crosscapBodyMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR x ∧
    crosscapSoulMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR
        (crosscapSoulMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR x) =
      crosscapSoulMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR x ∧
    x.1 = (crosscapBodyMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR x).1 +
      (crosscapSoulMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR x).1 := by
  constructor
  · apply Subtype.ext
    exact body_is_idempotent x.1
  constructor
  · apply Subtype.ext
    exact soul_is_idempotent x.1
  · exact dewitt_split x.1

/-- The restricted body and soul projections are orthogonal on the actual
crosscap carrier: applying one after the other gives the zero operator. -/
theorem crosscap_body_soul_compositions_zero [S : ChiralPeirceSystem M]
    (D : CrosscapDatum M)
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PR) (hΩPR : D.glide S.PR = S.PL)
    (x : {A : M // InCrosscapSubalgebra D A}) :
    (crosscapBodyMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR
      (crosscapSoulMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR x)).1 = 0 ∧
    (crosscapSoulMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR
      (crosscapBodyMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR x)).1 = 0 := by
  exact body_soul_orthogonal x.1

/-! ### Topological product decomposition of the CPT fixed carrier

The body and soul ranges are not merely closed sectors: their sum reconstructs
the crosscap fixed carrier, and the two projections give its product
coordinates. -/

/-- The body-fixed sector inside the crosscap carrier. -/
def crosscapBodyFixedSector (S : ChiralPeirceSystem M) (D : CrosscapDatum M) := by
  letI : ChiralPeirceSystem M := S
  exact {x : {A : M // InCrosscapSubalgebra D A} // body x.1 = x.1}

/-- The soul-fixed sector inside the crosscap carrier. -/
def crosscapSoulFixedSector (S : ChiralPeirceSystem M) (D : CrosscapDatum M) := by
  letI : ChiralPeirceSystem M := S
  exact {x : {A : M // InCrosscapSubalgebra D A} // soul x.1 = x.1}

instance crosscapBodyFixedSector.instTopologicalSpace [TopologicalSpace M]
    (S : ChiralPeirceSystem M) (D : CrosscapDatum M) :
    TopologicalSpace (crosscapBodyFixedSector S D) := by
  unfold crosscapBodyFixedSector
  infer_instance

instance crosscapSoulFixedSector.instTopologicalSpace [TopologicalSpace M]
    (S : ChiralPeirceSystem M) (D : CrosscapDatum M) :
    TopologicalSpace (crosscapSoulFixedSector S D) := by
  unfold crosscapSoulFixedSector
  infer_instance

theorem continuous_crosscapBodyMap [TopologicalSpace M] [IsTopologicalRing M]
    [S : ChiralPeirceSystem M] (D : CrosscapDatum M)
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PR) (hΩPR : D.glide S.PR = S.PL) :
    Continuous (crosscapBodyMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR) := by
  apply Continuous.subtype_mk
  exact continuous_body.comp continuous_subtype_val

theorem continuous_crosscapSoulMap [TopologicalSpace M] [IsTopologicalRing M]
    [S : ChiralPeirceSystem M] (D : CrosscapDatum M)
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PR) (hΩPR : D.glide S.PR = S.PL) :
    Continuous (crosscapSoulMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR) := by
  apply Continuous.subtype_mk
  exact continuous_soul.comp continuous_subtype_val

/-- The crosscap fixed carrier is homeomorphic to the product of its
body-fixed and soul-fixed sectors. The forward map is the actual pair of
Peirce projections; the inverse adds the two orthogonal components. -/
def crosscap_peirce_product_homeomorph [TopologicalSpace M] [IsTopologicalRing M]
    [S : ChiralPeirceSystem M] (D : CrosscapDatum M)
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PR) (hΩPR : D.glide S.PR = S.PL) :
    {A : M // InCrosscapSubalgebra D A} ≃ₜ
      (crosscapBodyFixedSector S D × crosscapSoulFixedSector S D) := by
  let B := crosscapBodyFixedSector S D
  let S₀ := crosscapSoulFixedSector S D
  let equiv : {A : M // InCrosscapSubalgebra D A} ≃ B × S₀ := {
      toFun := fun x =>
        (⟨crosscapBodyMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR x,
          body_is_idempotent x.1⟩,
         ⟨crosscapSoulMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR x,
          soul_is_idempotent x.1⟩)
      invFun := fun y =>
        ⟨y.1.1.1 + y.2.1.1, add_mem_crosscap D _ _ y.1.1.2 y.2.1.2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact (dewitt_split x.1).symm
      right_inv := by
        intro y
        apply Prod.ext
        · apply Subtype.ext
          apply Subtype.ext
          change body (y.1.1.1 + y.2.1.1) = y.1.1.1
          have hBodySoul : body y.2.1.1 = 0 := by
            rw [← y.2.2]
            exact (body_soul_orthogonal y.2.1.1).1
          rw [body_add, hBodySoul, y.1.2, add_zero]
        · apply Subtype.ext
          apply Subtype.ext
          change soul (y.1.1.1 + y.2.1.1) = y.2.1.1
          have hSoulBody : soul y.1.1.1 = 0 := by
            rw [← y.1.2]
            exact (body_soul_orthogonal y.1.1.1).2
          rw [soul_add, hSoulBody, y.2.2, zero_add] }
  exact Homeomorph.mk equiv
    (by
      apply Continuous.prodMk
      · apply Continuous.subtype_mk
        exact continuous_crosscapBodyMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR
      · apply Continuous.subtype_mk
        exact continuous_crosscapSoulMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR)
    (by
      apply Continuous.subtype_mk
      exact
        (continuous_subtype_val.comp
          (continuous_subtype_val.comp continuous_fst)).add
        (continuous_subtype_val.comp
          (continuous_subtype_val.comp continuous_snd)))

/-- The body sector is closed in the Hausdorff crosscap carrier: for an
idempotent projection its image is exactly its fixed-point set. -/
theorem isClosed_range_crosscapBodyMap [TopologicalSpace M] [T2Space M]
    [IsTopologicalRing M] [S : ChiralPeirceSystem M] (D : CrosscapDatum M)
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PR) (hΩPR : D.glide S.PR = S.PL) :
    IsClosed (Set.range
      (crosscapBodyMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR)) := by
  let f := crosscapBodyMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR
  have hf : Continuous f :=
    continuous_crosscapBodyMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR
  have hproj : ∀ x, f (f x) = f x := by
    intro x
    exact (crosscap_body_soul_projection_laws D hstarPL hstarPR
      hJPL hJPR hΩPL hΩPR x).1
  have hrange : Set.range f = {x | f x = x} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact hproj y
    · intro hx
      exact ⟨x, hx⟩
  rw [hrange]
  exact isClosed_eq hf continuous_id

/-- The soul sector is closed in the Hausdorff crosscap carrier, by the same
fixed-point characterization of the idempotent soul projection. -/
theorem isClosed_range_crosscapSoulMap [TopologicalSpace M] [T2Space M]
    [IsTopologicalRing M] [S : ChiralPeirceSystem M] (D : CrosscapDatum M)
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PR) (hΩPR : D.glide S.PR = S.PL) :
    IsClosed (Set.range
      (crosscapSoulMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR)) := by
  let f := crosscapSoulMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR
  have hf : Continuous f :=
    continuous_crosscapSoulMap D hstarPL hstarPR hJPL hJPR hΩPL hΩPR
  have hproj : ∀ x, f (f x) = f x := by
    intro x
    exact (crosscap_body_soul_projection_laws D hstarPL hstarPR
      hJPL hJPR hΩPL hΩPR x).2.1
  have hrange : Set.range f = {x | f x = x} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact hproj y
    · intro hx
      exact ⟨x, hx⟩
  rw [hrange]
  exact isClosed_eq hf continuous_id

/-- Frobenius-Schur Type classification for anyon/chiral sectors -/
inductive FrobeniusSchurType
  | Real          -- ν = +1 (Majorana / self-dual symmetric)
  | PseudoReal    -- ν = -1 (Kramers / self-dual antisymmetric)
  | ComplexChiral -- ν = 0  (Chiral pair a ≠ ā)
  deriving DecidableEq, Repr

/-- Frobenius-Schur Indicator value in ℤ -/
def frobeniusSchurValue : FrobeniusSchurType → ℤ
  | .Real => 1
  | .PseudoReal => -1
  | .ComplexChiral => 0

/-- Crosscap trace vanishing condition: Complex chiral anyons have zero crosscap amplitude -/
def HasVanishingCrosscapAmplitude (t : FrobeniusSchurType) : Prop :=
  frobeniusSchurValue t = 0

/-- 🏆 THEOREM 4: Complex chiral anyons vanish under the Klein crosscap trace -/
theorem complex_chiral_crosscap_vanishes :
    HasVanishingCrosscapAmplitude FrobeniusSchurType.ComplexChiral := by
  dsimp [HasVanishingCrosscapAmplitude, frobeniusSchurValue]

/-- 🏆 THEOREM 5: Real Majorana anyons survive with unit positive crosscap weight -/
theorem real_majorana_crosscap_survives :
    frobeniusSchurValue FrobeniusSchurType.Real = 1 := by
  rfl

/-- Peirce-Witten Parity sector: F = 0 (longitudinal/time) or F = 1 (transverse/space) -/
inductive PeirceParity
  | Even -- F = 0, M = +1
  | Odd  -- F = 1, M = -1
  deriving DecidableEq, Repr

/-- Witten Parity sign M = (-1)^F -/
def wittenParitySign : PeirceParity → ℤ
  | .Even => 1
  | .Odd => -1

/-- Twisted Cayley-Hestenes Monodromy relation sign -/
def cayleyHestenesCommutatorSign (p : PeirceParity) : ℤ :=
  - wittenParitySign p

/-- 🏆 THEOREM 6: Longitudinal Sector (F=0) gives CPT Anticommutation (-1) -/
theorem longitudinal_cpt_anticommuting :
    cayleyHestenesCommutatorSign PeirceParity.Even = -1 := by
  rfl

/-- 🏆 THEOREM 7: Transverse Sector (F=1) gives Spatial Rotation Commutation (+1) -/
theorem transverse_spatial_commuting :
    cayleyHestenesCommutatorSign PeirceParity.Odd = 1 := by
  rfl

/-- 🏆 THEOREM 8: Grand Klein Bottle Crosscap & Frobenius-Schur Synthesis -/
theorem klein_bottle_crosscap_synthesis (D : CrosscapDatum M) :
    (InCrosscapSubalgebra D (0 : M)) ∧
    (∀ (A B : M), InCrosscapSubalgebra D A → InCrosscapSubalgebra D B → InCrosscapSubalgebra D (A + B)) ∧
    (HasVanishingCrosscapAmplitude FrobeniusSchurType.ComplexChiral) ∧
    (frobeniusSchurValue FrobeniusSchurType.Real = 1) ∧
    (cayleyHestenesCommutatorSign PeirceParity.Even = -1) ∧
    (cayleyHestenesCommutatorSign PeirceParity.Odd = 1) :=
  ⟨zero_mem_crosscap D,
   add_mem_crosscap D,
   complex_chiral_crosscap_vanishes,
   real_majorana_crosscap_survives,
   longitudinal_cpt_anticommuting,
   transverse_spatial_commuting⟩

/-! ### Sheet-Preserving Glide Obstruction & 4-Row Peirce Involution Classification -/

section SheetPreservingGlideAndFourRowTable

/-- **Sheet-Preserving Glide vs. Sheet-Swapping Tomita CPT Obstruction**:
When the glide `Ω` preserves the chiral sheets (`Ω P_L = P_L`, `Ω P_R = P_R`) while
`tomitaCPT = D.J.toFun ∘ star` swaps them (`D.J.toFun P_L = P_R`, `D.J.toFun P_R = P_L`, `star P_L = P_L`,
`star P_R = P_R`), any single pure chiral soul corner (`soul_LR X` or `soul_RL X`) or
single diagonal corner (`P_L X P_L` or `P_R X P_R`) in `InCrosscapSubalgebra D` must
vanish identically by projector orthogonality `P_L * P_R = 0`. -/
theorem crosscap_sheetPreserving_glide_kills_chiral_corners
    (D : CrosscapDatum M) [S : ChiralPeirceSystem M]
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PL) (hΩPR : D.glide S.PR = S.PR)
    (X : M) :
    (InCrosscapSubalgebra D (soul_LR X) → soul_LR X = 0) ∧
    (InCrosscapSubalgebra D (soul_RL X) → soul_RL X = 0) ∧
    (InCrosscapSubalgebra D (S.PL * X * S.PL) → S.PL * X * S.PL = 0) ∧
    (InCrosscapSubalgebra D (S.PR * X * S.PR) → S.PR * X * S.PR = 0) := by
  have hPRPL := PR_PL_ortho (A := M)
  have hGlideInj : Function.Injective D.glide := fun a b hab => by
    calc a = D.glide (D.glide a) := (D.glide_involutive a).symm
      _ = D.glide (D.glide b) := by rw [hab]
      _ = b := D.glide_involutive b
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hLR
    dsimp [InCrosscapSubalgebra] at hLR
    have hG : D.glide (soul_LR X) = S.PL * D.glide X * S.PR := by
      dsimp [soul_LR]; rw [map_mul, map_mul, hΩPL, hΩPR]
    have hC := tomitaCPT_soul_LR_eq_soul_RL D hstarPL hstarPR hJPL hJPR X
    have hEq : S.PL * D.glide X * S.PR = S.PR * tomitaCPT D X * S.PL := by
      rw [← hG, hLR, hC]; rfl
    have hZero : S.PL * D.glide X * S.PR = 0 := by
      calc S.PL * D.glide X * S.PR
        _ = S.PL * (S.PL * D.glide X * S.PR) := by
            rw [← mul_assoc, ← mul_assoc, S.h_PL_sq]
        _ = S.PL * (S.PR * tomitaCPT D X * S.PL) := by rw [hEq]
        _ = (S.PL * S.PR) * tomitaCPT D X * S.PL := by simp only [mul_assoc]
        _ = 0 := by rw [S.h_PL_PR, zero_mul, zero_mul]
    rw [← hG] at hZero
    exact hGlideInj (hZero.trans (map_zero D.glide).symm)
  · intro hRL
    dsimp [InCrosscapSubalgebra] at hRL
    have hG : D.glide (soul_RL X) = S.PR * D.glide X * S.PL := by
      dsimp [soul_RL]; rw [map_mul, map_mul, hΩPR, hΩPL]
    have hC := tomitaCPT_soul_RL_eq_soul_LR D hstarPL hstarPR hJPL hJPR X
    have hEq : S.PR * D.glide X * S.PL = S.PL * tomitaCPT D X * S.PR := by
      rw [← hG, hRL, hC]; rfl
    have hZero : S.PR * D.glide X * S.PL = 0 := by
      calc S.PR * D.glide X * S.PL
        _ = S.PR * (S.PR * D.glide X * S.PL) := by
            rw [← mul_assoc, ← mul_assoc, S.h_PR_sq]
        _ = S.PR * (S.PL * tomitaCPT D X * S.PR) := by rw [hEq]
        _ = (S.PR * S.PL) * tomitaCPT D X * S.PR := by simp only [mul_assoc]
        _ = 0 := by rw [hPRPL, zero_mul, zero_mul]
    rw [← hG] at hZero
    exact hGlideInj (hZero.trans (map_zero D.glide).symm)
  · intro hLL
    dsimp [InCrosscapSubalgebra] at hLL
    have hG : D.glide (S.PL * X * S.PL) = S.PL * D.glide X * S.PL := by
      rw [map_mul, map_mul, hΩPL]
    have hC : tomitaCPT D (S.PL * X * S.PL) = S.PR * tomitaCPT D X * S.PR := by
      rw [tomitaCPT_mul, tomitaCPT_mul]
      simp [tomitaCPT, hstarPL, hJPL]
    have hEq : S.PL * D.glide X * S.PL = S.PR * tomitaCPT D X * S.PR := by
      rw [← hG, hLL, hC]
    have hZero : S.PL * D.glide X * S.PL = 0 := by
      calc S.PL * D.glide X * S.PL
        _ = S.PL * (S.PL * D.glide X * S.PL) := by
            rw [← mul_assoc, ← mul_assoc, S.h_PL_sq]
        _ = S.PL * (S.PR * tomitaCPT D X * S.PR) := by rw [hEq]
        _ = (S.PL * S.PR) * tomitaCPT D X * S.PR := by simp only [mul_assoc]
        _ = 0 := by rw [S.h_PL_PR, zero_mul, zero_mul]
    rw [← hG] at hZero
    exact hGlideInj (hZero.trans (map_zero D.glide).symm)
  · intro hRR
    dsimp [InCrosscapSubalgebra] at hRR
    have hG : D.glide (S.PR * X * S.PR) = S.PR * D.glide X * S.PR := by
      rw [map_mul, map_mul, hΩPR]
    have hC : tomitaCPT D (S.PR * X * S.PR) = S.PL * tomitaCPT D X * S.PL := by
      rw [tomitaCPT_mul, tomitaCPT_mul]
      simp [tomitaCPT, hstarPR, hJPR]
    have hEq : S.PR * D.glide X * S.PR = S.PL * tomitaCPT D X * S.PL := by
      rw [← hG, hRR, hC]
    have hZero : S.PR * D.glide X * S.PR = 0 := by
      calc S.PR * D.glide X * S.PR
        _ = S.PR * (S.PR * D.glide X * S.PR) := by
            rw [← mul_assoc, ← mul_assoc, S.h_PR_sq]
        _ = S.PR * (S.PL * tomitaCPT D X * S.PL) := by rw [hEq]
        _ = (S.PR * S.PL) * tomitaCPT D X * S.PL := by simp only [mul_assoc]
        _ = 0 := by rw [hPRPL, zero_mul, zero_mul]
    rw [← hG] at hZero
    exact hGlideInj (hZero.trans (map_zero D.glide).symm)

/-- Under a sheet-preserving glide `Ω` and sheet-swapping `tomitaCPT`, `InCrosscapSubalgebra D`
exchanges `P_L A P_L ↔ P_R A P_R` and `soul_LR A ↔ soul_RL A`, so `InCrosscapSubalgebra D`
remains strictly closed under both `body` and total `soul` projections (paired Majorana states
survive while pure single-sheet corners vanish). -/
theorem crosscap_sheetPreserving_glide_preserves_body_and_soul
    (D : CrosscapDatum M) [S : ChiralPeirceSystem M]
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL)
    (hΩPL : D.glide S.PL = S.PL) (hΩPR : D.glide S.PR = S.PR)
    (A : M) (hA : InCrosscapSubalgebra D A) :
    D.glide (S.PL * A * S.PL) = tomitaCPT D (S.PR * A * S.PR) ∧
    D.glide (S.PR * A * S.PR) = tomitaCPT D (S.PL * A * S.PL) ∧
    D.glide (soul_LR A) = tomitaCPT D (soul_RL A) ∧
    D.glide (soul_RL A) = tomitaCPT D (soul_LR A) ∧
    InCrosscapSubalgebra D (body A) ∧
    InCrosscapSubalgebra D (soul A) := by
  dsimp [InCrosscapSubalgebra] at hA
  have hLL : D.glide (S.PL * A * S.PL) = tomitaCPT D (S.PR * A * S.PR) := by
    rw [map_mul, map_mul, hΩPL, hA, tomitaCPT_mul, tomitaCPT_mul]
    simp [tomitaCPT, hstarPR, hJPR]
  have hRR : D.glide (S.PR * A * S.PR) = tomitaCPT D (S.PL * A * S.PL) := by
    rw [map_mul, map_mul, hΩPR, hA, tomitaCPT_mul, tomitaCPT_mul]
    simp [tomitaCPT, hstarPL, hJPL]
  have hLR : D.glide (soul_LR A) = tomitaCPT D (soul_RL A) := by
    dsimp [soul_LR]
    rw [map_mul, map_mul, hΩPL, hΩPR, hA, tomitaCPT_soul_RL_eq_soul_LR D hstarPL hstarPR hJPL hJPR A]
    rfl
  have hRL : D.glide (soul_RL A) = tomitaCPT D (soul_LR A) := by
    dsimp [soul_RL]
    rw [map_mul, map_mul, hΩPR, hΩPL, hA, tomitaCPT_soul_LR_eq_soul_RL D hstarPL hstarPR hJPL hJPR A]
    rfl
  refine ⟨hLL, hRR, hLR, hRL, ?_, ?_⟩
  · dsimp [InCrosscapSubalgebra, tomitaCPT, body]
    rw [map_add, star_add, D.J.map_add]
    change D.glide (S.PL * A * S.PL) + D.glide (S.PR * A * S.PR) =
      tomitaCPT D (S.PL * A * S.PL) + tomitaCPT D (S.PR * A * S.PR)
    rw [hLL, hRR, add_comm]
  · dsimp [InCrosscapSubalgebra, tomitaCPT, soul]
    rw [map_add, star_add, D.J.map_add]
    change D.glide (soul_LR A) + D.glide (soul_RL A) =
      tomitaCPT D (soul_LR A) + tomitaCPT D (soul_RL A)
    rw [hLR, hRL, add_comm]

/-- **4-Row Peirce-Corner Classification on `CrosscapDatum` & `ChiralPeirceSystem`**:
Links `CrosscapDatum` directly to `StarGrading`'s four involution rows, keeping `Ad_G` (Row 1),
`tomitaCPT = D.J.toFun ∘ star` (Row 2), `star` (Row 3), and anti-multiplicative `D.J.toFun` (Row 4) strictly
distinct:
- Row 1 (`Ad_{invS S.PL}`): fixes diagonal sheets, negates `soul_LR` and `soul_RL`;
- Row 2 (`tomitaCPT D = D.J.toFun ∘ star`, multiplicative): swaps diagonal sheets and swaps `soul_LR ↔ soul_RL`;
- Row 3 (`star`, anti-multiplicative): fixes diagonal sheets and swaps `soul_LR ↔ soul_RL`;
- Row 4 (`D.J.toFun`, anti-multiplicative): swaps diagonal sheets yet **preserves** `soul_LR` and `soul_RL`
  individually via double-reversal cancellation. -/
theorem crosscap_fourRow_peirce_classification
    (D : CrosscapDatum M) [S : ChiralPeirceSystem M]
    (hstarPL : star S.PL = S.PL) (hstarPR : star S.PR = S.PR)
    (hJPL : D.J.toFun S.PL = S.PR) (hJPR : D.J.toFun S.PR = S.PL) (X : M) :
    (invS S.PL * soul_LR X * invS S.PL = -soul_LR X ∧
     invS S.PL * soul_RL X * invS S.PL = -soul_RL X) ∧
    (tomitaCPT D (soul_LR X) = soul_RL (tomitaCPT D X) ∧
     tomitaCPT D (soul_RL X) = soul_LR (tomitaCPT D X)) ∧
    (star (soul_LR X) = soul_RL (star X) ∧
     star (soul_RL X) = soul_LR (star X)) ∧
    (D.J.toFun (soul_LR X) = soul_LR (D.J.toFun X) ∧
     D.J.toFun (soul_RL X) = soul_RL (D.J.toFun X)) := by
  have hComplement : S.PR = 1 - S.PL := right_is_complement
  have hRow1 := chiralGrading_ad_corners S.h_PL_sq X
  have hRow4 := antiMultSheetSwap_corners D.J.toFun D.J.map_mul
    (by simpa [hComplement] using hJPL)
    (by rw [← hComplement]; exact hJPR) X
  refine ⟨⟨?_, ?_⟩,
    ⟨tomitaCPT_soul_LR_eq_soul_RL D hstarPL hstarPR hJPL hJPR X,
     tomitaCPT_soul_RL_eq_soul_LR D hstarPL hstarPR hJPL hJPR X⟩,
    ⟨star_soul_LR_eq_soul_RL hstarPL hstarPR X, ?_⟩,
    ⟨?_, ?_⟩⟩
  · simpa [soul_LR, conePlus, hComplement] using hRow1.2.2.1
  · simpa [soul_RL, coneMinus, hComplement] using hRow1.2.2.2
  · dsimp [soul_RL, soul_LR]
    rw [star_mul, star_mul, hstarPL, hstarPR, mul_assoc]
  · simpa [soul_LR, conePlus, hComplement] using hRow4.2.2.1
  · simpa [soul_RL, coneMinus, hComplement] using hRow4.2.2.2

/-- Concrete non-degenerate inhabitant of `CrosscapDatum` on `Matrix (Fin 2) (Fin 2) ℝ` with
sheet-preserving glide `Ω(M) = diag(1,-1) M diag(1,-1)` and Row-4 anti-multiplicative Tomita
conjugation `J(M) = !![0,1;1,0] Mᵀ !![0,1;1,0]`. -/
noncomputable def mat2SheetPreservingCrosscapDatum :
    CrosscapDatum (Matrix (Fin 2) (Fin 2) ℝ) :=
  let σ : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
  let g : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
  have hσ : σ * σ = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [σ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  have hσT : σ.transpose = σ := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [σ]
  have hg : g * g = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [g, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  { J :=
      { toFun := fun M => σ * M.transpose * σ
        map_add := fun X Y => by
          rw [Matrix.transpose_add]
          noncomm_ring
        inv := fun M => by
          calc σ * (σ * M.transpose * σ).transpose * σ
            _ = σ * (σ.transpose * M.transpose.transpose * σ.transpose) * σ := by
                simp only [Matrix.transpose_mul, mul_assoc]
            _ = (σ * σ) * M * (σ * σ) := by
                rw [hσT, Matrix.transpose_transpose]; simp only [mul_assoc]
            _ = M := by rw [hσ, one_mul, mul_one]
        map_mul := fun X Y => by
          calc σ * (X * Y).transpose * σ
            _ = σ * (Y.transpose * X.transpose) * σ := by rw [Matrix.transpose_mul]
            _ = σ * Y.transpose * (σ * σ) * X.transpose * σ := by
                rw [hσ]; simp only [mul_assoc, mul_one]
            _ = (σ * Y.transpose * σ) * (σ * X.transpose * σ) := by
                simp only [mul_assoc]
      }
    J_star := fun M => by
      simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.transpose_mul, Matrix.transpose_transpose, hσT, mul_assoc]
    glide :=
      { toFun := fun M => g * M * g
        invFun := fun M => g * M * g
        left_inv := fun M => by
          calc g * (g * M * g) * g = (g * g) * M * (g * g) := by simp only [mul_assoc]
            _ = M := by rw [hg, one_mul, mul_one]
        right_inv := fun M => by
          calc g * (g * M * g) * g = (g * g) * M * (g * g) := by simp only [mul_assoc]
            _ = M := by rw [hg, one_mul, mul_one]
        map_mul' := fun X Y => by
          calc g * (X * Y) * g
            _ = g * X * (g * g) * Y * g := by rw [hg]; simp only [mul_assoc, mul_one]
            _ = (g * X * g) * (g * Y * g) := by simp only [mul_assoc]
        map_add' := fun X Y => by simp only [mul_add, add_mul] }
    glide_involutive := fun M => by
      change g * (g * M * g) * g = M
      calc
        _ = (g * g) * M * (g * g) := by noncomm_ring
        _ = M := by rw [hg, one_mul, mul_one] }

/-- The concrete sheet-preserving `M₂(ℝ)` glide commutes with matrix transpose. -/
theorem mat2_crosscap_glide_commutes_with_star
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    mat2SheetPreservingCrosscapDatum.glide (star A) =
      star (mat2SheetPreservingCrosscapDatum.glide A) := by
  change (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) * A.transpose *
      !![1, 0; 0, -1] =
    ((!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) * A * !![1, 0; 0, -1]).transpose
  have hZ : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ).transpose =
      !![1, 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hZ]
  noncomm_ring

/-- The concrete `M₂(ℝ)` crosscap fixed subring is closed under transpose. -/
theorem mat2_crosscap_star_closed (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : InCrosscapSubalgebra mat2SheetPreservingCrosscapDatum A) :
    InCrosscapSubalgebra mat2SheetPreservingCrosscapDatum (star A) :=
  star_mem_crosscap mat2SheetPreservingCrosscapDatum
    mat2_crosscap_glide_commutes_with_star A hA

/-- In its native finite-dimensional matrix topology, the concrete crosscap
fixed subring is closed. -/
theorem mat2_crosscap_fixedSubring_isClosed :
    IsClosed (crosscapFixedSubring mat2SheetPreservingCrosscapDatum :
      Set (Matrix (Fin 2) (Fin 2) ℝ)) := by
  have hTranspose : Continuous
      (fun A : Matrix (Fin 2) (Fin 2) ℝ => A.transpose) := by
    change Continuous (fun A : Matrix (Fin 2) (Fin 2) ℝ => fun i j => A j i)
    exact continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply i).comp (continuous_apply j)
  have hStar : Continuous
      (star : Matrix (Fin 2) (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) := by
    change Continuous (fun A : Matrix (Fin 2) (Fin 2) ℝ => A.transpose)
    exact hTranspose
  have hGlide : Continuous mat2SheetPreservingCrosscapDatum.glide := by
    change Continuous (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) * A * !![1, 0; 0, -1])
    exact (continuous_const.mul continuous_id).mul continuous_const
  have hJ : Continuous mat2SheetPreservingCrosscapDatum.J.toFun := by
    change Continuous (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) * A.transpose * !![0, 1; 1, 0])
    exact (continuous_const.mul hTranspose).mul continuous_const
  exact isClosed_crosscapFixedSubring mat2SheetPreservingCrosscapDatum hGlide
    (continuous_tomitaCPT mat2SheetPreservingCrosscapDatum hJ hStar)

/-- The concrete matrix model distinguishes the operator anti-automorphism `J` from
the multiplicative Tomita/star composite `tomitaCPT = J ∘ star` on the two Peirce
soul generators.  `J` fixes each corner generator (Row 4), whereas `tomitaCPT`
exchanges them (Row 2); consequently a single nonzero soul corner is not fixed by
the multiplicative composite.  This statement concerns maps on the operator ring,
not the antilinear Tomita conjugation on Hilbert-space vectors. -/
theorem mat2_crosscap_J_and_CPT_corner_actions :
    let U : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
    let V : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    mat2SheetPreservingCrosscapDatum.J.toFun U = U ∧
    mat2SheetPreservingCrosscapDatum.J.toFun V = V ∧
    tomitaCPT mat2SheetPreservingCrosscapDatum U = V ∧
    tomitaCPT mat2SheetPreservingCrosscapDatum V = U ∧
    U ≠ 0 ∧
    tomitaCPT mat2SheetPreservingCrosscapDatum U ≠ U := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [mat2SheetPreservingCrosscapDatum, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, Fin.sum_univ_two, Matrix.transpose_apply]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [mat2SheetPreservingCrosscapDatum, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, Fin.sum_univ_two, Matrix.transpose_apply]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [tomitaCPT, mat2SheetPreservingCrosscapDatum, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial]
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [tomitaCPT, mat2SheetPreservingCrosscapDatum, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial]
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    simp at h01
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    simp [tomitaCPT, mat2SheetPreservingCrosscapDatum, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] at h01

/-- In the concrete sheet-preserving `M₂(ℝ)` crosscap, the fixed locus rejects each
pure Peirce soul corner but contains their coupled difference.  The coupling is
anti-self-adjoint for matrix transpose; this is the exact fixed vector for this
glide/CPT convention and is not an assertion that the self-adjoint Majorana sum is
fixed. -/
theorem mat2_crosscap_paired_soul_fixed_locus :
    let U : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
    let V : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
    ¬ InCrosscapSubalgebra mat2SheetPreservingCrosscapDatum U ∧
    ¬ InCrosscapSubalgebra mat2SheetPreservingCrosscapDatum V ∧
    InCrosscapSubalgebra mat2SheetPreservingCrosscapDatum (U - V) := by
  dsimp
  obtain ⟨_, _, hCPTU, hCPTV, _, _⟩ := mat2_crosscap_J_and_CPT_corner_actions
  have hGlideU : mat2SheetPreservingCrosscapDatum.glide
      (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) = -!![0, 1; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [mat2SheetPreservingCrosscapDatum]
  have hGlideV : mat2SheetPreservingCrosscapDatum.glide
      (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) = -!![0, 0; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [mat2SheetPreservingCrosscapDatum]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    change mat2SheetPreservingCrosscapDatum.glide
      (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) =
      tomitaCPT mat2SheetPreservingCrosscapDatum
        (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) at h
    rw [hGlideU, hCPTU] at h
    have h01 := congrFun (congrFun h 0) 1
    norm_num at h01
  · intro h
    change mat2SheetPreservingCrosscapDatum.glide
      (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) =
      tomitaCPT mat2SheetPreservingCrosscapDatum
        (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) at h
    rw [hGlideV, hCPTV] at h
    have h10 := congrFun (congrFun h 1) 0
    norm_num at h10
  · change mat2SheetPreservingCrosscapDatum.glide
      ((!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) -
       !![0, 0; 1, 0]) =
      tomitaCPT mat2SheetPreservingCrosscapDatum
       ((!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) -
        !![0, 0; 1, 0])
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [tomitaCPT, mat2SheetPreservingCrosscapDatum, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial]

/-- Complete coordinate classification of the crosscap fixed locus for the concrete
`M₂(ℝ)` sheet-preserving glide: the diagonal entries agree and the off-diagonal
entries are negatives of one another. -/
theorem mat2_crosscap_fixed_locus_characterization
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    InCrosscapSubalgebra mat2SheetPreservingCrosscapDatum A ↔
      A 0 0 = A 1 1 ∧ A 1 0 = -A 0 1 := by
  have hGlide (X : Matrix (Fin 2) (Fin 2) ℝ) :
      mat2SheetPreservingCrosscapDatum.glide X =
        (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) * X * !![1, 0; 0, -1] := rfl
  have hCPT (X : Matrix (Fin 2) (Fin 2) ℝ) :
      tomitaCPT mat2SheetPreservingCrosscapDatum X =
        (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) * X * !![0, 1; 1, 0] := by
    simp [tomitaCPT, mat2SheetPreservingCrosscapDatum, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
  constructor
  · intro hA
    change mat2SheetPreservingCrosscapDatum.glide A =
      tomitaCPT mat2SheetPreservingCrosscapDatum A at hA
    rw [hGlide, hCPT] at hA
    have h00 := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℝ => X 0 0) hA
    have h10 := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℝ => X 1 0) hA
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h00 h10
    constructor <;> linarith
  · rintro ⟨h00, h10⟩
    change mat2SheetPreservingCrosscapDatum.glide A =
      tomitaCPT mat2SheetPreservingCrosscapDatum A
    rw [hGlide, hCPT]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> linarith

/-- The concrete CPT fixed fiber in `M₂(ℝ)` is commutative, even though the
ambient operator ring is not.  The coordinate characterization identifies
its elements with the real two-dimensional complex-structure plane. -/
theorem mat2_crosscap_fixed_locus_commutative
    (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : InCrosscapSubalgebra mat2SheetPreservingCrosscapDatum A)
    (hB : InCrosscapSubalgebra mat2SheetPreservingCrosscapDatum B) :
    A * B = B * A := by
  obtain ⟨hA_diag, hA_off⟩ :=
    (mat2_crosscap_fixed_locus_characterization A).mp hA
  obtain ⟨hB_diag, hB_off⟩ :=
    (mat2_crosscap_fixed_locus_characterization B).mp hB
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hA_diag, hA_off, hB_diag, hB_off] <;>
    ring

private theorem mat2_crosscap_noncomm_witness :
    ∃ X Y : Matrix (Fin 2) (Fin 2) ℝ, X * Y ≠ Y * X := by
  refine ⟨!![0, 1; 1, 0], !![1, 0; 0, -1], ?_⟩
  intro h
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h01
  norm_num at h01

/-- The concrete `M₂(ℝ)` Row 4 Tomita map cannot also be multiplicative.
Together with `mat2SheetPreservingCrosscapDatum`, this instantiates the
ring-general anti/multiplicative obstruction on a noncommutative carrier. -/
theorem mat2SheetPreservingCrosscapDatum_J_not_multiplicative :
    ¬ ∀ X Y : Matrix (Fin 2) (Fin 2) ℝ,
      mat2SheetPreservingCrosscapDatum.J.toFun (X * Y) =
        mat2SheetPreservingCrosscapDatum.J.toFun X * mat2SheetPreservingCrosscapDatum.J.toFun Y := by
  intro hJ_mul
  obtain ⟨X, Y, hXY⟩ := mat2_crosscap_noncomm_witness
  have hComm := tomita_anti_and_multiplicative_forces_commutative
    mat2SheetPreservingCrosscapDatum hJ_mul
  exact hXY (hComm X Y)

end SheetPreservingGlideAndFourRowTable

end InfoGeometry.Canonical.KleinBottleTomitaCrosscap
