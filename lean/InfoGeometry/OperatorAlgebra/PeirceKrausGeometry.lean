/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.PeirceTraceGeometry
import InfoGeometry.Quantum.KrausAmplificationCP

/-!
# Peirce pinching as an existing Kraus channel

The two Kraus coefficients are `p` and `1-p`. The channel is the existing
`Choi.krausMap`, and its amplification is the existing block amplification.
The map's range is the commutant of `p`, which need not be commutative.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra.PeirceKrausGeometry

open Matrix InfoGeometry.Core.IdempotentCartan InfoGeometry.Core.PeirceDecomposition
open InfoGeometry.OperatorAlgebra.PeirceTraceGeometry
open InfoGeometry.Quantum.Choi InfoGeometry.Quantum.KrausAmplification
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Trace preservation for an arbitrary finite complete Kraus family. The
coefficients need not commute with each other or with the input matrix. -/
theorem trace_krausMap_of_complete {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Matrix n n ℂ) (hV : (∑ i, star (V i) * V i) = 1)
    (A : Matrix n n ℂ) : trace (krausMap V A) = trace A := by
  change trace (∑ i, V i * A * star (V i)) = trace A
  rw [trace_sum]
  calc
    (∑ i, trace (V i * A * star (V i))) =
        ∑ i, trace ((star (V i) * V i) * A) := by
      apply Finset.sum_congr rfl
      intro i _
      exact trace_mul_cycle (V i) A (star (V i))
    _ = trace ((∑ i, star (V i) * V i) * A) := by rw [Finset.sum_mul, trace_sum]
    _ = trace A := by rw [hV, one_mul]

/-- The two coefficients of Peirce pinching, inside the full matrix algebra. -/
def peirceKraus (p : Matrix n n ℂ) : Fin 2 → Matrix n n ℂ := ![p, 1 - p]

/-- Literal equality of the pre-existing Kraus and Peirce operations. -/
theorem krausMap_peirceKraus {p : Matrix n n ℂ} (hp : IsSelfAdjoint p) :
    krausMap (peirceKraus p) = evenLinearMap p := by
  ext A i j
  simp [krausMap, peirceKraus, evenLinearMap, evenPart, component11, component00,
    complementIdempotent, Fin.sum_univ_two, hp.star_eq]

/-- The Kraus completeness relation is derived from native star-projection laws. -/
theorem peirceKraus_complete {p : Matrix n n ℂ} (hp : IsStarProjection p) :
    (∑ i, star (peirceKraus p i) * peirceKraus p i) = 1 := by
  simp [peirceKraus, Fin.sum_univ_two, hp.isSelfAdjoint.star_eq,
    hp.isIdempotentElem.eq, hp.one_sub.isIdempotentElem.eq]

/-- The channel is unital as well as trace preserving. -/
theorem evenLinearMap_one {p : Matrix n n ℂ} (hp : IsIdempotentElem p) :
    evenLinearMap p 1 = 1 :=
  even_eq_self_of_commute hp (by simp)

/-- Complete positivity: an arbitrary finite ancillary matrix size is allowed. -/
theorem amplification_evenLinearMap_posSemidef
    {r : Type*} [Fintype r] [DecidableEq r]
    {p : Matrix n n ℂ} (hp : IsStarProjection p)
    (X : Matrix (r × n) (r × n) ℂ) (hX : X.PosSemidef) :
    (amplification (r := r) (evenLinearMap p) X).PosSemidef := by
  rw [← krausMap_peirceKraus hp.isSelfAdjoint]
  exact amplification_krausChannel_posSemidef (peirceKraus p) X hX

/-- Both corners of a positive input remain positive under pinching. -/
theorem evenPart_posSemidef {p A : Matrix n n ℂ} (hp : IsStarProjection p)
    (hA : A.PosSemidef) : (evenPart p A).PosSemidef := by
  have hpstar : pᴴ = p := hp.isSelfAdjoint.star_eq
  have hqstar : (1 - p)ᴴ = 1 - p := hp.one_sub.isSelfAdjoint.star_eq
  simpa only [evenPart, component11, component00, complementIdempotent,
    hpstar, hqstar] using
    (hA.mul_mul_conjTranspose_same p).add (hA.mul_mul_conjTranspose_same (1 - p))

/-- The fixed matrices of pinching are exactly those commuting with `p`. -/
theorem evenPart_eq_self_iff_commute {p : Matrix n n ℂ}
    (hp : IsIdempotentElem p) (A : Matrix n n ℂ) :
    evenPart p A = A ↔ Commute p A := by
  constructor
  · intro h
    have ho : oddPart p A = 0 := by
      have hs := even_add_odd p A
      rw [h] at hs
      exact add_left_cancel (hs.trans (add_zero A).symm)
    exact (odd_zero_iff_commute hp A).mp ho
  · exact even_eq_self_of_commute hp

/-- The range of the linear map is characterized by the commutant equation. -/
theorem mem_range_evenLinearMap_iff {p : Matrix n n ℂ}
    (hp : IsIdempotentElem p) (A : Matrix n n ℂ) :
    A ∈ LinearMap.range (evenLinearMap p) ↔ Commute p A := by
  constructor
  · rintro ⟨B, rfl⟩
    exact (evenPart_eq_self_iff_commute hp _).mp (projection_laws hp B).1
  · intro h
    exact ⟨A, (evenPart_eq_self_iff_commute hp A).mpr h⟩

/-- The conditional-expectation bimodule identity, with explicit membership
conditions in the commutant and arbitrary middle operator. -/
theorem evenPart_bimodule {p : Matrix n n ℂ} (hp : IsIdempotentElem p)
    (A B C : Matrix n n ℂ) (hB : Commute p B) (hC : Commute p C) :
    evenPart p (B * A * C) = B * evenPart p A * C := by
  have hBe := even_eq_self_of_commute hp hB
  have hCe := even_eq_self_of_commute hp hC
  have hBo := (odd_zero_iff_commute hp B).mpr hB
  have hCo := (odd_zero_iff_commute hp C).mpr hC
  rw [(multiplication_rules hp (B * A) C).1,
    (multiplication_rules hp B A).1, hBe, hCe, hBo, hCo]
  simp

/-- Pinching covaries when both its projection and input are conjugated. -/
theorem conjStarAlgAut_evenPart (u : unitary (Matrix n n ℂ))
    (p A : Matrix n n ℂ) :
    Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u (evenPart p A) =
      evenPart (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u p)
        (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u A) := by
  simp only [evenPart, component11, component00, complementIdempotent,
    map_add, map_mul, map_sub, map_one]

/-- The same native conjugation transports the tangent/off-diagonal projection. -/
theorem conjStarAlgAut_oddPart (u : unitary (Matrix n n ℂ))
    (p A : Matrix n n ℂ) :
    Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u (oddPart p A) =
      oddPart (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u p)
        (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u A) := by
  simp only [oddPart, component10, component01, complementIdempotent,
    map_add, map_mul, map_sub, map_one]

/-- The projection parameter itself stays in the native star-projection carrier. -/
theorem isStarProjection_conjStarAlgAut (u : unitary (Matrix n n ℂ))
    {p : Matrix n n ℂ} (hp : IsStarProjection p) :
    IsStarProjection (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) u p) :=
  hp.map _

end InfoGeometry.OperatorAlgebra.PeirceKrausGeometry
