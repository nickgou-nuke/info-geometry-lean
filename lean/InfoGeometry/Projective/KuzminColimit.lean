import InfoGeometry.Canonical.KuzminColimit
import InfoGeometry.Projective.KuzminInductiveLimitBridge

/-!
# Projective Kuzmin Colimit

Thin projective-facing re-export of the canonical Kuzmin colimit interface.

This file does not add a new theorem layer. It keeps the projective import
surface stable while delegating all colimit transport to the canonical owner
file in `InfoGeometry.Canonical.KuzminColimit`.
-/

namespace KuzminColimit

open InfoGeometry.Canonical.KuzminColimit
open InfoGeometry.Projective.KuzminInductiveLimitBridge

/-- Projective alias for the conservative Kuzmin inductive-limit input data. -/
abbrev KuzminLimitInput
    (R AInf : Type*) [CommRing R] [StarRing R] [CommRing AInf] :=
  KuzminInductiveLimitData (R := R) (AInf := AInf)

/-- The `q = 0` finite-stage readout, re-exported on the projective surface. -/
theorem qccr_n2_gram_positive_stage
    (q : ℝ) (hq : |q| < 1) (x : Fin 4 → ℝ) (hx : x ≠ 0) :
    0 < x ⬝ᵥ ((InfoGeometry.Algebra.QCCR.Proved.gram_matrix_k2_n2 q).mulVec x) :=
  InfoGeometry.Canonical.KuzminColimit.qccr_n2_gram_positive_stage q hq x hx

/-- The finite `q = 0` Cuntz--Toeplitz readout, re-exported on the projective surface. -/
theorem finite_cuntz_toeplitz_q_zero_readout
    {R : Type*} [CommRing R] [StarRing R]
    (a astar : Fin 2 → R) (hstar : ∀ i, star (a i) = astar i)
    (hrel : ∀ i j, astar i * a j = (if i = j then 1 else 0) + (0 : R) * (a j * astar i))
    (i j : Fin 2) :
    astar i * a j = (if i = j then 1 else 0) :=
  InfoGeometry.Canonical.KuzminColimit.finite_cuntz_toeplitz_q_zero_readout
    (a := a) (astar := astar) (hstar := hstar) (hrel := hrel) i j

/-- Projective re-export of the finite q-CCR relation readout into an explicit colimit. -/
theorem qCCR_relation_survives_colimit
    (T : InfoGeometry.Canonical.InductiveColimitBridge.CompatibleFiniteEquivalenceTower)
    (qCCRRel : ∀ n : ℕ, T.Left.Stage n → Prop)
    (qCCRLimitRel : T.Left.Limit → Prop)
    (qCCRLimitReadout : T.Left.LimitReadout qCCRRel qCCRLimitRel)
    (n : ℕ) (x : T.Left.Stage n) (hx : qCCRRel n x) :
    qCCRLimitRel (T.Left.toLimit n x) :=
  InfoGeometry.Canonical.KuzminColimit.qCCR_relation_survives_colimit
    T qCCRRel qCCRLimitRel qCCRLimitReadout n x hx

/-- Projective re-export of the finite Cuntz--Toeplitz relation readout into an explicit colimit. -/
theorem toeplitz_relation_survives_colimit
    (T : InfoGeometry.Canonical.InductiveColimitBridge.CompatibleFiniteEquivalenceTower)
    (toeplitzRel : ∀ n : ℕ, T.Right.Stage n → Prop)
    (toeplitzLimitRel : T.Right.Limit → Prop)
    (toeplitzLimitReadout : T.Right.LimitReadout toeplitzRel toeplitzLimitRel)
    (n : ℕ) (y : T.Right.Stage n) (hy : toeplitzRel n y) :
    toeplitzLimitRel (T.Right.toLimit n y) :=
  InfoGeometry.Canonical.KuzminColimit.toeplitz_relation_survives_colimit
    T toeplitzRel toeplitzLimitRel toeplitzLimitReadout n y hy

end KuzminColimit
