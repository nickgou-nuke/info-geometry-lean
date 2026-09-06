import InfoGeometry.Lie.SplitOctonionAxialCartanFlow

/-!
# Native one-parameter subgroup readout for the traceless Cartan flow

The concrete traceless Cartan family already lives in the native subgroup of
real-linear Zorn multiplication automorphisms.  This file records its group
law as a Mathlib `MonoidHom` from the additive real parameter, represented by
`Multiplicative ℝ`.  It does not identify the full subgroup with a named Lie
group.
-/

noncomputable section

namespace InfoGeometry.Lie.SplitOctonionAxialCartanMonoidHom

open InfoGeometry.Algebra.Zorn.KingdonCanonicalBridge
open InfoGeometry.Lie.SplitOctonionAxialCartanFlow

abbrev CZAut := realZornCompositionAut

def axialCartanCompositionAutHom (k : Fin 3 → ℝ)
    (hk : ∑ i, k i = 0) : Multiplicative ℝ →* CZAut where
  toFun t := axialCartanCompositionAut k hk t
  map_one' := by
    exact axialCartanCompositionAut_zero k hk
  map_mul' s t := by
    exact axialCartanCompositionAut_add k hk s t

@[simp] theorem axialCartanCompositionAutHom_apply
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (t : Multiplicative ℝ) :
    axialCartanCompositionAutHom k hk t =
      axialCartanCompositionAut k hk t :=
  rfl

theorem axialCartanCompositionAutHom_map_mul
    (k : Fin 3 → ℝ) (hk : ∑ i, k i = 0) (s t : Multiplicative ℝ) :
    axialCartanCompositionAutHom k hk (s * t) =
      axialCartanCompositionAutHom k hk s *
        axialCartanCompositionAutHom k hk t := by
  exact map_mul (axialCartanCompositionAutHom k hk) s t

end InfoGeometry.Lie.SplitOctonionAxialCartanMonoidHom
