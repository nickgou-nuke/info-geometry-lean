import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.Basic
import InfoGeometry.Cartan.Involution

namespace InfoGeometry.Krein

open scoped BigOperators

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Doubled space `E ⊕ E` (geometric doubling of primal/dual sectors). -/
abbrev DoubledSpace (E : Type _) := E × E

/-- Swap involution `J(x, y) = (y, x)`. -/
def modularJ : DoubledSpace E →L[ℝ] DoubledSpace E :=
  (ContinuousLinearMap.snd ℝ E E).prod (ContinuousLinearMap.fst ℝ E E)

/-- Sign involution `ε(x, y) = (x, -y)`. -/
def spectralEpsilon : DoubledSpace E →L[ℝ] DoubledSpace E :=
  (ContinuousLinearMap.fst ℝ E E).prod (-(ContinuousLinearMap.snd ℝ E E))

/-- `I = J ∘ ε`, the canonical third generator. -/
def complexI : DoubledSpace E →L[ℝ] DoubledSpace E :=
  modularJ.comp spectralEpsilon

structure Cl11Relations
    (J ε : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop where
  j_involution : J.comp J = ContinuousLinearMap.id ℝ (DoubledSpace E)
  eps_involution : ε.comp ε = ContinuousLinearMap.id ℝ (DoubledSpace E)
  anticommute : J.comp ε = -(ε.comp J)

abbrev Cl11Algebra
    (J ε : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  Cl11Relations J ε

@[simp] lemma modularJ_apply (v : DoubledSpace E) :
    modularJ (E := E) v = (v.2, v.1) := by
  rcases v with ⟨x, y⟩
  simp [modularJ, ContinuousLinearMap.prod_apply]

@[simp] lemma spectralEpsilon_apply (v : DoubledSpace E) :
    spectralEpsilon (E := E) v = (v.1, -v.2) := by
  rcases v with ⟨x, y⟩
  simp [spectralEpsilon, ContinuousLinearMap.prod_apply]

@[simp] lemma complexI_apply (v : DoubledSpace E) :
    complexI (E := E) v = (-v.2, v.1) := by
  rcases v with ⟨x, y⟩
  simp [complexI, modularJ, spectralEpsilon, ContinuousLinearMap.prod_apply]

lemma modularJ_involution :
    modularJ (E := E).comp (modularJ (E := E)) =
      ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  apply ContinuousLinearMap.ext; intro v; rcases v with ⟨x, y⟩
  simp [modularJ, ContinuousLinearMap.prod_apply]

lemma spectralEpsilon_involution :
    spectralEpsilon (E := E).comp (spectralEpsilon (E := E)) =
      ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  apply ContinuousLinearMap.ext; intro v; rcases v with ⟨x, y⟩
  simp [spectralEpsilon, ContinuousLinearMap.prod_apply]

lemma modularJ_spectralEpsilon_anticommute :
    modularJ (E := E).comp (spectralEpsilon (E := E)) =
      -((spectralEpsilon (E := E)).comp (modularJ (E := E))) := by
  apply ContinuousLinearMap.ext; intro v; rcases v with ⟨x, y⟩
  simp [modularJ, spectralEpsilon, ContinuousLinearMap.prod_apply]

/-- The canonical generator `I = J ∘ ε` squares to `-id`. -/
lemma complexI_sq :
    (complexI (E := E)).comp (complexI (E := E))
      = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  apply ContinuousLinearMap.ext; intro v; rcases v with ⟨x, y⟩
  simp [complexI, modularJ, spectralEpsilon, ContinuousLinearMap.prod_apply]

theorem modularJ_spectralEpsilon_hasCl11Relations :
    Cl11Relations (modularJ (E := E)) (spectralEpsilon (E := E)) := by
  refine ⟨modularJ_involution (E := E), spectralEpsilon_involution (E := E),
    modularJ_spectralEpsilon_anticommute (E := E)⟩

theorem modularJ_spectralEpsilon_isCl11 :
    Cl11Algebra (modularJ (E := E)) (spectralEpsilon (E := E)) :=
  modularJ_spectralEpsilon_hasCl11Relations (E := E)

/-!
Lift to Cartan API: register `modularJ` as a Cartan involution on the doubled space.
-/
noncomputable instance instCartanInvolutionDoubled :
    Cartan.CartanInvolution (DoubledSpace E) where
  θ := (modularJ (E := E)).toLinearMap
  invol := by
    apply LinearMap.ext
    intro v
    rcases v with ⟨x, y⟩
    simp [modularJ, ContinuousLinearMap.prod_apply]

end InfoGeometry.Krein
