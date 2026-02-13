import Mathlib

section KreinClifford

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Doubled space `E ⊕ E` (geometric doubling of primal/dual sectors). -/
abbrev DoubledSpace (E : Type*) := E × E

/-- Swap involution `J(x, y) = (y, x)`. -/
def modularJ : DoubledSpace E →L[ℝ] DoubledSpace E where
  toLinearMap :=
    { toFun := fun v => (v.2, v.1)
      map_add' := by
        intro v w
        simp
      map_smul' := by
        intro a v
        simp }
  cont := by
    continuity

/-- Sign involution `ε(x, y) = (x, -y)`. -/
def spectralEpsilon : DoubledSpace E →L[ℝ] DoubledSpace E where
  toLinearMap :=
    { toFun := fun v => (v.1, -v.2)
      map_add' := by
        intro v w
        simp [add_comm]
      map_smul' := by
        intro a v
        simp [smul_neg] }
  cont := by
    continuity

/-- `I = J ∘ ε`, the canonical third generator. -/
def complexI : DoubledSpace E →L[ℝ] DoubledSpace E :=
  modularJ.comp spectralEpsilon

/-- Abstract `Cl(1,1)` relations for a pair of endomorphisms. -/
structure Cl11Algebra
    (J ε : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop where
  j_involution : J.comp J = ContinuousLinearMap.id ℝ (DoubledSpace E)
  eps_involution : ε.comp ε = ContinuousLinearMap.id ℝ (DoubledSpace E)
  anticommute : J.comp ε = -(ε.comp J)

lemma modularJ_involution :
    modularJ (E := E).comp (modularJ (E := E)) =
      ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  ext v <;> simp [modularJ]

lemma spectralEpsilon_involution :
    spectralEpsilon (E := E).comp (spectralEpsilon (E := E)) =
      ContinuousLinearMap.id ℝ (DoubledSpace E) := by
  ext v <;> simp [spectralEpsilon]

lemma modularJ_spectralEpsilon_anticommute :
    modularJ (E := E).comp (spectralEpsilon (E := E)) =
      -((spectralEpsilon (E := E)).comp (modularJ (E := E))) := by
  ext v <;> simp [modularJ, spectralEpsilon]

theorem modularJ_spectralEpsilon_isCl11 :
    Cl11Algebra (modularJ (E := E)) (spectralEpsilon (E := E)) := by
  refine ⟨modularJ_involution (E := E), spectralEpsilon_involution (E := E),
    modularJ_spectralEpsilon_anticommute (E := E)⟩

end KreinClifford
