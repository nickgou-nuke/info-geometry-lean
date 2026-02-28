import Mathlib.Analysis.Normed.Module.Basic
import InfoGeometry.Cartan.Involution

namespace InfoGeometry.Krein

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Doubled space `E ⊕ E` (geometric doubling of primal/dual sectors). -/
abbrev DoubledSpace (E : Type _) := E × E

/-- Swap involution `J(x, y) = (y, x)`. -/
def modularJ : DoubledSpace E →L[ℝ] DoubledSpace E where
  toLinearMap :=
    { toFun := fun v => (v.2, v.1)
      map_add' := by intro v w; simp
      map_smul' := by intro a v; simp }
  cont := by continuity

/-- Sign involution `ε(x, y) = (x, -y)`. -/
def spectralEpsilon : DoubledSpace E →L[ℝ] DoubledSpace E where
  toLinearMap :=
    { toFun := fun v => (v.1, -v.2)
      map_add' := by intro v w; simp
      map_smul' := by intro a v; simp [smul_neg] }
  cont := by continuity

/-- `I = J ∘ ε`, the canonical third generator. -/
def complexI : DoubledSpace E →L[ℝ] DoubledSpace E :=
  modularJ.comp spectralEpsilon

structure Cl11Relations
    (J ε : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop where
  j_involution : J * J = 1
  eps_involution : ε * ε = 1
  anticommute : J * ε = -(ε * J)

abbrev Cl11Algebra
    (J ε : DoubledSpace E →L[ℝ] DoubledSpace E) : Prop :=
  Cl11Relations (E := E) J ε

@[simp] lemma modularJ_apply (v : DoubledSpace E) :
    modularJ (E := E) v = (v.2, v.1) := rfl

@[simp] lemma spectralEpsilon_apply (v : DoubledSpace E) :
    spectralEpsilon (E := E) v = (v.1, -v.2) := rfl

@[simp] lemma complexI_apply (v : DoubledSpace E) :
    complexI (E := E) v = (-v.2, v.1) := by
  simp [complexI, modularJ, spectralEpsilon]

lemma modularJ_involution :
    (modularJ (E := E)) * (modularJ (E := E)) = (1 : DoubledSpace E →L[ℝ] DoubledSpace E) := by
  ext v <;> simp [modularJ]

lemma spectralEpsilon_involution :
    (spectralEpsilon (E := E)) * (spectralEpsilon (E := E)) = (1 : DoubledSpace E →L[ℝ] DoubledSpace E) := by
  ext v <;> simp [spectralEpsilon]

lemma modularJ_spectralEpsilon_anticommute :
    (modularJ (E := E)) * (spectralEpsilon (E := E))
      = -((spectralEpsilon (E := E)) * (modularJ (E := E))) := by
  ext v <;> simp [modularJ, spectralEpsilon]

lemma complexI_sq :
    (complexI (E := E)) * (complexI (E := E))
      = -(1 : DoubledSpace E →L[ℝ] DoubledSpace E) := by
  ext v <;> simp [complexI, modularJ, spectralEpsilon]

theorem modularJ_spectralEpsilon_hasCl11Relations :
    Cl11Relations (E := E) (modularJ (E := E)) (spectralEpsilon (E := E)) := by
  refine ⟨modularJ_involution (E := E), spectralEpsilon_involution (E := E),
    ?_⟩
  simpa using modularJ_spectralEpsilon_anticommute (E := E)

theorem modularJ_spectralEpsilon_isCl11 :
    Cl11Algebra (E := E) (modularJ (E := E)) (spectralEpsilon (E := E)) :=
  modularJ_spectralEpsilon_hasCl11Relations (E := E)

/--
LIFT TO CARTAN API:
Register `modularJ` as a Cartan involution on the doubled space (vector-level).
-/
noncomputable instance instCartanInvolutionDoubled :
    InfoGeometry.Cartan.CartanInvolution (DoubledSpace E) where
  θ := (modularJ (E := E)).toLinearMap
  invol := by
    intro v
    rcases v with ⟨x, y⟩
    simp [modularJ]

end InfoGeometry.Krein
