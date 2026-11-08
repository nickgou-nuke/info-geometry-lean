import InfoGeometry.Projective.HadjiivanovFiniteLaurentModeTower
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Projective.HadjiivanovLogConnectionKleinBridge

/-!
# Klein inversion on finite symmetric Laurent windows

Reflection of the coordinate window realizes Laurent-degree reversal
`m ↦ -m`.  It is involutive, compatible with the zero-boundary bonding maps,
and anti-intertwines the finite logarithmic connection after simultaneous
residue reversal.

This is a finite algebraic Klein symmetry, not a CPT or analytic theorem.
-/

namespace InfoGeometry.Projective.HadjiivanovFiniteLaurentModeKleinInversion

open HadjiivanovLogConnectionBridge
open HadjiivanovLogConnectionKleinBridge
open HadjiivanovFiniteLaurentModeTower

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Reflection of a coordinate in the symmetric Laurent window. -/
def mirrorIndex (n : ℕ) (i : Fin (2 * n + 1)) : Fin (2 * n + 1) :=
  ⟨2 * n - i.1, by omega⟩

@[simp] theorem mirrorIndex_involutive
    (n : ℕ) (i : Fin (2 * n + 1)) :
    mirrorIndex n (mirrorIndex n i) = i := by
  apply Fin.ext
  simp [mirrorIndex]
  omega

theorem modeDegree_mirrorIndex
    (n : ℕ) (i : Fin (2 * n + 1)) :
    modeDegree n (mirrorIndex n i) = -modeDegree n i := by
  simp [modeDegree, mirrorIndex]
  omega

/-- Coordinate reflection implementing finite Laurent inversion. -/
def finiteModeInversion (n : ℕ) :
    FiniteModeSection n V →ₗ[ℂ] FiniteModeSection n V where
  toFun x i := x (mirrorIndex n i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem finiteModeInversion_apply
    (n : ℕ) (x : FiniteModeSection n V) (i : Fin (2 * n + 1)) :
    finiteModeInversion n x i = x (mirrorIndex n i) := rfl

theorem finiteModeInversion_involutive (n : ℕ) :
    (finiteModeInversion (V := V) n).comp (finiteModeInversion n) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext i
  change x (mirrorIndex n (mirrorIndex n i)) = x i
  rw [mirrorIndex_involutive]

/-- Finite inversion respects the successor embeddings of symmetric windows. -/
theorem finiteModeInversion_modeBond (n : ℕ) :
    (finiteModeInversion (V := V) (n + 1)).comp (modeBond n) =
      (modeBond n).comp (finiteModeInversion n) := by
  apply LinearMap.ext
  intro x
  funext i
  by_cases h : IsInterior n i
  · have hm : IsInterior n (mirrorIndex (n + 1) i) := by
      simp only [IsInterior, mirrorIndex]
      rcases h with ⟨h0, h1⟩
      omega
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      finiteModeInversion_apply,
      modeBond_apply_interior n x (mirrorIndex (n + 1) i) hm,
      modeBond_apply_interior n (finiteModeInversion n x) i h,
      finiteModeInversion_apply]
    congr 1
    apply Fin.ext
    simp [mirrorIndex]
    rcases h with ⟨h0, h1⟩
    omega
  · have hm : ¬IsInterior n (mirrorIndex (n + 1) i) := by
      intro hm
      apply h
      simp only [IsInterior, mirrorIndex] at hm ⊢
      omega
    rw [LinearMap.comp_apply, LinearMap.comp_apply,
      finiteModeInversion_apply,
      modeBond_apply_boundary n x (mirrorIndex (n + 1) i) hm,
      modeBond_apply_boundary n (finiteModeInversion n x) i h]

/-- Finite cochain identity `∇[-H] ι = -ι ∇[H]`. -/
theorem finiteModeConnection_reverse
    (R : LogResidue V) (n : ℕ) :
    (finiteModeConnection (reverseResidue R) n).comp
        (finiteModeInversion n) =
      (-finiteModeInversion n).comp (finiteModeConnection R n) := by
  apply LinearMap.ext
  intro x
  funext i
  change finiteModeConnection (reverseResidue R) n
      (finiteModeInversion n x) i =
    -finiteModeConnection R n x (mirrorIndex n i)
  rw [finiteModeConnection_apply, finiteModeInversion_apply,
    finiteModeConnection_apply]
  rw [residueOperator_reverse, LinearMap.neg_apply,
    modeDegree_mirrorIndex]
  simp only [Int.cast_neg, neg_smul]
  abel

end

end InfoGeometry.Projective.HadjiivanovFiniteLaurentModeKleinInversion
