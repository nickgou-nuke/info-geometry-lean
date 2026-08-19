import InfoGeometry.Canonical.TomitaTakesaki
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-!
# InfoGeometry.Canonical.RealBdG

Real Majorana/BdG operator core over doubled space using the canonical modular
complex structure

`K := J ∘ ε`.

No separate scalar `Complex.I` is used at operator level: complex action is
implemented as a derived real action through `K`.
-/

namespace InfoGeometry.Canonical.RealBdG

open InfoGeometry.Krein
open InfoGeometry.Canonical.TomitaTakesaki

section Core

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Endomorphisms on doubled space. -/
abbrev EndH := DoubledSpace E →L[ℝ] DoubledSpace E

/-- Canonical real complex-structure operator `K := J ∘ ε`. -/
noncomputable def modularK : EndH (E := E) :=
  (modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E))

@[simp] lemma modularK_def :
    modularK (E := E)
      = (modularConjugationJ (E := E)).comp (modularSignEpsilon (E := E)) := rfl

/-- `K` agrees with the legacy `Jε` axis. -/
lemma modularK_eq_modularComplexI :
    modularK (E := E) = modularComplexI (E := E) := by
  unfold modularK modularComplexI modularConjugationJ modularSignEpsilon
  rfl

@[simp] lemma modularK_eq_modular_j_comp_spectral_epsilon :
    modularK (E := E) = (modular_j (E := E)).comp (spectral_epsilon (E := E)) := by
  rfl

@[simp] lemma modularK_eq_complex_i :
    modularK (E := E) = complex_i (E := E) := by
  unfold modularK modularConjugationJ modularSignEpsilon
  rfl

/-- Core identity: `K² = -Id`. -/
@[simp] lemma modularK_sq :
    (modularK (E := E)).comp (modularK (E := E))
      = -(ContinuousLinearMap.id ℝ (DoubledSpace E)) := by
  change (complex_i (E := E)).comp (complex_i (E := E))
      = -(ContinuousLinearMap.id ℝ (DoubledSpace E))
  exact complex_i_sq (E := E)

@[simp] lemma modularK_apply_modularK (v : DoubledSpace E) :
    modularK (E := E) (modularK (E := E) v) = -v := by
  have h := congrArg (fun f : EndH (E := E) => f v) (modularK_sq (E := E))
  calc
    modularK (E := E) (modularK (E := E) v)
        = (-(ContinuousLinearMap.id ℝ (DoubledSpace E))) v := h
    _ = -v := by simp

/-- `K`-linear operators commute with `K`. -/
def KLinear (A : EndH (E := E)) : Prop :=
  A.comp (modularK (E := E)) = (modularK (E := E)).comp A

/-- `K`-antilinear operators anticommute with `K`. -/
def KAntilinear (A : EndH (E := E)) : Prop :=
  A.comp (modularK (E := E)) = -((modularK (E := E)).comp A)

/-- Conjugation by `K`: `A ↦ K A K`. -/
noncomputable def KConjugate (A : EndH (E := E)) : EndH (E := E) :=
  (modularK (E := E)).comp (A.comp (modularK (E := E)))

@[simp] lemma KConjugate_KConjugate (A : EndH (E := E)) :
    KConjugate (E := E) (KConjugate (E := E) A) = A := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [KConjugate, ContinuousLinearMap.comp_apply]
  rw [modularK_apply_modularK]
  rw [modularK_apply_modularK v]
  simp [modularK_apply_modularK]

@[simp] lemma KConjugate_add (A B : EndH (E := E)) :
    KConjugate (E := E) (A + B) =
      KConjugate (E := E) A + KConjugate (E := E) B := by
  apply ContinuousLinearMap.ext
  intro v
  apply DoubledSpace.ext <;>
    simp [KConjugate, ContinuousLinearMap.comp_apply]

@[simp] lemma KConjugate_sub (A B : EndH (E := E)) :
    KConjugate (E := E) (A - B) =
      KConjugate (E := E) A - KConjugate (E := E) B := by
  apply ContinuousLinearMap.ext
  intro v
  apply DoubledSpace.ext <;>
    simp [KConjugate, ContinuousLinearMap.comp_apply]

@[simp] lemma KConjugate_smul (c : ℝ) (A : EndH (E := E)) :
    KConjugate (E := E) (c • A) = c • KConjugate (E := E) A := by
  apply ContinuousLinearMap.ext
  intro v
  apply DoubledSpace.ext <;>
    simp [KConjugate, ContinuousLinearMap.comp_apply]

/-- `K`-linear part of an operator. -/
noncomputable def KLinearPart (A : EndH (E := E)) : EndH (E := E) :=
  (1 / 2 : ℝ) • (A - KConjugate (E := E) A)

/-- `K`-antilinear part of an operator. -/
noncomputable def KAntilinearPart (A : EndH (E := E)) : EndH (E := E) :=
  (1 / 2 : ℝ) • (A + KConjugate (E := E) A)

@[simp] theorem KLinearPart_idempotent (A : EndH (E := E)) :
    KLinearPart (E := E) (KLinearPart (E := E) A) =
      KLinearPart (E := E) A := by
  unfold KLinearPart
  rw [KConjugate_smul, KConjugate_sub, KConjugate_KConjugate]
  module

@[simp] theorem KAntilinearPart_idempotent (A : EndH (E := E)) :
    KAntilinearPart (E := E) (KAntilinearPart (E := E) A) =
      KAntilinearPart (E := E) A := by
  unfold KAntilinearPart
  rw [KConjugate_smul, KConjugate_add, KConjugate_KConjugate]
  module

@[simp] theorem KLinearPart_KAntilinearPart (A : EndH (E := E)) :
    KLinearPart (E := E) (KAntilinearPart (E := E) A) = 0 := by
  unfold KLinearPart KAntilinearPart
  rw [KConjugate_smul, KConjugate_add, KConjugate_KConjugate]
  module

@[simp] theorem KAntilinearPart_KLinearPart (A : EndH (E := E)) :
    KAntilinearPart (E := E) (KLinearPart (E := E) A) = 0 := by
  unfold KAntilinearPart KLinearPart
  rw [KConjugate_smul, KConjugate_sub, KConjugate_KConjugate]
  module

lemma KLinearPart_add_KAntilinearPart (A : EndH (E := E)) :
    KLinearPart (E := E) A + KAntilinearPart (E := E) A = A := by
  unfold KLinearPart KAntilinearPart
  calc
    (1 / 2 : ℝ) • (A - KConjugate (E := E) A) +
        (1 / 2 : ℝ) • (A + KConjugate (E := E) A)
      = ((1 / 2 : ℝ) • A - (1 / 2 : ℝ) • KConjugate (E := E) A) +
          ((1 / 2 : ℝ) • A + (1 / 2 : ℝ) • KConjugate (E := E) A) := by
          simp [smul_sub, smul_add]
    _ = (1 / 2 : ℝ) • A + (1 / 2 : ℝ) • A := by
          abel
    _ = (2 : ℝ) • ((1 / 2 : ℝ) • A) := by
          simpa [two_smul] using (two_smul ℝ ((1 / 2 : ℝ) • A)).symm
    _ = ((2 : ℝ) * (1 / 2 : ℝ)) • A := by
          simp [smul_smul]
    _ = A := by
          have htwo : ((2 : ℝ) * (1 / 2 : ℝ)) = 1 := by norm_num
          simp [htwo]

/-- Right-composition of `K`-conjugation with `K`. -/
lemma KConjugate_comp_modularK (A : EndH (E := E)) :
    (KConjugate (E := E) A).comp (modularK (E := E))
      = -((modularK (E := E)).comp A) := by
  calc
    (KConjugate (E := E) A).comp (modularK (E := E))
        = (modularK (E := E)).comp ((A.comp (modularK (E := E))).comp (modularK (E := E))) := by
            simp [KConjugate, ContinuousLinearMap.comp_assoc]
    _ = (modularK (E := E)).comp (A.comp ((modularK (E := E)).comp (modularK (E := E)))) := by
          simp [ContinuousLinearMap.comp_assoc]
    _ = (modularK (E := E)).comp (A.comp (-(ContinuousLinearMap.id ℝ (DoubledSpace E)))) := by
          rw [modularK_sq (E := E)]
    _ = -((modularK (E := E)).comp (A.comp (ContinuousLinearMap.id ℝ (DoubledSpace E)))) := by
          simp
    _ = -((modularK (E := E)).comp A) := by
          simp

/-- Left-composition of `K` with `K`-conjugation. -/
lemma modularK_comp_KConjugate (A : EndH (E := E)) :
    (modularK (E := E)).comp (KConjugate (E := E) A)
      = -(A.comp (modularK (E := E))) := by
  calc
    (modularK (E := E)).comp (KConjugate (E := E) A)
        = ((modularK (E := E)).comp (modularK (E := E))).comp (A.comp (modularK (E := E))) := by
            simp [KConjugate, ContinuousLinearMap.comp_assoc]
    _ = (-(ContinuousLinearMap.id ℝ (DoubledSpace E))).comp (A.comp (modularK (E := E))) := by
          rw [modularK_sq (E := E)]
    _ = -(A.comp (modularK (E := E))) := by
          simp

/-- The `K`-linear split component commutes with `K`. -/
theorem kSplit_linear (A : EndH (E := E)) :
    KLinear (E := E) (KLinearPart (E := E) A) := by
  unfold KLinear KLinearPart
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  congr 1
  calc
    (A - KConjugate (E := E) A).comp (modularK (E := E))
        = A.comp (modularK (E := E)) - (KConjugate (E := E) A).comp (modularK (E := E)) := by
            simp [ContinuousLinearMap.sub_comp]
    _ = A.comp (modularK (E := E)) + (modularK (E := E)).comp A := by
          rw [KConjugate_comp_modularK (E := E) A]
          abel
    _ = (modularK (E := E)).comp A + A.comp (modularK (E := E)) := by
          abel
    _ = (modularK (E := E)).comp A - (modularK (E := E)).comp (KConjugate (E := E) A) := by
          rw [modularK_comp_KConjugate (E := E) A]
          abel
    _ = (modularK (E := E)).comp (A - KConjugate (E := E) A) := by
          simp [ContinuousLinearMap.comp_sub]

/-- The `K`-antilinear split component anticommutes with `K`. -/
theorem kSplit_antilinear (A : EndH (E := E)) :
    KAntilinear (E := E) (KAntilinearPart (E := E) A) := by
  unfold KAntilinear KAntilinearPart
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  have hCore :
      (A + KConjugate (E := E) A).comp (modularK (E := E))
        = -((modularK (E := E)).comp (A + KConjugate (E := E) A)) := by
    calc
      (A + KConjugate (E := E) A).comp (modularK (E := E))
          = A.comp (modularK (E := E)) + (KConjugate (E := E) A).comp (modularK (E := E)) := by
              simp [ContinuousLinearMap.add_comp]
      _ = A.comp (modularK (E := E)) - (modularK (E := E)).comp A := by
            rw [KConjugate_comp_modularK (E := E) A]
            abel
      _ = -((modularK (E := E)).comp A - A.comp (modularK (E := E))) := by
            abel
      _ = -((modularK (E := E)).comp A + (modularK (E := E)).comp (KConjugate (E := E) A)) := by
            rw [modularK_comp_KConjugate (E := E) A]
            abel
      _ = -((modularK (E := E)).comp (A + KConjugate (E := E) A)) := by
            simp [ContinuousLinearMap.comp_add]
  calc
    (1 / 2 : ℝ) • ((A + KConjugate (E := E) A).comp (modularK (E := E)))
        = (1 / 2 : ℝ) • (-((modularK (E := E)).comp (A + KConjugate (E := E) A))) := by
            exact congrArg (fun T => (1 / 2 : ℝ) • T) hCore
    _ = -((1 / 2 : ℝ) • ((modularK (E := E)).comp (A + KConjugate (E := E) A))) := by
          simp

/--
Real BdG datum with internal complex axis `K = J ∘ ε` and symmetry package.
-/
structure RealBdGDatum where
  H : EndH (E := E)
  particleHole : EndH (E := E)
  timeReversal : EndH (E := E)
  chiral : EndH (E := E) := modularConjugationJ (E := E)

  H_KLinear : KLinear (E := E) H
  H_chiral : chiral.comp H = -(H.comp chiral)

  PH_sq : particleHole.comp particleHole = ContinuousLinearMap.id ℝ (DoubledSpace E)
  TR_sq : timeReversal.comp timeReversal = -(ContinuousLinearMap.id ℝ (DoubledSpace E))

  PH_KAnti : KAntilinear (E := E) particleHole
  TR_KAnti : KAntilinear (E := E) timeReversal

/--
Derived real action of complex scalars through `K`.
`(a + bI) • v := a•v + b•K(v)`.
-/
noncomputable def complexAction (z : ℂ) (v : DoubledSpace E) : DoubledSpace E :=
  z.re • v + z.im • (modularK (E := E) v)

/-- In the derived real action, `Complex.I` acts exactly as `K`. -/
lemma complexI_action_eq_modularK (v : DoubledSpace E) :
    complexAction (E := E) Complex.I v = modularK (E := E) v := by
  simp [complexAction]

end Core

end InfoGeometry.Canonical.RealBdG
