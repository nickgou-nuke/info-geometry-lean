import Mathlib
import InfoGeometry.Algebra.ChiralOperatorSageTranslation

/-!
# Topological readout for the chiral operator carrier

The noncommutative Zorn carrier deliberately has no additive or topological
structure.  This owner therefore uses the native finite product carrier for
the four operator-valued coordinates and supplies only the continuous
coordinate maps and the translation to `NCZornElement`.

No norm, completion, C*-structure, or continuity of Zorn multiplication is
asserted here.
-/

namespace InfoGeometry.Algebra

open InfoGeometry.Physics.NCG

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The topological carrier for `(n₊, n₋, s₊, s₋)`. -/
abbrev OperatorSageTopologicalCarrier A :=
  A × A × (Fin 3 → A) × (Fin 3 → A)

/-- Forget the product presentation and recover the existing Zorn record. -/
def operatorSageTopologicalToZorn
    (X : OperatorSageTopologicalCarrier A) : OperatorSageCarrier A :=
  { n_plus := X.1
    n_minus := X.2.1
    sigma_plus := X.2.2.1
    sigma_minus := X.2.2.2 }

/-- The inverse product presentation of the existing Zorn record. -/
def operatorSageZornToTopological
    (X : OperatorSageCarrier A) : OperatorSageTopologicalCarrier A :=
  (X.n_plus, X.n_minus, X.sigma_plus, X.sigma_minus)

@[simp] theorem operatorSageTopologicalToZorn_toTopological
    (X : OperatorSageCarrier A) :
    operatorSageTopologicalToZorn (operatorSageZornToTopological X) = X := by
  cases X
  rfl

@[simp] theorem operatorSageZornToTopological_toZorn
    (X : OperatorSageTopologicalCarrier A) :
    operatorSageZornToTopological (operatorSageTopologicalToZorn X) = X := by
  rcases X with ⟨nPlus, nMinus, sigmaPlus, sigmaMinus⟩
  rfl

/-! ### Continuous coordinate readouts -/

@[continuity, fun_prop]
theorem continuous_operatorSage_nPlus :
    Continuous (fun X : OperatorSageTopologicalCarrier A => X.1) :=
  continuous_fst

@[continuity, fun_prop]
theorem continuous_operatorSage_nMinus :
    Continuous (fun X : OperatorSageTopologicalCarrier A => X.2.1) :=
  continuous_fst.comp continuous_snd

@[continuity, fun_prop]
theorem continuous_operatorSage_sigmaPlus :
    Continuous (fun X : OperatorSageTopologicalCarrier A => X.2.2.1) :=
  continuous_fst.comp (continuous_snd.comp continuous_snd)

@[continuity, fun_prop]
theorem continuous_operatorSage_sigmaMinus :
    Continuous (fun X : OperatorSageTopologicalCarrier A => X.2.2.2) :=
  continuous_snd.comp (continuous_snd.comp continuous_snd)

/-! ### Sage generators in the topological presentation -/

def topologicalOperatorSageGenerator
    (c : Fin 8) : OperatorSageTopologicalCarrier A :=
  operatorSageZornToTopological (operatorSageGenerator c)

@[simp] theorem topologicalOperatorSageGenerator_toZorn
    (c : Fin 8) :
    operatorSageTopologicalToZorn (topologicalOperatorSageGenerator (A := A) c) =
      operatorSageGenerator c := by
  simp [topologicalOperatorSageGenerator]

theorem continuous_topologicalOperatorSageGenerator
    (c : Fin 8) :
    Continuous (fun _ : Unit => topologicalOperatorSageGenerator (A := A) c) :=
  continuous_const

theorem topologicalOperatorSageGenerator_table :
    (topologicalOperatorSageGenerator (A := A) 0,
      topologicalOperatorSageGenerator (A := A) 1,
      topologicalOperatorSageGenerator (A := A) 2,
      topologicalOperatorSageGenerator (A := A) 3,
      topologicalOperatorSageGenerator (A := A) 4,
      topologicalOperatorSageGenerator (A := A) 5,
      topologicalOperatorSageGenerator (A := A) 6,
      topologicalOperatorSageGenerator (A := A) 7) =
    (operatorSageZornToTopological (operatorSageGenerator (A := A) 0),
      operatorSageZornToTopological (operatorSageGenerator (A := A) 1),
      operatorSageZornToTopological (operatorSageGenerator (A := A) 2),
      operatorSageZornToTopological (operatorSageGenerator (A := A) 3),
      operatorSageZornToTopological (operatorSageGenerator (A := A) 4),
      operatorSageZornToTopological (operatorSageGenerator (A := A) 5),
      operatorSageZornToTopological (operatorSageGenerator (A := A) 6),
      operatorSageZornToTopological (operatorSageGenerator (A := A) 7)) := by
  rfl

end InfoGeometry.Algebra
