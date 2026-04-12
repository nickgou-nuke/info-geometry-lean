import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.DrazinExistenceBridge
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Canonical.DrazinInfiniteCore

Infinite-dimensional operator core for the canonical Drazin lane.

This file separates:
- algebraic owner predicate: `Drazin.IsDrazinInverse`,
- spectral/ascent-descent/Riesz interfaces (assumption surfaces),
- constructive finite-dimensional bridge into a Riesz-style package.
-/

namespace InfoGeometry.Canonical.DrazinInfiniteCore

open InfoGeometry.Canonical

section AscentDescent

variable {K V : Type*}
variable [DivisionRing K] [AddCommGroup V] [Module K V]

/-- Kernel stabilization at index `k` (ascent interface). -/
@[rep_depth operator]
def AscentAtZero (T : Module.End K V) (k : ℕ) : Prop :=
  (T ^ k).ker = (T ^ (k + 1)).ker

/-- Range stabilization at index `k` (descent interface). -/
@[rep_depth operator]
def DescentAtZero (T : Module.End K V) (k : ℕ) : Prop :=
  (T ^ k).range = (T ^ (k + 1)).range

/-- Finite ascent/descent witness at the spectral point `0`. -/
@[rep_depth operator]
structure HasFiniteAscentDescentAtZero (T : Module.End K V) where
  k : ℕ
  ascent : AscentAtZero T k
  descent : DescentAtZero T k
  D : Module.End K V
  hIsDrazin : Drazin.IsDrazinInverse T D k

variable {T TD : Module.End K V} {k m : ℕ}

/--
Descent stabilization from a canonical Drazin witness at any step `m ≥ k`.
-/
@[rep_depth operator]
theorem descentAtZero_of_isDrazinInverse_le
    (hD : Drazin.IsDrazinInverse T TD k)
    (hm : k ≤ m) :
    DescentAtZero T m := by
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨TD x, ?_⟩
    have hPow : T ^ (m + 1) * TD = T ^ m :=
      Drazin.IsDrazinInverse.power_le hD hm
    simpa using congrArg (fun f : Module.End K V => f x) hPow
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨T x, ?_⟩
    simp [pow_succ]

/--
Ascent stabilization from a canonical Drazin witness at any step `m ≥ k`.
-/
@[rep_depth operator]
theorem ascentAtZero_of_isDrazinInverse_le
    (hD : Drazin.IsDrazinInverse T TD k)
    (hm : k ≤ m) :
    AscentAtZero T m := by
  apply le_antisymm
  · intro x hx
    change (T ^ (m + 1)) x = 0
    have hx0 : (T ^ m) x = 0 := by
      simpa [LinearMap.mem_ker] using hx
    calc
      (T ^ (m + 1)) x = (T * T ^ m) x := by simp [pow_succ']
      _ = T ((T ^ m) x) := rfl
      _ = T 0 := by rw [hx0]
      _ = 0 := by simp
  · intro x hx
    change (T ^ m) x = 0
    have hx0 : (T ^ (m + 1)) x = 0 := by
      simpa [LinearMap.mem_ker] using hx
    have hPow : T ^ (m + 1) * TD = T ^ m :=
      Drazin.IsDrazinInverse.power_le hD hm
    have hCommute : Commute T TD := Drazin.IsDrazinInverse.comm hD
    have hPowComm : T ^ (m + 1) * TD = TD * T ^ (m + 1) :=
      (hCommute.pow_left (m + 1)).eq
    have hLeft : TD * T ^ (m + 1) = T ^ m := by
      calc
        TD * T ^ (m + 1) = T ^ (m + 1) * TD := hPowComm.symm
        _ = T ^ m := hPow
    calc
      (T ^ m) x = (TD * T ^ (m + 1)) x := by
        simpa using congrArg (fun f : Module.End K V => f x) hLeft.symm
      _ = TD ((T ^ (m + 1)) x) := rfl
      _ = TD 0 := by rw [hx0]
      _ = 0 := by simp

/-- Descent stabilization at the canonical Drazin index. -/
@[rep_depth operator]
theorem descentAtZero_of_isDrazinInverse
    (hD : Drazin.IsDrazinInverse T TD k) :
    DescentAtZero T k :=
  descentAtZero_of_isDrazinInverse_le (T := T) (TD := TD) (k := k) (m := k) hD le_rfl

/-- Ascent stabilization at the canonical Drazin index. -/
@[rep_depth operator]
theorem ascentAtZero_of_isDrazinInverse
    (hD : Drazin.IsDrazinInverse T TD k) :
    AscentAtZero T k :=
  ascentAtZero_of_isDrazinInverse_le (T := T) (TD := TD) (k := k) (m := k) hD le_rfl

/--
Canonical Drazin witness induces a finite ascent/descent witness at zero.
-/
@[rep_depth operator]
def finiteAscentDescentAtZero_of_isDrazinInverse
    (hD : Drazin.IsDrazinInverse T TD k) :
    HasFiniteAscentDescentAtZero T where
  k := k
  ascent := ascentAtZero_of_isDrazinInverse (T := T) (TD := TD) (k := k) hD
  descent := descentAtZero_of_isDrazinInverse (T := T) (TD := TD) (k := k) hD
  D := TD
  hIsDrazin := hD

/--
Finite ascent/descent interface yields a canonical Drazin witness.
-/
@[rep_depth operator]
theorem exists_drazinInverse_of_finiteAscentDescent
    (h : HasFiniteAscentDescentAtZero T) :
    ∃ k' TD', Drazin.IsDrazinInverse T TD' k' :=
  ⟨h.k, h.D, h.hIsDrazin⟩

end AscentDescent

section SpectralInterfaces

variable {𝕂 E : Type*}
variable [NormedField 𝕂]
variable [NormedAddCommGroup E] [NormedSpace 𝕂 E]

/--
Topological isolation interface for the spectral point `0`.

This is intentionally stated as neighborhood isolation to stay lightweight.
-/
@[rep_depth operator]
def ZeroIsolatedInSpectrum (T : E →L[𝕂] E) : Prop :=
  ∃ U : Set 𝕂, IsOpen U ∧ (0 : 𝕂) ∈ U ∧
    ∀ z : 𝕂, z ∈ U → z ∈ spectrum 𝕂 T → z = 0

/--
Riesz-style decomposition interface at `0` for a bounded operator.
-/
@[rep_depth operator]
structure HasClassicalRieszDecompositionAtZero (T : E →L[𝕂] E) where
  P : E →L[𝕂] E
  P_idempotent : P * P = P
  PT_comm : T * P = P * T
  k : ℕ
  D : E →L[𝕂] E
  hIsDrazin : Drazin.IsDrazinInverse T D k
  hP : P = Drazin.IsDrazinInverse.projection T D

/--
Generalized Riesz-style interface at `0` for a bounded operator.

This is intentionally weaker than the classical finite-index Drazin lane:
the defect side is tracked via a separate quasinilpotent witness field.
-/
@[rep_depth operator]
structure HasGeneralizedRieszDecompositionAtZero (T : E →L[𝕂] E) where
  P : E →L[𝕂] E
  P_idempotent : P * P = P
  PT_comm : T * P = P * T
  S : E →L[𝕂] E
  left_inverse_on_regular :
    (T * P) * S = P
  right_inverse_on_regular :
    S * (T * P) = P
  quasinilpotent_on_defect : Prop

/--
Bundle of spectral interfaces commonly used for infinite-dimensional Drazin
existence statements.
-/
@[rep_depth operator]
structure DrazinInfiniteAssumptions (T : E →L[𝕂] E) where
  finite_ascent_descent : HasFiniteAscentDescentAtZero (K := 𝕂) (V := E) T.toLinearMap
  zero_isolated_spectrum : ZeroIsolatedInSpectrum (𝕂 := 𝕂) T
  classical_riesz : HasClassicalRieszDecompositionAtZero (𝕂 := 𝕂) T
  generalized_riesz : HasGeneralizedRieszDecompositionAtZero (𝕂 := 𝕂) T

/--
Classical Riesz decomposition immediately yields the canonical Drazin witness.
-/
@[rep_depth operator]
theorem isDrazinInverse_of_hasClassicalRieszDecompositionAtZero
    {T : E →L[𝕂] E}
    (h : HasClassicalRieszDecompositionAtZero (𝕂 := 𝕂) T) :
    Drazin.IsDrazinInverse T h.D h.k :=
  h.hIsDrazin

/--
Classical Riesz decomposition interface yields a canonical Drazin witness.
-/
@[rep_depth operator]
theorem exists_drazinInverse_of_rieszDecomposition
    {T : E →L[𝕂] E}
    (h : HasClassicalRieszDecompositionAtZero (𝕂 := 𝕂) T) :
    ∃ k TD, Drazin.IsDrazinInverse T TD k :=
  ⟨h.k, h.D, h.hIsDrazin⟩

end SpectralInterfaces

section RieszData

variable {R : Type*} [Ring R]

/--
Riesz-style Drazin package on an operator ring.

The load-bearing field remains the canonical algebraic witness.
-/
@[rep_depth operator]
structure RieszDrazinData (T : R) where
  k : ℕ
  D : R
  P : R
  hIsDrazin : Drazin.IsDrazinInverse T D k
  hP : P = Drazin.IsDrazinInverse.projection T D

variable {T : R}

/-- Extract canonical Drazin witness from a Riesz package. -/
@[rep_depth operator]
theorem isDrazinInverse_of_riesz
    (h : RieszDrazinData T) :
    Drazin.IsDrazinInverse T h.D h.k :=
  h.hIsDrazin

/-- The regular projector in a Riesz package is idempotent. -/
@[rep_depth operator]
theorem projector_idempotent_of_riesz
    (h : RieszDrazinData T) :
    h.P * h.P = h.P := by
  rw [h.hP]
  exact Drazin.IsDrazinInverse.projection_is_idempotent h.hIsDrazin

/-- Complementary projector attached to a Riesz package. -/
@[rep_depth operator]
def complementaryProjector (h : RieszDrazinData T) : R :=
  Drazin.IsDrazinInverse.complementaryProjection T h.D

/-- Complementary projector in a Riesz package is idempotent. -/
@[rep_depth operator]
theorem complementaryProjector_idempotent_of_riesz
    (h : RieszDrazinData T) :
    complementaryProjector h * complementaryProjector h = complementaryProjector h := by
  unfold complementaryProjector
  exact Drazin.IsDrazinInverse.complementaryProjection_is_idempotent h.hIsDrazin

/-- Regular/complementary projectors are left-orthogonal. -/
@[rep_depth operator]
theorem projector_mul_complementaryProjector_of_riesz
    (h : RieszDrazinData T) :
    h.P * complementaryProjector h = 0 := by
  rw [h.hP]
  unfold complementaryProjector
  exact Drazin.IsDrazinInverse.projection_mul_complementaryProjection h.hIsDrazin

/-- Regular/complementary projectors are right-orthogonal. -/
@[rep_depth operator]
theorem complementaryProjector_mul_projector_of_riesz
    (h : RieszDrazinData T) :
    complementaryProjector h * h.P = 0 := by
  rw [h.hP]
  unfold complementaryProjector
  exact Drazin.IsDrazinInverse.complementaryProjection_mul_projection h.hIsDrazin

end RieszData

section FiniteDimensionalBridge

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

/--
Finite-dimensional continuous-operator bridge into the Riesz-style package.
-/
@[rep_depth operator]
theorem nonempty_rieszDrazinData_endCLM (T : E →L[ℝ] E) :
    Nonempty (RieszDrazinData T) := by
  rcases DrazinExistenceBridge.exists_canonicalDrazinInverse_global_endCLM
      (E := E) T with ⟨k, D, hD⟩
  exact ⟨
    { k := k
      D := D
      P := Drazin.IsDrazinInverse.projection T D
      hIsDrazin := hD
      hP := rfl
    }⟩

/--
Canonical finite-dimensional Riesz-Drazin package chosen from existence.
-/
noncomputable def canonicalRieszDrazinData_endCLM (T : E →L[ℝ] E) :
    RieszDrazinData T :=
  Classical.choice (nonempty_rieszDrazinData_endCLM (E := E) T)

/-- Canonical finite-dimensional Drazin index. -/
noncomputable def canonicalDrazinIndex_endCLM (T : E →L[ℝ] E) : ℕ :=
  (canonicalRieszDrazinData_endCLM (E := E) T).k

/-- Canonical finite-dimensional Drazin inverse. -/
noncomputable def canonicalDrazinInverse_endCLM (T : E →L[ℝ] E) : E →L[ℝ] E :=
  (canonicalRieszDrazinData_endCLM (E := E) T).D

/-- Canonical finite-dimensional Drazin witness specification. -/
theorem canonicalDrazinInverse_endCLM_spec (T : E →L[ℝ] E) :
    Drazin.IsDrazinInverse T
      (canonicalDrazinInverse_endCLM (E := E) T)
      (canonicalDrazinIndex_endCLM (E := E) T) := by
  simpa [canonicalDrazinInverse_endCLM, canonicalDrazinIndex_endCLM] using
    (canonicalRieszDrazinData_endCLM (E := E) T).hIsDrazin

end FiniteDimensionalBridge

end InfoGeometry.Canonical.DrazinInfiniteCore
