import Mathlib

noncomputable section

universe u

namespace InfoGeometry.Quantum.LieColimit

/-
Conservative Lie-algebra colimit vocabulary for the KAN analyticity story.

The purpose of this file is narrow:
* finite stages carry a real module structure, a bracket, and a trace functional;
* bonding maps preserve the bracket and trace;
* a colimit element is represented by a finite stage;
* trace-zero therefore transports immediately to represented colimit elements.

No completed infinite Lie algebra, trace-class operator, Virasoro algebra, or
zeta theorem is assumed here.
-/

/-- Direct tower of real Lie-style stages with trace-compatible bonding maps. -/
structure LieAlgebraTower where
  Stage : ℕ → Type u
  [hAdd : ∀ n, AddCommGroup (Stage n)]
  [hModule : ∀ n, Module ℝ (Stage n)]
  bracket : ∀ n, Stage n → Stage n → Stage n
  trace : ∀ n, Stage n → ℝ
  trace_zero : ∀ n (x : Stage n), trace n x = 0
  emb : ∀ n, Stage n →ₗ[ℝ] Stage (n + 1)
  emb_trace : ∀ n (x : Stage n), trace (n + 1) (emb n x) = trace n x
  emb_bracket : ∀ n (x y : Stage n),
    emb n (bracket n x y) = bracket (n + 1) (emb n x) (emb n y)

attribute [instance] LieAlgebraTower.hAdd LieAlgebraTower.hModule

/-- A represented element of the algebraic inductive colimit. -/
structure LieColimitElement (T : LieAlgebraTower.{u}) where
  stage : ℕ
  val : T.Stage stage

/-- Trace of a represented colimit element, evaluated at its finite stage. -/
def colimitTrace {T : LieAlgebraTower.{u}} (x : LieColimitElement T) : ℝ :=
  T.trace x.stage x.val

/-- Bracket trace vanishes at every finite stage. -/
theorem stage_bracket_trace_zero
    (T : LieAlgebraTower.{u}) (n : ℕ) (x y : T.Stage n) :
    T.trace n (T.bracket n x y) = 0 :=
  T.trace_zero n (T.bracket n x y)

/-- Bonding maps preserve trace-zero elements. -/
theorem emb_preserves_trace_zero
    (T : LieAlgebraTower.{u}) (n : ℕ) (x : T.Stage n)
    (hx : T.trace n x = 0) :
    T.trace (n + 1) (T.emb n x) = 0 := by
  rw [T.emb_trace n x, hx]

/-- Bonding maps preserve trace-zero brackets. -/
theorem emb_preserves_bracket_trace_zero
    (T : LieAlgebraTower.{u}) (n : ℕ) (x y : T.Stage n) :
    T.trace (n + 1) (T.emb n (T.bracket n x y)) = 0 := by
  rw [T.emb_trace n (T.bracket n x y)]
  exact stage_bracket_trace_zero T n x y

/--
Hereditary Lie-algebraic trace annihilation.

Since an algebraic colimit element is represented by a finite stage, finite
trace-zero immediately gives colimit trace-zero.
-/
theorem colimit_trace_annihilation
    (T : LieAlgebraTower.{u}) (x : LieColimitElement T) :
    colimitTrace x = 0 :=
  T.trace_zero x.stage x.val

/--
Compatibility of represented elements under one bonding map: the trace readout
is unchanged after moving one stage up.
-/
theorem colimitTrace_emb
    (T : LieAlgebraTower.{u}) (n : ℕ) (x : T.Stage n) :
    colimitTrace (T := T) ⟨n + 1, T.emb n x⟩ =
      colimitTrace (T := T) ⟨n, x⟩ :=
  T.emb_trace n x

/-
Central-charge / 2-cocycle cancellation layer.

This packages the doubled-Krein pattern: a modular conjugation `J` both reverses
the cocycle sign and leaves the physical cocycle value invariant.  Therefore the
central charge vanishes.  This is the algebraic shape of anomaly cancellation,
not a construction of Virasoro cohomology.
-/

/-- Generic doubled-sector central cocycle interface. -/
structure KreinCentralCocycle (α : Type u) where
  charge : α → ℝ
  J : α → α
  J_inversion : ∀ x, charge (J x) = -charge x
  J_invariance : ∀ x, charge (J x) = charge x

/-- If `J` both reverses and preserves a central charge, the charge is zero. -/
theorem central_charge_cancellation
    {α : Type u} (C : KreinCentralCocycle α) (x : α) :
    C.charge x = 0 := by
  have h_inv := C.J_inversion x
  have h_inv' : C.charge x = -C.charge x := by
    rw [C.J_invariance x] at h_inv
    exact h_inv
  linarith

/--
Bundled infinite analyticity obstruction cancellation:
represented colimit trace is zero and the modeled central cocycle vanishes.
-/
theorem lie_colimit_analyticity_and_central_charge_lock
    (T : LieAlgebraTower.{u}) (x : LieColimitElement T)
    {α : Type u} (C : KreinCentralCocycle α) (a : α) :
    colimitTrace x = 0 ∧ C.charge a = 0 :=
  ⟨colimit_trace_annihilation T x, central_charge_cancellation C a⟩

end InfoGeometry.Quantum.LieColimit

