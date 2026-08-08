import InfoGeometry.Arithmetic.RHRealDoubledKreinReformulation
import InfoGeometry.Arithmetic.SpectralGap
import InfoGeometry.Canonical.LogCftMonodromyBridge
import InfoGeometry.Capstone.ZornOrderCapstone

/-!
# Hestenes--Krein critical-line statement sockets

This file does **not** prove the Riemann Hypothesis.  It packages conditional
finite Hestenes--Krein readouts: if a supplied spectral chart/property says
that the declared zero sector is represented by finite stages or by a
Zorn-maximal subsystem with no leakage, then the chart's own throat predicate
contains that declared zero sector.

The complex-coordinate statement is available only through explicit chart data
in `RHRealDoubledKreinReformulation`; no chart is manufactured here and no
zeta-zero theorem is asserted.
-/

open scoped InnerProductSpace

noncomputable section

namespace InfoGeometry.Capstone.KreinRH

open InfoGeometry.Arithmetic.RHRealDoubledKreinReformulation
open InfoGeometry.Arithmetic.SpectralGap
open InfoGeometry.Capstone.ZornOrderCapstone
open InfoGeometry.Krein

/-! ## Real doubled Hestenes/Krein chart -/

/--
Tomita reflection reverses the Hestenes phase axis on the real doubled carrier:
`J * I_h * J = -I_h`.
-/
theorem hestenes_klein_bottle_twist
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    modular_j (E := E) * complex_i (E := E) * modular_j (E := E) =
      -complex_i (E := E) :=
  hestenes_phaseAxis_conjugation E

/--
Möbius-tape gluing in the real doubled model.

The physical and ghost sheets are glued by `modular_j`; the gluing reverses
the Hestenes phase axis.  This is the operator-level content of the
orientation-reversing branch-cut language.
-/
theorem mobius_tape_gluing_twist
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    modular_j (E := E) * complex_i (E := E) * modular_j (E := E) =
      -complex_i (E := E) :=
  hestenes_klein_bottle_twist E

/--
The Hestenes complex-coordinate chart is conjugated by Tomita reflection:
`J * hestenesScalar z * J = hestenesScalar (star z)`.
-/
theorem hestenes_scalar_conjugation
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (z : ℂ) :
    modular_j (E := E) * hestenesComplexCoordinate E z * modular_j (E := E) =
      hestenesComplexCoordinate E (star z) :=
  hestenesComplexCoordinate_conjugation E z

/--
The same `J`-gluing acts on the embedded complex-coordinate chart by
conjugation.  This is the chart-level reflection used to compare the real
doubled theorem with the original complex-coordinate formulation.
-/
theorem mobius_tape_scalar_reflection
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (z : ℂ) :
    modular_j (E := E) * hestenesComplexCoordinate E z * modular_j (E := E) =
      hestenesComplexCoordinate E (star z) :=
  hestenes_scalar_conjugation E z

/-! ## Finite monodromy readout replacing branch-cut language -/

/--
Finite LCFT monodromy decomposes into a scalar phase and a nilpotent
logarithmic shear.

This is the owner-backed algebraic readout behind the branch-cut/monodromy
language: the capstone uses the monodromy matrix identity, not a global
analytic branch-cut theorem.
-/
theorem logCFT_monodromy_decomposition (h : ℂ) :
    InfoGeometry.Canonical.LogCftMonodromyBridge.hadjiivanovMonodromy h =
      InfoGeometry.Canonical.LogCftMonodromyBridge.lcftPhase h •
          (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        InfoGeometry.Clifford.LogCftMonodromy.monodromyNilpotentPart h :=
  InfoGeometry.Canonical.LogCftMonodromyBridge.monodromy_decomposition h

/--
After `n` wraps, the lower logarithmic monodromy has the exact winding law.

The nilpotent shear coefficient is linear in the winding number; this is the
finite algebraic monodromy surface used here.
-/
theorem logCFT_lower_monodromy_winding_law (h : ℂ) (n : ℕ) :
    InfoGeometry.Clifford.LogCftMonodromy.lowerHadjiivanovMonodromy h ^ n =
      InfoGeometry.Canonical.LogCftMonodromyBridge.lcftPhase h ^ n •
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
          ((n : ℂ) * InfoGeometry.Canonical.LogCftMonodromyBridge.logShearBase) •
            InfoGeometry.Clifford.LogCftMonodromy.lowerJordanNilpotent) :=
  InfoGeometry.Canonical.LogCftMonodromyBridge.lowerHadjiivanovMonodromy_pow_winding h n

/-! ## Finite-stage contraction feeding the colimit -/

/--
At every finite excited stage `n ≥ 2`, the primon weight is a strict
contraction for `Re(s) > 1/2`.

This is the finite-stage estimate used before passing to an inductive-colimit
support property.
-/
theorem finite_stage_spectral_contraction
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) ^ (-s.re) < 1 := by
  exact primon_norm_bound s (by linarith) n hn

/-! ## Zorn/order surfaces already proved in the repository -/

/--
The bundled order surfaces currently proved in the repository:

* symbolic boundary Zorn closure;
* braid-colimit Zorn closure;
* finite JKO/Jaynes readout;
* `Cl(5,5)` finite-window absorption and representative completeness.
-/
theorem zorn_colimit_order_surfaces : TwinOrderStability :=
  twin_orders_stabilize

/-! ## Certificate-based translated theorem completion -/

/--
The proof-carrying closure package for one real doubled Krein spectral chart.

The `colimitSupport` field says every zero-state is represented at a finite
stage and every finite stage already proves the throat condition.  The
`zornSubsystem` field says every zero-state lies in a Zorn-maximal admissible
subsystem where no leakage is possible.
-/
structure KreinRHColimitZornClosure
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    (C : KreinSpectralChart H) where
  colimitSupport : KreinFiniteStageSupportData C
  zornSubsystem : KreinZornMaximalSubsystemData C

namespace KreinRHColimitZornClosure

/-- The order-surface theorem is shared by every closure package. -/
def orderSurfaces
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] {C : KreinSpectralChart H}
    (_P : KreinRHColimitZornClosure C) : TwinOrderStability :=
  zorn_colimit_order_surfaces

@[simp] theorem orderSurfaces_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H] {C : KreinSpectralChart H}
    (P : KreinRHColimitZornClosure C) :
    P.orderSurfaces = zorn_colimit_order_surfaces := rfl

end KreinRHColimitZornClosure

/--
An explicit `J`-odd obstruction property proves the chart-local no-leakage
statement.
-/
theorem translated_krein_rh_from_odd_obstruction
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    {C : KreinSpectralChart H}
    (O : KreinOddObstructionData C) :
    HestenesKreinTranslatedRH C :=
  kreinRH_of_oddObstructionCertificate O

/--
Inductive-colimit finite-stage support proves the chart-local no-leakage
statement.
-/
theorem translated_krein_rh_from_inductive_colimit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    {C : KreinSpectralChart H}
    (L : KreinFiniteStageSupportData C) :
    HestenesKreinTranslatedRH C :=
  kreinRH_of_inductiveColimitSupport L

/--
Zorn-maximal subsystem containment proves the chart-local no-leakage statement.
-/
theorem translated_krein_rh_from_zorn_maximal_subsystem
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    {C : KreinSpectralChart H}
    (Z : KreinZornMaximalSubsystemData C) :
    HestenesKreinTranslatedRH C :=
  kreinRH_of_zornMaximalSubsystem Z

/--
Full capstone via the inductive-colimit branch of the closure package.

This is the pure colimit formulation: finite-stage no-leakage is transported
through the support property to the real doubled Krein zero sector.
-/
theorem translated_krein_rh_completion_colimit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    {C : KreinSpectralChart H}
    (P : KreinRHColimitZornClosure C) :
    HestenesKreinTranslatedRH C :=
  translated_krein_rh_from_inductive_colimit P.colimitSupport

/--
Full capstone via the Zorn-maximal subsystem branch of the closure package.

This is the global order formulation: all zero-states are contained in a
Zorn-maximal admissible subsystem, and that subsystem proves no leakage.
-/
theorem translated_krein_rh_completion_zorn
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    {C : KreinSpectralChart H}
    (P : KreinRHColimitZornClosure C) :
    HestenesKreinTranslatedRH C :=
  translated_krein_rh_from_zorn_maximal_subsystem P.zornSubsystem

/--
Compatibility alias: the colimit branch also returns the historical `KreinRH`
name, definitionally equal to `HestenesKreinTranslatedRH`.
-/
theorem krein_rh_topological_completion_colimit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    {C : KreinSpectralChart H}
    (P : KreinRHColimitZornClosure C) :
    KreinRH C :=
  translated_krein_rh_completion_colimit P

/--
Compatibility alias: the Zorn branch also returns the historical `KreinRH`
name, definitionally equal to `HestenesKreinTranslatedRH`.
-/
theorem krein_rh_topological_completion_zorn
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    {C : KreinSpectralChart H}
    (P : KreinRHColimitZornClosure C) :
    KreinRH C :=
  translated_krein_rh_completion_zorn P

/--
The same closure package gives concentration of the declared chart-zero sector
on the chart throat.
-/
theorem krein_spectral_concentration_topological_completion
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    {C : KreinSpectralChart H}
    (P : KreinRHColimitZornClosure C) :
    KreinSpectralConcentration C :=
  kreinSpectralConcentration_of_zornMaximalSubsystem P.zornSubsystem

end InfoGeometry.Capstone.KreinRH

end
