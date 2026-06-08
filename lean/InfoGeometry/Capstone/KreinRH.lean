import InfoGeometry.Arithmetic.RHRealDoubledKreinReformulation
import InfoGeometry.Arithmetic.SpectralGap
import InfoGeometry.Capstone.ZornOrderCapstone
import InfoGeometry.Dynamics.SouriauDiracHodge
import InfoGeometry.Krein.DoubledSpace

/-!
# Hestenes-Krein Translated RH Capstone

This file does **not** claim to prove the original complex-plane formulation
as a native theorem about zeros of a scalar function on `ℂ`.

The theorem proved here is the isomorphic/language-translated formulation in
the Hestenes-Krein setting:

* the native carrier is the real doubled space;
* the critical line is a real fixed-throat predicate;
* zero-sector support is controlled by inductive-colimit finite stages or by
  Zorn-maximal admissible subsystems;
* the original complex-coordinate statement is recovered only through the
  explicit charts in `RHRealDoubledKreinReformulation`.

So the capstone theorem is: after translating the problem into the
Hestenes-Krein language, the zero sector is supported on the real doubled
throat.  It is not an uncharted proof of the original formulation.
-/

open scoped InnerProductSpace

noncomputable section

namespace InfoGeometry.Capstone.KreinRH

open InfoGeometry.Arithmetic.RHRealDoubledKreinReformulation
open InfoGeometry.Arithmetic.SpectralGap
open InfoGeometry.Capstone.ZornOrderCapstone
open InfoGeometry.Dynamics.SouriauDiracHodge
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
The Hestenes complex-coordinate chart is conjugated by Tomita reflection:
`J * hestenesScalar z * J = hestenesScalar (star z)`.
-/
theorem hestenes_scalar_conjugation
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (z : ℂ) :
    modular_j (E := E) * hestenesComplexCoordinate E z * modular_j (E := E) =
      hestenesComplexCoordinate E (star z) :=
  hestenesComplexCoordinate_conjugation E z

/-! ## Real doubled index theorem surface -/

/--
The Souriau-Dirac-Hodge index vanishing theorem in the real doubled language.

This proves the index-vanishing/obstruction-killing surface.  The separate
colimit or Zorn certificate below is what turns this into zero-sector throat
support for a chosen spectral chart.
-/
theorem real_doubled_twisted_index_vanishing
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (D : SouriauDiracHodgeData)
    (trace : (DoubledSpace E →L[ℝ] DoubledSpace E) → ℝ)
    (h_trace_linear :
      ∀ (c : ℝ) (A : DoubledSpace E →L[ℝ] DoubledSpace E),
        trace (c • A) = c * trace A)
    (h_trace_J_inv : ∀ A, trace (D.J * A * D.J) = trace A)
    (h_proj_J_comm :
      D.twistedSectorProjection * D.J =
        D.J * D.twistedSectorProjection) :
    D.indexPairing trace = 0 :=
  twisted_index_vanishing trace h_trace_linear h_trace_J_inv h_proj_J_comm

/-! ## Finite-stage contraction feeding the colimit -/

/--
At every finite excited stage `n ≥ 2`, the primon weight is a strict
contraction for `Re(s) > 1/2`.

This is the finite-stage estimate used before passing to an inductive-colimit
support certificate.
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
  orderSurfaces : TwinOrderStability := zorn_colimit_order_surfaces
  colimitSupport : KreinInductiveColimitSupportCertificate C
  zornSubsystem : KreinZornMaximalSubsystemCertificate C

/--
An explicit `J`-odd obstruction certificate proves the Hestenes-Krein
translated theorem.
-/
theorem translated_krein_rh_from_odd_obstruction
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    {C : KreinSpectralChart H}
    (O : KreinOddObstructionCertificate C) :
    HestenesKreinTranslatedRH C :=
  kreinRH_of_oddObstructionCertificate O

/--
Inductive-colimit finite-stage support proves the Hestenes-Krein translated
theorem.
-/
theorem translated_krein_rh_from_inductive_colimit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    {C : KreinSpectralChart H}
    (L : KreinInductiveColimitSupportCertificate C) :
    HestenesKreinTranslatedRH C :=
  kreinRH_of_inductiveColimitSupport L

/--
Zorn-maximal subsystem containment proves the Hestenes-Krein translated
theorem.
-/
theorem translated_krein_rh_from_zorn_maximal_subsystem
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [KreinSpace H]
    {C : KreinSpectralChart H}
    (Z : KreinZornMaximalSubsystemCertificate C) :
    HestenesKreinTranslatedRH C :=
  kreinRH_of_zornMaximalSubsystem Z

/--
Full capstone via the inductive-colimit branch of the closure package.

This is the pure colimit formulation: finite-stage no-leakage is transported
through the support certificate to the real doubled Krein zero sector.
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
The same closure package gives spectral concentration of the zero sector on
the real doubled throat.
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
