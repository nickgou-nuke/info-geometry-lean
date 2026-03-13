import InfoGeometry.Canonical.BottDirac
import InfoGeometry.Canonical.ChiralAnomaly
import InfoGeometry.Canonical.KMSSinkhornBridge
import InfoGeometry.Canonical.RicciMongeAmpere
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map

open scoped TensorProduct

namespace InfoGeometry.Canonical.AnalyticalIndex

open InfoGeometry.Krein
open InfoGeometry.Canonical.BottDirac
open InfoGeometry.Canonical.ChiralAnomaly
open InfoGeometry.Canonical.KMSSinkhornBridge
open InfoGeometry.Canonical.MoE
open InfoGeometry.Canonical.RicciMongeAmpere

section Core

variable {V : Type*}
  [AddCommGroup V] [Module ℝ V]

/-- Chiral projector `P₊ = (1/2)(Id + Γ)`. -/
noncomputable def chiralProjectorPlus (Γ : Endomorphism V) : Endomorphism V :=
  ((1 / 2 : ℝ) • ((LinearMap.id : Endomorphism V) + Γ))

/-- Chiral projector `P₋ = (1/2)(Id - Γ)`. -/
noncomputable def chiralProjectorMinus (Γ : Endomorphism V) : Endomorphism V :=
  ((1 / 2 : ℝ) • ((LinearMap.id : Endomorphism V) - Γ))

/-- Positive-chiral component `D⁺ := D ∘ P₊`. -/
noncomputable def chiralPartPlus (D Γ : Endomorphism V) : Endomorphism V :=
  D.comp (chiralProjectorPlus Γ)

/-- Negative-chiral component `D⁻ := D ∘ P₋`. -/
noncomputable def chiralPartMinus (D Γ : Endomorphism V) : Endomorphism V :=
  D.comp (chiralProjectorMinus Γ)

/-- Positive-chiral index slice `ker(D) ∩ Im(P₊)`. -/
noncomputable def chiralKernelSlicePlus (D Γ : Endomorphism V) : Submodule ℝ V :=
  LinearMap.ker D ⊓ LinearMap.range (chiralProjectorPlus Γ)

/-- Negative-chiral index slice `ker(D) ∩ Im(P₋)`. -/
noncomputable def chiralKernelSliceMinus (D Γ : Endomorphism V) : Submodule ℝ V :=
  LinearMap.ker D ⊓ LinearMap.range (chiralProjectorMinus Γ)

/--
Analytical index model:
`Index(D) = dim(ker(D) ∩ Im(P₊)) - dim(ker(D) ∩ Im(P₋))`.
-/
noncomputable def analyticalIndex [FiniteDimensional ℝ V] (D Γ : Endomorphism V) : ℤ :=
  (Module.finrank ℝ (chiralKernelSlicePlus D Γ) : ℤ) -
    (Module.finrank ℝ (chiralKernelSliceMinus D Γ) : ℤ)

/-- Chiral decomposition identity: `D⁺ + D⁻ = D`. -/
lemma chiralPartPlus_add_chiralPartMinus (D Γ : Endomorphism V) :
    chiralPartPlus D Γ + chiralPartMinus D Γ = D := by
  ext v
  rw [show (chiralPartPlus D Γ + chiralPartMinus D Γ) v
        = D ((chiralProjectorPlus Γ + chiralProjectorMinus Γ) v) by
          simp [chiralPartPlus, chiralPartMinus, map_add]]
  have hproj :
      (chiralProjectorPlus Γ + chiralProjectorMinus Γ) v = v := by
    calc
      (chiralProjectorPlus Γ + chiralProjectorMinus Γ) v
          = (1 / 2 : ℝ) • (((LinearMap.id : Endomorphism V) + Γ) v) +
              (1 / 2 : ℝ) • (((LinearMap.id : Endomorphism V) - Γ) v) := by
                simp [chiralProjectorPlus, chiralProjectorMinus]
      _ = (1 / 2 : ℝ) •
            ((((LinearMap.id : Endomorphism V) + Γ) v) +
              (((LinearMap.id : Endomorphism V) - Γ) v)) := by
              rw [← smul_add]
      _ = (1 / 2 : ℝ) • (v + v) := by
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • v := by
            simpa using (add_smul (1 / 2 : ℝ) (1 / 2 : ℝ) v).symm
      _ = (1 : ℝ) • v := by norm_num
      _ = v := by simp
  simp [hproj]

/--
If both chiral parts coincide, the corresponding Dirac endomorphisms coincide.

This is exactly the identity `D = D ∘ P₊ + D ∘ P₋` with `P₊ + P₋ = Id`.
-/
lemma dirac_eq_of_chiralParts_eq
    (D Γ D' Γ' : Endomorphism V)
    (hplus : chiralPartPlus D Γ = chiralPartPlus D' Γ')
    (hminus : chiralPartMinus D Γ = chiralPartMinus D' Γ') :
    D = D' := by
  calc
    D = chiralPartPlus D Γ + chiralPartMinus D Γ := by
      symm
      exact chiralPartPlus_add_chiralPartMinus (D := D) (Γ := Γ)
    _ = chiralPartPlus D' Γ' + chiralPartMinus D' Γ' := by
      rw [hplus, hminus]
    _ = D' := chiralPartPlus_add_chiralPartMinus (D := D') (Γ := Γ')

/-- Lemma `analyticalIndex_eq_of_chiralParts_eq`. -/
lemma analyticalIndex_eq_of_chiralParts_eq
    [FiniteDimensional ℝ V]
    (D Γ D' Γ' : Endomorphism V)
    (hplus : chiralPartPlus D Γ = chiralPartPlus D' Γ')
    (hminus : chiralPartMinus D Γ = chiralPartMinus D' Γ')
    (hRangePlus :
      LinearMap.range (chiralProjectorPlus Γ) = LinearMap.range (chiralProjectorPlus Γ'))
    (hRangeMinus :
      LinearMap.range (chiralProjectorMinus Γ) = LinearMap.range (chiralProjectorMinus Γ')) :
    analyticalIndex D Γ = analyticalIndex D' Γ' := by
  have hD : D = D' := dirac_eq_of_chiralParts_eq D Γ D' Γ' hplus hminus
  subst hD
  unfold analyticalIndex chiralKernelSlicePlus chiralKernelSliceMinus
  rw [hRangePlus, hRangeMinus]

/-- Index invariance along a parameterized Dirac/grading family. -/
def IndexInvariantAlong [FiniteDimensional ℝ V] (D Γ : ℝ → Endomorphism V) : Prop :=
  ∀ s : ℝ, analyticalIndex (D s) (Γ s) = analyticalIndex (D 0) (Γ 0)

/--
Deformation data for index invariance: each chiral kernel slice at time `s` is
linearly equivalent to the baseline slice at `0`.
-/
def ChiralSliceIsoAlong [FiniteDimensional ℝ V] (D Γ : ℝ → Endomorphism V) : Prop :=
  (∀ s : ℝ,
      Nonempty
        ((chiralKernelSlicePlus (D s) (Γ s)) ≃ₗ[ℝ]
          (chiralKernelSlicePlus (D 0) (Γ 0))))
    ∧
  (∀ s : ℝ,
      Nonempty
        ((chiralKernelSliceMinus (D s) (Γ s)) ≃ₗ[ℝ]
          (chiralKernelSliceMinus (D 0) (Γ 0))))

/--
Conjugacy data for a Dirac/grading family along a transport flow of linear
equivalences.
-/
def ChiralConjugacyAlong [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    (eFlow : ℝ → V ≃ₗ[ℝ] V) : Prop :=
  (∀ s : ℝ, (D 0).comp (eFlow s).toLinearMap = (eFlow s).toLinearMap.comp (D s)) ∧
    (∀ s : ℝ, (Γ 0).comp (eFlow s).toLinearMap = (eFlow s).toLinearMap.comp (Γ s))

/-- Conjugacy transports kernels exactly along a linear equivalence. -/
lemma map_ker_eq_of_conjugacy
    (Ds D0 : Endomorphism V)
    (e : V ≃ₗ[ℝ] V)
    (hConj : D0.comp e.toLinearMap = e.toLinearMap.comp Ds) :
    (LinearMap.ker Ds).map e.toLinearMap = LinearMap.ker D0 := by
  ext v
  constructor
  · intro hv
    rcases hv with ⟨x, hx, rfl⟩
    change D0 (e x) = 0
    have hConjX : D0 (e x) = e (Ds x) := by
      simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hConj x)
    rw [hConjX, hx, map_zero]
  · intro hv
    refine ⟨e.symm v, ?_, by simp⟩
    have hConjX : D0 (e (e.symm v)) = e (Ds (e.symm v)) := by
      simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hConj (e.symm v))
    have hImageZero : e (Ds (e.symm v)) = 0 := by
      calc
        e (Ds (e.symm v)) = D0 (e (e.symm v)) := by simpa using hConjX.symm
        _ = D0 v := by simp
        _ = 0 := hv
    exact e.injective (by simpa using hImageZero)

/-- Conjugacy transports ranges exactly along a linear equivalence. -/
lemma map_range_eq_of_conjugacy
    (Ps P0 : Endomorphism V)
    (e : V ≃ₗ[ℝ] V)
    (hConj : P0.comp e.toLinearMap = e.toLinearMap.comp Ps) :
    (LinearMap.range Ps).map e.toLinearMap = LinearMap.range P0 := by
  ext v
  constructor
  · intro hv
    rcases hv with ⟨x, hx, rfl⟩
    rcases hx with ⟨y, rfl⟩
    refine ⟨e y, ?_⟩
    have hConjY : P0 (e y) = e (Ps y) := by
      simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hConj y)
    simpa [hConjY]
  · intro hv
    rcases hv with ⟨x, rfl⟩
    refine ⟨Ps (e.symm x), ?_, ?_⟩
    · exact ⟨e.symm x, rfl⟩
    · have hConjX : P0 (e (e.symm x)) = e (Ps (e.symm x)) := by
        simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hConj (e.symm x))
      simpa using hConjX.symm

/-- Chiral projector `P₊` respects grading conjugacy. -/
lemma chiralProjectorPlus_comp_of_conjugacy
    (Γs Γ0 : Endomorphism V)
    (e : V ≃ₗ[ℝ] V)
    (hConj : Γ0.comp e.toLinearMap = e.toLinearMap.comp Γs) :
    (chiralProjectorPlus Γ0).comp e.toLinearMap =
      e.toLinearMap.comp (chiralProjectorPlus Γs) := by
  ext v
  have hConjV : Γ0 (e v) = e (Γs v) := by
    simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hConj v)
  simp [chiralProjectorPlus, LinearMap.comp_apply, hConjV, map_add, map_smul]

/-- Chiral projector `P₋` respects grading conjugacy. -/
lemma chiralProjectorMinus_comp_of_conjugacy
    (Γs Γ0 : Endomorphism V)
    (e : V ≃ₗ[ℝ] V)
    (hConj : Γ0.comp e.toLinearMap = e.toLinearMap.comp Γs) :
    (chiralProjectorMinus Γ0).comp e.toLinearMap =
      e.toLinearMap.comp (chiralProjectorMinus Γs) := by
  ext v
  have hConjV : Γ0 (e v) = e (Γs v) := by
    simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hConj v)
  simp [chiralProjectorMinus, LinearMap.comp_apply, hConjV, map_sub, map_smul]

/-- Conjugacy transports the positive chiral kernel slice exactly. -/
lemma map_chiralKernelSlicePlus_eq_of_conjugacy
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    (s : ℝ)
    (e : V ≃ₗ[ℝ] V)
    (hD : (D 0).comp e.toLinearMap = e.toLinearMap.comp (D s))
    (hΓ : (Γ 0).comp e.toLinearMap = e.toLinearMap.comp (Γ s)) :
    (chiralKernelSlicePlus (D s) (Γ s)).map e.toLinearMap =
      chiralKernelSlicePlus (D 0) (Γ 0) := by
  unfold chiralKernelSlicePlus
  calc
    (LinearMap.ker (D s) ⊓ LinearMap.range (chiralProjectorPlus (Γ s))).map e.toLinearMap
        =
      (LinearMap.ker (D s)).map e.toLinearMap ⊓
        (LinearMap.range (chiralProjectorPlus (Γ s))).map e.toLinearMap := by
          simpa using
            (Submodule.map_inf (f := e.toLinearMap)
              (p := LinearMap.ker (D s))
              (q := LinearMap.range (chiralProjectorPlus (Γ s)))
              e.injective)
    _ = LinearMap.ker (D 0) ⊓ LinearMap.range (chiralProjectorPlus (Γ 0)) := by
      rw [map_ker_eq_of_conjugacy (Ds := D s) (D0 := D 0) (e := e) hD,
        map_range_eq_of_conjugacy
          (Ps := chiralProjectorPlus (Γ s))
          (P0 := chiralProjectorPlus (Γ 0))
          (e := e)
          (chiralProjectorPlus_comp_of_conjugacy
            (Γs := Γ s) (Γ0 := Γ 0) (e := e) hΓ)]

/-- Conjugacy transports the negative chiral kernel slice exactly. -/
lemma map_chiralKernelSliceMinus_eq_of_conjugacy
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    (s : ℝ)
    (e : V ≃ₗ[ℝ] V)
    (hD : (D 0).comp e.toLinearMap = e.toLinearMap.comp (D s))
    (hΓ : (Γ 0).comp e.toLinearMap = e.toLinearMap.comp (Γ s)) :
    (chiralKernelSliceMinus (D s) (Γ s)).map e.toLinearMap =
      chiralKernelSliceMinus (D 0) (Γ 0) := by
  unfold chiralKernelSliceMinus
  calc
    (LinearMap.ker (D s) ⊓ LinearMap.range (chiralProjectorMinus (Γ s))).map e.toLinearMap
        =
      (LinearMap.ker (D s)).map e.toLinearMap ⊓
        (LinearMap.range (chiralProjectorMinus (Γ s))).map e.toLinearMap := by
          simpa using
            (Submodule.map_inf (f := e.toLinearMap)
              (p := LinearMap.ker (D s))
              (q := LinearMap.range (chiralProjectorMinus (Γ s)))
              e.injective)
    _ = LinearMap.ker (D 0) ⊓ LinearMap.range (chiralProjectorMinus (Γ 0)) := by
      rw [map_ker_eq_of_conjugacy (Ds := D s) (D0 := D 0) (e := e) hD,
        map_range_eq_of_conjugacy
          (Ps := chiralProjectorMinus (Γ s))
          (P0 := chiralProjectorMinus (Γ 0))
          (e := e)
          (chiralProjectorMinus_comp_of_conjugacy
            (Γs := Γ s) (Γ0 := Γ 0) (e := e) hΓ)]

/--
Conjugacy-to-iso bridge: if `D(s), Γ(s)` are conjugate to the baseline by a
linear-equivalence flow, then both chiral kernel slices are linearly equivalent
to their baseline slices.
-/
theorem chiralSliceIsoAlong_of_conjugacy
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    (eFlow : ℝ → V ≃ₗ[ℝ] V)
    (hConj : ChiralConjugacyAlong D Γ eFlow) :
    ChiralSliceIsoAlong D Γ := by
  rcases hConj with ⟨hDConj, hΓConj⟩
  refine ⟨?_, ?_⟩
  · intro s
    let e := eFlow s
    let eMap :
        (chiralKernelSlicePlus (D s) (Γ s)) ≃ₗ[ℝ]
          ((chiralKernelSlicePlus (D s) (Γ s)).map e.toLinearMap) :=
      Submodule.equivMapOfInjective
        (f := e.toLinearMap) (i := e.injective)
        (p := chiralKernelSlicePlus (D s) (Γ s))
    have hMap :
        (chiralKernelSlicePlus (D s) (Γ s)).map e.toLinearMap =
          chiralKernelSlicePlus (D 0) (Γ 0) :=
      map_chiralKernelSlicePlus_eq_of_conjugacy
        (D := D) (Γ := Γ) (s := s) (e := e) (hD := hDConj s) (hΓ := hΓConj s)
    exact ⟨eMap.trans (LinearEquiv.ofEq _ _ hMap)⟩
  · intro s
    let e := eFlow s
    let eMap :
        (chiralKernelSliceMinus (D s) (Γ s)) ≃ₗ[ℝ]
          ((chiralKernelSliceMinus (D s) (Γ s)).map e.toLinearMap) :=
      Submodule.equivMapOfInjective
        (f := e.toLinearMap) (i := e.injective)
        (p := chiralKernelSliceMinus (D s) (Γ s))
    have hMap :
        (chiralKernelSliceMinus (D s) (Γ s)).map e.toLinearMap =
          chiralKernelSliceMinus (D 0) (Γ 0) :=
      map_chiralKernelSliceMinus_eq_of_conjugacy
        (D := D) (Γ := Γ) (s := s) (e := e) (hD := hDConj s) (hΓ := hΓConj s)
    exact ⟨eMap.trans (LinearEquiv.ofEq _ _ hMap)⟩

/--
Modular-flow / Clifford-bundle transport hypothesis for the chiral kernel slices.

At each scale `s`, transport by `σ s` and Clifford action `clAct ℓ` sends the
`±` chiral kernel slice at `s` to the baseline slice at `0`. The designated
`unit` Clifford label acts as identity.
-/
def ChiralSliceModularCliffordTransportAlong
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    {ι : Type*}
    (σ : ℝ → Endomorphism V)
    (clAct : ι → Endomorphism V)
    (unit : ι) : Prop :=
  clAct unit = LinearMap.id ∧
    (∀ s : ℝ, Function.Injective (σ s)) ∧
    (∀ s : ℝ, ∀ ℓ : ι,
      (chiralKernelSlicePlus (D s) (Γ s)).map ((clAct ℓ).comp (σ s))
        = chiralKernelSlicePlus (D 0) (Γ 0)) ∧
    (∀ s : ℝ, ∀ ℓ : ι,
      (chiralKernelSliceMinus (D s) (Γ s)).map ((clAct ℓ).comp (σ s))
        = chiralKernelSliceMinus (D 0) (Γ 0))

/--
Transport-to-iso bridge: modular/Clifford transport of the chiral slices yields
the deformation-style slice isomorphisms used by index invariance.
-/
theorem chiralSliceIsoAlong_of_modularCliffordTransport
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    {ι : Type*}
    (σ : ℝ → Endomorphism V)
    (clAct : ι → Endomorphism V)
    (unit : ι)
    (hTrans : ChiralSliceModularCliffordTransportAlong (D := D) (Γ := Γ) σ clAct unit) :
    ChiralSliceIsoAlong D Γ := by
  rcases hTrans with ⟨hUnit, hσInj, hPlusMap, hMinusMap⟩
  refine ⟨?_, ?_⟩
  · intro s
    let f : Endomorphism V := (clAct unit).comp (σ s)
    have hf : Function.Injective f := by
      intro x y hxy
      have hxy' : (σ s) x = (σ s) y := by
        simpa [f, hUnit] using hxy
      exact hσInj s hxy'
    let eMap :
        (chiralKernelSlicePlus (D s) (Γ s)) ≃ₗ[ℝ]
          ((chiralKernelSlicePlus (D s) (Γ s)).map f) :=
      Submodule.equivMapOfInjective
        (f := f) (i := hf) (p := chiralKernelSlicePlus (D s) (Γ s))
    have hEq :
        (chiralKernelSlicePlus (D s) (Γ s)).map f
          = chiralKernelSlicePlus (D 0) (Γ 0) := by
      simpa [f] using hPlusMap s unit
    exact ⟨eMap.trans (LinearEquiv.ofEq _ _ hEq)⟩
  · intro s
    let f : Endomorphism V := (clAct unit).comp (σ s)
    have hf : Function.Injective f := by
      intro x y hxy
      have hxy' : (σ s) x = (σ s) y := by
        simpa [f, hUnit] using hxy
      exact hσInj s hxy'
    let eMap :
        (chiralKernelSliceMinus (D s) (Γ s)) ≃ₗ[ℝ]
          ((chiralKernelSliceMinus (D s) (Γ s)).map f) :=
      Submodule.equivMapOfInjective
        (f := f) (i := hf) (p := chiralKernelSliceMinus (D s) (Γ s))
    have hEq :
        (chiralKernelSliceMinus (D s) (Γ s)).map f
          = chiralKernelSliceMinus (D 0) (Γ 0) := by
      simpa [f] using hMinusMap s unit
    exact ⟨eMap.trans (LinearEquiv.ofEq _ _ hEq)⟩

/--
Genuine deformation-style index invariance:
if both chiral index slices are linearly equivalent along the path, the
analytical index is invariant.
-/
theorem indexInvariantAlong_of_chiralSliceIso
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    (hIso : ChiralSliceIsoAlong D Γ) :
    IndexInvariantAlong D Γ := by
  intro s
  rcases hIso.1 s with ⟨ePlus⟩
  rcases hIso.2 s with ⟨eMinus⟩
  have hPlusFinrank :
      Module.finrank ℝ (chiralKernelSlicePlus (D s) (Γ s)) =
        Module.finrank ℝ (chiralKernelSlicePlus (D 0) (Γ 0)) := by
    simpa using ePlus.finrank_eq
  have hMinusFinrank :
      Module.finrank ℝ (chiralKernelSliceMinus (D s) (Γ s)) =
        Module.finrank ℝ (chiralKernelSliceMinus (D 0) (Γ 0)) := by
    simpa using eMinus.finrank_eq
  unfold analyticalIndex
  simp [hPlusFinrank, hMinusFinrank]

/-- Index invariance from flow-conjugacy of the Dirac/grading family. -/
theorem indexInvariantAlong_of_conjugacy
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    (eFlow : ℝ → V ≃ₗ[ℝ] V)
    (hConj : ChiralConjugacyAlong D Γ eFlow) :
    IndexInvariantAlong D Γ := by
  exact indexInvariantAlong_of_chiralSliceIso
    (D := D) (Γ := Γ)
    (hIso := chiralSliceIsoAlong_of_conjugacy
      (D := D) (Γ := Γ) (eFlow := eFlow) hConj)

/--
Direct deformation invariance route:
modular-flow / Clifford-bundle transport of chiral slices implies analytical
index invariance along the full family.
-/
theorem indexInvariantAlong_of_modularCliffordTransport
    [FiniteDimensional ℝ V]
    (D Γ : ℝ → Endomorphism V)
    {ι : Type*}
    (σ : ℝ → Endomorphism V)
    (clAct : ι → Endomorphism V)
    (unit : ι)
    (hTrans : ChiralSliceModularCliffordTransportAlong (D := D) (Γ := Γ) σ clAct unit) :
    IndexInvariantAlong D Γ := by
  exact indexInvariantAlong_of_chiralSliceIso (D := D) (Γ := Γ)
    (chiralSliceIsoAlong_of_modularCliffordTransport
      (D := D) (Γ := Γ) (σ := σ) (clAct := clAct) (unit := unit) hTrans)

end Core

section Bott

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Global grading on the Bott tensor space: `Γ_bott = Γ₁ ⊗ Γₙ`. -/
def globalGrading (Γ1 : Endomorphism E) (Γn : Endomorphism F) :
    Endomorphism (E ⊗[ℝ] F) :=
  TensorProduct.map Γ1 Γn

/-- Analytical index of the Bott-Dirac operator with chosen grading pair. -/
noncomputable def bottAnalyticalIndex
    [FiniteDimensional ℝ (E ⊗[ℝ] F)]
    (D1 Γ1 : Endomorphism E) (Dn Γn : Endomorphism F) : ℤ :=
  analyticalIndex (bottDirac D1 Γ1 Dn) (globalGrading Γ1 Γn)

/-- `Cl(1,1)` specialization of the global grading. -/
noncomputable def cl11GlobalGrading (Γn : Endomorphism F) :
    Endomorphism (DoubledSpace E ⊗[ℝ] F) :=
  globalGrading (cl11Grading (E := E)) Γn

/-- `Cl(1,1)` specialization of the Bott analytical index. -/
noncomputable def cl11BottAnalyticalIndex
    [FiniteDimensional ℝ (DoubledSpace E ⊗[ℝ] F)]
    (Dn Γn : Endomorphism F) : ℤ :=
  analyticalIndex
    (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn)
    (cl11GlobalGrading (E := E) Γn)

end Bott

section Laplacian

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Vanishing condition for the split Bott Laplacian term. -/
def Cl11BottLaplacianZero (Dn : Endomorphism F) : Prop :=
  cl11BottLaplacian (E := E) Dn = 0

/-- Theorem `cl11_bottDirac_sq_eq_zero_of_laplacian_zero`. -/
theorem cl11_bottDirac_sq_eq_zero_of_laplacian_zero
    (Dn : Endomorphism F)
    (hZero : Cl11BottLaplacianZero (E := E) Dn) :
    (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn).comp
      (bottDirac (cl11DiracSeed (E := E)) (cl11Grading (E := E)) Dn) = 0 := by
  exact (cl11_bottDirac_sq_eq_cl11BottLaplacian (E := E) (F := F) (Dn := Dn)).trans hZero

end Laplacian

section CoupledInvariant

variable (n : Nat)
variable {X V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/--
Coupled invariant package:
thermodynamic Sinkhorn control, scalar-Ricci fixed-point collapse, and
analytical index invariance along a Dirac/grading family.
-/
def SinkhornRicciIndexInvariant
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V) : Prop :=
  (∀ k : Nat, ∀ label : PermMode n → CliffordLabel,
    trajectoryLyapunovNext n T.traj k ≤ trajectoryLyapunov n T.traj k ∧
      trajectorySelectedRoutingEpsilon n T (k + 1) label ≤ 1)
    ∧ (∀ s : ℝ, flow s = 0)
    ∧ IndexInvariantAlong D Γ

/--
Canonical constructor for the coupled invariant package from its three proved
components.
-/
theorem sinkhornRicciIndexInvariant_of_components
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (hSinkhorn : ∀ k : Nat, ∀ label : PermMode n → CliffordLabel,
      trajectoryLyapunovNext n T.traj k ≤ trajectoryLyapunov n T.traj k ∧
        trajectorySelectedRoutingEpsilon n T (k + 1) label ≤ 1)
    (hRicciZero : ∀ s : ℝ, flow s = 0)
    (hIndex : IndexInvariantAlong D Γ) :
    SinkhornRicciIndexInvariant n T flow D Γ := by
  exact ⟨hSinkhorn, hRicciZero, hIndex⟩

/--
Derived constructor using modular-flow / Clifford-bundle transport hypotheses
for the chiral slices.
-/
theorem sinkhornRicciIndexInvariant_of_modularCliffordTransport_state_hypotheses
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    {ι : Type*}
    (σ : ℝ → Endomorphism V)
    (clAct : ι → Endomorphism V)
    (unit : ι)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := X) flow)
    (hFixed : ∀ s : ℝ, scalarRicciBetaFunction (E := X) flow s = 0)
    (hTrans :
      ChiralSliceModularCliffordTransportAlong (D := D) (Γ := Γ) σ clAct unit) :
    SinkhornRicciIndexInvariant n T flow D Γ := by
  refine sinkhornRicciIndexInvariant_of_components
    (n := n) (T := T) (flow := flow) (D := D) (Γ := Γ)
    ?_ ?_ ?_
  · intro k label
    exact sinkhorn_dynamics_step_control (n := n) T k label
  · exact normalizedKaehlerRicci_fixedpoint_eq_zero
      (E := X) flow hNorm hFixed
  · exact indexInvariantAlong_of_modularCliffordTransport
      (D := D) (Γ := Γ) (σ := σ) (clAct := clAct) (unit := unit) hTrans

/--
Derived constructor using primitive flow-conjugacy hypotheses:
the Dirac/grading family is transported to baseline by linear equivalences.
-/
theorem sinkhornRicciIndexInvariant_of_conjugacy_state_hypotheses
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (eFlow : ℝ → V ≃ₗ[ℝ] V)
    (hNorm : SatisfiesNormalizedKaehlerRicciFlow (E := X) flow)
    (hFixed : ∀ s : ℝ, scalarRicciBetaFunction (E := X) flow s = 0)
    (hConj : ChiralConjugacyAlong D Γ eFlow) :
    SinkhornRicciIndexInvariant n T flow D Γ := by
  refine sinkhornRicciIndexInvariant_of_components
    (n := n) (T := T) (flow := flow) (D := D) (Γ := Γ)
    ?_ ?_ ?_
  · intro k label
    exact sinkhorn_dynamics_step_control (n := n) T k label
  · exact normalizedKaehlerRicci_fixedpoint_eq_zero
      (E := X) flow hNorm hFixed
  · exact indexInvariantAlong_of_conjugacy
      (D := D) (Γ := Γ) (eFlow := eFlow) hConj

end CoupledInvariant

section KMSCapstone

variable (n : Nat)
variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/--
Explicit thermodynamic KMS capstone package:
exact KMS closure at each next step.
-/
def SinkhornKMSCapstone
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ) : Prop :=
  SinkhornKMSClosure n T K ω β

/-- Lemma `SinkhornKMSCapstone`. -/
lemma SinkhornKMSCapstone.kmsState
    (T : SinkhornTrajectory n)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hCap : SinkhornKMSCapstone n T K ω β) :
    SinkhornKMSClosure n T K ω β :=
  hCap

/--
Constructive iterate specialization from closure (primary closure-first form).
-/
theorem sinkhornIterate_sinkhornKMSCapstone_of_closure
    (M0 : SinkhornMatrix n)
    (hrow : ∀ M : SinkhornMatrix n, HasPositiveRowSums n M)
    (hcol : ∀ M : SinkhornMatrix n, HasPositiveColSums n M)
    (K : AlgebraEnd F)
    (ω : Nat → AlgebraEnd F →L[ℝ] ℝ)
    (β : ℝ)
    (hClosure : SinkhornKMSClosure n
      (sinkhornIterateTrajectory (n := n) M0 hrow hcol) K ω β) :
    SinkhornKMSCapstone n (sinkhornIterateTrajectory (n := n) M0 hrow hcol) K ω β := by
  exact hClosure

end KMSCapstone

section FullCapstone

variable (n : Nat)
variable {X V Fth : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Fth] [InnerProductSpace ℝ Fth] [CompleteSpace Fth]

/--
Full capstone package:
thermodynamic/KMS control + geometric fixed-point collapse + index invariance.
-/
def FullThermoGeoIndexCapstone
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ) : Prop :=
  SinkhornRicciIndexInvariant n T flow D Γ ∧
    SinkhornKMSCapstone n T.traj K ω β

/--
Canonical constructor for the full capstone package from the two state-level
components.
-/
theorem fullThermoGeoIndexCapstone_of_states
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ)
    (hGeoAlg : SinkhornRicciIndexInvariant n T flow D Γ)
    (hClosure : SinkhornKMSClosure n T.traj K ω β) :
    FullThermoGeoIndexCapstone n T flow D Γ K ω β := by
  exact ⟨hGeoAlg, hClosure⟩

/-- Lemma `FullThermoGeoIndexCapstone`. -/
lemma FullThermoGeoIndexCapstone.geometricAlgebraicState
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ)
    (hCap : FullThermoGeoIndexCapstone n T flow D Γ K ω β) :
    SinkhornRicciIndexInvariant n T flow D Γ :=
  hCap.1

/-- Lemma `FullThermoGeoIndexCapstone`. -/
lemma FullThermoGeoIndexCapstone.thermodynamicKMSState
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ)
    (hCap : FullThermoGeoIndexCapstone n T flow D Γ K ω β) :
    SinkhornKMSClosure n T.traj K ω β :=
  hCap.2

end FullCapstone

section UnifiedNaming

variable (n : Nat)
variable {X V Fth : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup Fth] [InnerProductSpace ℝ Fth] [CompleteSpace Fth]

/--
Unified thermodynamic state naming used by higher-level synthesis modules.
-/
abbrev ThermodynamicKMSState
    (T : DoublyStochasticSinkhornTrajectory n)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ) : Prop :=
  SinkhornKMSClosure n T.traj K ω β

/--
Unified geometric-algebraic state naming used by higher-level synthesis modules.
-/
abbrev GeometricAlgebraicState
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V) : Prop :=
  SinkhornRicciIndexInvariant n T flow D Γ

/--
Unified full capstone naming used by higher-level synthesis modules.
-/
abbrev ThermoGeoIndexCapstoneState
    (T : DoublyStochasticSinkhornTrajectory n)
    (flow : ScalarRicciFlow X)
    (D Γ : ℝ → Endomorphism V)
    (K : AlgebraEnd Fth)
    (ω : Nat → AlgebraEnd Fth →L[ℝ] ℝ)
    (β : ℝ) : Prop :=
  FullThermoGeoIndexCapstone n T flow D Γ K ω β

end UnifiedNaming

end InfoGeometry.Canonical.AnalyticalIndex
