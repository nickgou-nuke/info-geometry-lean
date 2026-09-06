import InfoGeometry.Quantum.KitaevChain
import InfoGeometry.Quantum.RealMajorana
import InfoGeometry.Meta.Architecture
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# InfoGeometry.Quantum.BulkBoundary

Finite-dimensional algebraic bulk-boundary core for the real Majorana scaffold.

This file isolates the linear-algebraic mechanism behind boundary zero modes:

* a polarization-odd operator swaps the plus and minus sectors;
* therefore it restricts to maps `plus → minus` and `minus → plus`;
* if these sectors have different finite dimensions, the operator is not injective;
* hence its kernel is nontrivial.

The chain-level bridge below is stated with explicit hypotheses linking
`topologicalIndexZ2` to a polarization-dimension mismatch and oddness.
No axioms are introduced.
-/

namespace InfoGeometry.Quantum.BulkBoundary

open InfoGeometry.Quantum.KitaevChain
open InfoGeometry.Quantum.RealMajorana

set_option linter.unusedSectionVars false

section Core

variable {S : Type*}
variable [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]

/-- Endomorphisms on the real Majorana carrier. -/
abbrev EndS := S →L[ℝ] S

variable (M : RealMajoranaDatum (S := S))

/-- A zero mode means the kernel is nontrivial. -/
def HasZeroMode (H : EndS (S := S)) : Prop :=
  H.toLinearMap.ker ≠ ⊥

/-! The operator-level zero-mode proposition is the native existential
statement: a nonzero vector lies in the kernel. -/
@[rep_depth operator]
def OperatorZeroMode
    (H : EndS (S := S)) : Prop :=
  ∃ v : S, H v = 0 ∧ v ≠ 0

/-- Oddness with respect to a chosen polarization involution. -/
def PolarizationOdd
    (P0 : KPolarization (S := S) M)
    (H : EndS (S := S)) : Prop :=
  P0.P.comp H = -(H.comp P0.P)

namespace PolarizationOdd

variable {M}

omit [CompleteSpace S] in
/-- Zero map is polarization-odd. -/
lemma zero
    (P0 : KPolarization (S := S) M) :
    PolarizationOdd (M := M) P0 (0 : EndS (S := S)) := by
  unfold PolarizationOdd
  simp

omit [CompleteSpace S] in
/-- Oddness is closed under addition. -/
lemma add
    (P0 : KPolarization (S := S) M)
    {H1 H2 : EndS (S := S)}
    (h1 : PolarizationOdd (M := M) P0 H1)
    (h2 : PolarizationOdd (M := M) P0 H2) :
    PolarizationOdd (M := M) P0 (H1 + H2) := by
  unfold PolarizationOdd at h1 h2 ⊢
  calc
    P0.P.comp (H1 + H2)
        = P0.P.comp H1 + P0.P.comp H2 := by
            simp [ContinuousLinearMap.comp_add]
    _ = -(H1.comp P0.P) + -(H2.comp P0.P) := by
        simp [h1, h2]
    _ = -((H1 + H2).comp P0.P) := by
          ext x
          simp [ContinuousLinearMap.add_comp, add_comm]

    omit [CompleteSpace S] in
/-- Oddness is closed under real scaling. -/
lemma smul
    (P0 : KPolarization (S := S) M)
    (a : ℝ)
    {H : EndS (S := S)}
    (hodd : PolarizationOdd (M := M) P0 H) :
    PolarizationOdd (M := M) P0 (a • H) := by
  unfold PolarizationOdd at hodd ⊢
  calc
    P0.P.comp (a • H) = a • (P0.P.comp H) := by
      simp
    _ = a • (-(H.comp P0.P)) := by rw [hodd]
    _ = -(a • (H.comp P0.P)) := by simp
    _ = -((a • H).comp P0.P) := by
      simp [ContinuousLinearMap.smul_comp]

/-- A polarization-odd operator sends the `+` sector into the `-` sector. -/
lemma maps_plus_to_minus
    (P0 : KPolarization (S := S) M)
    {H : EndS (S := S)}
    (hodd : PolarizationOdd (M := M) P0 H)
    {x : S} (hx : x ∈ P0.plus) :
    H x ∈ P0.minus := by
  rw [KPolarization.mem_plus_iff] at hx
  rw [KPolarization.mem_minus_iff]
  have h := congrArg (fun f : EndS (S := S) => f x) hodd
  calc
    P0.P (H x) = -(H (P0.P x)) := by
      simpa [PolarizationOdd, ContinuousLinearMap.comp_apply] using h
    _ = -(H x) := by
      simp [hx]

/-- A polarization-odd operator sends the `-` sector into the `+` sector. -/
lemma maps_minus_to_plus
    (P0 : KPolarization (S := S) M)
    {H : EndS (S := S)}
    (hodd : PolarizationOdd (M := M) P0 H)
    {x : S} (hx : x ∈ P0.minus) :
    H x ∈ P0.plus := by
  rw [KPolarization.mem_minus_iff] at hx
  rw [KPolarization.mem_plus_iff]
  have h := congrArg (fun f : EndS (S := S) => f x) hodd
  calc
    P0.P (H x) = -(H (P0.P x)) := by
      simpa [PolarizationOdd, ContinuousLinearMap.comp_apply] using h
    _ = -(H (-x)) := by
      simp [hx]
    _ = H x := by
      simp

/-- Restriction of `H` to a map `plus → minus`. -/
noncomputable def toMinus
    (P0 : KPolarization (S := S) M)
    (H : EndS (S := S))
    (hodd : PolarizationOdd (M := M) P0 H) :
    P0.plus →ₗ[ℝ] P0.minus where
  toFun x := ⟨H x, maps_plus_to_minus (M := M) P0 hodd x.property⟩
  map_add' x y := by
    ext
    simp
  map_smul' r x := by
    ext
    simp

/-- Restriction of `H` to a map `minus → plus`. -/
noncomputable def toPlus
    (P0 : KPolarization (S := S) M)
    (H : EndS (S := S))
    (hodd : PolarizationOdd (M := M) P0 H) :
    P0.minus →ₗ[ℝ] P0.plus where
  toFun x := ⟨H x, maps_minus_to_plus (M := M) P0 hodd x.property⟩
  map_add' x y := by
    ext
    simp
  map_smul' r x := by
    ext
    simp

end PolarizationOdd

omit [CompleteSpace S] in
/-- A nontrivial kernel yields an explicit nonzero zero-mode property. -/
theorem exists_zeroMode_of_hasZeroMode
    {H : EndS (S := S)}
  (hH : HasZeroMode (S := S) H) :
    ∃ v : S, H v = 0 ∧ v ≠ 0 := by
  unfold HasZeroMode at hH
  rcases (H.toLinearMap.ker).ne_bot_iff.mp hH with ⟨v, hv, hv0⟩
  refine ⟨v, ?_, hv0⟩
  simpa using hv

/-- An operator-level zero-mode property certifies a nontrivial kernel. -/
theorem hasZeroMode_of_operatorZeroModeWitness
    {H : EndS (S := S)}
    (W : OperatorZeroMode (S := S) H) :
    HasZeroMode (S := S) H := by
  rcases W with ⟨v, hv, hv0⟩
  unfold HasZeroMode
  refine (H.toLinearMap.ker).ne_bot_iff.mpr ?_
  refine ⟨v, ?_, hv0⟩
  simpa [LinearMap.mem_ker] using hv

/-- Read the kernel property directly from an operator-level zero-mode packet. -/
theorem exists_zeroMode_of_operatorZeroModeWitness
    {H : EndS (S := S)}
    (W : OperatorZeroMode (S := S) H) :
    ∃ v : S, H v = 0 ∧ v ≠ 0 := by
  exact W

/--
Finite-dimensional algebraic bulk-boundary core:

If `H` is odd with respect to a polarization involution and the plus/minus sectors
have different dimensions, then `H` has a nontrivial kernel.
-/
theorem hasZeroMode_of_dim_mismatch
    [FiniteDimensional ℝ S]
    (P0 : KPolarization (S := S) M)
    (H : EndS (S := S))
    (hodd : PolarizationOdd (M := M) P0 H)
    (hdim :
      Module.finrank ℝ P0.plus
        ≠ Module.finrank ℝ P0.minus) :
    HasZeroMode (S := S) H := by
  by_contra hNoZero
  unfold HasZeroMode at hNoZero
  have hker : H.toLinearMap.ker = ⊥ := by
    simpa using hNoZero
  have hHinj : Function.Injective H.toLinearMap :=
    LinearMap.ker_eq_bot.mp hker

  let Hpm : P0.plus →ₗ[ℝ] P0.minus :=
    PolarizationOdd.toMinus (M := M) P0 H hodd
  let Hmp : P0.minus →ₗ[ℝ] P0.plus :=
    PolarizationOdd.toPlus (M := M) P0 H hodd

  have hHpm_inj : Function.Injective Hpm := by
    intro x y hxy
    apply Subtype.ext
    apply hHinj
    exact congrArg Subtype.val hxy

  have hHmp_inj : Function.Injective Hmp := by
    intro x y hxy
    apply Subtype.ext
    apply hHinj
    exact congrArg Subtype.val hxy

  have hle₁ :
      Module.finrank ℝ P0.plus
        ≤ Module.finrank ℝ P0.minus := by
    simpa [Hpm] using
      LinearMap.finrank_le_finrank_of_injective (f := Hpm) hHpm_inj

  have hle₂ :
      Module.finrank ℝ P0.minus
        ≤ Module.finrank ℝ P0.plus := by
    simpa [Hmp] using
      LinearMap.finrank_le_finrank_of_injective (f := Hmp) hHmp_inj

  exact hdim (le_antisymm hle₁ hle₂)

/-- Explicit property form of `hasZeroMode_of_dim_mismatch`. -/
theorem exists_zeroMode_of_dim_mismatch
    [FiniteDimensional ℝ S]
    (P0 : KPolarization (S := S) M)
    (H : EndS (S := S))
    (hodd : PolarizationOdd (M := M) P0 H)
    (hdim :
      Module.finrank ℝ P0.plus
        ≠ Module.finrank ℝ P0.minus) :
    ∃ v : S, H v = 0 ∧ v ≠ 0 := by
  exact exists_zeroMode_of_hasZeroMode (S := S)
    (H := H)
    (hasZeroMode_of_dim_mismatch (M := M) P0 H hodd hdim)

/--
Bogoliubov conjugation preserves nontrivial kernel: any zero mode of `H`
pushes forward to a zero mode of `B ∘ H ∘ B⁻¹`.
-/
theorem hasZeroMode_conjugate_of_hasZeroMode
    (T : RealBogoliubovTransform (S := S) M)
    {H : EndS (S := S)}
    (hH : HasZeroMode (S := S) H) :
    HasZeroMode (S := S) (T.B.comp (H.comp T.Binv)) := by
  rcases exists_zeroMode_of_hasZeroMode (S := S) (H := H) hH with ⟨v, hv, hv0⟩
  unfold HasZeroMode
  intro hbot
  have hBv_ne : T.B v ≠ 0 := by
    intro hBv
    apply hv0
    have h := congrArg T.Binv hBv
    simpa using h
  have hKerEq :
      (T.B.comp (H.comp T.Binv)) (T.B v) = 0 := by
    calc
      (T.B.comp (H.comp T.Binv)) (T.B v)
          = T.B (H (T.Binv (T.B v))) := by
              simp [ContinuousLinearMap.comp_apply]
      _ = T.B (H v) := by simp
      _ = 0 := by simp [hv]
  have hKer :
      T.B v ∈ (T.B.comp (H.comp T.Binv)).toLinearMap.ker := by
    simpa using hKerEq
  have : T.B v ∈ (⊥ : Submodule ℝ S) := by
    rw [← hbot]
    exact hKer
  have hBvZero : T.B v = 0 := by
    simpa using this
  exact hBv_ne hBvZero

/--
Explicit property form of `hasZeroMode_conjugate_of_hasZeroMode`.
-/
theorem exists_zeroMode_of_hasZeroMode_conjugate
    (T : RealBogoliubovTransform (S := S) M)
    {H : EndS (S := S)}
    (hH : HasZeroMode (S := S) H) :
    ∃ v : S, (T.B.comp (H.comp T.Binv)) v = 0 ∧ v ≠ 0 := by
  exact exists_zeroMode_of_hasZeroMode (S := S)
    (H := T.B.comp (H.comp T.Binv))
    (hasZeroMode_conjugate_of_hasZeroMode (M := M) (T := T) hH)

end Core

section ChainBridge

variable {S : Type*}
variable [NormedAddCommGroup S] [InnerProductSpace ℝ S] [CompleteSpace S]
variable [FiniteDimensional ℝ S]

variable (M : RealMajoranaDatum (S := S))
variable (P0 : KPolarization (S := S) M)

/-- Concrete particle-hole symmetry predicate for one chain operator channel. -/
abbrev ParticleHoleSymmetric
    (H : EndS (S := S)) : Prop :=
  PolarizationOdd (M := M) P0 H

/--
Concrete finite open-chain operator from local channels:
Pfaffian-weighted finite sum over cells.
-/
noncomputable def globalChainOperatorFromOpenChain
    (localOp : KitaevCell → EndS (S := S)) :
    List KitaevCell → EndS (S := S)
  | [] => 0
  | c :: cs => c.pfaffian • localOp c + globalChainOperatorFromOpenChain localOp cs

omit [CompleteSpace S] [FiniteDimensional ℝ S] in
@[simp] lemma globalChainOperatorFromOpenChain_nil
    (localOp : KitaevCell → EndS (S := S)) :
    globalChainOperatorFromOpenChain (S := S) localOp [] = 0 := rfl

omit [CompleteSpace S] [FiniteDimensional ℝ S] in
@[simp] lemma globalChainOperatorFromOpenChain_cons
    (localOp : KitaevCell → EndS (S := S))
    (c : KitaevCell)
    (cs : List KitaevCell) :
    globalChainOperatorFromOpenChain (S := S) localOp (c :: cs)
      = c.pfaffian • localOp c
          + globalChainOperatorFromOpenChain (S := S) localOp cs := rfl

omit [CompleteSpace S] [FiniteDimensional ℝ S] in
/--
If each local open-chain channel is particle-hole symmetric, then the concrete
global open-chain operator is polarization-odd.
-/
theorem polarizationOdd_globalChainOperatorFromOpenChain
    (localOp : KitaevCell → EndS (S := S))
    (hPHS : ∀ c : KitaevCell,
      ParticleHoleSymmetric (M := M) (P0 := P0) (localOp c))
    (chain : List KitaevCell) :
    PolarizationOdd (M := M) P0
      (globalChainOperatorFromOpenChain (S := S) localOp chain) := by
  induction chain with
  | nil =>
      simpa [globalChainOperatorFromOpenChain] using
        (PolarizationOdd.zero (M := M) (P0 := P0))
  | cons c cs ih =>
      have hhead : PolarizationOdd (M := M) P0 (c.pfaffian • localOp c) :=
        PolarizationOdd.smul (M := M) (P0 := P0) c.pfaffian
          (hPHS c)
      have htail :
          PolarizationOdd (M := M) P0
            (globalChainOperatorFromOpenChain (S := S) localOp cs) :=
        ih
      simpa [globalChainOperatorFromOpenChain] using
        (PolarizationOdd.add (M := M) (P0 := P0) hhead htail)

/-- Index-1 in `ℤ₂` forces negative sign-phase in this finite sign model. -/
theorem topologicalIndex_eq_neg_one_of_topologicalIndexZ2_eq_one
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1) :
    topologicalIndex chain = -1 := by
  unfold topologicalIndexZ2 signTypeToZ2 at hTopo
  rcases SignType.trichotomy (topologicalIndex chain) with hneg | hzero | hpos
  · simpa using hneg
  · exfalso
    simp [hzero] at hTopo
  · exfalso
    simp [hpos] at hTopo

omit [CompleteSpace S] [FiniteDimensional ℝ S] in
/--
Dimension mismatch derived directly from `topologicalIndexZ2 = 1` via the
sign-phase branch rule.
-/
theorem dim_mismatch_of_topologicalIndexZ2_eq_one
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hNegPhaseDimMismatch :
      topologicalIndex chain = -1 →
        Module.finrank ℝ P0.plus
          ≠ Module.finrank ℝ P0.minus) :
    Module.finrank ℝ P0.plus
      ≠ Module.finrank ℝ P0.minus := by
  apply hNegPhaseDimMismatch
  exact topologicalIndex_eq_neg_one_of_topologicalIndexZ2_eq_one
    (chain := chain) hTopo

/--
Boundary-localized open-chain property: there are nonzero zero modes in both
polarization sectors for the concrete Pfaffian-weighted chain operator.
-/
def BoundaryLocalizedZeroModePair
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell) : Prop :=
  ∃ ψplus ψminus : S,
    ψplus ≠ 0 ∧ ψminus ≠ 0
      ∧ ψplus ∈ P0.plus ∧ ψminus ∈ P0.minus
      ∧ (globalChainOperatorFromOpenChain (S := S) localOp chain) ψplus = 0
      ∧ (globalChainOperatorFromOpenChain (S := S) localOp chain) ψminus = 0

/- The existing existential predicate is the owner; no second proof package is
   introduced for the same pair of zero-mode witnesses. -/
abbrev BoundaryLocalizedZeroMode
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell) : Prop :=
  BoundaryLocalizedZeroModePair (M := M) (P0 := P0) localOp chain

omit [FiniteDimensional ℝ S] in
/--
Forget the polarization support and keep only the plus-sector operator kernel
property.
-/
lemma operatorZeroMode_of_boundaryLocalizedPlus
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (W : BoundaryLocalizedZeroMode (M := M) (P0 := P0) localOp chain) :
    OperatorZeroMode
      (S := S)
      (globalChainOperatorFromOpenChain (S := S) localOp chain) :=
  by
    classical
    let hPair1 := Classical.choose_spec W
    let hPair2 := Classical.choose_spec hPair1
    exact ⟨Classical.choose W, hPair2.2.2.2.2.1, hPair2.1⟩

omit [FiniteDimensional ℝ S] in
/--
Forget the polarization support and keep only the minus-sector operator kernel
property.
-/
lemma operatorZeroMode_of_boundaryLocalizedMinus
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (W : BoundaryLocalizedZeroMode (M := M) (P0 := P0) localOp chain) :
    OperatorZeroMode
      (S := S)
      (globalChainOperatorFromOpenChain (S := S) localOp chain) :=
  by
    classical
    let hPair1 := Classical.choose_spec W
    let hPair2 := Classical.choose_spec hPair1
    exact ⟨Classical.choose hPair1, hPair2.2.2.2.2.2, hPair2.2.1⟩

/--
Any boundary-localized plus/minus zero-mode property already certifies a
dimension-agnostic operator zero mode.
-/
theorem hasZeroMode_of_boundaryLocalizedZeroModeWitness
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (W : BoundaryLocalizedZeroMode (M := M) (P0 := P0) localOp chain) :
    HasZeroMode
      (S := S)
      (globalChainOperatorFromOpenChain (S := S) localOp chain) := by
  exact hasZeroMode_of_operatorZeroModeWitness
    (S := S)
    (operatorZeroMode_of_boundaryLocalizedPlus
      (M := M) (P0 := P0) localOp chain W)

/--
Boundary-localized witnesses give an explicit nonzero kernel vector without any
finite-dimensional argument.
-/
theorem exists_zeroMode_of_boundaryLocalizedZeroModeWitness
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (W : BoundaryLocalizedZeroMode (M := M) (P0 := P0) localOp chain) :
    ∃ v : S,
      (globalChainOperatorFromOpenChain (S := S) localOp chain) v = 0 ∧ v ≠ 0 := by
  exact exists_zeroMode_of_operatorZeroModeWitness
    (S := S)
    (operatorZeroMode_of_boundaryLocalizedPlus
      (M := M) (P0 := P0) localOp chain W)

/--
Boundary-localization bridge data for deriving dimension mismatch from
negative sign phase.
-/
abbrev BoundaryLocalizationBridge
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell) : Prop :=
  (topologicalIndex chain = -1 →
      BoundaryLocalizedZeroModePair (M := M) (P0 := P0) localOp chain) ∧
  (BoundaryLocalizedZeroModePair (M := M) (P0 := P0) localOp chain →
      Module.finrank ℝ P0.plus ≠ Module.finrank ℝ P0.minus)

/--
Simplified boundary model for turnkey usage:
1) negative phase implies a boundary-localized zero-mode pair,
2) such a pair forces polarization-dimension mismatch.
-/
abbrev SimplifiedBoundaryModel
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell) : Prop :=
  (topologicalIndex chain = -1 →
      BoundaryLocalizedZeroModePair (M := M) (P0 := P0) localOp chain) ∧
  (BoundaryLocalizedZeroModePair (M := M) (P0 := P0) localOp chain →
      Module.finrank ℝ P0.plus ≠ Module.finrank ℝ P0.minus)

theorem exists_zeroMode_of_simplifiedBoundaryModel_of_negativePhase
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hNeg : topologicalIndex chain = -1)
    (hSimple : SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain) :
    ∃ v : S,
      (globalChainOperatorFromOpenChain (S := S) localOp chain) v = 0 ∧
        v ≠ 0 := by
  rcases hSimple.1 hNeg with
    ⟨ψplus, ψminus, hψplus, hψminus, hψplus_mem, hψminus_mem,
      hψplus_zero, hψminus_zero⟩
  exact ⟨ψplus, hψplus_zero, hψplus⟩

theorem exists_zeroMode_of_simplifiedBoundaryModel_of_topologicalIndexZ2_eq_one
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hSimple : SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain) :
    ∃ v : S,
      (globalChainOperatorFromOpenChain (S := S) localOp chain) v = 0 ∧
        v ≠ 0 := by
  exact exists_zeroMode_of_simplifiedBoundaryModel_of_negativePhase
    (M := M) (P0 := P0) localOp chain
    (topologicalIndex_eq_neg_one_of_topologicalIndexZ2_eq_one chain hTopo)
    hSimple

theorem hasZeroMode_of_simplifiedBoundaryModel_of_negativePhase
    [FiniteDimensional ℝ S]
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hNeg : topologicalIndex chain = -1)
    (hSimple : SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain) :
    HasZeroMode
      (S := S) (globalChainOperatorFromOpenChain (S := S) localOp chain) := by
  unfold HasZeroMode
  refine (ContinuousLinearMap.toLinearMap
      (globalChainOperatorFromOpenChain (S := S) localOp chain)).ker.ne_bot_iff.mpr ?_
  rcases exists_zeroMode_of_simplifiedBoundaryModel_of_negativePhase
      (M := M) (P0 := P0) localOp chain hNeg hSimple with ⟨v, hv, hv0⟩
  exact ⟨v, by simpa [LinearMap.mem_ker] using hv, hv0⟩

theorem hasZeroMode_of_simplifiedBoundaryModel_of_topologicalIndexZ2_eq_one
    [FiniteDimensional ℝ S]
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hSimple : SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain) :
    HasZeroMode
      (S := S) (globalChainOperatorFromOpenChain (S := S) localOp chain) := by
  exact hasZeroMode_of_simplifiedBoundaryModel_of_negativePhase
    (M := M) (P0 := P0) localOp chain
    (topologicalIndex_eq_neg_one_of_topologicalIndexZ2_eq_one chain hTopo)
    hSimple

theorem exists_zeroMode_of_boundaryLocalizationBridge_of_negativePhase
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hNeg : topologicalIndex chain = -1)
    (hBridge : BoundaryLocalizationBridge
      (M := M) (P0 := P0) localOp chain) :
    ∃ v : S,
      (globalChainOperatorFromOpenChain (S := S) localOp chain) v = 0 ∧
        v ≠ 0 := by
  rcases hBridge.1 hNeg with
    ⟨ψplus, ψminus, hψplus, hψminus, hψplus_mem, hψminus_mem,
      hψplus_zero, hψminus_zero⟩
  exact ⟨ψplus, hψplus_zero, hψplus⟩

/--
Structure-valued boundary property extracted directly from a simplified boundary
model in the negative phase.
-/
@[rep_depth krein]
noncomputable def boundaryLocalizedZeroModeWitness_of_negativePhase_of_simplifiedBoundaryModel
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hNeg : topologicalIndex chain = -1)
    (hSimple : SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain) :
    BoundaryLocalizedZeroMode (M := M) (P0 := P0) localOp chain :=
  hSimple.1 hNeg

/--
Structure-valued boundary property extracted from the turnkey `topologicalIndexZ2`
phase property and a simplified boundary model.
-/
@[rep_depth krein]
noncomputable def boundaryLocalizedZeroModeWitness_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hSimple : SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain) :
    BoundaryLocalizedZeroMode (M := M) (P0 := P0) localOp chain := by
  have hNeg : topologicalIndex chain = -1 :=
    topologicalIndex_eq_neg_one_of_topologicalIndexZ2_eq_one
      (chain := chain) hTopo
  exact boundaryLocalizedZeroModeWitness_of_negativePhase_of_simplifiedBoundaryModel
    (M := M) (P0 := P0) localOp chain hNeg hSimple

/--
Dimension-agnostic operator zero-mode property extracted from a simplified
boundary model in the negative phase.
-/
@[rep_depth operator]
noncomputable def operatorZeroModeWitness_of_negativePhase_of_simplifiedBoundaryModel
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hNeg : topologicalIndex chain = -1)
    (hSimple : SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain) :
    OperatorZeroMode
      (S := S)
      (globalChainOperatorFromOpenChain (S := S) localOp chain) :=
operatorZeroMode_of_boundaryLocalizedPlus
    (M := M) (P0 := P0) localOp chain
    (boundaryLocalizedZeroModeWitness_of_negativePhase_of_simplifiedBoundaryModel
      (M := M) (P0 := P0) localOp chain hNeg hSimple)

/--
Dimension-agnostic operator zero-mode property extracted from the turnkey
`topologicalIndexZ2 = 1` phase property and a simplified boundary model.
-/
@[rep_depth operator]
noncomputable def operatorZeroModeWitness_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hSimple : SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain) :
    OperatorZeroMode
      (S := S)
      (globalChainOperatorFromOpenChain (S := S) localOp chain) :=
  operatorZeroMode_of_boundaryLocalizedPlus
    (M := M) (P0 := P0) localOp chain
    (boundaryLocalizedZeroModeWitness_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel
      (M := M) (P0 := P0) localOp chain hTopo hSimple)

/--
Dimension-agnostic bulk-boundary consequence from a simplified boundary model:
the operator has a nontrivial kernel directly from the explicit boundary
zero-mode property, without passing through a finite-dimensional mismatch
argument.
-/
theorem hasSurfaceZeroMode_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hSimple : SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain) :
    HasZeroMode
      (S := S)
      (globalChainOperatorFromOpenChain (S := S) localOp chain) := by
  exact hasZeroMode_of_operatorZeroModeWitness
    (S := S)
    (operatorZeroModeWitness_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel
      (M := M) (P0 := P0) localOp chain hTopo hSimple)

/--
Dimension-agnostic explicit kernel vector extracted from a simplified boundary
model in the `topologicalIndexZ2 = 1` phase.
-/
theorem exists_zeroMode_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hSimple : SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain) :
    ∃ v : S,
      (globalChainOperatorFromOpenChain (S := S) localOp chain) v = 0 ∧ v ≠ 0 := by
  exact exists_zeroMode_of_operatorZeroModeWitness
    (S := S)
    (operatorZeroModeWitness_of_topologicalIndexZ2_eq_one_of_simplifiedBoundaryModel
      (M := M) (P0 := P0) localOp chain hTopo hSimple)

omit [FiniteDimensional ℝ S] in
/--
If a real Bogoliubov transform preserves the chosen polarization, then a
boundary-localized `(plus/minus)` zero-mode pair is transported to a new
boundary-localized pair for the conjugated open-chain operator.
-/
theorem boundaryLocalizedZeroModePair_under_bogoliubov_of_preservesPolarization
    (T : RealBogoliubovTransform (S := S) M)
    (hpres : T.preservesPolarization P0)
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hPair : BoundaryLocalizedZeroModePair (M := M) (P0 := P0) localOp chain) :
    ∃ ψplus ψminus : S,
      ψplus ≠ 0 ∧ ψminus ≠ 0
        ∧ ψplus ∈ P0.plus ∧ ψminus ∈ P0.minus
        ∧ (T.B.comp
            ((globalChainOperatorFromOpenChain (S := S) localOp chain).comp T.Binv)) ψplus = 0
        ∧ (T.B.comp
            ((globalChainOperatorFromOpenChain (S := S) localOp chain).comp T.Binv)) ψminus = 0 := by
  rcases hPair with ⟨ψplus, ψminus, hψplus0, hψminus0, hplus, hminus, hkerPlus, hkerMinus⟩
  refine ⟨T.B ψplus, T.B ψminus, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hzero
    apply hψplus0
    have h := congrArg T.Binv hzero
    simpa using h
  · intro hzero
    apply hψminus0
    have h := congrArg T.Binv hzero
    simpa using h
  · exact T.map_plus_of_preserves (P0 := P0) hpres ψplus hplus
  · exact T.map_minus_of_preserves (P0 := P0) hpres ψminus hminus
  · calc
      (T.B.comp
          ((globalChainOperatorFromOpenChain (S := S) localOp chain).comp T.Binv)) (T.B ψplus)
          = T.B
              ((globalChainOperatorFromOpenChain (S := S) localOp chain)
                (T.Binv (T.B ψplus))) := by
                  simp [ContinuousLinearMap.comp_apply]
      _ = T.B
            ((globalChainOperatorFromOpenChain (S := S) localOp chain) ψplus) := by
              simp
      _ = 0 := by simp [hkerPlus]
  · calc
      (T.B.comp
          ((globalChainOperatorFromOpenChain (S := S) localOp chain).comp T.Binv)) (T.B ψminus)
          = T.B
              ((globalChainOperatorFromOpenChain (S := S) localOp chain)
                (T.Binv (T.B ψminus))) := by
                  simp [ContinuousLinearMap.comp_apply]
      _ = T.B
            ((globalChainOperatorFromOpenChain (S := S) localOp chain) ψminus) := by
              simp
      _ = 0 := by simp [hkerMinus]

omit [FiniteDimensional ℝ S] in
/--
Specialization of the transported boundary-localized zero-mode pair to the
canonical chirality polarization `P = J`. The resulting pair lies directly in
the primitive real Weyl sectors.
-/
theorem weylZeroModePair_under_bogoliubov_of_preservesChiralityPolarization
    (T : RealBogoliubovTransform (S := S) M)
    (hpres : T.preservesPolarization (M.chiralityPolarization))
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hPair : BoundaryLocalizedZeroModePair
      (M := M) (P0 := M.chiralityPolarization) localOp chain) :
    ∃ ψplus ψminus : S,
      ψplus ≠ 0 ∧ ψminus ≠ 0
        ∧ ψplus ∈ M.weylPlus ∧ ψminus ∈ M.weylMinus
        ∧ (T.B.comp
            ((globalChainOperatorFromOpenChain (S := S) localOp chain).comp T.Binv)) ψplus = 0
        ∧ (T.B.comp
            ((globalChainOperatorFromOpenChain (S := S) localOp chain).comp T.Binv)) ψminus = 0 := by
  simpa using boundaryLocalizedZeroModePair_under_bogoliubov_of_preservesPolarization
    (M := M) (P0 := M.chiralityPolarization) (T := T) (hpres := hpres)
    (localOp := localOp) (chain := chain) hPair

omit [FiniteDimensional ℝ S] in
/--
Canonical data package for a transported Weyl zero-mode pair under a real
Bogoliubov transform.
-/
@[rep_depth krein]
abbrev WeylZeroModeUnderBogoliubov
    (T : RealBogoliubovTransform (S := S) M)
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell) : Prop :=
  ∃ ψplus ψminus : S,
    ψplus ≠ 0 ∧ ψminus ≠ 0
      ∧ ψplus ∈ M.weylPlus ∧ ψminus ∈ M.weylMinus
      ∧ (T.B.comp
          ((globalChainOperatorFromOpenChain (S := S) localOp chain).comp T.Binv)) ψplus = 0
      ∧ (T.B.comp
          ((globalChainOperatorFromOpenChain (S := S) localOp chain).comp T.Binv)) ψminus = 0

omit [FiniteDimensional ℝ S] in
/--
Structure-valued transported Weyl property extracted from the existential
Bogoliubov transport theorem.
-/
@[rep_depth krein]
noncomputable def weylZeroModeWitnessUnderBogoliubov_of_preservesChiralityPolarization
    (T : RealBogoliubovTransform (S := S) M)
    (hpres : T.preservesPolarization (M.chiralityPolarization))
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hPair : BoundaryLocalizedZeroModePair
      (M := M) (P0 := M.chiralityPolarization) localOp chain) :
    WeylZeroModeUnderBogoliubov (S := S) (M := M) T localOp chain := by
  exact weylZeroModePair_under_bogoliubov_of_preservesChiralityPolarization
    (M := M) (T := T) (hpres := hpres) (localOp := localOp) (chain := chain) hPair

omit [FiniteDimensional ℝ S] in
/--
Structure-valued transported Weyl property extracted directly from a simplified
boundary model in the negative phase.
-/
@[rep_depth krein]
noncomputable def weylZeroModeWitnessUnderBogoliubov_of_negativePhase_of_simplifiedBoundaryModel
    (T : RealBogoliubovTransform (S := S) M)
    (hpres : T.preservesPolarization (M.chiralityPolarization))
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hNeg : topologicalIndex chain = -1)
    (hSimple : SimplifiedBoundaryModel (M := M) (P0 := M.chiralityPolarization) localOp chain) :
    WeylZeroModeUnderBogoliubov (S := S) (M := M) T localOp chain :=
  weylZeroModeWitnessUnderBogoliubov_of_preservesChiralityPolarization
    (M := M) (T := T) (hpres := hpres) (localOp := localOp) (chain := chain)
    (hSimple.1 hNeg)

omit [FiniteDimensional ℝ S] in
/--
Simplified-boundary-model transport:
negative phase still yields a boundary-localized `(plus/minus)` zero-mode pair
after Bogoliubov conjugation, provided the transform preserves the chosen
polarization.
-/
theorem boundaryLocalizedZeroModePair_of_negativePhase_under_bogoliubov_of_simplifiedBoundaryModel_of_preservesPolarization
    (T : RealBogoliubovTransform (S := S) M)
    (hpres : T.preservesPolarization P0)
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hNeg : topologicalIndex chain = -1)
    (hSimple : SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain) :
    ∃ ψplus ψminus : S,
      ψplus ≠ 0 ∧ ψminus ≠ 0
        ∧ ψplus ∈ P0.plus ∧ ψminus ∈ P0.minus
        ∧ (T.B.comp
            ((globalChainOperatorFromOpenChain (S := S) localOp chain).comp T.Binv)) ψplus = 0
        ∧ (T.B.comp
            ((globalChainOperatorFromOpenChain (S := S) localOp chain).comp T.Binv)) ψminus = 0 := by
  exact boundaryLocalizedZeroModePair_under_bogoliubov_of_preservesPolarization
    (M := M) (P0 := P0) (T := T) (hpres := hpres)
    (localOp := localOp) (chain := chain)
    (hSimple.1 hNeg)

omit [CompleteSpace S] [FiniteDimensional ℝ S] in
/--
Instantiate `BoundaryLocalizationBridge` from the simplified boundary model.
-/
theorem boundaryLocalizationBridge_of_simplifiedBoundaryModel
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hSimple : SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain) :
    BoundaryLocalizationBridge (M := M) (P0 := P0) localOp chain := by
  refine ⟨?_, ?_⟩
  · intro hNeg
    exact hSimple.1 hNeg
  · intro hPair
    exact hSimple.2 hPair

omit [CompleteSpace S] [FiniteDimensional ℝ S] in
/--
Concrete source for `hNegPhaseDimMismatch` obtained from a boundary-localization
bridge package.
-/
theorem hNegPhaseDimMismatch_of_boundaryLocalizationBridge
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hLoc : BoundaryLocalizationBridge (M := M) (P0 := P0) localOp chain) :
    topologicalIndex chain = -1 →
      Module.finrank ℝ P0.plus ≠ Module.finrank ℝ P0.minus := by
  intro hNeg
  exact hLoc.2 (hLoc.1 hNeg)

-- Abstract global open-chain operator assignment into one fixed carrier.
-- This keeps chain-level statements explicit while avoiding hidden axioms.
variable (globalChainOperator : List KitaevCell → EndS (S := S))

/-- Surface zero mode: nontrivial kernel of the global chain operator. -/
def HasSurfaceZeroMode (chain : List KitaevCell) : Prop :=
  HasZeroMode (S := S) (globalChainOperator chain)

/--
Bulk-boundary correspondence under explicit bridge hypotheses.

`hOdd` encodes particle-hole-type spectral symmetry at the operator level,
and `hDimFromIndex` is the index-to-dimension-mismatch bridge property.
-/
theorem bulk_boundary_correspondence
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hOdd : PolarizationOdd (M := M) P0 (globalChainOperator chain))
    (hDimFromIndex :
      topologicalIndexZ2 chain = 1 →
        Module.finrank ℝ P0.plus
          ≠ Module.finrank ℝ P0.minus) :
    HasSurfaceZeroMode (globalChainOperator := globalChainOperator) chain := by
  unfold HasSurfaceZeroMode
  exact hasZeroMode_of_dim_mismatch (M := M) P0 (globalChainOperator chain)
    hOdd (hDimFromIndex hTopo)

/--
Corollary: in the topologically nontrivial phase, a nonzero kernel vector
exists for the global chain operator under the same bridge hypotheses.
-/
theorem zero_mode_is_information_sink
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hOdd : PolarizationOdd (M := M) P0 (globalChainOperator chain))
    (hDimFromIndex :
      topologicalIndexZ2 chain = 1 →
        Module.finrank ℝ P0.plus
          ≠ Module.finrank ℝ P0.minus) :
    ∃ v : S,
      v ∈ (globalChainOperator chain).toLinearMap.ker ∧ v ≠ 0 := by
  have hSurf : HasSurfaceZeroMode (globalChainOperator := globalChainOperator) chain :=
    bulk_boundary_correspondence (M := M) (P0 := P0)
      (globalChainOperator := globalChainOperator)
      chain hTopo hOdd hDimFromIndex
  rcases exists_zeroMode_of_hasZeroMode (S := S)
      (H := globalChainOperator chain) hSurf with ⟨v, hv, hv0⟩
  refine ⟨v, ?_, hv0⟩
  simpa using hv

/--
Concrete bulk-boundary correspondence for the Pfaffian-weighted finite open-chain
operator: oddness is derived from particle-hole symmetry, and dimension mismatch
is derived from `topologicalIndexZ2 = 1`.
-/
theorem bulk_boundary_correspondence_concrete
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hPHS : ∀ c : KitaevCell,
      ParticleHoleSymmetric (M := M) (P0 := P0) (localOp c))
    (hNegPhaseDimMismatch :
      topologicalIndex chain = -1 →
        Module.finrank ℝ P0.plus
          ≠ Module.finrank ℝ P0.minus) :
    HasSurfaceZeroMode
      (globalChainOperator :=
        globalChainOperatorFromOpenChain (S := S) localOp)
      chain := by
  unfold HasSurfaceZeroMode
  exact hasZeroMode_of_dim_mismatch (M := M) P0
    (globalChainOperatorFromOpenChain (S := S) localOp chain)
    (polarizationOdd_globalChainOperatorFromOpenChain
      (M := M) (P0 := P0) (localOp := localOp) hPHS chain)
    (dim_mismatch_of_topologicalIndexZ2_eq_one
      (M := M) (P0 := P0) chain hTopo hNegPhaseDimMismatch)

theorem hasZeroMode_bulk_boundary_concrete
    [FiniteDimensional ℝ S]
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hPHS : ∀ c : KitaevCell,
      ParticleHoleSymmetric (M := M) (P0 := P0) (localOp c))
    (hNegPhaseDimMismatch :
      topologicalIndex chain = -1 →
        Module.finrank ℝ P0.plus
          ≠ Module.finrank ℝ P0.minus) :
    HasZeroMode
      (S := S) (globalChainOperatorFromOpenChain (S := S) localOp chain) := by
  exact hasZeroMode_of_dim_mismatch (M := M) P0
    (globalChainOperatorFromOpenChain (S := S) localOp chain)
    (polarizationOdd_globalChainOperatorFromOpenChain
      (M := M) (P0 := P0) (localOp := localOp) hPHS chain)
    (dim_mismatch_of_topologicalIndexZ2_eq_one
      (M := M) (P0 := P0) chain hTopo hNegPhaseDimMismatch)

/--
Concrete information-sink property in the topological phase for the
Pfaffian-weighted finite open-chain operator.
-/
theorem zero_mode_is_information_sink_concrete
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hPHS : ∀ c : KitaevCell,
      ParticleHoleSymmetric (M := M) (P0 := P0) (localOp c))
    (hNegPhaseDimMismatch :
      topologicalIndex chain = -1 →
        Module.finrank ℝ P0.plus
          ≠ Module.finrank ℝ P0.minus) :
    ∃ v : S,
      v ∈ (globalChainOperatorFromOpenChain (S := S) localOp chain).toLinearMap.ker
        ∧ v ≠ 0 := by
  have hSurf :
      HasSurfaceZeroMode
        (globalChainOperator :=
          globalChainOperatorFromOpenChain (S := S) localOp)
        chain :=
    bulk_boundary_correspondence_concrete
      (M := M) (P0 := P0)
      (localOp := localOp)
      chain hTopo hPHS hNegPhaseDimMismatch
  rcases exists_zeroMode_of_hasZeroMode (S := S)
      (H := globalChainOperatorFromOpenChain (S := S) localOp chain) hSurf
      with ⟨v, hv, hv0⟩
  refine ⟨v, ?_, hv0⟩
  simpa using hv

/--
End-to-end concrete correspondence from chain data plus boundary-localization
assumptions: oddness and mismatch bridges are both internally derived.
-/
theorem bulk_boundary_correspondence_concrete_of_boundaryLocalization
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hPHS : ∀ c : KitaevCell,
      ParticleHoleSymmetric (M := M) (P0 := P0) (localOp c))
    (hLoc : BoundaryLocalizationBridge (M := M) (P0 := P0) localOp chain) :
    HasSurfaceZeroMode
      (globalChainOperator :=
        globalChainOperatorFromOpenChain (S := S) localOp)
      chain := by
  exact bulk_boundary_correspondence_concrete
    (M := M) (P0 := P0)
    (localOp := localOp)
    chain
    hTopo
    hPHS
    (hNegPhaseDimMismatch_of_boundaryLocalizationBridge
      (M := M) (P0 := P0) (localOp := localOp) (chain := chain) hLoc)

/--
End-to-end concrete zero-mode property from chain data plus
boundary-localization assumptions.
-/
theorem zero_mode_is_information_sink_concrete_of_boundaryLocalization
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hPHS : ∀ c : KitaevCell,
      ParticleHoleSymmetric (M := M) (P0 := P0) (localOp c))
    (hLoc : BoundaryLocalizationBridge (M := M) (P0 := P0) localOp chain) :
    ∃ v : S,
      v ∈ (globalChainOperatorFromOpenChain (S := S) localOp chain).toLinearMap.ker
        ∧ v ≠ 0 := by
  exact zero_mode_is_information_sink_concrete
    (M := M) (P0 := P0)
    (localOp := localOp)
    chain
    hTopo
    hPHS
    (hNegPhaseDimMismatch_of_boundaryLocalizationBridge
      (M := M) (P0 := P0) (localOp := localOp) (chain := chain) hLoc)

/--
Bogoliubov-stable concrete bulk-boundary correspondence:
the zero-mode conclusion survives conjugation by any real Bogoliubov transform.
-/
theorem bulk_boundary_correspondence_concrete_of_boundaryLocalization_under_bogoliubov
    (T : RealBogoliubovTransform (S := S) M)
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hPHS : ∀ c : KitaevCell,
      ParticleHoleSymmetric (M := M) (P0 := P0) (localOp c))
    (hLoc : BoundaryLocalizationBridge (M := M) (P0 := P0) localOp chain) :
    HasZeroMode (S := S)
      (T.B.comp
        ((globalChainOperatorFromOpenChain (S := S) localOp chain).comp T.Binv)) := by
  exact hasZeroMode_conjugate_of_hasZeroMode (M := M) (T := T)
    (bulk_boundary_correspondence_concrete_of_boundaryLocalization
      (M := M) (P0 := P0) (localOp := localOp)
      (chain := chain) hTopo hPHS hLoc)

/--
Bogoliubov-stable concrete information-sink property:
a boundary-localized zero mode persists under real Bogoliubov conjugation.
-/
theorem zero_mode_is_information_sink_concrete_of_boundaryLocalization_under_bogoliubov
    (T : RealBogoliubovTransform (S := S) M)
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hPHS : ∀ c : KitaevCell,
      ParticleHoleSymmetric (M := M) (P0 := P0) (localOp c))
    (hLoc : BoundaryLocalizationBridge (M := M) (P0 := P0) localOp chain) :
    ∃ v : S,
      v ∈ (T.B.comp
        ((globalChainOperatorFromOpenChain (S := S) localOp chain).comp T.Binv)).toLinearMap.ker
        ∧ v ≠ 0 := by
  rcases exists_zeroMode_of_hasZeroMode_conjugate (M := M) (T := T)
      (H := globalChainOperatorFromOpenChain (S := S) localOp chain)
      (bulk_boundary_correspondence_concrete_of_boundaryLocalization
        (M := M) (P0 := P0) (localOp := localOp)
        (chain := chain) hTopo hPHS hLoc) with ⟨v, hv, hv0⟩
  exact ⟨v, hv, hv0⟩

/--
Turnkey example theorem:
from a simplified boundary model package, derive the concrete end-to-end
bulk-boundary correspondence in one step.
-/
theorem bulk_boundary_correspondence_concrete_of_simplifiedBoundaryModel
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hPHS : ∀ c : KitaevCell,
      ParticleHoleSymmetric (M := M) (P0 := P0) (localOp c))
    (hSimple : SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain) :
    HasSurfaceZeroMode
      (globalChainOperator :=
        globalChainOperatorFromOpenChain (S := S) localOp)
      chain := by
  exact bulk_boundary_correspondence_concrete_of_boundaryLocalization
    (M := M) (P0 := P0)
    (localOp := localOp)
    chain
    hTopo
    hPHS
    (boundaryLocalizationBridge_of_simplifiedBoundaryModel
      (M := M) (P0 := P0) (localOp := localOp) (chain := chain) hSimple)

/--
Turnkey sibling theorem:
from a simplified boundary model package, derive the concrete end-to-end
zero-mode sink property in one step.
-/
theorem zero_mode_is_information_sink_concrete_of_simplifiedBoundaryModel
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hPHS : ∀ c : KitaevCell,
      ParticleHoleSymmetric (M := M) (P0 := P0) (localOp c))
    (hSimple : SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain) :
    ∃ v : S,
      v ∈ (globalChainOperatorFromOpenChain (S := S) localOp chain).toLinearMap.ker
        ∧ v ≠ 0 := by
  exact zero_mode_is_information_sink_concrete_of_boundaryLocalization
    (M := M) (P0 := P0)
    (localOp := localOp)
    chain
    hTopo
    hPHS
    (boundaryLocalizationBridge_of_simplifiedBoundaryModel
      (M := M) (P0 := P0) (localOp := localOp) (chain := chain) hSimple)

/--
Bogoliubov-stable simplified-boundary-model bulk-boundary correspondence.
-/
theorem bulk_boundary_correspondence_concrete_of_simplifiedBoundaryModel_under_bogoliubov
    (T : RealBogoliubovTransform (S := S) M)
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hPHS : ∀ c : KitaevCell,
      ParticleHoleSymmetric (M := M) (P0 := P0) (localOp c))
    (hSimple : SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain) :
    HasZeroMode (S := S)
      (T.B.comp
        ((globalChainOperatorFromOpenChain (S := S) localOp chain).comp T.Binv)) := by
  exact bulk_boundary_correspondence_concrete_of_boundaryLocalization_under_bogoliubov
    (M := M) (P0 := P0) (T := T)
    (localOp := localOp) (chain := chain) hTopo hPHS
    (boundaryLocalizationBridge_of_simplifiedBoundaryModel
      (M := M) (P0 := P0) (localOp := localOp) (chain := chain) hSimple)

/--
Bogoliubov-stable simplified-boundary-model zero-mode property.
-/
theorem zero_mode_is_information_sink_concrete_of_simplifiedBoundaryModel_under_bogoliubov
    (T : RealBogoliubovTransform (S := S) M)
    (localOp : KitaevCell → EndS (S := S))
    (chain : List KitaevCell)
    (hTopo : topologicalIndexZ2 chain = 1)
    (hPHS : ∀ c : KitaevCell,
      ParticleHoleSymmetric (M := M) (P0 := P0) (localOp c))
    (hSimple : SimplifiedBoundaryModel (M := M) (P0 := P0) localOp chain) :
    ∃ v : S,
      v ∈ (T.B.comp
        ((globalChainOperatorFromOpenChain (S := S) localOp chain).comp T.Binv)).toLinearMap.ker
        ∧ v ≠ 0 := by
  exact zero_mode_is_information_sink_concrete_of_boundaryLocalization_under_bogoliubov
    (M := M) (P0 := P0) (T := T)
    (localOp := localOp) (chain := chain) hTopo hPHS
    (boundaryLocalizationBridge_of_simplifiedBoundaryModel
      (M := M) (P0 := P0) (localOp := localOp) (chain := chain) hSimple)

end ChainBridge

end InfoGeometry.Quantum.BulkBoundary
