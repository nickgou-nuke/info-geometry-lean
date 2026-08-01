import InfoGeometry.Canonical.NavierStokesBridge
import InfoGeometry.Canonical.MixtureOfExperts
import InfoGeometry.Canonical.GrandCanonicalExperts
import InfoGeometry.Quantum.RealMajorana
import InfoGeometry.Quantum.BulkBoundary

open scoped BigOperators

namespace InfoGeometry.Canonical.MoE

open InfoGeometry.Quantum.RealMajorana

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
Arnold-Majorana Network:
A specialized MoE layer where experts operate on the doubled `ArnoldMajoranaCarrier`.
- Experts: `Experts (ArnoldMajoranaCarrier E)`
- Input: `ArnoldMajoranaCarrier E`
- Output: `ArnoldMajoranaCarrier E`
-/
structure ArnoldMajoranaNetwork (n : Nat) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E] where
  moe : MoELayer n (ArnoldMajoranaCarrier E)

/--
Canonical Arnold-Majorana routing energy:
The energy depends on the Clifford norm on the doubled space.
-/
noncomputable def arnoldRoutingEnergy (n : Nat) {Tok : Type*} [Fintype Tok] (x : Tok → ArnoldMajoranaCarrier E) (i : Tok) (e : ExpertIdx n) : ℝ :=
  -- Physics-informed energy: depends on the doubled-space norm
  ‖x i‖ + ((e : ℕ) : ℝ)

/--
Normalized output of an Arnold-Majorana network layer.
This realizes the "context-adaptive" flow in a thermodynamic expert setting.
-/
noncomputable def arnoldNetworkOutput (n : Nat) (net : ArnoldMajoranaNetwork n E) (β : ℝ) {Tok : Type*} [Fintype Tok] [DecidableEq Tok] (x : Tok → ArnoldMajoranaCarrier E) (i : Tok) : ArnoldMajoranaCarrier E :=
  let experts := net.moe.experts
  -- We reuse the MoE normalized weight logic
  ∑ e : ExpertIdx n,
    (normalizedWeights n β x i e) • (experts e).apply (x i)

/--
If every expert preserves a linear subspace, then the normalized Arnold-Majorana
output stays in that subspace.
-/
theorem arnoldNetwork_preserves_submodule
    (n : Nat)
    (net : ArnoldMajoranaNetwork n E)
    (β : ℝ)
    {Tok : Type*} [Fintype Tok] [DecidableEq Tok]
    (U : Submodule ℝ (ArnoldMajoranaCarrier E))
    (x : Tok → ArnoldMajoranaCarrier E)
    (i : Tok)
    (hU : ∀ e : ExpertIdx n, ∀ v : ArnoldMajoranaCarrier E,
      v ∈ U → (net.moe.experts e).apply v ∈ U)
    (hx : x i ∈ U) :
    arnoldNetworkOutput n net β x i ∈ U := by
  classical
  unfold arnoldNetworkOutput
  refine Submodule.sum_mem U ?_
  intro e _
  exact U.smul_mem (normalizedWeights n β x i e) (hU e (x i) hx)

omit [FiniteDimensional ℝ E] in
/--
A pointwise expert action that commutes with transported chirality preserves the
transported Weyl-plus sector.
-/
theorem expert_apply_mem_transportWeylPlus_of_commutes_transportJ
    {M : RealMajoranaDatum (S := ArnoldMajoranaCarrier E)}
    (T : RealBogoliubovTransform (S := ArnoldMajoranaCarrier E) M)
    {f : ArnoldMajoranaCarrier E → ArnoldMajoranaCarrier E}
    (hcomm : ∀ v : ArnoldMajoranaCarrier E, T.transportJ (f v) = f (T.transportJ v))
    {v : ArnoldMajoranaCarrier E}
    (hv : v ∈ T.transportWeylPlus) :
    f v ∈ T.transportWeylPlus := by
  rw [T.mem_transportWeylPlus_iff] at hv ⊢
  calc
    T.transportJ (f v) = f (T.transportJ v) := hcomm v
    _ = f v := by simp [hv]

omit [FiniteDimensional ℝ E] in
/--
A linear expert whose action commutes with transported chirality preserves the
transported Weyl-plus sector.
-/
theorem expert_apply_mem_transportWeylPlus_of_clm_commutes_transportJ
    {M : RealMajoranaDatum (S := ArnoldMajoranaCarrier E)}
    (T : RealBogoliubovTransform (S := ArnoldMajoranaCarrier E) M)
    {A : ArnoldMajoranaCarrier E →L[ℝ] ArnoldMajoranaCarrier E}
    (hcomm : T.transportJ.comp A = A.comp T.transportJ)
    {v : ArnoldMajoranaCarrier E}
    (hv : v ∈ T.transportWeylPlus) :
    A v ∈ T.transportWeylPlus := by
  apply expert_apply_mem_transportWeylPlus_of_commutes_transportJ
    (T := T) (f := A)
  · intro w
    have hw := congrArg (fun F => F w) hcomm
    simpa [ContinuousLinearMap.comp_apply] using hw
  · exact hv

/--
If every expert commutes with transported chirality, then the Arnold-Majorana
network preserves the transported Weyl-plus sector.
-/
theorem arnoldNetwork_preserves_transportWeylPlus_of_commutes_transportJ
    {M : RealMajoranaDatum (S := ArnoldMajoranaCarrier E)}
    (T : RealBogoliubovTransform (S := ArnoldMajoranaCarrier E) M)
    (n : Nat)
    (net : ArnoldMajoranaNetwork n E)
    (β : ℝ)
    {Tok : Type*} [Fintype Tok] [DecidableEq Tok]
    (x : Tok → ArnoldMajoranaCarrier E)
    (i : Tok)
    (hComm : ∀ e : ExpertIdx n, ∀ v : ArnoldMajoranaCarrier E,
      T.transportJ ((net.moe.experts e).apply v) = (net.moe.experts e).apply (T.transportJ v))
    (hx : x i ∈ T.transportWeylPlus) :
    arnoldNetworkOutput n net β x i ∈ T.transportWeylPlus := by
  refine arnoldNetwork_preserves_submodule
    (n := n) (net := net) (β := β) (U := T.transportWeylPlus)
    (x := x) (i := i) ?_ hx
  intro e v hv
  exact expert_apply_mem_transportWeylPlus_of_commutes_transportJ
    (T := T) (f := (net.moe.experts e).apply) (hcomm := hComm e) hv

omit [FiniteDimensional ℝ E] in
/--
A pointwise expert action that commutes with transported chirality and is odd
preserves the transported Weyl-minus sector.
-/
theorem expert_apply_mem_transportWeylMinus_of_commutes_transportJ_and_odd
    {M : RealMajoranaDatum (S := ArnoldMajoranaCarrier E)}
    (T : RealBogoliubovTransform (S := ArnoldMajoranaCarrier E) M)
    {f : ArnoldMajoranaCarrier E → ArnoldMajoranaCarrier E}
    (hcomm : ∀ v : ArnoldMajoranaCarrier E, T.transportJ (f v) = f (T.transportJ v))
    (hodd : ∀ v : ArnoldMajoranaCarrier E, f (-v) = -f v)
    {v : ArnoldMajoranaCarrier E}
    (hv : v ∈ T.transportWeylMinus) :
    f v ∈ T.transportWeylMinus := by
  rw [T.mem_transportWeylMinus_iff] at hv ⊢
  calc
    T.transportJ (f v) = f (T.transportJ v) := hcomm v
    _ = f (-v) := by simp [hv]
    _ = -(f v) := hodd v

omit [FiniteDimensional ℝ E] in
/--
A linear expert whose action commutes with transported chirality preserves the
transported Weyl-minus sector; oddness is automatic from linearity.
-/
theorem expert_apply_mem_transportWeylMinus_of_clm_commutes_transportJ
    {M : RealMajoranaDatum (S := ArnoldMajoranaCarrier E)}
    (T : RealBogoliubovTransform (S := ArnoldMajoranaCarrier E) M)
    {A : ArnoldMajoranaCarrier E →L[ℝ] ArnoldMajoranaCarrier E}
    (hcomm : T.transportJ.comp A = A.comp T.transportJ)
    {v : ArnoldMajoranaCarrier E}
    (hv : v ∈ T.transportWeylMinus) :
    A v ∈ T.transportWeylMinus := by
  apply expert_apply_mem_transportWeylMinus_of_commutes_transportJ_and_odd
    (T := T) (f := A)
  · intro w
    have hw := congrArg (fun F => F w) hcomm
    simpa [ContinuousLinearMap.comp_apply] using hw
  · intro w
    exact A.map_neg w
  · exact hv

/--
If every expert commutes with transported chirality and is odd, then the
Arnold-Majorana network preserves the transported Weyl-minus sector.
-/
theorem arnoldNetwork_preserves_transportWeylMinus_of_commutes_transportJ_and_odd
    {M : RealMajoranaDatum (S := ArnoldMajoranaCarrier E)}
    (T : RealBogoliubovTransform (S := ArnoldMajoranaCarrier E) M)
    (n : Nat)
    (net : ArnoldMajoranaNetwork n E)
    (β : ℝ)
    {Tok : Type*} [Fintype Tok] [DecidableEq Tok]
    (x : Tok → ArnoldMajoranaCarrier E)
    (i : Tok)
    (hComm : ∀ e : ExpertIdx n, ∀ v : ArnoldMajoranaCarrier E,
      T.transportJ ((net.moe.experts e).apply v) = (net.moe.experts e).apply (T.transportJ v))
    (hOdd : ∀ e : ExpertIdx n, ∀ v : ArnoldMajoranaCarrier E,
      (net.moe.experts e).apply (-v) = -((net.moe.experts e).apply v))
    (hx : x i ∈ T.transportWeylMinus) :
    arnoldNetworkOutput n net β x i ∈ T.transportWeylMinus := by
  refine arnoldNetwork_preserves_submodule
    (n := n) (net := net) (β := β) (U := T.transportWeylMinus)
    (x := x) (i := i) ?_ hx
  intro e v hv
  exact expert_apply_mem_transportWeylMinus_of_commutes_transportJ_and_odd
    (T := T) (f := (net.moe.experts e).apply) (hcomm := hComm e) (hodd := hOdd e) hv

/--
Theorem: The Arnold-Majorana network preserves the subspace of base states
if all experts do.
-/
theorem arnoldNetwork_preserves_base (n : Nat) (net : ArnoldMajoranaNetwork n E) (β : ℝ) {Tok : Type*} [Fintype Tok] [DecidableEq Tok] (x : Tok → ArnoldMajoranaCarrier E) (i : Tok)
    (hBase : ∀ e : ExpertIdx n, ∀ v : ArnoldMajoranaCarrier E, (WithLp.ofLp v).2 = 0 → (WithLp.ofLp ((net.moe.experts e).apply v)).2 = 0)
    (hx : (WithLp.ofLp (x i)).2 = 0) :
    (WithLp.ofLp (arnoldNetworkOutput n net β x i)).2 = 0 := by
  unfold arnoldNetworkOutput
  have hzero : ∀ e : ExpertIdx n, WithLp.snd ((net.moe.experts e).apply (x i)) = 0 := by
    intro e
    simpa using hBase e (x i) hx
  simp [Prod.snd_sum, hzero]

/--
If every expert preserves the transported Weyl-plus sector of a real
Bogoliubov transform, then the Arnold-Majorana network output stays in that
sector.
-/
theorem arnoldNetwork_preserves_transportWeylPlus
    {M : RealMajoranaDatum (S := ArnoldMajoranaCarrier E)}
    (T : RealBogoliubovTransform (S := ArnoldMajoranaCarrier E) M)
    (n : Nat)
    (net : ArnoldMajoranaNetwork n E)
    (β : ℝ)
    {Tok : Type*} [Fintype Tok] [DecidableEq Tok]
    (x : Tok → ArnoldMajoranaCarrier E)
    (i : Tok)
    (hPlus : ∀ e : ExpertIdx n, ∀ v : ArnoldMajoranaCarrier E,
      v ∈ T.transportWeylPlus →
        (net.moe.experts e).apply v ∈ T.transportWeylPlus)
    (hx : x i ∈ T.transportWeylPlus) :
    arnoldNetworkOutput n net β x i ∈ T.transportWeylPlus := by
  exact arnoldNetwork_preserves_submodule
    (n := n) (net := net) (β := β) (U := T.transportWeylPlus)
    (x := x) (i := i) hPlus hx

/--
If every expert preserves the transported Weyl-minus sector of a real
Bogoliubov transform, then the Arnold-Majorana network output stays in that
sector.
-/
theorem arnoldNetwork_preserves_transportWeylMinus
    {M : RealMajoranaDatum (S := ArnoldMajoranaCarrier E)}
    (T : RealBogoliubovTransform (S := ArnoldMajoranaCarrier E) M)
    (n : Nat)
    (net : ArnoldMajoranaNetwork n E)
    (β : ℝ)
    {Tok : Type*} [Fintype Tok] [DecidableEq Tok]
    (x : Tok → ArnoldMajoranaCarrier E)
    (i : Tok)
    (hMinus : ∀ e : ExpertIdx n, ∀ v : ArnoldMajoranaCarrier E,
      v ∈ T.transportWeylMinus →
        (net.moe.experts e).apply v ∈ T.transportWeylMinus)
    (hx : x i ∈ T.transportWeylMinus) :
    arnoldNetworkOutput n net β x i ∈ T.transportWeylMinus := by
  exact arnoldNetwork_preserves_submodule
    (n := n) (net := net) (β := β) (U := T.transportWeylMinus)
    (x := x) (i := i) hMinus hx

/--
If the network experts are realized by linear operators that commute with the
transported chirality, then the Arnold-Majorana network preserves the
transported Weyl-plus sector.
-/
theorem arnoldNetwork_preserves_transportWeylPlus_of_linearExperts_commute_transportJ
    {M : RealMajoranaDatum (S := ArnoldMajoranaCarrier E)}
    (T : RealBogoliubovTransform (S := ArnoldMajoranaCarrier E) M)
    (n : Nat)
    (net : ArnoldMajoranaNetwork n E)
    (β : ℝ)
    {Tok : Type*} [Fintype Tok] [DecidableEq Tok]
    (x : Tok → ArnoldMajoranaCarrier E)
    (i : Tok)
    (A : ExpertIdx n → ArnoldMajoranaCarrier E →L[ℝ] ArnoldMajoranaCarrier E)
    (happly : ∀ e : ExpertIdx n, ∀ v : ArnoldMajoranaCarrier E,
      (net.moe.experts e).apply v = A e v)
    (hComm : ∀ e : ExpertIdx n, T.transportJ.comp (A e) = (A e).comp T.transportJ)
    (hx : x i ∈ T.transportWeylPlus) :
    arnoldNetworkOutput n net β x i ∈ T.transportWeylPlus := by
  apply arnoldNetwork_preserves_transportWeylPlus_of_commutes_transportJ
    (T := T) (n := n) (net := net) (β := β) (x := x) (i := i)
  · intro e v
    rw [happly e v, happly e (T.transportJ v)]
    have hv := congrArg (fun F => F v) (hComm e)
    simpa [ContinuousLinearMap.comp_apply] using hv
  · exact hx

/--
If the network experts are realized by linear operators that commute with the
transported chirality, then the Arnold-Majorana network preserves the
transported Weyl-minus sector; oddness is supplied by linearity.
-/
theorem arnoldNetwork_preserves_transportWeylMinus_of_linearExperts_commute_transportJ
    {M : RealMajoranaDatum (S := ArnoldMajoranaCarrier E)}
    (T : RealBogoliubovTransform (S := ArnoldMajoranaCarrier E) M)
    (n : Nat)
    (net : ArnoldMajoranaNetwork n E)
    (β : ℝ)
    {Tok : Type*} [Fintype Tok] [DecidableEq Tok]
    (x : Tok → ArnoldMajoranaCarrier E)
    (i : Tok)
    (A : ExpertIdx n → ArnoldMajoranaCarrier E →L[ℝ] ArnoldMajoranaCarrier E)
    (happly : ∀ e : ExpertIdx n, ∀ v : ArnoldMajoranaCarrier E,
      (net.moe.experts e).apply v = A e v)
    (hComm : ∀ e : ExpertIdx n, T.transportJ.comp (A e) = (A e).comp T.transportJ)
    (hx : x i ∈ T.transportWeylMinus) :
    arnoldNetworkOutput n net β x i ∈ T.transportWeylMinus := by
  apply arnoldNetwork_preserves_transportWeylMinus_of_commutes_transportJ_and_odd
    (T := T) (n := n) (net := net) (β := β) (x := x) (i := i)
  · intro e v
    rw [happly e v, happly e (T.transportJ v)]
    have hv := congrArg (fun F => F v) (hComm e)
    simpa [ContinuousLinearMap.comp_apply] using hv
  · intro e v
    rw [happly e (-v), happly e v]
    exact (A e).map_neg v
  · exact hx

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/--
A linear expert that commutes with an operator preserves its kernel.
-/
theorem expert_apply_mem_ker_of_clm_commutes
    {H A : ArnoldMajoranaCarrier E →L[ℝ] ArnoldMajoranaCarrier E}
    (hcomm : H.comp A = A.comp H)
    {v : ArnoldMajoranaCarrier E}
    (hv : H v = 0) :
    H (A v) = 0 := by
  have hw : H (A v) = A (H v) := by
    have hEq := congrArg (fun F => F v) hcomm
    simpa [ContinuousLinearMap.comp_apply] using hEq
  simpa [ContinuousLinearMap.comp_apply, hv] using hw

/--
If the network experts are realized by linear operators that commute with both
transported chirality and a target operator `H`, then the Arnold-Majorana
network preserves the transported Weyl-plus sector together with the `H`-kernel.
-/
theorem arnoldNetwork_preserves_transportWeylPlus_and_ker_of_linearExperts_commuting
    {M : RealMajoranaDatum (S := ArnoldMajoranaCarrier E)}
    (T : RealBogoliubovTransform (S := ArnoldMajoranaCarrier E) M)
    (H : ArnoldMajoranaCarrier E →L[ℝ] ArnoldMajoranaCarrier E)
    (n : Nat)
    (net : ArnoldMajoranaNetwork n E)
    (β : ℝ)
    {Tok : Type*} [Fintype Tok] [DecidableEq Tok]
    (x : Tok → ArnoldMajoranaCarrier E)
    (i : Tok)
    (A : ExpertIdx n → ArnoldMajoranaCarrier E →L[ℝ] ArnoldMajoranaCarrier E)
    (happly : ∀ e : ExpertIdx n, ∀ v : ArnoldMajoranaCarrier E,
      (net.moe.experts e).apply v = A e v)
    (hCommJ : ∀ e : ExpertIdx n, T.transportJ.comp (A e) = (A e).comp T.transportJ)
    (hCommH : ∀ e : ExpertIdx n, H.comp (A e) = (A e).comp H)
    (hxPlus : x i ∈ T.transportWeylPlus)
    (hxKer : H (x i) = 0) :
    arnoldNetworkOutput n net β x i ∈ T.transportWeylPlus
      ∧ H (arnoldNetworkOutput n net β x i) = 0 := by
  let U : Submodule ℝ (ArnoldMajoranaCarrier E) := T.transportWeylPlus ⊓ H.toLinearMap.ker
  have hx : x i ∈ U := by
    refine ⟨hxPlus, ?_⟩
    simpa using hxKer
  have hout : arnoldNetworkOutput n net β x i ∈ U := by
    apply arnoldNetwork_preserves_submodule
      (n := n) (net := net) (β := β) (U := U) (x := x) (i := i)
    · intro e v hv
      rcases hv with ⟨hvPlus, hvKer⟩
      refine ⟨?_, ?_⟩
      · rw [happly e v]
        exact expert_apply_mem_transportWeylPlus_of_clm_commutes_transportJ
          (T := T) (A := A e) (hcomm := hCommJ e) hvPlus
      · rw [happly e v]
        exact expert_apply_mem_ker_of_clm_commutes
          (H := H) (A := A e) (hcomm := hCommH e) (by simpa using hvKer)
    · exact hx
  exact hout

/--
If the network experts are realized by linear operators that commute with both
transported chirality and a target operator `H`, then the Arnold-Majorana
network preserves the transported Weyl-minus sector together with the `H`-kernel.
-/
theorem arnoldNetwork_preserves_transportWeylMinus_and_ker_of_linearExperts_commuting
    {M : RealMajoranaDatum (S := ArnoldMajoranaCarrier E)}
    (T : RealBogoliubovTransform (S := ArnoldMajoranaCarrier E) M)
    (H : ArnoldMajoranaCarrier E →L[ℝ] ArnoldMajoranaCarrier E)
    (n : Nat)
    (net : ArnoldMajoranaNetwork n E)
    (β : ℝ)
    {Tok : Type*} [Fintype Tok] [DecidableEq Tok]
    (x : Tok → ArnoldMajoranaCarrier E)
    (i : Tok)
    (A : ExpertIdx n → ArnoldMajoranaCarrier E →L[ℝ] ArnoldMajoranaCarrier E)
    (happly : ∀ e : ExpertIdx n, ∀ v : ArnoldMajoranaCarrier E,
      (net.moe.experts e).apply v = A e v)
    (hCommJ : ∀ e : ExpertIdx n, T.transportJ.comp (A e) = (A e).comp T.transportJ)
    (hCommH : ∀ e : ExpertIdx n, H.comp (A e) = (A e).comp H)
    (hxMinus : x i ∈ T.transportWeylMinus)
    (hxKer : H (x i) = 0) :
    arnoldNetworkOutput n net β x i ∈ T.transportWeylMinus
      ∧ H (arnoldNetworkOutput n net β x i) = 0 := by
  let U : Submodule ℝ (ArnoldMajoranaCarrier E) := T.transportWeylMinus ⊓ H.toLinearMap.ker
  have hx : x i ∈ U := by
    refine ⟨hxMinus, ?_⟩
    simpa using hxKer
  have hout : arnoldNetworkOutput n net β x i ∈ U := by
    apply arnoldNetwork_preserves_submodule
      (n := n) (net := net) (β := β) (U := U) (x := x) (i := i)
    · intro e v hv
      rcases hv with ⟨hvMinus, hvKer⟩
      refine ⟨?_, ?_⟩
      · rw [happly e v]
        exact expert_apply_mem_transportWeylMinus_of_clm_commutes_transportJ
          (T := T) (A := A e) (hcomm := hCommJ e) hvMinus
      · rw [happly e v]
        exact expert_apply_mem_ker_of_clm_commutes
          (H := H) (A := A e) (hcomm := hCommH e) (by simpa using hvKer)
    · exact hx
  exact hout

/--
If every expert fixes the current token state, the Arnold-Majorana network
returns that state exactly.
-/
theorem arnoldNetworkOutput_eq_of_experts_fix
    (n : Nat)
    (net : ArnoldMajoranaNetwork n E)
    (β : ℝ)
    {Tok : Type*} [Fintype Tok] [DecidableEq Tok]
    [Nonempty (Fin n)]
    (x : Tok → ArnoldMajoranaCarrier E)
    (i : Tok)
    (hfix : ∀ e : ExpertIdx n, (net.moe.experts e).apply (x i) = x i) :
    arnoldNetworkOutput n net β x i = x i := by
  classical
  unfold arnoldNetworkOutput
  calc
    ∑ e : ExpertIdx n, normalizedWeights n β x i e • (net.moe.experts e).apply (x i)
        = ∑ e : ExpertIdx n, normalizedWeights n β x i e • (x i) := by
            refine Finset.sum_congr rfl ?_
            intro e _
            rw [hfix e]
    _ = (∑ e : ExpertIdx n, normalizedWeights n β x i e) • (x i) := by
          rw [← Finset.sum_smul]
    _ = (1 : ℝ) • (x i) := by
          rw [normalizedWeights_sum_one (n := n) β x i]
    _ = x i := by simp

/--
If every expert fixes a nonzero transported Weyl-plus zero mode, the
Arnold-Majorana network output is the same nonzero transported Weyl-plus zero
mode.
-/
theorem arnoldNetwork_preserves_transportWeylPlus_nonzero_ker_of_experts_fix
    {M : RealMajoranaDatum (S := ArnoldMajoranaCarrier E)}
    (T : RealBogoliubovTransform (S := ArnoldMajoranaCarrier E) M)
    (H : ArnoldMajoranaCarrier E →L[ℝ] ArnoldMajoranaCarrier E)
    (n : Nat)
    (net : ArnoldMajoranaNetwork n E)
    (β : ℝ)
    {Tok : Type*} [Fintype Tok] [DecidableEq Tok]
    [Nonempty (Fin n)]
    (x : Tok → ArnoldMajoranaCarrier E)
    (i : Tok)
    (hxPlus : x i ∈ T.transportWeylPlus)
    (hxKer : H (x i) = 0)
    (hxNe : x i ≠ 0)
    (hfix : ∀ e : ExpertIdx n, (net.moe.experts e).apply (x i) = x i) :
    arnoldNetworkOutput n net β x i ∈ T.transportWeylPlus
      ∧ H (arnoldNetworkOutput n net β x i) = 0
      ∧ arnoldNetworkOutput n net β x i ≠ 0 := by
  have hEq := arnoldNetworkOutput_eq_of_experts_fix
    (n := n) (net := net) (β := β) (x := x) (i := i) hfix
  refine ⟨?_, ?_, ?_⟩
  · simpa [hEq] using hxPlus
  · simpa [hEq] using hxKer
  · simpa [hEq] using hxNe

/--
If every expert fixes a nonzero transported Weyl-minus zero mode, the
Arnold-Majorana network output is the same nonzero transported Weyl-minus zero
mode.
-/
theorem arnoldNetwork_preserves_transportWeylMinus_nonzero_ker_of_experts_fix
    {M : RealMajoranaDatum (S := ArnoldMajoranaCarrier E)}
    (T : RealBogoliubovTransform (S := ArnoldMajoranaCarrier E) M)
    (H : ArnoldMajoranaCarrier E →L[ℝ] ArnoldMajoranaCarrier E)
    (n : Nat)
    (net : ArnoldMajoranaNetwork n E)
    (β : ℝ)
    {Tok : Type*} [Fintype Tok] [DecidableEq Tok]
    [Nonempty (Fin n)]
    (x : Tok → ArnoldMajoranaCarrier E)
    (i : Tok)
    (hxMinus : x i ∈ T.transportWeylMinus)
    (hxKer : H (x i) = 0)
    (hxNe : x i ≠ 0)
    (hfix : ∀ e : ExpertIdx n, (net.moe.experts e).apply (x i) = x i) :
    arnoldNetworkOutput n net β x i ∈ T.transportWeylMinus
      ∧ H (arnoldNetworkOutput n net β x i) = 0
      ∧ arnoldNetworkOutput n net β x i ≠ 0 := by
  have hEq := arnoldNetworkOutput_eq_of_experts_fix
    (n := n) (net := net) (β := β) (x := x) (i := i) hfix
  refine ⟨?_, ?_, ?_⟩
  · simpa [hEq] using hxMinus
  · simpa [hEq] using hxKer
  · simpa [hEq] using hxNe

/--
If a transported Weyl-plus zero-mode witness already exists for the conjugated
chain operator, and every expert fixes any such witness pointwise, then the
Arnold-Majorana network has a concrete fixed nonzero transported Weyl-plus zero
mode on the constant-token input generated by that witness.
-/
theorem exists_network_fixed_transportWeylPlus_nonzero_ker_of_experts_fix_of_weylZeroModePair
    {M : RealMajoranaDatum (S := ArnoldMajoranaCarrier E)}
    (T : RealBogoliubovTransform (S := ArnoldMajoranaCarrier E) M)
    (n : Nat)
    (net : ArnoldMajoranaNetwork n E)
    (β : ℝ)
    [Nonempty (Fin n)]
    (localOp : InfoGeometry.Quantum.KitaevChain.KitaevCell → ArnoldMajoranaCarrier E →L[ℝ] ArnoldMajoranaCarrier E)
    (chain : List InfoGeometry.Quantum.KitaevChain.KitaevCell)
    (hPair :
      ∃ ψplus ψminus : ArnoldMajoranaCarrier E,
        ψplus ≠ 0 ∧ ψminus ≠ 0
          ∧ ψplus ∈ T.transportWeylPlus ∧ ψminus ∈ T.transportWeylMinus
          ∧ (T.B.comp
              ((InfoGeometry.Quantum.BulkBoundary.globalChainOperatorFromOpenChain
                (S := ArnoldMajoranaCarrier E) localOp chain).comp T.Binv)) ψplus = 0
          ∧ (T.B.comp
              ((InfoGeometry.Quantum.BulkBoundary.globalChainOperatorFromOpenChain
                (S := ArnoldMajoranaCarrier E) localOp chain).comp T.Binv)) ψminus = 0)
    (hfix : ∀ e : ExpertIdx n, ∀ v : ArnoldMajoranaCarrier E,
      v ∈ T.transportWeylPlus →
      (T.B.comp
        ((InfoGeometry.Quantum.BulkBoundary.globalChainOperatorFromOpenChain
          (S := ArnoldMajoranaCarrier E) localOp chain).comp T.Binv)) v = 0 →
      (net.moe.experts e).apply v = v) :
    ∃ ψplus : ArnoldMajoranaCarrier E,
      arnoldNetworkOutput n net β (fun _ : Unit => ψplus) () = ψplus
        ∧ ψplus ∈ T.transportWeylPlus
        ∧ (T.B.comp
            ((InfoGeometry.Quantum.BulkBoundary.globalChainOperatorFromOpenChain
              (S := ArnoldMajoranaCarrier E) localOp chain).comp T.Binv)) ψplus = 0
        ∧ ψplus ≠ 0 := by
  rcases hPair with ⟨ψplus, ψminus, hψplusNe, hψminusNe, hPlus, hMinus, hKerPlus, hKerMinus⟩
  refine ⟨ψplus, ?_, hPlus, hKerPlus, hψplusNe⟩
  exact arnoldNetworkOutput_eq_of_experts_fix
    (n := n) (net := net) (β := β) (x := fun _ : Unit => ψplus) (i := ())
    (hfix := fun e => hfix e ψplus hPlus hKerPlus)

/--
If a transported Weyl-minus zero-mode witness already exists for the conjugated
chain operator, and every expert fixes any such witness pointwise, then the
Arnold-Majorana network has a concrete fixed nonzero transported Weyl-minus zero
mode on the constant-token input generated by that witness.
-/
theorem exists_network_fixed_transportWeylMinus_nonzero_ker_of_experts_fix_of_weylZeroModePair
    {M : RealMajoranaDatum (S := ArnoldMajoranaCarrier E)}
    (T : RealBogoliubovTransform (S := ArnoldMajoranaCarrier E) M)
    (n : Nat)
    (net : ArnoldMajoranaNetwork n E)
    (β : ℝ)
    [Nonempty (Fin n)]
    (localOp : InfoGeometry.Quantum.KitaevChain.KitaevCell → ArnoldMajoranaCarrier E →L[ℝ] ArnoldMajoranaCarrier E)
    (chain : List InfoGeometry.Quantum.KitaevChain.KitaevCell)
    (hPair :
      ∃ ψplus ψminus : ArnoldMajoranaCarrier E,
        ψplus ≠ 0 ∧ ψminus ≠ 0
          ∧ ψplus ∈ T.transportWeylPlus ∧ ψminus ∈ T.transportWeylMinus
          ∧ (T.B.comp
              ((InfoGeometry.Quantum.BulkBoundary.globalChainOperatorFromOpenChain
                (S := ArnoldMajoranaCarrier E) localOp chain).comp T.Binv)) ψplus = 0
          ∧ (T.B.comp
              ((InfoGeometry.Quantum.BulkBoundary.globalChainOperatorFromOpenChain
                (S := ArnoldMajoranaCarrier E) localOp chain).comp T.Binv)) ψminus = 0)
    (hfix : ∀ e : ExpertIdx n, ∀ v : ArnoldMajoranaCarrier E,
      v ∈ T.transportWeylMinus →
      (T.B.comp
        ((InfoGeometry.Quantum.BulkBoundary.globalChainOperatorFromOpenChain
          (S := ArnoldMajoranaCarrier E) localOp chain).comp T.Binv)) v = 0 →
      (net.moe.experts e).apply v = v) :
    ∃ ψminus : ArnoldMajoranaCarrier E,
      arnoldNetworkOutput n net β (fun _ : Unit => ψminus) () = ψminus
        ∧ ψminus ∈ T.transportWeylMinus
        ∧ (T.B.comp
            ((InfoGeometry.Quantum.BulkBoundary.globalChainOperatorFromOpenChain
              (S := ArnoldMajoranaCarrier E) localOp chain).comp T.Binv)) ψminus = 0
        ∧ ψminus ≠ 0 := by
  rcases hPair with ⟨ψplus, ψminus, hψplusNe, hψminusNe, hPlus, hMinus, hKerPlus, hKerMinus⟩
  refine ⟨ψminus, ?_, hMinus, hKerMinus, hψminusNe⟩
  exact arnoldNetworkOutput_eq_of_experts_fix
    (n := n) (net := net) (β := β) (x := fun _ : Unit => ψminus) (i := ())
    (hfix := fun e => hfix e ψminus hMinus hKerMinus)

/--
Turn a simplified-boundary-model negative phase into a concrete fixed nonzero
transported Weyl-plus zero mode for the Arnold-Majorana network, provided the
Bogoliubov transform preserves chirality polarization and the experts fix every
transported Weyl-plus zero-mode witness.
-/
theorem exists_network_fixed_transportWeylPlus_nonzero_ker_of_experts_fix_of_simplifiedBoundaryModel_under_bogoliubov
    {M : RealMajoranaDatum (S := ArnoldMajoranaCarrier E)}
    (T : RealBogoliubovTransform (S := ArnoldMajoranaCarrier E) M)
    (hpres : T.preservesPolarization (M.chiralityPolarization))
    (n : Nat)
    (net : ArnoldMajoranaNetwork n E)
    (β : ℝ)
    [Nonempty (Fin n)]
    (localOp : InfoGeometry.Quantum.KitaevChain.KitaevCell → ArnoldMajoranaCarrier E →L[ℝ] ArnoldMajoranaCarrier E)
    (chain : List InfoGeometry.Quantum.KitaevChain.KitaevCell)
    (hNeg : InfoGeometry.Quantum.KitaevChain.topologicalIndex chain = -1)
    (hSimple :
      InfoGeometry.Quantum.BulkBoundary.SimplifiedBoundaryModel
        (M := M) (P0 := M.chiralityPolarization) localOp chain)
    (hfix : ∀ e : ExpertIdx n, ∀ v : ArnoldMajoranaCarrier E,
      v ∈ M.weylPlus →
      (T.B.comp
        ((InfoGeometry.Quantum.BulkBoundary.globalChainOperatorFromOpenChain
          (S := ArnoldMajoranaCarrier E) localOp chain).comp T.Binv)) v = 0 →
      (net.moe.experts e).apply v = v) :
    ∃ ψplus : ArnoldMajoranaCarrier E,
      arnoldNetworkOutput n net β (fun _ : Unit => ψplus) () = ψplus
        ∧ ψplus ∈ M.weylPlus
        ∧ (T.B.comp
            ((InfoGeometry.Quantum.BulkBoundary.globalChainOperatorFromOpenChain
              (S := ArnoldMajoranaCarrier E) localOp chain).comp T.Binv)) ψplus = 0
        ∧ ψplus ≠ 0 := by
  let hWeyl :=
    InfoGeometry.Quantum.BulkBoundary.weylZeroModeWitnessUnderBogoliubov_of_negativePhase_of_simplifiedBoundaryModel
      (M := M) (T := T) (hpres := hpres) (localOp := localOp) (chain := chain) hNeg hSimple
  rcases hWeyl with
    ⟨ψplus, ψminus, hψplusNe, hψminusNe, hPlus, hMinus, hKerPlus, hKerMinus⟩
  refine ⟨ψplus, ?_, hPlus, hKerPlus, hψplusNe⟩
  exact arnoldNetworkOutput_eq_of_experts_fix
    (n := n) (net := net) (β := β) (x := fun _ : Unit => ψplus) (i := ())
    (hfix := fun e => hfix e ψplus hPlus hKerPlus)

/--
Turn a simplified-boundary-model negative phase into a concrete fixed nonzero
transported Weyl-minus zero mode for the Arnold-Majorana network, provided the
Bogoliubov transform preserves chirality polarization and the experts fix every
transported Weyl-minus zero-mode witness.
-/
theorem exists_network_fixed_transportWeylMinus_nonzero_ker_of_experts_fix_of_simplifiedBoundaryModel_under_bogoliubov
    {M : RealMajoranaDatum (S := ArnoldMajoranaCarrier E)}
    (T : RealBogoliubovTransform (S := ArnoldMajoranaCarrier E) M)
    (hpres : T.preservesPolarization (M.chiralityPolarization))
    (n : Nat)
    (net : ArnoldMajoranaNetwork n E)
    (β : ℝ)
    [Nonempty (Fin n)]
    (localOp : InfoGeometry.Quantum.KitaevChain.KitaevCell → ArnoldMajoranaCarrier E →L[ℝ] ArnoldMajoranaCarrier E)
    (chain : List InfoGeometry.Quantum.KitaevChain.KitaevCell)
    (hNeg : InfoGeometry.Quantum.KitaevChain.topologicalIndex chain = -1)
    (hSimple :
      InfoGeometry.Quantum.BulkBoundary.SimplifiedBoundaryModel
        (M := M) (P0 := M.chiralityPolarization) localOp chain)
    (hfix : ∀ e : ExpertIdx n, ∀ v : ArnoldMajoranaCarrier E,
      v ∈ M.weylMinus →
      (T.B.comp
        ((InfoGeometry.Quantum.BulkBoundary.globalChainOperatorFromOpenChain
          (S := ArnoldMajoranaCarrier E) localOp chain).comp T.Binv)) v = 0 →
      (net.moe.experts e).apply v = v) :
    ∃ ψminus : ArnoldMajoranaCarrier E,
      arnoldNetworkOutput n net β (fun _ : Unit => ψminus) () = ψminus
        ∧ ψminus ∈ M.weylMinus
        ∧ (T.B.comp
            ((InfoGeometry.Quantum.BulkBoundary.globalChainOperatorFromOpenChain
              (S := ArnoldMajoranaCarrier E) localOp chain).comp T.Binv)) ψminus = 0
        ∧ ψminus ≠ 0 := by
  let hWeyl :=
    InfoGeometry.Quantum.BulkBoundary.weylZeroModeWitnessUnderBogoliubov_of_negativePhase_of_simplifiedBoundaryModel
      (M := M) (T := T) (hpres := hpres) (localOp := localOp) (chain := chain) hNeg hSimple
  rcases hWeyl with
    ⟨ψplus, ψminus, hψplusNe, hψminusNe, hPlus, hMinus, hKerPlus, hKerMinus⟩
  refine ⟨ψminus, ?_, hMinus, hKerMinus, hψminusNe⟩
  exact arnoldNetworkOutput_eq_of_experts_fix
    (n := n) (net := net) (β := β) (x := fun _ : Unit => ψminus) (i := ())
    (hfix := fun e => hfix e ψminus hMinus hKerMinus)

/-- 
A cost matrix for the Sinkhorn optimal transport problem, representing the 
transport cost between tokens and experts. 
-/
def SinkhornCostMatrix (Tok : Type*) [Fintype Tok] (n : Nat) := Tok → ExpertIdx n → ℝ

/-- A transport plan for Sinkhorn routing. -/
def SinkhornPlan (Tok : Type*) [Fintype Tok] (n : Nat) := Tok → ExpertIdx n → ℝ

/-- 
Extract the Sinkhorn cost matrix directly from the Arnold-Majorana network's routing energy.
This formally bridges the algebraic expert routing with the PyTorch Sinkhorn optimal transport pipeline.
-/
noncomputable def arnoldToSinkhornCost (n : Nat) {Tok : Type*} [Fintype Tok] (x : Tok → ArnoldMajoranaCarrier E) :
    SinkhornCostMatrix Tok n :=
  fun i e => arnoldRoutingEnergy n x i e

/-- 
The Sinkhorn target objective (without entropy regularization) given a transport plan P 
and the Arnold-Majorana cost matrix C.
-/
noncomputable def sinkhornObjective {Tok : Type*} [Fintype Tok] (n : Nat)
    (P : SinkhornPlan (Tok := Tok) n) (C : SinkhornCostMatrix (Tok := Tok) n) : ℝ :=
  ∑ i : Tok, ∑ e : ExpertIdx n, P i e * C i e

end InfoGeometry.Canonical.MoE
