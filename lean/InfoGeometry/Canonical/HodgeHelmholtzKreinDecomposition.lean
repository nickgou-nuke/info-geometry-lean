import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Canonical.HodgeHelmholtzKreinDecomposition

Explicit algebraic corridor for the global layer:

* differential `d` with `d ∘ d = 0`,
* adjoint-like partner `δ` with `δ ∘ δ = 0`,
* Laplacian `Δ = d ∘ δ + δ ∘ d`.

No analytic closure claims are made here.  This file proves the concrete
algebraic commutation and annihilation identities under explicit hypotheses.
-/

namespace InfoGeometry.Canonical.HodgeHelmholtzKreinDecomposition

open LinearMap
open scoped InnerProductSpace

section

variable {R V : Type*}
variable [Ring R] [AddCommGroup V] [Module R V]

/-- Commutator of endomorphisms. -/
def commutator (A B : Module.End R V) : Module.End R V :=
  A.comp B - B.comp A

/--
Algebraic Hodge packet with explicit differential, codifferential,
and Laplacian definition.
-/
structure HodgePacket where
  d : Module.End R V
  δ : Module.End R V
  d_sq : d.comp d = 0
  δ_sq : δ.comp δ = 0
  Δ : Module.End R V
  Δ_def : Δ = d.comp δ + δ.comp d

namespace HodgePacket

variable (H : HodgePacket (R := R) (V := V))

/-- `[d, Δ] = 0` under the explicit Hodge packet laws. -/
theorem d_commutes_Δ : commutator H.d H.Δ = 0 := by
  ext x
  dsimp [commutator]
  have hd2δx : H.d (H.d (H.δ x)) = 0 := by
    simpa using congrArg (fun f : Module.End R V => f (H.δ x)) H.d_sq
  have hd2x : H.δ (H.d (H.d x)) = 0 := by
    simpa using congrArg (fun f : Module.End R V => H.δ (f x)) H.d_sq
  rw [H.Δ_def]
  simp [LinearMap.comp_apply, LinearMap.add_apply, hd2δx, hd2x]

/-- `[δ, Δ] = 0` under the explicit Hodge packet laws. -/
theorem δ_commutes_Δ : commutator H.δ H.Δ = 0 := by
  ext x
  dsimp [commutator]
  have hδ2dx : H.δ (H.δ (H.d x)) = 0 := by
    simpa using congrArg (fun f : Module.End R V => f (H.d x)) H.δ_sq
  have hδ2x : H.d (H.δ (H.δ x)) = 0 := by
    simpa using congrArg (fun f : Module.End R V => H.d (f x)) H.δ_sq
  rw [H.Δ_def]
  simp [LinearMap.comp_apply, LinearMap.add_apply, hδ2dx, hδ2x]

/--
Exact lane into harmonic kernel:
if `x = d y` and `δ x = 0`, then `Δ x = 0`.
-/
theorem exact_into_harmonic_of_δ_closed
    {x y : V}
    (hx : x = H.d y)
    (hδx : H.δ x = 0) :
    H.Δ x = 0 := by
  rw [H.Δ_def, hx]
  have hd2 : H.d (H.d y) = 0 := by
    simpa using congrArg (fun f : Module.End R V => f y) H.d_sq
  have hδterm : H.δ (H.d y) = 0 := by simpa [hx] using hδx
  simp [LinearMap.add_apply, LinearMap.comp_apply, hd2, hδterm]

/--
Coexact lane into harmonic kernel:
if `x = δ y` and `d x = 0`, then `Δ x = 0`.
-/
theorem coexact_into_harmonic_of_d_closed
    {x y : V}
    (hx : x = H.δ y)
    (hdx : H.d x = 0) :
    H.Δ x = 0 := by
  rw [H.Δ_def, hx]
  have hδ2 : H.δ (H.δ y) = 0 := by
    simpa using congrArg (fun f : Module.End R V => f y) H.δ_sq
  have hdterm : H.d (H.δ y) = 0 := by simpa [hx] using hdx
  simp [LinearMap.add_apply, LinearMap.comp_apply, hδ2, hdterm]

/--
Hypothesis-gated exact/coexact/harmonic decomposition data via projectors.

This is the algebraic interface layer: no analytic closed-range/Fredholm
proof is asserted here; those hypotheses are represented by explicit projector
equations.
-/
structure DecompositionPacket where
  Pex : Module.End R V
  Pcoex : Module.End R V
  Pharm : Module.End R V
  Pex_idem : Pex.comp Pex = Pex
  Pcoex_idem : Pcoex.comp Pcoex = Pcoex
  Pharm_idem : Pharm.comp Pharm = Pharm
  Pex_Pcoex_zero : Pex.comp Pcoex = 0
  Pcoex_Pex_zero : Pcoex.comp Pex = 0
  Pex_Pharm_zero : Pex.comp Pharm = 0
  Pharm_Pex_zero : Pharm.comp Pex = 0
  Pcoex_Pharm_zero : Pcoex.comp Pharm = 0
  Pharm_Pcoex_zero : Pharm.comp Pcoex = 0
  partition_unity : Pex + Pcoex + Pharm = 1

namespace DecompositionPacket

variable (D : DecompositionPacket (R := R) (V := V))

/-- Projector partition gives pointwise decomposition `x = Pex x + Pcoex x + Pharm x`. -/
theorem decompose (x : V) :
    x = D.Pex x + D.Pcoex x + D.Pharm x := by
  have h := congrArg (fun f : Module.End R V => f x) D.partition_unity
  simpa [LinearMap.add_apply, add_assoc] using h.symm

/-!
The projector laws also give uniqueness of the three components.  This is
purely algebraic: no inner product, closed-range, or analytic Green operator
is being smuggled into the statement.
-/
theorem unique_decomposition (x a b c : V)
    (hx : x = a + b + c)
    (ha : D.Pex a = a) (hb : D.Pcoex b = b) (hc : D.Pharm c = c) :
    a = D.Pex x ∧ b = D.Pcoex x ∧ c = D.Pharm x := by
  have hxa : D.Pex x = a := by
    rw [hx, map_add, map_add]
    have hPexb : D.Pex b = 0 := by
      have h := congrArg (fun f : Module.End R V => f b) D.Pex_Pcoex_zero
      simpa [LinearMap.comp_apply, hb] using h
    have hPexc : D.Pex c = 0 := by
      have h := congrArg (fun f : Module.End R V => f c) D.Pex_Pharm_zero
      simpa [LinearMap.comp_apply, hc] using h
    simp [ha, hPexb, hPexc]
  have hxb : D.Pcoex x = b := by
    rw [hx, map_add, map_add]
    have hPcoexa : D.Pcoex a = 0 := by
      have h := congrArg (fun f : Module.End R V => f a) D.Pcoex_Pex_zero
      simpa [LinearMap.comp_apply, ha] using h
    have hPcoexc : D.Pcoex c = 0 := by
      have h := congrArg (fun f : Module.End R V => f c) D.Pcoex_Pharm_zero
      simpa [LinearMap.comp_apply, hc] using h
    simp [hPcoexa, hb, hPcoexc]
  have hxc : D.Pharm x = c := by
    rw [hx, map_add, map_add]
    have hPharma : D.Pharm a = 0 := by
      have h := congrArg (fun f : Module.End R V => f a) D.Pharm_Pex_zero
      simpa [LinearMap.comp_apply, ha] using h
    have hPharmb : D.Pharm b = 0 := by
      have h := congrArg (fun f : Module.End R V => f b) D.Pharm_Pcoex_zero
      simpa [LinearMap.comp_apply, hb] using h
    simp [hPharma, hPharmb, hc]
  exact ⟨hxa.symm, hxb.symm, hxc.symm⟩

/-- Pairwise orthogonality implies `(Pex + Pcoex)` is idempotent. -/
theorem exact_coexact_sum_idem :
    (D.Pex + D.Pcoex).comp (D.Pex + D.Pcoex) = D.Pex + D.Pcoex := by
  ext x
  simp [LinearMap.add_comp, LinearMap.comp_add, D.Pex_idem, D.Pcoex_idem,
    D.Pex_Pcoex_zero, D.Pcoex_Pex_zero]

/-- Harmonic projector as complement of exact/coexact projector sum. -/
theorem harmonic_as_complement :
    D.Pharm = 1 - (D.Pex + D.Pcoex) := by
  have hpart : D.Pex + D.Pcoex + D.Pharm = 1 := D.partition_unity
  apply eq_sub_iff_add_eq.mpr
  simpa [add_assoc, add_comm, add_left_comm] using hpart

/-- Expanded partition identity with explicit complement form. -/
theorem partition_unity_explicit :
    D.Pex + D.Pcoex + (1 - (D.Pex + D.Pcoex)) = (1 : Module.End R V) := by
  rw [← D.harmonic_as_complement]
  exact D.partition_unity

/-!
The Pythagorean identity belongs to the inner-product layer, not to the
algebraic projector packet.  We therefore state it with exactly the three
pairwise orthogonality facts needed by the norm-addition theorem.
-/
theorem hodge_norm_sq_additive
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a b h : V)
    (hab : ⟪a, b⟫_ℝ = 0) (hah : ⟪a, h⟫_ℝ = 0)
    (hbh : ⟪b, h⟫_ℝ = 0) :
    ‖a + b + h‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖h‖ ^ 2 := by
  have habh : ⟪a + b, h⟫_ℝ = 0 := by
    simp [inner_add_left, hah, hbh]
  have hfirst : ‖a + b + h‖ ^ 2 = ‖a + b‖ ^ 2 + ‖h‖ ^ 2 := by
    simpa [pow_two] using
      (norm_add_sq_eq_norm_sq_add_norm_sq_real habh)
  have hsecond : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    simpa [pow_two] using
      (norm_add_sq_eq_norm_sq_add_norm_sq_real hab)
  rw [hfirst, hsecond]

theorem projector_norm_sq_additive
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (D : DecompositionPacket (R := ℝ) (V := V)) (x : V)
    (hexcoex : ⟪D.Pex x, D.Pcoex x⟫_ℝ = 0)
    (hexharm : ⟪D.Pex x, D.Pharm x⟫_ℝ = 0)
    (hcoexharm : ⟪D.Pcoex x, D.Pharm x⟫_ℝ = 0) :
    ‖x‖ ^ 2 = ‖D.Pex x‖ ^ 2 + ‖D.Pcoex x‖ ^ 2 + ‖D.Pharm x‖ ^ 2 := by
  have hx := D.decompose x
  calc
    ‖x‖ ^ 2 = ‖D.Pex x + D.Pcoex x + D.Pharm x‖ ^ 2 := by
      rw [← hx]
    _ = ‖D.Pex x‖ ^ 2 + ‖D.Pcoex x‖ ^ 2 + ‖D.Pharm x‖ ^ 2 :=
      hodge_norm_sq_additive (D.Pex x) (D.Pcoex x) (D.Pharm x)
        hexcoex hexharm hcoexharm

end DecompositionPacket

end HodgePacket
end

end InfoGeometry.Canonical.HodgeHelmholtzKreinDecomposition
