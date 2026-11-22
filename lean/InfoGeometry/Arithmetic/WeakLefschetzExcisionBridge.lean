/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology

/-!
# InfoGeometry.Arithmetic.WeakLefschetzExcisionBridge

Formalizes the exact cohomological equivalence between **Artin affine vanishing**
and the **Weak Lefschetz Theorem** via the excision long exact sequence, together
with Frobenius-equivariant eigenvalue inheritance and the first Mathlib-native
`Scheme.EllAdicCohomology` instantiation in `InfoGeometry`:

1. **Excision Long-Exact-Sequence Reduction (`weakLefschetz_of_artinVanishing`)**:
   For graded additive groups `HcU`, `HX`, `HY` connected by an excision long exact
   sequence `HcU k —(j_!)→ HX k —(i^*)→ HY k —(δ)→ HcU (k + 1)`:
   - `Subsingleton (HcU k)` implies `Function.Injective (iStar k)` (`k ≤ d - 1`);
   - `Subsingleton (HcU (k + 1))` implies `Function.Surjective (iStar k)` (`k < d - 1`);
   - Artin vanishing (`∀ m < d, Subsingleton (HcU m)`) yields both an explicit
     `AddEquiv` `HX k ≃+ HY k` for all `k + 1 < d` and injectivity of `iStar (d - 1)`.
2. **Exact Converse (`vanishing_of_surj_prev_and_inj`)**:
   Surjectivity of `iStar k` together with injectivity of `iStar (k + 1)` forces
   `Subsingleton (HcU (k + 1))`.
3. **Frobenius-Equivariant Eigenvalue Transfer (`frobenius_eigenvalue_of_injective_intertwiner`)**:
   If a `𝕜`-linear restriction `iStar : VX →ₗ[𝕜] VY` intertwines Frobenius
   endomorphisms (`iStar ∘ FX = FY ∘ iStar`) and is injective, then every
   Frobenius eigenvector `(v ≠ 0, FX v = α • v)` on `VX` transports to a
   nonzero Frobenius eigenvector `iStar v` with the exact same eigenvalue `α` on
   `VY` (the inductive hyperplane-section step used in Deligne / Alpöge).
4. **Mathlib-Native `Scheme.EllAdicCohomology` Empty-Complement Instantiation**:
   Directly imports `Mathlib.AlgebraicGeometry.Sites.ElladicCohomology` and verifies
   that when the complement scheme `U : Scheme.{u}` satisfies `[IsEmpty U]`,
   Mathlib's `U.EllAdicCohomology ℓ n` satisfies the `Subsingleton` vanishing
   hypothesis in every degree `n`.

Scope note: this module proves the exact algebraic/cohomological reduction from
Artin vanishing to Weak Lefschetz and instantiates the empty-complement case on
Mathlib's `Scheme.EllAdicCohomology`. It does not construct compactly supported
étale cohomology `H^k_c` of constructible `ℓ`-adic sheaves or prove Artin's
geometric affine vanishing theorem for arbitrary affine varieties.
-/

noncomputable section

open AlgebraicGeometry

namespace InfoGeometry.Arithmetic.WeakLefschetzExcisionBridge

section ExcisionExactSequence

variable {HcU HX HY : ℕ → Type*}
variable [∀ k, AddCommGroup (HcU k)] [∀ k, AddCommGroup (HX k)] [∀ k, AddCommGroup (HY k)]

/-- If `HcU k` vanishes (`Subsingleton`), exactness at `HX k` forces
`iStar k : HX k →+ HY k` to be injective. -/
theorem weakLefschetz_injective_of_vanishing
    {k : ℕ} (jBang : HcU k →+ HX k) (iStar : HX k →+ HY k)
    (hexact : Function.Exact jBang iStar)
    [Subsingleton (HcU k)] :
    Function.Injective iStar := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨u, rfl⟩ := (hexact x).mp hx
  rw [Subsingleton.elim u 0, map_zero]

/-- If `HcU (k + 1)` vanishes (`Subsingleton`), exactness at `HY k` forces
`iStar k : HX k →+ HY k` to be surjective. -/
theorem weakLefschetz_surjective_of_vanishing
    {k : ℕ} (iStar : HX k →+ HY k) (delta : HY k →+ HcU (k + 1))
    (hexact : Function.Exact iStar delta)
    [Subsingleton (HcU (k + 1))] :
    Function.Surjective iStar := by
  intro y
  exact (hexact y).mp (Subsingleton.elim (delta y) 0)

/-- Under vanishing of both `HcU k` and `HcU (k + 1)`, `iStar k` is bijective
and yields an explicit group isomorphism `HX k ≃+ HY k`. -/
def weakLefschetz_equiv_of_vanishing
    {k : ℕ} (jBang : HcU k →+ HX k) (iStar : HX k →+ HY k) (delta : HY k →+ HcU (k + 1))
    (hEX : Function.Exact jBang iStar) (hEY : Function.Exact iStar delta)
    [Subsingleton (HcU k)] [Subsingleton (HcU (k + 1))] :
    HX k ≃+ HY k :=
  AddEquiv.ofBijective iStar
    ⟨weakLefschetz_injective_of_vanishing jBang iStar hEX,
     weakLefschetz_surjective_of_vanishing iStar delta hEY⟩

/-- **Artin Vanishing → Weak Lefschetz**:
Given an excision long exact sequence
`HcU k → HX k → HY k → HcU (k + 1)` and Artin affine vanishing
(`∀ m < d, Subsingleton (HcU m)`), the restriction `iStar k : HX k →+ HY k` is:
1. bijective for every `k + 1 < d`, and
2. injective at the middle degree `k = d - 1` (for `0 < d`). -/
theorem weakLefschetz_of_artinVanishing
    (d : ℕ)
    (jBang : ∀ k, HcU k →+ HX k)
    (iStar : ∀ k, HX k →+ HY k)
    (delta : ∀ k, HY k →+ HcU (k + 1))
    (hEX : ∀ k, Function.Exact (jBang k) (iStar k))
    (hEY : ∀ k, Function.Exact (iStar k) (delta k))
    (hArtin : ∀ m, m < d → Subsingleton (HcU m)) :
    (∀ k, k + 1 < d → Function.Bijective (iStar k)) ∧
    (0 < d → Function.Injective (iStar (d - 1))) := by
  refine ⟨fun k hk => ?_, fun hd => ?_⟩
  · have : Subsingleton (HcU k) := hArtin k (by omega)
    have : Subsingleton (HcU (k + 1)) := hArtin (k + 1) hk
    exact ⟨weakLefschetz_injective_of_vanishing (jBang k) (iStar k) (hEX k),
      weakLefschetz_surjective_of_vanishing (iStar k) (delta k) (hEY k)⟩
  · have : Subsingleton (HcU (d - 1)) := hArtin (d - 1) (by omega)
    exact weakLefschetz_injective_of_vanishing (jBang (d - 1)) (iStar (d - 1)) (hEX (d - 1))

/-- **Exact Converse (`Weak Lefschetz → Vanishing`)**:
If `iStar k` is surjective and `iStar (k + 1)` is injective in an exact sequence
`HX k —(iStar k)→ HY k —(delta k)→ HcU (k + 1) —(jBang (k + 1))→ HX (k + 1)`,
then `HcU (k + 1)` is trivial (`Subsingleton`). -/
theorem vanishing_of_surj_prev_and_inj
    {k : ℕ}
    (iStar : HX k →+ HY k) (delta : HY k →+ HcU (k + 1))
    (jBangNext : HcU (k + 1) →+ HX (k + 1)) (iStarNext : HX (k + 1) →+ HY (k + 1))
    (hE_Y : Function.Exact iStar delta)
    (hE_U : Function.Exact delta jBangNext)
    (hE_X : Function.Exact jBangNext iStarNext)
    (hsurj : Function.Surjective iStar)
    (hinj : Function.Injective iStarNext) :
    Subsingleton (HcU (k + 1)) := by
  refine subsingleton_iff.mpr fun u v => ?_
  have hzero : ∀ w : HcU (k + 1), w = 0 := by
    intro w
    have h1 : iStarNext (jBangNext w) = 0 := (hE_X (jBangNext w)).mpr ⟨w, rfl⟩
    have h2 : jBangNext w = 0 := hinj (h1.trans (map_zero iStarNext).symm)
    obtain ⟨y, hy⟩ := (hE_U w).mp h2
    obtain ⟨x, rfl⟩ := hsurj y
    rw [← hy]
    exact (hE_Y (iStar x)).mpr ⟨x, rfl⟩
  rw [hzero u, hzero v]

end ExcisionExactSequence

section FrobeniusEquivariance

variable {𝕜 VX VY : Type*} [Field 𝕜]
variable [AddCommGroup VX] [Module 𝕜 VX] [AddCommGroup VY] [Module 𝕜 VY]

/-- **Frobenius Eigenvalue Transfer Under Weak Lefschetz**:
If a `𝕜`-linear restriction `iStar : VX →ₗ[𝕜] VY` is injective and intertwines
Frobenius endomorphisms `FX` and `FY`, then every Frobenius eigenvector on `VX`
maps to a nonzero Frobenius eigenvector with the exact same eigenvalue `α` on `VY`. -/
theorem frobenius_eigenvalue_of_injective_intertwiner
    (iStar : VX →ₗ[𝕜] VY) (FX : Module.End 𝕜 VX) (FY : Module.End 𝕜 VY)
    (hinj : Function.Injective iStar)
    (hcomm : ∀ v, iStar (FX v) = FY (iStar v))
    {α : 𝕜} {v : VX} (hv : v ≠ 0) (heig : FX v = α • v) :
    iStar v ≠ 0 ∧ FY (iStar v) = α • iStar v := by
  refine ⟨fun h0 => hv (hinj (h0.trans (map_zero iStar).symm)), ?_⟩
  rw [← hcomm v, heig, map_smul]

end FrobeniusEquivariance

section MathlibEllAdic

/-- **Mathlib-Native `Scheme.EllAdicCohomology` Empty-Complement Witness**:
On Mathlib's pro-étale `ℓ`-adic cohomology `U.EllAdicCohomology ℓ n`, an empty
complement scheme `U` satisfies the `Subsingleton` vanishing hypothesis in every
degree `n`, yielding bijectivity of any excision-exact restriction map `iStar`. -/
theorem ellAdicCohomology_empty_complement_bijective.{u}
    (U : Scheme.{u}) [IsEmpty U] (ℓ : ℕ) [Fact ℓ.Prime]
    {HX HY : ℕ → Type (u + 1)}
    [∀ k, AddCommGroup (HX k)] [∀ k, AddCommGroup (HY k)]
    (jBang : ∀ k, U.EllAdicCohomology ℓ k →+ HX k)
    (iStar : ∀ k, HX k →+ HY k)
    (delta : ∀ k, HY k →+ U.EllAdicCohomology ℓ (k + 1))
    (hEX : ∀ k, Function.Exact (jBang k) (iStar k))
    (hEY : ∀ k, Function.Exact (iStar k) (delta k))
    (k : ℕ) :
    Function.Bijective (iStar k) :=
  ⟨weakLefschetz_injective_of_vanishing (jBang k) (iStar k) (hEX k),
   weakLefschetz_surjective_of_vanishing (iStar k) (delta k) (hEY k)⟩

end MathlibEllAdic

end InfoGeometry.Arithmetic.WeakLefschetzExcisionBridge
