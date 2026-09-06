import Mathlib.Tactic
import InfoGeometry.External.Virasoro.HeisenbergAlgebra

/-!
# Heisenberg mode orientation flip

This file proves the orientation-reversal theorem for the centrally extended
Heisenberg algebra.

The mode flip is

`Jₙ ↦ J₋ₙ`

and the central generator transforms by

`K ↦ -K`.

This is the algebra-level Lie automorphism. It is not a same-level
representation conjugation theorem.
-/

namespace VirasoroProject

open Module

namespace AbelianLieAlgebraOn

variable (𝕜 : Type*) [Field 𝕜]

/--
Mode orientation reversal on the abelian current algebra.

On basis currents:

`Iₙ ↦ I₋ₙ`.
-/
noncomputable def modeFlip :
    AbelianLieAlgebraOn ℤ 𝕜 →ₗ[𝕜] AbelianLieAlgebraOn ℤ 𝕜 :=
  (jgen 𝕜).constr 𝕜 fun n : ℤ => jgen 𝕜 (-n)

@[simp] lemma modeFlip_jgen (n : ℤ) :
    modeFlip 𝕜 (jgen 𝕜 n) = jgen 𝕜 (-n) := by
  simpa [modeFlip, jgen_eq_single] using
    ((jgen 𝕜).constr_basis 𝕜 (fun m : ℤ => jgen 𝕜 (-m)) n)

/--
Pointwise cocycle orientation-flip theorem.

This is the atomic sign calculation:

`ω(I₋ₖ, I₋ₗ) = -ω(Iₖ, Iₗ)`.
-/
theorem heisenbergCocycle_modeFlip_jgen_jgen (k l : ℤ) :
    heisenbergCocycleBilin 𝕜
        (modeFlip 𝕜 (jgen 𝕜 k))
        (modeFlip 𝕜 (jgen 𝕜 l))
      =
    - heisenbergCocycleBilin 𝕜 (jgen 𝕜 k) (jgen 𝕜 l) := by
  simp only [modeFlip_jgen, heisenbergCocycleBilin_apply_jgen_jgen]
  by_cases h : k + l = 0
  · have hflip : -k + -l = 0 := by omega
    simp [h, hflip]
  · have hflip : -k + -l ≠ 0 := by omega
    simp [h, hflip]

/-- The abelian mode flip is involutive. -/
theorem modeFlip_involutive :
    (modeFlip 𝕜).comp (modeFlip 𝕜)
      =
    (LinearMap.id : AbelianLieAlgebraOn ℤ 𝕜 →ₗ[𝕜] AbelianLieAlgebraOn ℤ 𝕜) := by
  apply (jgen 𝕜).ext
  intro n
  apply Finsupp.ext
  intro i
  simp [LinearMap.comp_apply, modeFlip]

end AbelianLieAlgebraOn

namespace HeisenbergAlgebra

variable (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]

/--
Orientation reversal of the centrally extended Heisenberg algebra.

On generators:

* `Jₙ ↦ J₋ₙ`
* `K ↦ -K`

The central sign is necessary.
-/
noncomputable def modeFlip :
    HeisenbergAlgebra 𝕜 →ₗ[𝕜] HeisenbergAlgebra 𝕜 :=
  { toFun := fun X => ⟨AbelianLieAlgebraOn.modeFlip 𝕜 X.fst, -X.snd⟩
    map_add' := by
      intro X Y
      apply ext'
      · simp [AbelianLieAlgebraOn.modeFlip]
      · simp [add_comm]
    map_smul' := by
      intro c X
      apply ext'
      · simp [AbelianLieAlgebraOn.modeFlip]
      · simp }

@[simp] lemma modeFlip_kgen :
    modeFlip 𝕜 (kgen 𝕜) = - kgen 𝕜 := by
  rw [kgen_eq']
  have hneg :
      - (⟨(0 : AbelianLieAlgebraOn ℤ 𝕜), (1 : 𝕜)⟩ : HeisenbergAlgebra 𝕜) =
      ⟨(0 : AbelianLieAlgebraOn ℤ 𝕜), (-1 : 𝕜)⟩ := by
    apply ext'
    · let p : HeisenbergAlgebra 𝕜 →+ AbelianLieAlgebraOn ℤ 𝕜 :=
        { toFun := fun X => X.fst
          map_zero' := rfl
          map_add' := by
            intro X Y
            rfl }
      have h := p.map_neg
        (⟨(0 : AbelianLieAlgebraOn ℤ 𝕜), (1 : 𝕜)⟩ : HeisenbergAlgebra 𝕜)
      rw [show p (⟨(0 : AbelianLieAlgebraOn ℤ 𝕜), (1 : 𝕜)⟩ : HeisenbergAlgebra 𝕜) = 0 by rfl] at h
      simpa [p] using h
    · let q : HeisenbergAlgebra 𝕜 →+ 𝕜 :=
        { toFun := fun X => X.snd
          map_zero' := rfl
          map_add' := by
            intro X Y
            rfl }
      have h := q.map_neg
        (⟨(0 : AbelianLieAlgebraOn ℤ 𝕜), (1 : 𝕜)⟩ : HeisenbergAlgebra 𝕜)
      rw [show q (⟨(0 : AbelianLieAlgebraOn ℤ 𝕜), (1 : 𝕜)⟩ : HeisenbergAlgebra 𝕜) = 1 by rfl] at h
      simpa [q] using h
  simpa [modeFlip, kgen_eq'] using hneg.symm

@[simp] lemma modeFlip_jgen (n : ℤ) :
    modeFlip 𝕜 (jgen 𝕜 n) = jgen 𝕜 (-n) := by
  apply ext'
  · simp [modeFlip, jgen_eq', AbelianLieAlgebraOn.modeFlip_jgen]
  · simp [modeFlip, jgen_eq']

@[simp] lemma lie_jgen_kgen (n : ℤ) :
    ⁅jgen 𝕜 n, kgen 𝕜⁆ = 0 := by
  apply ext'
  · simp [bracket_def', toAbelianLieAlgebraOn_kgen]
  · simp [bracket_def', toAbelianLieAlgebraOn_kgen]

/--
Generator-level Lie compatibility for two current modes.

This proves the key obstruction is handled correctly:

`Φ [Jₘ, Jₙ] = [Φ Jₘ, Φ Jₙ]`

where `Φ Jₙ = J₋ₙ` and `Φ K = -K`.
-/
theorem modeFlip_lie_jgen_jgen (m n : ℤ) :
    modeFlip 𝕜 ⁅jgen 𝕜 m, jgen 𝕜 n⁆
      =
    ⁅modeFlip 𝕜 (jgen 𝕜 m), modeFlip 𝕜 (jgen 𝕜 n)⁆ := by
  by_cases h : m + n = 0
  · have hflip : -m + -n = 0 := by omega
    rw [lie_jgen, if_pos h]
    simp [modeFlip_kgen, modeFlip_jgen, hflip]
  · have hflip : -m + -n ≠ 0 := by omega
    rw [lie_jgen, if_neg h]
    simp [modeFlip_jgen, hflip]

/--
Basis-level Lie compatibility.

This covers all four generator cases:

* `K,K`
* `K,Jₙ`
* `Jₘ,K`
* `Jₘ,Jₙ`

The final case is `modeFlip_lie_jgen_jgen`.
-/
theorem modeFlip_lie_basis (a b : Option ℤ) :
    modeFlip 𝕜 ⁅basisJK 𝕜 a, basisJK 𝕜 b⁆
      =
    ⁅modeFlip 𝕜 (basisJK 𝕜 a), modeFlip 𝕜 (basisJK 𝕜 b)⁆ := by
  cases a with
  | none =>
      cases b with
      | none =>
          simp [basisJK_none, modeFlip_kgen]
      | some n =>
          simp [basisJK_none, basisJK_some, modeFlip_kgen, modeFlip_jgen]
  | some m =>
      cases b with
      | none =>
          simp [basisJK_none, basisJK_some, modeFlip_kgen, modeFlip_jgen]
      | some n =>
          simpa using modeFlip_lie_jgen_jgen (𝕜 := 𝕜) m n

/-- The mode flip is involutive. -/
theorem modeFlip_comp_modeFlip :
    (modeFlip 𝕜).comp (modeFlip 𝕜)
      =
    LinearMap.id := by
  apply (basisJK 𝕜).ext
  intro a
  cases a with
  | none =>
      simp [LinearMap.comp_apply, map_neg, modeFlip_kgen]
  | some n =>
      simp [LinearMap.comp_apply]

/-- Bilinear map `X,Y ↦ Φ [X,Y]`. -/
noncomputable def flipBracketBilin :
    HeisenbergAlgebra 𝕜 →ₗ[𝕜]
      HeisenbergAlgebra 𝕜 →ₗ[𝕜]
        HeisenbergAlgebra 𝕜 where
  toFun X :=
    { toFun := fun Y => modeFlip 𝕜 ⁅X, Y⁆
      map_add' := by
        intro Y Z
        simp [lie_add, map_add]
      map_smul' := by
        intro c Y
        simp [lie_smul, map_smul] }
  map_add' := by
    intro X Y
    ext Z
    simp [add_lie, map_add]
  map_smul' := by
    intro c X
    ext Y
    simp [smul_lie, map_smul]

/-- Bilinear map `X,Y ↦ [Φ X, Φ Y]`. -/
noncomputable def bracketFlipBilin :
    HeisenbergAlgebra 𝕜 →ₗ[𝕜]
      HeisenbergAlgebra 𝕜 →ₗ[𝕜]
        HeisenbergAlgebra 𝕜 where
  toFun X :=
    { toFun := fun Y => ⁅modeFlip 𝕜 X, modeFlip 𝕜 Y⁆
      map_add' := by
        intro Y Z
        simp [map_add, lie_add]
      map_smul' := by
        intro c Y
        simp [map_smul, lie_smul] }
  map_add' := by
    intro X Y
    ext Z
    simp [map_add, add_lie]
  map_smul' := by
    intro c X
    ext Y
    simp [map_smul, smul_lie]

/--
Full Lie compatibility.

This upgrades the generator calculation to arbitrary Heisenberg algebra elements
by bilinear extension over the basis `basisJK`.
-/
theorem modeFlip_lie (X Y : HeisenbergAlgebra 𝕜) :
    modeFlip 𝕜 ⁅X, Y⁆
      =
    ⁅modeFlip 𝕜 X, modeFlip 𝕜 Y⁆ := by
  have h : flipBracketBilin 𝕜 = bracketFlipBilin 𝕜 := by
    apply LinearMap.ext_basis (basisJK 𝕜) (basisJK 𝕜)
    intro a b
    exact modeFlip_lie_basis (𝕜 := 𝕜) a b
  exact LinearMap.congr_fun₂ h X Y

/-- The honest Heisenberg orientation-reversal Lie automorphism. -/
noncomputable def modeFlipLieHom :
    HeisenbergAlgebra 𝕜 →ₗ⁅𝕜⁆ HeisenbergAlgebra 𝕜 :=
  LieHom.mk (modeFlip 𝕜) (by
    intro X Y
    exact modeFlip_lie (𝕜 := 𝕜) X Y)

end HeisenbergAlgebra

end VirasoroProject
