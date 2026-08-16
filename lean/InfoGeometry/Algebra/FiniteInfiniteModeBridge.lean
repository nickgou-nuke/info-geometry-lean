import InfoGeometry.Algebra.FiniteN2Induction
import InfoGeometry.Algebra.N2ModeCentralExtension
import InfoGeometry.Algebra.SupergradedCocycle
import InfoGeometry.External.Virasoro.AffineKacMoody
import InfoGeometry.External.Virasoro.HeisenbergAlgebra
import InfoGeometry.External.Virasoro.Sugawara
import InfoGeometry.External.Virasoro.VirasoroAlgebra

/-!
# Finite N=2 closure and infinite-mode current closure

This file applies the finite-to-infinite SOP without asserting an analytic
limit theorem.

The bridge is equation-shape only:

* finite N=2 closure is `anticommutator Q R = H + Z`;
* Virasoro closure is a shifted mode plus an explicit central cocycle;
* Heisenberg closure is a central cocycle on resonant modes;
* affine Kac-Moody closure is a loop-current bracket plus residue cocycle;
* Sugawara closure is available only under the local truncation property.

No wrappers. No property fields. No completion claim.
-/

namespace InfoGeometry.Algebra.FiniteInfiniteModeBridge

open InfoGeometry.Algebra.FiniteN2Induction

universe u

/-! ## Finite source invariant -/

/--
Finite N=2 closure transported through an iterated bonding/symmetry
endomorphism.

This is the finite source invariant used before comparing with infinite-mode
central-extension laws.
-/
theorem finite_iterate_n2_closure_structural_plus_central
    {A : Type*} [Ring A]
    (φ : A →+* A)
    (n : ℕ)
    (Q R H Z : A)
    (hQR : anticommutator Q R = H + Z) :
    anticommutator ((iterateEnd φ n) Q) ((iterateEnd φ n) R) =
      (iterateEnd φ n) H + (iterateEnd φ n) Z := by
  exact iterateEnd_preserves_n2_closure φ n Q R H Z hQR

/--
Finite N=2 square closure transported through an iterated bonding/symmetry
endomorphism.
-/
theorem finite_iterate_n2_square_structural_plus_central
    {A : Type*} [Ring A]
    (φ : A →+* A)
    (n : ℕ)
    (Q R H Z : A)
    (hQ : Q * Q = 0)
    (hR : R * R = 0)
    (hQR : anticommutator Q R = H + Z) :
    (iterateEnd φ n) (Q + R) * (iterateEnd φ n) (Q + R) =
      (iterateEnd φ n) H + (iterateEnd φ n) Z := by
  exact iterateEnd_preserves_n2_square_closure φ n Q R H Z hQ hR hQR

/-! ## N=2 mode central-extension closure -/

/--
N=2 mode central-extension generator closure.

This integrates the direct-sum N=2 lane with the external-Virasoro-style
central-extension lane: the lifted `Qᵢ,Rⱼ` bracket closes on the resonant
central generator.
-/
theorem n2_mode_qgen_rgen_bracket_central
    {ι : Type u} [DecidableEq ι]
    (𝕜 : Type u) [Field 𝕜] [CharZero 𝕜]
    (i j : ι) :
    ⁅N2ModeCentralExtension.N2CentralExt.qgen 𝕜 i,
      N2ModeCentralExtension.N2CentralExt.rgen 𝕜 j⁆
      =
      if i = j
      then N2ModeCentralExtension.N2CentralExt.cgen (ι := ι) 𝕜
      else 0 := by
  simpa [N2ModeCentralExtension.N2CentralExt.cgen] using
    N2ModeCentralExtension.N2CentralExt.qgen_lie_rgen (ι := ι) (𝕜 := 𝕜) i j

/--
The central component of the N=2 lifted `Qᵢ,Rⱼ` bracket is the resonant
Kronecker coefficient.
-/
theorem n2_mode_qgen_rgen_central_component
    {ι : Type u} [DecidableEq ι]
    (𝕜 : Type u) [Field 𝕜] [CharZero 𝕜]
    (i j : ι) :
    ⁅N2ModeCentralExtension.N2CentralExt.qgen 𝕜 i,
      N2ModeCentralExtension.N2CentralExt.rgen 𝕜 j⁆.snd
      =
      if i = j then 1 else 0 := by
  simp [N2ModeCentralExtension.N2CentralExt.qgen,
    N2ModeCentralExtension.N2CentralExt.rgen,
    N2ModeCentralExtension.N2CentralExt.ofBase,
    VirasoroProject.LieTwoCocycle.CentralExtension.lie_def]

/--
The ordinary central-extension bracket and the supergraded odd-odd cocycle
carry the same resonant central coefficient on `Qᵢ,Rⱼ`.

The signs differ only in the opposite order: ordinary Lie cocycles are skew,
while the N=2 odd-odd super-cocycle is symmetric.
-/
theorem n2_mode_lie_central_component_eq_super_oddOdd_cocycle
    {ι : Type u} [DecidableEq ι]
    (𝕜 : Type u) [Field 𝕜] [CharZero 𝕜]
    (i j : ι) :
    ⁅N2ModeCentralExtension.N2CentralExt.qgen 𝕜 i,
      N2ModeCentralExtension.N2CentralExt.rgen 𝕜 j⁆.snd
      =
      SupergradedCocycle.superBilin 𝕜
        (N2ModeCentralExtension.N2ModeBase.qgen 𝕜 i)
        (N2ModeCentralExtension.N2ModeBase.rgen 𝕜 j) := by
  simp [N2ModeCentralExtension.N2CentralExt.qgen,
    N2ModeCentralExtension.N2CentralExt.rgen,
    N2ModeCentralExtension.N2CentralExt.ofBase,
    VirasoroProject.LieTwoCocycle.CentralExtension.lie_def]

/-! ## Virasoro mode closure -/

/--
Virasoro generator closure: shifted Witt mode plus the explicit central
cocycle at the resonance `n + m = 0`.
-/
theorem virasoro_lgen_bracket_structural_plus_central
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (n m : ℤ) :
    ⁅VirasoroProject.VirasoroAlgebra.lgen 𝕜 n,
      VirasoroProject.VirasoroAlgebra.lgen 𝕜 m⁆
      =
      (n - m : 𝕜) • VirasoroProject.VirasoroAlgebra.lgen 𝕜 (n + m)
        + if n + m = 0
          then ((n ^ 3 - n : 𝕜) / 12) • VirasoroProject.VirasoroAlgebra.cgen 𝕜
          else 0 := by
  exact VirasoroProject.VirasoroAlgebra.lgen_bracket (𝕜 := 𝕜) n m

/-- The Virasoro central generator commutes on the left. -/
theorem virasoro_cgen_bracket_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (X : VirasoroProject.VirasoroAlgebra 𝕜) :
    ⁅VirasoroProject.VirasoroAlgebra.cgen 𝕜, X⁆ = 0 := by
  exact VirasoroProject.VirasoroAlgebra.cgen_bracket (𝕜 := 𝕜) X

/-- The Virasoro central generator commutes on the right. -/
theorem virasoro_bracket_cgen_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (X : VirasoroProject.VirasoroAlgebra 𝕜) :
    ⁅X, VirasoroProject.VirasoroAlgebra.cgen 𝕜⁆ = 0 := by
  exact VirasoroProject.VirasoroAlgebra.bracket_cgen (𝕜 := 𝕜) X

/--
Virasoro central-extension readback for arbitrary elements.

This is the finite-support infinite-mode extension: the Witt component of the
bracket is the Witt bracket, and the central component is the Virasoro
2-cocycle evaluated on the projected Witt modes.
-/
theorem virasoro_bracket_eq_witt_bracket_plus_cocycle
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (X Y : VirasoroProject.VirasoroAlgebra 𝕜) :
    ⁅X, Y⁆ =
      ⟨⁅VirasoroProject.VirasoroAlgebra.toWittAlgebra X,
          VirasoroProject.VirasoroAlgebra.toWittAlgebra Y⁆,
        VirasoroProject.WittAlgebra.virasoroCocycle 𝕜
          (VirasoroProject.VirasoroAlgebra.toWittAlgebra X)
          (VirasoroProject.VirasoroAlgebra.toWittAlgebra Y)⟩ := by
  exact VirasoroProject.VirasoroAlgebra.bracket_def' (𝕜 := 𝕜) X Y

/--
The projected Virasoro bracket is the Witt bracket for arbitrary finite-support
mode combinations.
-/
theorem virasoro_toWitt_bracket
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (X Y : VirasoroProject.VirasoroAlgebra 𝕜) :
    VirasoroProject.VirasoroAlgebra.toWittAlgebra ⁅X, Y⁆ =
      ⁅VirasoroProject.VirasoroAlgebra.toWittAlgebra X,
        VirasoroProject.VirasoroAlgebra.toWittAlgebra Y⁆ := by
  exact VirasoroProject.VirasoroAlgebra.bracket_fst (𝕜 := 𝕜) X Y

/--
The central component of the Virasoro bracket is exactly the Virasoro cocycle
for arbitrary finite-support mode combinations.
-/
theorem virasoro_bracket_central_component_eq_cocycle
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (X Y : VirasoroProject.VirasoroAlgebra 𝕜) :
    ⁅X, Y⁆.snd =
      VirasoroProject.WittAlgebra.virasoroCocycle 𝕜
        (VirasoroProject.VirasoroAlgebra.toWittAlgebra X)
        (VirasoroProject.VirasoroAlgebra.toWittAlgebra Y) := by
  exact VirasoroProject.VirasoroAlgebra.bracket_snd (𝕜 := 𝕜) X Y

/-! ## Heisenberg current closure -/

/--
Heisenberg current closure: there is no shifted structural term because the
base algebra is abelian; only the resonant central cocycle remains.
-/
theorem heisenberg_jgen_bracket_central
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (k l : ℤ) :
    ⁅VirasoroProject.HeisenbergAlgebra.jgen 𝕜 k,
      VirasoroProject.HeisenbergAlgebra.jgen 𝕜 l⁆
      =
      if k + l = 0
      then (k : 𝕜) • VirasoroProject.HeisenbergAlgebra.kgen 𝕜
      else 0 := by
  exact VirasoroProject.HeisenbergAlgebra.lie_jgen (𝕜 := 𝕜) k l

/-- The Heisenberg central generator commutes on the left. -/
theorem heisenberg_kgen_bracket_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (X : VirasoroProject.HeisenbergAlgebra 𝕜) :
    ⁅VirasoroProject.HeisenbergAlgebra.kgen 𝕜, X⁆ = 0 := by
  exact VirasoroProject.HeisenbergAlgebra.lie_kgen (𝕜 := 𝕜) X

/--
Heisenberg central-extension readback for arbitrary elements.

The base Lie algebra is abelian, so the structural component is zero and the
central component is the Heisenberg 2-cocycle.
-/
theorem heisenberg_bracket_eq_cocycle
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (X Y : VirasoroProject.HeisenbergAlgebra 𝕜) :
    ⁅X, Y⁆ =
      ⟨⁅VirasoroProject.HeisenbergAlgebra.toAbelianLieAlgebraOn X,
          VirasoroProject.HeisenbergAlgebra.toAbelianLieAlgebraOn Y⁆,
        VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycle 𝕜
          (VirasoroProject.HeisenbergAlgebra.toAbelianLieAlgebraOn X)
          (VirasoroProject.HeisenbergAlgebra.toAbelianLieAlgebraOn Y)⟩ := by
  exact VirasoroProject.HeisenbergAlgebra.bracket_def' (𝕜 := 𝕜) X Y

/--
The projected Heisenberg bracket vanishes for arbitrary finite-support current
combinations.
-/
theorem heisenberg_projected_bracket_zero
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (X Y : VirasoroProject.HeisenbergAlgebra 𝕜) :
    VirasoroProject.HeisenbergAlgebra.toAbelianLieAlgebraOn ⁅X, Y⁆ = 0 := by
  exact VirasoroProject.HeisenbergAlgebra.toAbelianLieAlgebraOn_bracket (𝕜 := 𝕜) X Y

/--
The central component of the Heisenberg bracket is exactly the Heisenberg
cocycle for arbitrary finite-support current combinations.
-/
theorem heisenberg_bracket_central_component_eq_cocycle
    (𝕜 : Type*) [Field 𝕜] [CharZero 𝕜]
    (X Y : VirasoroProject.HeisenbergAlgebra 𝕜) :
    ⁅X, Y⁆.snd =
      VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycle 𝕜
        (VirasoroProject.HeisenbergAlgebra.toAbelianLieAlgebraOn X)
        (VirasoroProject.HeisenbergAlgebra.toAbelianLieAlgebraOn Y) := by
  exact VirasoroProject.HeisenbergAlgebra.bracket_snd (𝕜 := 𝕜) X Y

/-! ## Affine Kac-Moody current closure -/

/--
Affine Kac-Moody current closure: shifted loop-current bracket plus the
explicit residue central cocycle.
-/
theorem affine_current_bracket_structural_plus_central
    (𝕜 : Type u) [CommRing 𝕜] [IsAddTorsionFree 𝕜]
    (𝓰 : Type u) [LieRing 𝓰] [LieAlgebra 𝕜 𝓰]
    (Φ : LinearMap.BilinForm 𝕜 𝓰)
    (hΦ : Φ.lieInvariant 𝓰)
    (hΦs : Φ.IsSymm)
    (m n : ℤ)
    (x y : 𝓰) :
    ⁅VirasoroProject.affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs m x,
      VirasoroProject.affineCurrentGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs n y⁆
      =
      VirasoroProject.affineCurrentGen
          (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs (m + n) (⁅x, y⁆ : 𝓰)
        + if m + n = 0
          then ((m : 𝕜) * Φ x y) •
            VirasoroProject.affineCentralGen (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs
          else 0 := by
  exact VirasoroProject.affineCurrentGen_bracket
    (𝕜 := 𝕜) (𝓰 := 𝓰) Φ hΦ hΦs m n x y

/-! ## Sugawara closure under local truncation -/

/--
Sugawara Virasoro closure under the actual local truncation property.

This is the allowed finite-to-infinite step for operator modes: the theorem
uses `heiTrunc`, so the formal mode sums are locally finite on each vector.
-/
theorem sugawara_commutator_structural_plus_central_of_truncation
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (heiOper : ℤ → V →ₗ[𝕜] V)
    (heiTrunc : ∀ v, Filter.atTop.Eventually (fun l ↦ (heiOper l) v = 0))
    (heiComm : ∀ k l,
      (heiOper k).commutator (heiOper l) =
        if k + l = 0 then (k : 𝕜) • 1 else 0)
    (n m : ℤ) :
    (VirasoroProject.sugawaraGen heiTrunc n).commutator
        (VirasoroProject.sugawaraGen heiTrunc m)
      =
      (n - m) • VirasoroProject.sugawaraGen heiTrunc (n + m)
        + if n + m = 0
          then ((n ^ 3 - n : 𝕜) / (12 : 𝕜)) • (1 : V →ₗ[𝕜] V)
          else 0 := by
  exact VirasoroProject.commutator_sugawaraGen
    (heiOper := heiOper) heiTrunc heiComm n m

/-- The Sugawara representation has central charge one. -/
theorem sugawara_central_charge_one
    {𝕜 V : Type*} [Field 𝕜] [CharZero 𝕜] [AddCommGroup V] [Module 𝕜 V]
    (heiOper : ℤ → V →ₗ[𝕜] V)
    (heiTrunc : ∀ v, Filter.atTop.Eventually (fun l ↦ (heiOper l) v = 0))
    (heiComm : ∀ k l,
      (heiOper k).commutator (heiOper l) =
        if k + l = 0 then (k : 𝕜) • 1 else 0) :
    VirasoroProject.sugawaraRepresentation heiTrunc heiComm
        (VirasoroProject.VirasoroAlgebra.cgen 𝕜)
      =
      1 := by
  exact VirasoroProject.sugawaraRepresentation_cgen
    (heiOper := heiOper) heiTrunc heiComm

end InfoGeometry.Algebra.FiniteInfiniteModeBridge
