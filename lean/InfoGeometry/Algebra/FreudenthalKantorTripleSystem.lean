/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.NoncommRing
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Core.SymmetricLie

/-!
# Algebraic Freudenthal--Kantor triple-system contract

This file records the finite algebraic identities used in the supplied
Freudenthal--Kantor reference.  It is a contract for a triple system, not a
construction of a TKK or Kantor Lie algebra.  In particular, no grading or
analytic/Hermitian positivity is inferred from these fields.
-/

namespace InfoGeometry.Algebra

open InfoGeometry.Algebra.FiniteSpin

/-- Non-commutativity witness for the finite spin algebra carrier. -/
theorem exists_noncomm_pair :
    ∃ x y : Mat2C, x * y ≠ y * x :=
  ⟨J_plus, J_minus, j_plus_j_minus_ne⟩

section NonCommRingTripleSystem

variable {B : Type*} [Ring B]

/-- The non-commutative associative ternary product `⟨x, y, z⟩ = x * y * z`
on any ring `[Ring B]`. -/
def assocTriple (x y z : B) : B :=
  x * y * z

/-- The symmetrized Jordan ternary product `{x, y, z} = x * y * z + z * y * x`
on any non-commutative ring `[Ring B]`. -/
def jordanTriple (x y z : B) : B :=
  x * y * z + z * y * x

/-- Outer symmetry of the Jordan ternary product over any `[Ring B]`. -/
theorem jordanTriple_symm_outer (x y z : B) :
    jordanTriple x y z = jordanTriple z y x := by
  dsimp [jordanTriple]
  abel

/-- An element `c : B` in a non-commutative ring `[Ring B]` is ternary-tripotent
when `c * c * c = c`. -/
def IsRingTripotent (c : B) : Prop :=
  assocTriple c c c = c

/-- Fundamental Freudenthal–Kantor left derivation identity for the associative
ternary product `assocTriple x y z = x * y * z` over any non-commutative ring `[Ring B]`
(with `ε = -1`):
`⟨x, y, ⟨z, w, u⟩⟩ - ⟨z, w, ⟨x, y, u⟩⟩ = ⟨⟨x, y, z⟩, w, u⟩ - ⟨z, ⟨w, x, y⟩, u⟩`. -/
theorem assocTriple_left_identity (x y z w u : B) :
    assocTriple x y (assocTriple z w u) - assocTriple z w (assocTriple x y u) =
      assocTriple (assocTriple x y z) w u - assocTriple z (assocTriple w x y) u := by
  dsimp [assocTriple]
  noncomm_ring

/-- Fundamental Jordan triple identity (Macdonald / Meyberg identity) over any
non-commutative ring `[Ring B]`:
`{x, y, {z, w, z}} = {{x, y, z}, w, z} - {z, {y, x, w}, z} + {z, w, {x, y, z}}`. -/
theorem jordanTriple_fundamental_identity (x y z w : B) :
    jordanTriple x y (jordanTriple z w z) =
      jordanTriple (jordanTriple x y z) w z -
        jordanTriple z (jordanTriple y x w) z +
        jordanTriple z w (jordanTriple x y z) := by
  dsimp [jordanTriple]
  noncomm_ring

theorem jordanTriple_left_identity (x y z w u : B) :
    jordanTriple x y (jordanTriple z w u) -
      jordanTriple z w (jordanTriple x y u) =
    jordanTriple (jordanTriple x y z) w u -
      jordanTriple z (jordanTriple y x w) u := by
  dsimp [jordanTriple]
  noncomm_ring

/-- Kantor operator of the associative Jordan triple, at parameter `δ = 1`.
This is an ordered expression in the noncommutative coefficient ring. -/
def jordanTripleK (x y z : B) : B :=
  jordanTriple x z y - jordanTriple y z x

/-- The second Freudenthal--Kantor identity for the associative Jordan triple
holds in every ring. This proves the K identity on an actual associative
noncommutative carrier rather than inhabiting the abstract structure with a
zero product. -/
theorem jordanTriple_K_identity (x y z w u : B) :
    jordanTripleK (jordanTriple x y z) w u +
      jordanTripleK z (jordanTriple x y w) u +
      jordanTripleK x (jordanTripleK z w y) u = 0 := by
  dsimp [jordanTripleK, jordanTriple]
  noncomm_ring

end NonCommRingTripleSystem

variable {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]

def fktsK (delta : R) (triple : U →ₗ[R] U →ₗ[R] U →ₗ[R] U)
    (x y z : U) : U :=
  triple x z y - delta • triple y z x

structure FreudenthalKantorTripleSystem where
  epsilon : R
  delta : R
  triple : U →ₗ[R] U →ₗ[R] U →ₗ[R] U
  left_identity :
    ∀ x y z w u,
      triple x y (triple z w u) - triple z w (triple x y u) =
        triple (triple x y z) w u +
          epsilon • triple z (triple y x w) u
  k_identity :
    ∀ x y z w u,
      fktsK delta triple (triple x y z) w u +
          fktsK delta triple z (triple x y w) u +
            delta • fktsK delta triple x
              (fktsK delta triple z w y) u = 0

namespace FreudenthalKantorTripleSystem

variable (data : FreudenthalKantorTripleSystem (R := R) (U := U))

def K (x y z : U) : U :=
  fktsK data.delta data.triple x y z

def IsTripotent (c : U) : Prop :=
  data.triple c c c = c

theorem tripotent_readout {c : U} (hc : IsTripotent data c) :
    data.triple c c c = c :=
  hc

def IsBitriponent (c₁ c₂ : U) (α β γ : R) : Prop :=
    data.triple c₁ c₁ c₂ = α • c₂ ∧
    data.triple c₂ c₂ c₁ = α • c₁ ∧
    data.triple c₁ c₂ c₁ = β • c₂ ∧
    data.triple c₂ c₁ c₂ = β • c₁ ∧
    data.triple c₂ c₁ c₁ = γ • c₂ ∧
    data.triple c₁ c₂ c₂ = γ • c₁

theorem left_identity_readout (x y z w u : U) :
    data.triple x y (data.triple z w u) - data.triple z w (data.triple x y u) =
      data.triple (data.triple x y z) w u +
        data.epsilon • data.triple z (data.triple y x w) u :=
  data.left_identity x y z w u

theorem k_identity_readout (x y z w u : U) :
    K data (data.triple x y z) w u +
        K data z (data.triple x y w) u +
          data.delta • K data x (K data z w y) u = 0 :=
  data.k_identity x y z w u

section PeirceDecomposition

open scoped DirectSum

/-- Left multiplication operator `L(c, c)(z) = ⟨c, c, z⟩`. -/
def leftMulOp (c : U) : Module.End R U :=
  data.triple c c

@[simp] theorem leftMulOp_apply (c z : U) :
    leftMulOp data c z = data.triple c c z := rfl

/-- Right multiplication operator `R(c, c)(z) = ⟨z, c, c⟩`. -/
def rightMulOp (c : U) : Module.End R U where
  toFun z := data.triple z c c
  map_add' x y := by simp
  map_smul' r x := by simp

@[simp] theorem rightMulOp_apply (c z : U) :
    rightMulOp data c z = data.triple z c c := rfl

/-- The Kantor-Peirce skewness operator `N_δ = L(c, c) - δ • R(c, c)`.
On any tripotent `c`, `peirceN data c z = data.K c z c`; it vanishes on Jordan triple
systems (`K = 0`) and creates the half-integer Peirce sector `V_{1/2}` beyond Jordan systems. -/
def peirceN (c : U) : Module.End R U :=
  leftMulOp data c - data.delta • rightMulOp data c

/-- The complementary Peirce operator `T_δ = (1 + δ) • L(c, c) - R(c, c) + Id`. -/
def peirceT (c : U) : Module.End R U :=
  (1 + data.delta) • leftMulOp data c - rightMulOp data c + 1

theorem peirceN_eq_K (c z : U) :
    peirceN data c z = data.K c z c := by
  simp [peirceN, leftMulOp, rightMulOp, K, fktsK]

theorem peirceT_apply (c z : U) :
    peirceT data c z =
      (1 + data.delta) • data.triple c c z - data.triple z c c + z := by
  simp [peirceT, leftMulOp, rightMulOp]

/-- In any `(-1, δ)`-FKTS, `L(c, c)` and `R(c, c)` commute for every tripotent `c`. -/
theorem leftMulOp_comm_rightMulOp {c : U}
    (heps : data.epsilon = -1) (hc : IsTripotent data c) :
    leftMulOp data c * rightMulOp data c = rightMulOp data c * leftMulOp data c := by
  apply LinearMap.ext
  intro z
  have hL := data.left_identity c c z c c
  have hc' : data.triple c c c = c := hc
  rw [heps, hc'] at hL
  simp only [neg_smul, one_smul] at hL
  have hEq : data.triple c c (data.triple z c c) = data.triple (data.triple c c z) c c := by
    have hL' : data.triple c c (data.triple z c c) - data.triple z c c =
        data.triple (data.triple c c z) c c - data.triple z c c := by
      simpa [sub_eq_add_neg] using hL
    exact eq_of_sub_eq_zero (by rw [← sub_sub_sub_cancel_right _ _ (data.triple z c c), hL', sub_self])
  simpa [Module.End.mul_apply, leftMulOp, rightMulOp] using hEq

/-- Fundamental Kamiya Peirce orthogonality `N_δ ∘ T_δ = 0` for any tripotent `c`
when `δ^2 = 1`. -/
theorem peirceN_mul_peirceT {c : U}
    (hdelta : data.delta ^ 2 = 1) (hc : IsTripotent data c) :
    peirceN data c * peirceT data c = 0 := by
  apply LinearMap.ext
  intro z
  have hK := data.k_identity c c c z c
  rw [hc] at hK
  have hK' :
      peirceN data c z + peirceN data c (leftMulOp data c z) +
        data.delta • peirceN data c (peirceN data c z) = 0 := by
    simpa [K, peirceN_eq_K, leftMulOp] using hK
  have hd2 : data.delta * data.delta = 1 := by simpa [sq] using hdelta
  have hinner :
      z + leftMulOp data c z + data.delta • peirceN data c z = peirceT data c z := by
    simp only [peirceN, peirceT, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply]
    rw [smul_sub, smul_smul, hd2, one_smul, add_smul, one_smul]
    abel
  have hmap :
      peirceN data c (z + leftMulOp data c z + data.delta • peirceN data c z) =
        peirceN data c z + peirceN data c (leftMulOp data c z) +
          data.delta • peirceN data c (peirceN data c z) := by
    simp [map_add, map_smul]
  rw [← hmap, hinner] at hK'
  simpa [Module.End.mul_apply] using hK'

/-- Commuting Peirce orthogonality `T_δ ∘ N_δ = 0` for any tripotent `c`
in a `(-1, δ)`-FKTS with `δ^2 = 1`. -/
theorem peirceT_mul_peirceN {c : U}
    (heps : data.epsilon = -1) (hdelta : data.delta ^ 2 = 1) (hc : IsTripotent data c) :
    peirceT data c * peirceN data c = 0 := by
  have hcomm : peirceT data c * peirceN data c = peirceN data c * peirceT data c := by
    apply LinearMap.ext
    intro z
    have hLR : leftMulOp data c (rightMulOp data c z) = rightMulOp data c (leftMulOp data c z) :=
      LinearMap.congr_fun (leftMulOp_comm_rightMulOp data heps hc) z
    simp only [Module.End.mul_apply, peirceT, peirceN, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply, map_add, map_sub, map_smul]
    rw [hLR]
    simp only [smul_add, smul_sub, smul_smul]
    module
  rw [hcomm, peirceN_mul_peirceT data hdelta hc]

/-- The three Peirce sectors `V_0`, `V_{1/2}`, `V_1` of a `(-1, δ)`-FKTS. -/
inductive PeirceSector : Type
  | zero
  | half
  | one
  deriving DecidableEq, Repr

instance : Fintype PeirceSector where
  elems := {.zero, .half, .one}
  complete s := by cases s <;> simp

/-- `V_0 = ker N_δ ⊓ ker T_δ`. -/
def peirceV0 (c : U) : Submodule R U :=
  LinearMap.ker (peirceN data c) ⊓ LinearMap.ker (peirceT data c)

/-- `V_{1/2} = range N_δ`. -/
def peirceVHalf (c : U) : Submodule R U :=
  LinearMap.range (peirceN data c)

/-- `V_1 = range T_δ`. -/
def peirceV1 (c : U) : Submodule R U :=
  LinearMap.range (peirceT data c)

/-- Indexed Peirce submodule family `V_0, V_{1/2}, V_1`. -/
def peirceSubmodule (c : U) : PeirceSector → Submodule R U
  | .zero => peirceV0 data c
  | .half => peirceVHalf data c
  | .one => peirceV1 data c

theorem peirceVHalf_le_ker_peirceT {c : U}
    (heps : data.epsilon = -1) (hdelta : data.delta ^ 2 = 1) (hc : IsTripotent data c) :
    peirceVHalf data c ≤ LinearMap.ker (peirceT data c) := by
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.mem_ker]
  have h := LinearMap.congr_fun (peirceT_mul_peirceN data heps hdelta hc) x
  simpa [Module.End.mul_apply] using h

theorem peirceV1_le_ker_peirceN {c : U}
    (hdelta : data.delta ^ 2 = 1) (hc : IsTripotent data c) :
    peirceV1 data c ≤ LinearMap.ker (peirceN data c) := by
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.mem_ker]
  have h := LinearMap.congr_fun (peirceN_mul_peirceT data hdelta hc) x
  simpa [Module.End.mul_apply] using h

theorem peirce_iSupIndep {c : U}
    (hNT : peirceN data c * peirceT data c = 0)
    (hTN : peirceT data c * peirceN data c = 0)
    (hN : IsCompl (LinearMap.range (peirceN data c)) (LinearMap.ker (peirceN data c)))
    (hT : IsCompl (LinearMap.range (peirceT data c)) (LinearMap.ker (peirceT data c))) :
    iSupIndep (peirceSubmodule data c) := by
  have hV1_kerN : peirceV1 data c ≤ LinearMap.ker (peirceN data c) := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    simpa [Module.End.mul_apply] using LinearMap.congr_fun hNT x
  have hVH_kerT : peirceVHalf data c ≤ LinearMap.ker (peirceT data c) := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    simpa [Module.End.mul_apply] using LinearMap.congr_fun hTN x
  have hN_bot : ∀ (y : U), y ∈ LinearMap.range (peirceN data c) →
      y ∈ LinearMap.ker (peirceN data c) → y = 0 := fun y hy1 hy2 => by
    have hbot : LinearMap.range (peirceN data c) ⊓ LinearMap.ker (peirceN data c) = ⊥ :=
      disjoint_iff.mp hN.disjoint
    have hy : y ∈ (⊥ : Submodule R U) := by
      rw [← hbot]
      exact ⟨hy1, hy2⟩
    rw [Submodule.mem_bot] at hy
    exact hy
  have hT_bot : ∀ (y : U), y ∈ LinearMap.range (peirceT data c) →
      y ∈ LinearMap.ker (peirceT data c) → y = 0 := fun y hy1 hy2 => by
    have hbot : LinearMap.range (peirceT data c) ⊓ LinearMap.ker (peirceT data c) = ⊥ :=
      disjoint_iff.mp hT.disjoint
    have hy : y ∈ (⊥ : Submodule R U) := by
      rw [← hbot]
      exact ⟨hy1, hy2⟩
    rw [Submodule.mem_bot] at hy
    exact hy
  rw [iSupIndep_def]
  intro s
  rw [disjoint_iff]
  ext x
  simp only [Submodule.mem_inf, Submodule.mem_bot]
  constructor
  · rintro ⟨hxs, hxsup⟩
    have hx_mem_sup : ∀ s₁ s₂ : PeirceSector,
        (∀ t, t ≠ s → t = s₁ ∨ t = s₂) →
        x ∈ peirceSubmodule data c s₁ ⊔ peirceSubmodule data c s₂ := by
      intro s₁ s₂ hall
      have hle : (⨆ t ≠ s, peirceSubmodule data c t) ≤
          peirceSubmodule data c s₁ ⊔ peirceSubmodule data c s₂ := by
        refine iSup₂_le fun t ht => ?_
        rcases hall t ht with rfl | rfl
        · exact le_sup_left
        · exact le_sup_right
      exact hle hxsup
    cases s with
    | zero =>
      have hx12 := hx_mem_sup .half .one (fun t ht => by
        cases t with
        | zero => exact absurd rfl ht
        | half => exact Or.inl rfl
        | one => exact Or.inr rfl)
      rcases Submodule.mem_sup.mp hx12 with ⟨n, hn, t, ht, rfl⟩
      have hx0 : n + t ∈ peirceV0 data c := hxs
      have hNn : n ∈ LinearMap.ker (peirceN data c) := by
        rw [LinearMap.mem_ker]
        have hsumN : peirceN data c (n + t) = 0 := LinearMap.mem_ker.mp hx0.1
        have hNt : peirceN data c t = 0 := LinearMap.mem_ker.mp (hV1_kerN ht)
        rw [map_add, hNt, add_zero] at hsumN
        exact hsumN
      have hTt : t ∈ LinearMap.ker (peirceT data c) := by
        rw [LinearMap.mem_ker]
        have hsumT : peirceT data c (n + t) = 0 := LinearMap.mem_ker.mp hx0.2
        have hTn : peirceT data c n = 0 := LinearMap.mem_ker.mp (hVH_kerT hn)
        rw [map_add, hTn, zero_add] at hsumT
        exact hsumT
      have hn0 : n = 0 := hN_bot n hn hNn
      have ht0 : t = 0 := hT_bot t ht hTt
      simp [hn0, ht0]
    | half =>
      have hx01 := hx_mem_sup .zero .one (fun t ht => by
        cases t with
        | zero => exact Or.inl rfl
        | half => exact absurd rfl ht
        | one => exact Or.inr rfl)
      rcases Submodule.mem_sup.mp hx01 with ⟨z, hz, t, ht, rfl⟩
      have hkerN : z + t ∈ LinearMap.ker (peirceN data c) :=
        Submodule.add_mem _ hz.1 (hV1_kerN ht)
      exact hN_bot (z + t) hxs hkerN
    | one =>
      have hx02 := hx_mem_sup .zero .half (fun t ht => by
        cases t with
        | zero => exact Or.inl rfl
        | half => exact Or.inr rfl
        | one => exact absurd rfl ht)
      rcases Submodule.mem_sup.mp hx02 with ⟨z, hz, n, hn, rfl⟩
      have hkerT : z + n ∈ LinearMap.ker (peirceT data c) :=
        Submodule.add_mem _ hz.2 (hVH_kerT hn)
      exact hT_bot (z + n) hxs hkerT
  · rintro rfl
    exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩

theorem peirce_iSup_eq_top {c : U}
    (hNT : peirceN data c * peirceT data c = 0)
    (hN : IsCompl (LinearMap.range (peirceN data c)) (LinearMap.ker (peirceN data c)))
    (hT : IsCompl (LinearMap.range (peirceT data c)) (LinearMap.ker (peirceT data c))) :
    ⨆ s, peirceSubmodule data c s = ⊤ := by
  have hV1_kerN : peirceV1 data c ≤ LinearMap.ker (peirceN data c) := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    simpa [Module.End.mul_apply] using LinearMap.congr_fun hNT x
  rw [eq_top_iff]
  intro x _
  have hxN : x ∈ LinearMap.range (peirceN data c) ⊔ LinearMap.ker (peirceN data c) := by
    rw [hN.sup_eq_top]
    exact Submodule.mem_top
  rcases Submodule.mem_sup.mp hxN with ⟨n, hn, k, hk, rfl⟩
  have hkT : k ∈ LinearMap.range (peirceT data c) ⊔ LinearMap.ker (peirceT data c) := by
    rw [hT.sup_eq_top]
    exact Submodule.mem_top
  rcases Submodule.mem_sup.mp hkT with ⟨t, ht, z, hz, rfl⟩
  have hz_kerN : z ∈ LinearMap.ker (peirceN data c) := by
    have hz_eq : z = (t + z) - t := by abel
    rw [hz_eq]
    exact Submodule.sub_mem _ hk (hV1_kerN ht)
  have hz0 : z ∈ peirceSubmodule data c .zero := ⟨hz_kerN, hz⟩
  have hn' : n ∈ peirceSubmodule data c .half := hn
  have ht' : t ∈ peirceSubmodule data c .one := ht
  exact Submodule.add_mem _ (Submodule.mem_iSup_of_mem .half hn')
    (Submodule.add_mem _ (Submodule.mem_iSup_of_mem .one ht')
      (Submodule.mem_iSup_of_mem .zero hz0))

/-- **Kamiya Peirce Direct-Sum Theorem**: Whenever `N_δ` and `T_δ` split `U` into range ⊕ kernel,
any `(-1, δ)`-FKTS with `δ^2 = 1` decomposes internally as `U = V_0 ⊕ V_{1/2} ⊕ V_1`. -/
theorem peirce_isInternal {c : U}
    (heps : data.epsilon = -1) (hdelta : data.delta ^ 2 = 1) (hc : IsTripotent data c)
    (hN : IsCompl (LinearMap.range (peirceN data c)) (LinearMap.ker (peirceN data c)))
    (hT : IsCompl (LinearMap.range (peirceT data c)) (LinearMap.ker (peirceT data c))) :
    DirectSum.IsInternal (peirceSubmodule data c) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  exact ⟨peirce_iSupIndep data (peirceN_mul_peirceT data hdelta hc)
    (peirceT_mul_peirceN data heps hdelta hc) hN hT,
    peirce_iSup_eq_top data (peirceN_mul_peirceT data hdelta hc) hN hT⟩

/-- Linear equivalence `(⨁ s : PeirceSector, V_s) ≃ₗ[R] U` from `DirectSum.IsInternal`. -/
noncomputable def peirceDirectSumEquiv {c : U}
    (hInt : DirectSum.IsInternal (peirceSubmodule data c)) :
    (⨁ s : PeirceSector, peirceSubmodule data c s) ≃ₗ[R] U :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap (peirceSubmodule data c)) hInt

/-- Canonical idempotent projector onto Peirce sector `s` (`0`, `1/2`, or `1`). -/
noncomputable def peirceProj {c : U}
    (hInt : DirectSum.IsInternal (peirceSubmodule data c)) (s : PeirceSector) :
    Module.End R U :=
  (peirceSubmodule data c s).subtype.comp
    ((DirectSum.component R PeirceSector (fun t => ↥(peirceSubmodule data c t)) s).comp
      (peirceDirectSumEquiv data hInt).symm.toLinearMap)

theorem peirceProj_apply_mem {c : U}
    (hInt : DirectSum.IsInternal (peirceSubmodule data c))
    (s t : PeirceSector) {x : U} (hx : x ∈ peirceSubmodule data c t) :
    peirceProj data hInt s x = if s = t then x else 0 := by
  have heq : (peirceDirectSumEquiv data hInt).symm x =
      DirectSum.of (fun r => ↥(peirceSubmodule data c r)) t ⟨x, hx⟩ := by
    apply (peirceDirectSumEquiv data hInt).injective
    rw [(peirceDirectSumEquiv data hInt).apply_symm_apply]
    change x = DirectSum.coeLinearMap (peirceSubmodule data c)
        (DirectSum.of (fun r => ↥(peirceSubmodule data c r)) t ⟨x, hx⟩)
    rw [DirectSum.coeLinearMap_of]
  dsimp [peirceProj]
  rw [heq]
  by_cases hst : s = t
  · subst hst
    simp only [↓reduceIte]
    change ((DirectSum.of (fun r => ↥(data.peirceSubmodule c r)) s ⟨x, hx⟩) s : U) = x
    rw [DirectSum.of_eq_same]
  · simp only [hst, ↓reduceIte]
    have hzero : (DirectSum.of (fun r => ↥(data.peirceSubmodule c r)) t ⟨x, hx⟩) s = 0 :=
      DirectSum.of_eq_of_ne _ _ _ hst
    exact congrArg (fun u : ↥(data.peirceSubmodule c s) => (u : U)) hzero

theorem peirceProj_mem {c : U}
    (hInt : DirectSum.IsInternal (peirceSubmodule data c))
    (s : PeirceSector) (x : U) :
    peirceProj data hInt s x ∈ peirceSubmodule data c s := by
  dsimp [peirceProj]
  exact (DirectSum.component R PeirceSector (fun t => ↥(peirceSubmodule data c t)) s
    ((peirceDirectSumEquiv data hInt).symm x)).2

theorem peirceProj_idem {c : U}
    (hInt : DirectSum.IsInternal (peirceSubmodule data c)) (s : PeirceSector) :
    peirceProj data hInt s * peirceProj data hInt s = peirceProj data hInt s := by
  apply LinearMap.ext
  intro x
  change peirceProj data hInt s (peirceProj data hInt s x) = peirceProj data hInt s x
  rw [peirceProj_apply_mem data hInt s s (peirceProj_mem data hInt s x)]
  simp

theorem peirceProj_orthogonal {c : U}
    (hInt : DirectSum.IsInternal (peirceSubmodule data c))
    {s t : PeirceSector} (hst : s ≠ t) :
    peirceProj data hInt s * peirceProj data hInt t = 0 := by
  apply LinearMap.ext
  intro x
  change peirceProj data hInt s (peirceProj data hInt t x) = 0
  rw [peirceProj_apply_mem data hInt s t (peirceProj_mem data hInt t x)]
  simp [hst]

theorem peirceProj_sum_eq_one {c : U}
    (hInt : DirectSum.IsInternal (peirceSubmodule data c)) :
    peirceProj data hInt .zero + peirceProj data hInt .half + peirceProj data hInt .one = 1 := by
  apply LinearMap.ext
  intro x
  have hdecomp : (peirceDirectSumEquiv data hInt)
      ((peirceDirectSumEquiv data hInt).symm x) = x :=
    (peirceDirectSumEquiv data hInt).apply_symm_apply x
  set d := (peirceDirectSumEquiv data hInt).symm x
  have hsum_d : d = DirectSum.of _ .zero (d .zero) +
      DirectSum.of _ .half (d .half) + DirectSum.of _ .one (d .one) := by
    ext s
    cases s <;> simp [DirectSum.of_eq_same, DirectSum.of_eq_of_ne]
  have hcoe : (peirceDirectSumEquiv data hInt) d =
      (d .zero : U) + (d .half : U) + (d .one : U) := by
    conv_lhs => rw [hsum_d]
    change DirectSum.coeLinearMap (peirceSubmodule data c) _ = _
    rw [map_add, map_add, DirectSum.coeLinearMap_of, DirectSum.coeLinearMap_of,
      DirectSum.coeLinearMap_of]
  change peirceProj data hInt .zero x + peirceProj data hInt .half x +
      peirceProj data hInt .one x = x
  have hcomp : ∀ s, peirceProj data hInt s x = (d s : U) := fun s => rfl
  rw [hcomp .zero, hcomp .half, hcomp .one, ← hcoe, hdecomp]

end PeirceDecomposition

section HermitianPeirce

theorem isCompl_range_ker_of_isSymmetric {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {A : Module.End ℝ V} (hA : A.IsSymmetric) :
    IsCompl (LinearMap.range A) (LinearMap.ker A) := by
  have hker : LinearMap.ker A = (LinearMap.range A)ᗮ := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_orthogonal]
    constructor
    · intro hx y hy
      rcases hy with ⟨z, rfl⟩
      rw [hA z x, hx, inner_zero_right]
    · intro h
      have hall : ∀ z : V, @inner ℝ V _ z (A x) = 0 := fun z => by
        rw [← hA z x]
        exact h (A z) ⟨z, rfl⟩
      exact inner_self_eq_zero.mp (hall (A x))
  rw [hker]
  exact (LinearMap.range A).isCompl_orthogonal

/-- **Hermitian `(-1, δ)`-FKTS Peirce Theorem**: Over a finite-dimensional real inner product
space, if `L(c, c)` and `R(c, c)` are symmetric at a tripotent `c`, then
`V = V_0 ⊕ V_{1/2} ⊕ V_1` holds unconditionally. -/
theorem peirce_isInternal_hermitian {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (data : FreudenthalKantorTripleSystem (R := ℝ) (U := V))
    {c : V} (heps : data.epsilon = -1) (hdelta : data.delta ^ 2 = 1) (hc : IsTripotent data c)
    (hL : (leftMulOp data c).IsSymmetric) (hR : (rightMulOp data c).IsSymmetric) :
    DirectSum.IsInternal (peirceSubmodule data c) := by
  have hN_sym : (peirceN data c).IsSymmetric := fun u v => by
    dsimp [peirceN]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      starRingEnd_apply, star_trivial]
    have hL' : @inner ℝ V _ (data.triple c c u) v = @inner ℝ V _ u (data.triple c c v) := hL u v
    have hR' : @inner ℝ V _ (data.triple u c c) v = @inner ℝ V _ u (data.triple v c c) := hR u v
    rw [hL', hR']
  have hT_sym : (peirceT data c).IsSymmetric := fun u v => by
    dsimp [peirceT]
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
    have hL' : @inner ℝ V _ (data.triple c c u) v = @inner ℝ V _ u (data.triple c c v) := hL u v
    have hR' : @inner ℝ V _ (data.triple u c c) v = @inner ℝ V _ u (data.triple v c c) := hR u v
    rw [hL', hR']
  exact peirce_isInternal data heps hdelta hc
    (isCompl_range_ker_of_isSymmetric hN_sym)
    (isCompl_range_ker_of_isSymmetric hT_sym)

end HermitianPeirce

section KamiyaLieTripleSystem

/-- A generalized `δ`-Lie triple system over `[CommRing R]`: a Lie triple system when `δ = 1`
and an anti-Lie triple system when `δ = -1`. -/
structure DeltaLieTripleSystem (R : Type*) [CommRing R] (δ : R)
    (V : Type*) [AddCommGroup V] [Module R V] where
  triple : V →ₗ[R] V →ₗ[R] V →ₗ[R] V
  skew_delta : ∀ x y z, triple x y z = -(δ • triple y x z)
  cyclic : ∀ x y z, triple x y z + triple y z x + triple z x y = 0
  deriv : ∀ x y z u v,
    triple x y (triple z u v) =
      triple (triple x y z) u v + triple z (triple x y u) v + triple z u (triple x y v)

instance (R : Type*) [CommRing R] (δ : R) (V : Type*) [AddCommGroup V] [Module R V] :
    Inhabited (DeltaLieTripleSystem R δ V) where
  default :=
    { triple := 0
      skew_delta := fun x y z =>
        (neg_eq_zero.mpr (smul_zero δ : δ • ((0 : V →ₗ[R] V →ₗ[R] V →ₗ[R] V) y x z) = 0)).symm
      cyclic := fun x y z =>
        (congrArg (fun t : V => t + ((0 : V →ₗ[R] V →ₗ[R] V →ₗ[R] V) z x y))
          (add_zero ((0 : V →ₗ[R] V →ₗ[R] V →ₗ[R] V) x y z))).trans (add_zero (0 : V))
      deriv := fun x y z u v =>
        ((congrArg (fun t : V => t + ((0 : V →ₗ[R] V →ₗ[R] V →ₗ[R] V) z u ((0 : V →ₗ[R] V →ₗ[R] V →ₗ[R] V) x y v)))
          (add_zero ((0 : V →ₗ[R] V →ₗ[R] V →ₗ[R] V) ((0 : V →ₗ[R] V →ₗ[R] V →ₗ[R] V) x y z) u v))).trans
          (add_zero (0 : V))).symm }

/-- Constructive inhabitant of `DeltaLieTripleSystem ℝ 1 ℝ` with concrete scalars/carrier. -/
def deltaLieTripleSystemRealWitness : DeltaLieTripleSystem ℝ 1 ℝ where
  triple := 0
  skew_delta x y z :=
    (neg_eq_zero.mpr (one_smul ℝ ((0 : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ) y x z))).symm
  cyclic x y z :=
    (congrArg (fun t : ℝ => t + ((0 : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ) z x y))
      (add_zero ((0 : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ) x y z))).trans (add_zero (0 : ℝ))
  deriv x y z u v :=
    ((congrArg (fun t : ℝ => t + ((0 : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ) z u ((0 : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ) x y v)))
      (add_zero ((0 : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ) ((0 : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ) x y z) u v))).trans
      (add_zero (0 : ℝ))).symm

/-- When `R = ℝ` and `δ = 1`, `DeltaLieTripleSystem` produces `InfoGeometry.Core.LieTripleSystem`. -/
def DeltaLieTripleSystem.toCoreLieTripleSystem {V : Type*} [AddCommGroup V] [Module ℝ V]
    (sys : DeltaLieTripleSystem ℝ 1 V) : InfoGeometry.Core.LieTripleSystem V where
  triple x y z := sys.triple x y z
  skew₁ x y z := by simpa using sys.skew_delta x y z
  jacobi_like := sys.deriv

/-- Skewness `K(y, x, z) = -δ • K(x, y, z)` when `δ^2 = 1`. -/
theorem K_skew (hdelta : data.delta ^ 2 = 1) (x y z : U) :
    data.K y x z = -(data.delta • data.K x y z) := by
  have hd2 : data.delta * data.delta = 1 := by simpa [sq] using hdelta
  simp only [K, fktsK, smul_sub, smul_smul, hd2, one_smul]
  abel

/-- Yamaguti–Ono / Kamiya identity (1.3):
`K(K(a, b, c), d, e) = ⟨d, c, K(a, b, e)⟩ - ε • K(a, b, ⟨c, d, e⟩)`. -/
theorem K_triple_left (hdelta : data.delta ^ 2 = 1) (a b c d e : U) :
    data.K (data.K a b c) d e =
      data.triple d c (data.K a b e) - data.epsilon • data.K a b (data.triple c d e) := by
  have hd2 : data.delta * data.delta = 1 := by simpa [sq] using hdelta
  have hk1 := data.k_identity a c b d e
  have hk2 := data.k_identity b c a d e
  have hk_comb :
      data.K (data.K a b c) d e - data.K a (data.triple d c b) e +
        data.delta • data.K b (data.triple d c a) e = 0 := by
    have hsum := congrArg₂ (· - data.delta • ·) hk1 hk2
    rw [smul_zero, sub_zero] at hsum
    dsimp [K, fktsK] at hsum ⊢
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply] at hsum ⊢
    rw [← hsum]
    simp only [smul_sub, smul_add, smul_smul, hd2, one_smul]
    module
  have hL1 := data.left_identity d c a e b
  have hL2 := data.left_identity d c b e a
  have hL_comb := congrArg₂ (· - data.delta • ·) hL1 hL2
  have hK_eq :
      data.K a (data.triple d c b) e - data.delta • data.K b (data.triple d c a) e =
        data.triple d c (data.K a b e) - data.epsilon • data.K a b (data.triple c d e) := by
    dsimp [K, fktsK] at hL_comb ⊢
    simp only [map_sub, map_smul]
    apply eq_of_sub_eq_zero
    have hL_zero :
        (data.triple d c (data.triple a e b) - data.triple a e (data.triple d c b) -
            data.delta • (data.triple d c (data.triple b e a) - data.triple b e (data.triple d c a))) -
          (data.triple (data.triple d c a) e b + data.epsilon • data.triple a (data.triple c d e) b -
            data.delta • (data.triple (data.triple d c b) e a +
              data.epsilon • data.triple b (data.triple c d e) a)) = 0 :=
      sub_eq_zero.mpr hL_comb
    rw [← neg_zero, ← hL_zero]
    simp only [smul_sub, smul_add, smul_smul, hd2, one_smul]
    module
  calc
    data.K (data.K a b c) d e
      = (data.K (data.K a b c) d e - data.K a (data.triple d c b) e +
          data.delta • data.K b (data.triple d c a) e) +
          (data.K a (data.triple d c b) e - data.delta • data.K b (data.triple d c a) e) := by abel
    _ = 0 + (data.triple d c (data.K a b e) - data.epsilon • data.K a b (data.triple c d e)) := by
          rw [hk_comb, hK_eq]
    _ = data.triple d c (data.K a b e) - data.epsilon • data.K a b (data.triple c d e) := by
          rw [zero_add]

/-- Yamaguti–Ono / Kamiya identity (1.4):
`K(a, b, K(c, d, e)) = εδ • ⟨K(a, b, d), c, e⟩ - ε • ⟨K(a, b, c), d, e⟩`. -/
theorem K_K_eq_left (heps : data.epsilon ^ 2 = 1) (hdelta : data.delta ^ 2 = 1)
    (a b c d e : U) :
    data.K a b (data.K c d e) =
      (data.epsilon * data.delta) • data.triple (data.K a b d) c e -
        data.epsilon • data.triple (data.K a b c) d e := by
  have he2 : data.epsilon * data.epsilon = 1 := by simpa [sq] using heps
  have hd2 : data.delta * data.delta = 1 := by simpa [sq] using hdelta
  have h1 := K_triple_left data hdelta a b c e d
  have h2 := K_triple_left data hdelta a b d e c
  have h1s : data.epsilon • data.K a b (data.triple c e d) =
      data.triple e c (data.K a b d) - data.K (data.K a b c) e d :=
    eq_sub_of_add_eq' (eq_add_of_sub_eq h1.symm).symm
  have h2s : data.epsilon • data.K a b (data.triple d e c) =
      data.triple e d (data.K a b c) - data.K (data.K a b d) e c :=
    eq_sub_of_add_eq' (eq_add_of_sub_eq h2.symm).symm
  have hcomb :
      data.epsilon • data.K a b (data.K c d e) =
        data.delta • data.triple (data.K a b d) c e - data.triple (data.K a b c) d e := by
    change data.epsilon • data.K a b (data.triple c e d - data.delta • data.triple d e c) = _
    rw [show data.K a b (data.triple c e d - data.delta • data.triple d e c) =
        data.K a b (data.triple c e d) - data.delta • data.K a b (data.triple d e c) by
      dsimp [K, fktsK]; simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply]
      module]
    rw [smul_sub, smul_comm data.epsilon data.delta, h1s, h2s]
    dsimp [K, fktsK]
    simp only [smul_sub, smul_smul, hd2, one_smul]
    module
  have he_mul := congrArg (fun u => data.epsilon • u) hcomb
  simp only [smul_smul, he2, one_smul, smul_sub] at he_mul
  exact he_mul

/-- Yamaguti–Ono / Kamiya identity (1.5):
`K(a, b, K(c, d, e)) = ⟨b, K(c, d, a), e⟩ - δ • ⟨a, K(c, d, b), e⟩`. -/
theorem K_K_eq_right (heps : data.epsilon ^ 2 = 1) (hdelta : data.delta ^ 2 = 1)
    (a b c d e : U) :
    data.K a b (data.K c d e) =
      data.triple b (data.K c d a) e - data.delta • data.triple a (data.K c d b) e := by
  have he2 : data.epsilon * data.epsilon = 1 := by simpa [sq] using heps
  have hd2 : data.delta * data.delta = 1 := by simpa [sq] using hdelta
  have hL1 := data.left_identity a c b d e
  have hL2 := data.left_identity a d b c e
  have hL3 := data.left_identity b c a d e
  have hL4 := data.left_identity b d a c e
  have h0 :
      (data.triple a c (data.triple b d e) - data.triple b d (data.triple a c e) -
        (data.triple (data.triple a c b) d e + data.epsilon • data.triple b (data.triple c a d) e)) -
      data.delta • (data.triple a d (data.triple b c e) - data.triple b c (data.triple a d e) -
        (data.triple (data.triple a d b) c e + data.epsilon • data.triple b (data.triple d a c) e)) -
      data.delta • (data.triple b c (data.triple a d e) - data.triple a d (data.triple b c e) -
        (data.triple (data.triple b c a) d e + data.epsilon • data.triple a (data.triple c b d) e)) +
      (data.delta * data.delta) • (data.triple b d (data.triple a c e) - data.triple a c (data.triple b d e) -
        (data.triple (data.triple b d a) c e + data.epsilon • data.triple a (data.triple d b c) e)) = 0 := by
    rw [sub_eq_zero.mpr hL1, sub_eq_zero.mpr hL2, sub_eq_zero.mpr hL3, sub_eq_zero.mpr hL4]
    simp
  have hsum :
      (data.triple (data.K a b c) d e - data.delta • data.triple (data.K a b d) c e) +
        data.epsilon • (data.triple b (data.K c d a) e - data.delta • data.triple a (data.K c d b) e) = 0 := by
    dsimp [K, fktsK]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply]
    apply eq_of_sub_eq_zero
    rw [sub_zero, ← neg_zero, ← h0]
    simp only [hd2, one_smul, smul_sub, smul_add, smul_smul]
    module
  have he_mul := congrArg (fun u => (-data.epsilon) • u) hsum
  rw [smul_zero, smul_add, smul_smul, neg_mul, he2, neg_one_smul, neg_smul,
    add_neg_eq_zero] at he_mul
  rw [K_K_eq_left data heps hdelta a b c d e, ← he_mul]
  module

/-- Kamiya Theorem 1 induced triple bracket `[x, y, z]_P = ⟨x, Py, z⟩ - δ⟨y, Px, z⟩ +
δ⟨x, Pz, y⟩ - ⟨y, Pz, x⟩`. -/
def inducedTripleBracket (P : Module.End R U) : U →ₗ[R] U →ₗ[R] U →ₗ[R] U where
  toFun x :=
    { toFun := fun y =>
        { toFun := fun z =>
            data.triple x (P y) z - data.delta • data.triple y (P x) z +
              data.delta • data.triple x (P z) y - data.triple y (P z) x
          map_add' := fun z₁ z₂ => by simp [map_add, smul_add]; abel
          map_smul' := fun r z => by
            simp only [map_smul, LinearMap.smul_apply, smul_sub, smul_add, RingHom.id_apply]
            module }
      map_add' := fun y₁ y₂ => by
        ext z
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add, smul_add]
        abel
      map_smul' := fun r y => by
        ext z
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, map_smul,
          smul_sub, smul_add, RingHom.id_apply]
        module }
  map_add' := fun x₁ x₂ => by
    ext y z
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add, smul_add]
    abel
  map_smul' := fun r x => by
    ext y z
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, map_smul,
      smul_sub, smul_add, RingHom.id_apply]
    module

private def kamiyaA (P : Module.End R U) (x y z : U) : U :=
  data.triple x (P y) z - data.delta • data.triple y (P x) z

private def kamiyaB (P : Module.End R U) (x y z : U) : U :=
  data.delta • data.K x y (P z)

private theorem inducedTripleBracket_eq_A_add_B (hdelta : data.delta ^ 2 = 1)
    (P : Module.End R U) (x y z : U) :
    inducedTripleBracket data P x y z = kamiyaA data P x y z + kamiyaB data P x y z := by
  have hd2 : data.delta * data.delta = 1 := by simpa [sq] using hdelta
  dsimp [inducedTripleBracket, kamiyaA, kamiyaB, K, fktsK]
  rw [smul_sub, smul_smul, hd2, one_smul]
  abel

theorem inducedTripleBracket_skew_delta (hdelta : data.delta ^ 2 = 1)
    (P : Module.End R U) (x y z : U) :
    inducedTripleBracket data P x y z = -(data.delta • inducedTripleBracket data P y x z) := by
  have hd2 : data.delta * data.delta = 1 := by simpa [sq] using hdelta
  dsimp [inducedTripleBracket]
  simp only [smul_sub, smul_add, smul_smul, hd2, one_smul]
  abel

theorem inducedTripleBracket_cyclic (P : Module.End R U) (x y z : U) :
    inducedTripleBracket data P x y z + inducedTripleBracket data P y z x +
      inducedTripleBracket data P z x y = 0 := by
  dsimp [inducedTripleBracket]
  abel

private theorem kamiya_P_K (P : Module.End R U)
    (hP_hom : ∀ a b c, P (data.triple a b c) = data.triple (P a) (P b) (P c))
    (a b c : U) :
    P (data.K a b c) = data.K (P a) (P b) (P c) := by
  dsimp [K, fktsK]
  rw [map_sub, map_smul, hP_hom, hP_hom]

private theorem kamiya_comm_AA (hdelta : data.delta ^ 2 = 1)
    (P : Module.End R U)
    (hP_sq : ∀ v, P (P v) = -(data.epsilon * data.delta) • v)
    (hP_hom : ∀ a b c, P (data.triple a b c) = data.triple (P a) (P b) (P c))
    (x y z w u : U) :
    kamiyaA data P x y (kamiyaA data P z w u) - kamiyaA data P z w (kamiyaA data P x y u) =
      kamiyaA data P (kamiyaA data P x y z) w u + kamiyaA data P z (kamiyaA data P x y w) u := by
  have hd2 : data.delta * data.delta = 1 := by simpa [sq] using hdelta
  have h1 := data.left_identity x (P y) z (P w) u
  have h2 := data.left_identity x (P y) w (P z) u
  have h3 := data.left_identity y (P x) z (P w) u
  have h4 := data.left_identity y (P x) w (P z) u
  have hP_A : ∀ a, P (kamiyaA data P x y a) =
      data.epsilon • (data.triple (P y) x (P a) - data.delta • data.triple (P x) y (P a)) := by
    intro a
    dsimp [kamiyaA]
    rw [map_sub, map_smul, hP_hom, hP_hom, hP_sq, hP_sq]
    simp only [LinearMap.map_smul₂, smul_sub, smul_smul]
    have h1' : data.delta * -(data.epsilon * data.delta) = -data.epsilon := by
      calc
        data.delta * -(data.epsilon * data.delta) = -(data.epsilon * (data.delta * data.delta)) := by
          rw [mul_neg, mul_comm data.delta (data.epsilon * data.delta), mul_assoc]
        _ = -data.epsilon := by rw [hd2, mul_one]
    rw [h1', neg_smul]
    module
  have hL :
      (data.triple x (P y) (data.triple z (P w) u) - data.triple z (P w) (data.triple x (P y) u)) -
      data.delta • (data.triple x (P y) (data.triple w (P z) u) - data.triple w (P z) (data.triple x (P y) u)) -
      data.delta • (data.triple y (P x) (data.triple z (P w) u) - data.triple z (P w) (data.triple y (P x) u)) +
      (data.delta * data.delta) •
        (data.triple y (P x) (data.triple w (P z) u) - data.triple w (P z) (data.triple y (P x) u)) =
      (data.triple (data.triple x (P y) z) (P w) u + data.epsilon • data.triple z (data.triple (P y) x (P w)) u) -
      data.delta • (data.triple (data.triple x (P y) w) (P z) u + data.epsilon • data.triple w (data.triple (P y) x (P z)) u) -
      data.delta • (data.triple (data.triple y (P x) z) (P w) u + data.epsilon • data.triple z (data.triple (P x) y (P w)) u) +
      (data.delta * data.delta) •
        (data.triple (data.triple y (P x) w) (P z) u + data.epsilon • data.triple w (data.triple (P x) y (P z)) u) := by
    rw [h1, h2, h3, h4]
  change (data.triple x (P y) (kamiyaA data P z w u) -
      data.delta • data.triple y (P x) (kamiyaA data P z w u)) -
      (data.triple z (P w) (kamiyaA data P x y u) -
        data.delta • data.triple w (P z) (kamiyaA data P x y u)) =
      (data.triple (kamiyaA data P x y z) (P w) u - data.delta • data.triple w (P (kamiyaA data P x y z)) u) +
      (data.triple z (P (kamiyaA data P x y w)) u - data.delta • data.triple (kamiyaA data P x y w) (P z) u)
  rw [hP_A z, hP_A w]
  dsimp [kamiyaA]
  apply eq_of_sub_eq_zero
  have hL0 := sub_eq_zero.mpr hL
  rw [← hL0]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_sub, smul_add, smul_smul, hd2, one_smul]
  have hded : data.delta * (data.epsilon * data.delta) = data.epsilon := by
    calc
      data.delta * (data.epsilon * data.delta) = data.epsilon * (data.delta * data.delta) := by
        rw [mul_comm data.delta, mul_assoc]
      _ = data.epsilon := by rw [hd2, mul_one]
  rw [hded]
  module

private theorem kamiya_comm_BA (hdelta : data.delta ^ 2 = 1)
    (P : Module.End R U)
    (hP_sq : ∀ v, P (P v) = -(data.epsilon * data.delta) • v)
    (hP_hom : ∀ a b c, P (data.triple a b c) = data.triple (P a) (P b) (P c))
    (x y z w u : U) :
    kamiyaB data P x y (kamiyaA data P z w u) - kamiyaA data P z w (kamiyaB data P x y u) =
      kamiyaB data P (kamiyaB data P x y z) w u + kamiyaB data P z (kamiyaB data P x y w) u := by
  have hd2 : data.delta * data.delta = 1 := by simpa [sq] using hdelta
  have hk1 := K_triple_left data hdelta x y (P z) w (P u)
  have hk2 := K_triple_left data hdelta x y (P w) z (P u)
  have hPA :
      P (kamiyaA data P z w u) =
        -(data.epsilon * data.delta) • (data.triple (P z) w (P u) - data.delta • data.triple (P w) z (P u)) := by
    dsimp [kamiyaA]
    rw [map_sub, map_smul, hP_hom, hP_hom, hP_sq, hP_sq]
    simp only [LinearMap.map_smul₂, smul_sub, smul_smul]
    congr 2
    exact mul_comm data.delta (-(data.epsilon * data.delta))
  have hK_smul1 : ∀ (r : R) a b c, data.K (r • a) b c = r • data.K a b c := fun r a b c => by
    dsimp [K, fktsK]
    simp only [map_smul, LinearMap.smul_apply, smul_sub]
    rw [smul_comm]
  have hrhs1 : kamiyaB data P (kamiyaB data P x y z) w u = data.K (data.K x y (P z)) w (P u) := by
    dsimp [kamiyaB]
    rw [hK_smul1, smul_smul, hd2, one_smul]
  have hrhs2 : kamiyaB data P z (kamiyaB data P x y w) u =
      -(data.delta • data.K (data.K x y (P w)) z (P u)) := by
    dsimp [kamiyaB]
    rw [K_skew data hdelta (data.delta • data.K x y (P w)) z (P u)]
    rw [hK_smul1, smul_neg, smul_smul, hd2, one_smul]
  have hK_lin : ∀ a b, data.K x y (a - b) = data.K x y a - data.K x y b := fun a b => by
    dsimp [K, fktsK]
    simp only [map_sub, LinearMap.sub_apply]
    module
  have hK_smul : ∀ (r : R) a, data.K x y (r • a) = r • data.K x y a := fun r a => by
    dsimp [K, fktsK]
    simp only [map_smul, LinearMap.smul_apply]
    module
  dsimp [kamiyaB] at hrhs1 hrhs2 ⊢
  rw [hrhs1, hrhs2, hk1, hk2]
  rw [show P (kamiyaA data P z w u) =
      -(data.epsilon * data.delta) • (data.triple (P z) w (P u) - data.delta • data.triple (P w) z (P u)) from hPA]
  rw [hK_smul, hK_lin, hK_smul]
  have hded : data.delta * (data.epsilon * data.delta) = data.epsilon := by
    calc
      data.delta * (data.epsilon * data.delta) = data.epsilon * (data.delta * data.delta) := by ring
      _ = data.epsilon := by rw [hd2, mul_one]
  have hde2 : data.delta * (-(data.epsilon * data.delta) * data.delta) = -(data.delta * data.epsilon) := by
    calc
      data.delta * (-(data.epsilon * data.delta) * data.delta) =
          -(data.delta * data.epsilon * (data.delta * data.delta)) := by ring
      _ = -(data.delta * data.epsilon) := by rw [hd2, mul_one]
  have hded_neg : data.delta * -(data.epsilon * data.delta) = -data.epsilon := by
    calc
      data.delta * -(data.epsilon * data.delta) = -(data.epsilon * (data.delta * data.delta)) := by ring
      _ = -data.epsilon := by rw [hd2, mul_one]
  dsimp [kamiyaA]
  simp only [map_smul, smul_sub, smul_smul, hd2, one_smul]
  rw [hded_neg, hde2]
  module

private theorem kamiya_comm_BB (heps : data.epsilon ^ 2 = 1) (hdelta : data.delta ^ 2 = 1)
    (P : Module.End R U)
    (hP_sq : ∀ v, P (P v) = -(data.epsilon * data.delta) • v)
    (hP_hom : ∀ a b c, P (data.triple a b c) = data.triple (P a) (P b) (P c))
    (x y z w u : U) :
    kamiyaB data P x y (kamiyaB data P z w u) - kamiyaB data P z w (kamiyaB data P x y u) =
      kamiyaA data P (kamiyaB data P x y z) w u + kamiyaA data P z (kamiyaB data P x y w) u := by
  have he2 : data.epsilon * data.epsilon = 1 := by simpa [sq] using heps
  have hd2 : data.delta * data.delta = 1 := by simpa [sq] using hdelta
  have hK_smul_trd : ∀ (r : R) a b c, data.K a b (r • c) = r • data.K a b c := by
    intro r a b c
    dsimp [K, fktsK]
    simp only [map_smul, LinearMap.smul_apply]
    module
  have hB_K : ∀ a b c d,
      kamiyaB data P a b (kamiyaB data P c d u) =
        -(data.epsilon * data.delta) • data.K a b (data.K (P c) (P d) u) := by
    intro a b c d
    dsimp [kamiyaB]
    rw [map_smul, kamiya_P_K data P hP_hom, hP_sq]
    simp only [hK_smul_trd, smul_smul]
    have hcoeff : data.delta * (data.delta * -(data.epsilon * data.delta)) = -(data.epsilon * data.delta) := by
      calc
        data.delta * (data.delta * -(data.epsilon * data.delta)) =
            (data.delta * data.delta) * -(data.epsilon * data.delta) := by ring
        _ = -(data.epsilon * data.delta) := by rw [hd2, one_mul]
    rw [hcoeff]
  have hP_B : ∀ a,
      P (kamiyaB data P x y a) = -data.epsilon • data.K (P x) (P y) a := by
    intro a
    dsimp [kamiyaB]
    rw [map_smul, kamiya_P_K data P hP_hom, hP_sq, hK_smul_trd, smul_smul]
    have hde : data.delta * -(data.epsilon * data.delta) = -data.epsilon := by
      calc
        data.delta * -(data.epsilon * data.delta) = -(data.epsilon * (data.delta * data.delta)) := by ring
        _ = -data.epsilon := by rw [hd2, mul_one]
    rw [hde]
  rw [hB_K x y z w, hB_K z w x y]
  rw [K_K_eq_left data heps hdelta x y (P z) (P w) u,
      K_K_eq_right data heps hdelta z w (P x) (P y) u]
  dsimp [kamiyaA]
  rw [hP_B z, hP_B w]
  dsimp [kamiyaB]
  simp only [map_smul, LinearMap.smul_apply, smul_sub, smul_smul]
  have h1 : -(data.epsilon * data.delta) * (data.epsilon * data.delta) = -1 := by
    calc
      -(data.epsilon * data.delta) * (data.epsilon * data.delta) =
          -((data.epsilon * data.epsilon) * (data.delta * data.delta)) := by ring
      _ = -1 := by rw [he2, hd2, mul_one]
  have h2 : -(data.epsilon * data.delta) * data.epsilon = -data.delta := by
    calc
      -(data.epsilon * data.delta) * data.epsilon = -((data.epsilon * data.epsilon) * data.delta) := by ring
      _ = -data.delta := by rw [he2, one_mul]
  have h3 : -(data.epsilon * data.delta) * data.delta = -data.epsilon := by
    calc
      -(data.epsilon * data.delta) * data.delta = -(data.epsilon * (data.delta * data.delta)) := by ring
      _ = -data.epsilon := by rw [hd2, mul_one]
  rw [h1, h2, h3, hd2, one_smul]
  module

private theorem kamiya_comm_AB (hdelta : data.delta ^ 2 = 1)
    (P : Module.End R U)
    (hP_sq : ∀ v, P (P v) = -(data.epsilon * data.delta) • v)
    (hP_hom : ∀ a b c, P (data.triple a b c) = data.triple (P a) (P b) (P c))
    (x y z w u : U) :
    kamiyaA data P x y (kamiyaB data P z w u) - kamiyaB data P z w (kamiyaA data P x y u) =
      kamiyaB data P (kamiyaA data P x y z) w u + kamiyaB data P z (kamiyaA data P x y w) u := by
  have hd2 : data.delta * data.delta = 1 := by simpa [sq] using hdelta
  have hkBA := kamiya_comm_BA data hdelta P hP_sq hP_hom z w x y u
  have hk1 := data.k_identity x (P y) z w (P u)
  have hk2 := data.k_identity y (P x) z w (P u)
  have hK_smul1 : ∀ (r : R) a b c, data.K (r • a) b c = r • data.K a b c := fun r a b c => by
    dsimp [K, fktsK]
    simp only [map_smul, LinearMap.smul_apply, smul_sub]
    rw [smul_comm]
  have hK_smul2 : ∀ (r : R) a b c, data.K a (r • b) c = r • data.K a b c := fun r a b c => by
    dsimp [K, fktsK]
    simp only [map_smul, LinearMap.smul_apply, smul_sub]
    rw [smul_comm]
  have hcomb :
      data.delta • (data.K (kamiyaA data P x y z) w (P u) + data.K z (kamiyaA data P x y w) (P u)) +
        (data.K x (data.K z w (P y)) (P u) - data.delta • data.K y (data.K z w (P x)) (P u)) = 0 := by
    have hsub := congrArg (data.delta • ·) (congrArg₂ (· - data.delta • ·) hk1 hk2)
    rw [smul_zero, sub_zero, smul_zero] at hsub
    dsimp [kamiyaA, K, fktsK] at hsub ⊢
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply] at hsub ⊢
    rw [← hsub]
    simp only [smul_sub, smul_add, smul_smul, hd2, one_smul]
    module
  have hskew :
      data.K x (data.K z w (P y)) (P u) - data.delta • data.K y (data.K z w (P x)) (P u) =
        kamiyaB data P (kamiyaB data P z w x) y u + kamiyaB data P x (kamiyaB data P z w y) u := by
    rw [K_skew data hdelta (data.K z w (P x)) y (P u)]
    dsimp [kamiyaB]
    rw [hK_smul1, hK_smul2]
    simp only [smul_neg, smul_smul, hd2, one_smul]
    module
  rw [hskew] at hcomb
  have hrhs_eq :
      kamiyaB data P (kamiyaA data P x y z) w u + kamiyaB data P z (kamiyaA data P x y w) u =
        data.delta • (data.K (kamiyaA data P x y z) w (P u) + data.K z (kamiyaA data P x y w) (P u)) := by
    dsimp [kamiyaB]
    rw [smul_add]
  rw [hrhs_eq]
  have hneg :
      data.delta • (data.K (kamiyaA data P x y z) w (P u) + data.K z (kamiyaA data P x y w) (P u)) =
        -(kamiyaB data P (kamiyaB data P z w x) y u + kamiyaB data P x (kamiyaB data P z w y) u) :=
    eq_neg_of_add_eq_zero_left hcomb
  rw [hneg, ← hkBA]
  abel

/-- **Kamiya Theorem 1**: For any `(ε, δ)`-FKTS with `ε^2 = 1`, `δ^2 = 1`, and any
triple-system automorphism `P : Module.End R U` satisfying `P^2 = -εδ • 1`,
`inducedTripleBracket data P` is a `δ`-Lie triple system (Lie triple system when `δ = 1`,
anti-Lie triple system when `δ = -1`). -/
theorem inducedTripleBracket_deriv (heps : data.epsilon ^ 2 = 1) (hdelta : data.delta ^ 2 = 1)
    (P : Module.End R U)
    (hP_sq : ∀ v, P (P v) = -(data.epsilon * data.delta) • v)
    (hP_hom : ∀ a b c, P (data.triple a b c) = data.triple (P a) (P b) (P c))
    (x y z w u : U) :
    inducedTripleBracket data P x y (inducedTripleBracket data P z w u) =
      inducedTripleBracket data P (inducedTripleBracket data P x y z) w u +
        inducedTripleBracket data P z (inducedTripleBracket data P x y w) u +
        inducedTripleBracket data P z w (inducedTripleBracket data P x y u) := by
  have hAA := kamiya_comm_AA data hdelta P hP_sq hP_hom x y z w u
  have hBA := kamiya_comm_BA data hdelta P hP_sq hP_hom x y z w u
  have hBB := kamiya_comm_BB data heps hdelta P hP_sq hP_hom x y z w u
  have hAB := kamiya_comm_AB data hdelta P hP_sq hP_hom x y z w u
  simp only [inducedTripleBracket_eq_A_add_B data hdelta]
  have hlin_D : ∀ a b c d,
      kamiyaA data P (a + b) c d + kamiyaB data P (a + b) c d =
        kamiyaA data P a c d + kamiyaA data P b c d +
          kamiyaB data P a c d + kamiyaB data P b c d := by
    intro a b c d
    dsimp [kamiyaA, kamiyaB, K, fktsK]
    simp only [map_add, LinearMap.add_apply, smul_add]
    module
  have hlin_D2 : ∀ a b c d,
      kamiyaA data P a (b + c) d + kamiyaB data P a (b + c) d =
        kamiyaA data P a b d + kamiyaA data P a c d +
          kamiyaB data P a b d + kamiyaB data P a c d := by
    intro a b c d
    dsimp [kamiyaA, kamiyaB, K, fktsK]
    simp only [map_add, LinearMap.add_apply, smul_add]
    module
  have hA_add : ∀ a b,
      kamiyaA data P x y (a + b) = kamiyaA data P x y a + kamiyaA data P x y b := by
    intro a b; dsimp [kamiyaA]; simp [map_add, smul_add]; abel
  have hB_add : ∀ a b,
      kamiyaB data P x y (a + b) = kamiyaB data P x y a + kamiyaB data P x y b := by
    intro a b; dsimp [kamiyaB, K, fktsK]; simp only [map_add, LinearMap.add_apply, smul_add]; module
  have hA_add_zw : ∀ a b,
      kamiyaA data P z w (a + b) = kamiyaA data P z w a + kamiyaA data P z w b := by
    intro a b; dsimp [kamiyaA]; simp [map_add, smul_add]; abel
  have hB_add_zw : ∀ a b,
      kamiyaB data P z w (a + b) = kamiyaB data P z w a + kamiyaB data P z w b := by
    intro a b; dsimp [kamiyaB, K, fktsK]; simp only [map_add, LinearMap.add_apply, smul_add]; module
  rw [hA_add, hB_add, hlin_D, hlin_D2, hA_add_zw, hB_add_zw]
  have hsum :
      (kamiyaA data P x y (kamiyaA data P z w u) - kamiyaA data P z w (kamiyaA data P x y u)) +
      (kamiyaA data P x y (kamiyaB data P z w u) - kamiyaB data P z w (kamiyaA data P x y u)) +
      (kamiyaB data P x y (kamiyaA data P z w u) - kamiyaA data P z w (kamiyaB data P x y u)) +
      (kamiyaB data P x y (kamiyaB data P z w u) - kamiyaB data P z w (kamiyaB data P x y u)) =
        (kamiyaA data P (kamiyaA data P x y z) w u + kamiyaA data P z (kamiyaA data P x y w) u) +
        (kamiyaB data P (kamiyaA data P x y z) w u + kamiyaB data P z (kamiyaA data P x y w) u) +
        (kamiyaB data P (kamiyaB data P x y z) w u + kamiyaB data P z (kamiyaB data P x y w) u) +
        (kamiyaA data P (kamiyaB data P x y z) w u + kamiyaA data P z (kamiyaB data P x y w) u) := by
    rw [hAA, hAB, hBA, hBB]
  exact eq_add_of_sub_eq (by
    calc
      (kamiyaA data P x y (kamiyaA data P z w u) + kamiyaA data P x y (kamiyaB data P z w u) +
        (kamiyaB data P x y (kamiyaA data P z w u) + kamiyaB data P x y (kamiyaB data P z w u))) -
        (kamiyaA data P z w (kamiyaA data P x y u) + kamiyaA data P z w (kamiyaB data P x y u) +
          (kamiyaB data P z w (kamiyaA data P x y u) + kamiyaB data P z w (kamiyaB data P x y u)))
        = (kamiyaA data P x y (kamiyaA data P z w u) - kamiyaA data P z w (kamiyaA data P x y u)) +
          (kamiyaA data P x y (kamiyaB data P z w u) - kamiyaB data P z w (kamiyaA data P x y u)) +
          (kamiyaB data P x y (kamiyaA data P z w u) - kamiyaA data P z w (kamiyaB data P x y u)) +
          (kamiyaB data P x y (kamiyaB data P z w u) - kamiyaB data P z w (kamiyaB data P x y u)) := by abel
      _ = _ := hsum
      _ = _ := by abel)

/-- Package `inducedTripleBracket` as a `DeltaLieTripleSystem` whenever `ε^2 = 1`, `δ^2 = 1`,
and `P` is a triple automorphism with `P^2 = -εδ • 1`. -/
def toDeltaLieTripleSystem (heps : data.epsilon ^ 2 = 1) (hdelta : data.delta ^ 2 = 1)
    (P : Module.End R U)
    (hP_sq : ∀ v, P (P v) = -(data.epsilon * data.delta) • v)
    (hP_hom : ∀ a b c, P (data.triple a b c) = data.triple (P a) (P b) (P c)) :
    DeltaLieTripleSystem R data.delta U where
  triple := inducedTripleBracket data P
  skew_delta := inducedTripleBracket_skew_delta data hdelta P
  cyclic := inducedTripleBracket_cyclic data P
  deriv := inducedTripleBracket_deriv data heps hdelta P hP_sq hP_hom

end KamiyaLieTripleSystem

section BilinearRankOneFKTS

/-- Generalized non-Jordan `(-1, δ)`-FKTS on any module `[Module R U]` equipped with a
symmetric bilinear form `β : U →ₗ[R] U →ₗ[R] R` and any `δ : R` with `δ^2 = 1`, via
`⟨x, y, z⟩ = β(y, z) • x`. Its Kantor operator is `K(x, y, z) = β(z, y) • x - δ β(z, x) • y`,
which is non-Jordan whenever `dim U ≥ 2` and creates a nontrivial `V_{1/2}` Peirce sector. -/
def bilinearRankOneTriple {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]
    (β : U →ₗ[R] U →ₗ[R] R) : U →ₗ[R] U →ₗ[R] U →ₗ[R] U where
  toFun x :=
    { toFun := fun y =>
        { toFun := fun z => β y z • x
          map_add' := fun z₁ z₂ => by simp [map_add, add_smul]
          map_smul' := fun r z => by simp [map_smul, smul_smul] }
      map_add' := fun y₁ y₂ => by
        ext z; simp [add_smul]
      map_smul' := fun r y => by
        ext z; simp [smul_smul] }
  map_add' := fun x₁ x₂ => by
    ext y z; simp [smul_add]
  map_smul' := fun r x => by
    ext y z
    exact smul_comm ((β y) z) r x

def bilinearRankOneFKTS {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]
    (β : U →ₗ[R] U →ₗ[R] R) (hβ : ∀ x y, β x y = β y x)
    (δ : R) (hδ : δ ^ 2 = 1) :
    FreudenthalKantorTripleSystem (R := R) (U := U) where
  epsilon := -1
  delta := δ
  triple := bilinearRankOneTriple β
  left_identity x y z w u := by
    dsimp [bilinearRankOneTriple]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, smul_smul]
    rw [hβ x w]
    module
  k_identity x y z w u := by
    have hd2 : δ * δ = 1 := by simpa [sq] using hδ
    dsimp [fktsK, bilinearRankOneTriple]
    simp only [map_sub, map_smul, smul_eq_mul, smul_sub, smul_smul]
    have h1 : δ * ((β y w * β u z - δ * β y z * β u w) * 1) =
        (δ * (β y w * β u z) - (δ * δ) * (β y z * β u w)) := by ring
    have h2 : δ * (δ * (β u x * β y w)) = (δ * δ) * (β u x * β y w) := by ring
    have h3 : δ * (δ * (β u x * (δ * β y z))) = (δ * δ) * (δ * (β u x * β y z)) := by ring
    have hc : ((β u w * β y z) • x - (δ * (β y z * β u x)) • w +
          ((β y w * β u x) • z - (δ * (β u z * β y w)) • x)) +
        ((δ * (β y w * β u z - δ * β y z * β u w)) • x -
          ((δ * (δ * (β u x * β y w))) • z - (δ * (δ * (β u x * (δ * β y z)))) • w)) = 0 := by
      rw [h2, h3, hd2, one_mul, one_mul]
      have hd_expand : δ * (β y w * β u z - δ * β y z * β u w) =
          δ * (β y w * β u z) - (δ * δ) * (β y z * β u w) := by ring
      rw [hd_expand, hd2, one_mul]
      have hsym1 : β u w * β y z = β y z * β u w := mul_comm _ _
      have hsym2 : β y z * β u x = β u x * β y z := mul_comm _ _
      have hsym3 : β y w * β u x = β u x * β y w := mul_comm _ _
      have hsym4 : β u z * β y w = β y w * β u z := mul_comm _ _
      rw [hsym1, hsym2, hsym3, hsym4]
      module
    exact hc

theorem bilinearRankOneFKTS_tripotent {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]
    (β : U →ₗ[R] U →ₗ[R] R) (hβ : ∀ x y, β x y = β y x)
    (δ : R) (hδ : δ ^ 2 = 1) {c : U} (hc : β c c = 1) :
    FreudenthalKantorTripleSystem.IsTripotent (bilinearRankOneFKTS β hβ δ hδ) c := by
  change β c c • c = c
  rw [hc, one_smul]

theorem bilinearRankOneFKTS_nonJordan {R U : Type*} [CommRing R] [AddCommGroup U] [Module R U]
    (β : U →ₗ[R] U →ₗ[R] R) (hβ : ∀ x y, β x y = β y x)
    (δ : R) (hδ : δ ^ 2 = 1) {x y z : U}
    (hne : β z y • x - δ • (β z x • y) ≠ 0) :
    (bilinearRankOneFKTS β hβ δ hδ).K x y z ≠ 0 := by
  simpa [FreudenthalKantorTripleSystem.K, fktsK, bilinearRankOneFKTS, bilinearRankOneTriple] using hne

end BilinearRankOneFKTS

end FreudenthalKantorTripleSystem

/-- Concrete ground inhabitant of `FreudenthalKantorTripleSystem` over `ℤ`. -/
def intZeroFKTS : FreudenthalKantorTripleSystem (R := ℤ) (U := ℤ) where
  epsilon := 0
  delta := 0
  triple := 0
  left_identity _ _ _ _ _ := by simp
  k_identity _ _ _ _ _ := by simp [fktsK]

section ConcreteMatrixFKTS

/-- The associative Jordan triple, curried as an actual complex-linear map on
the finite noncommutative spin matrix algebra. -/
def matrixJordanTriple : Mat2C →ₗ[ℂ] Mat2C →ₗ[ℂ] Mat2C →ₗ[ℂ] Mat2C where
  toFun x :=
    { toFun := fun y =>
        { toFun := fun z => jordanTriple x y z
          map_add' := by
            intro z₁ z₂
            simp only [jordanTriple, mul_add, add_mul]
            abel_nf
          map_smul' := by
            intro c z
            simp [jordanTriple, mul_assoc] }
      map_add' := by
        intro y₁ y₂
        apply LinearMap.ext
        intro z
        change jordanTriple x (y₁ + y₂) z = jordanTriple x y₁ z + jordanTriple x y₂ z
        simp only [jordanTriple, add_mul, mul_add]
        abel
      map_smul' := by
        intro c y
        apply LinearMap.ext
        intro z
        simp [jordanTriple, mul_assoc] }
  map_add' := by
    intro x₁ x₂
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro z
    change jordanTriple (x₁ + x₂) y z = jordanTriple x₁ y z + jordanTriple x₂ y z
    simp only [jordanTriple, add_mul, mul_add]
    abel
  map_smul' := by
    intro c x
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro z
    simp [jordanTriple, mul_assoc]

@[simp] theorem matrixJordanTriple_apply (x y z : Mat2C) :
    matrixJordanTriple x y z = jordanTriple x y z := rfl

/-- Concrete noncommutative FKTS on `Mat₂(ℂ)`, with the associative Jordan
triple `xyz + zyx`, `ε = -1`, and `δ = 1`. -/
def matrixJordanFKTS : FreudenthalKantorTripleSystem (R := ℂ) (U := Mat2C) where
  epsilon := -1
  delta := 1
  triple := matrixJordanTriple
  left_identity x y z w u := by
    simpa [sub_eq_add_neg] using
      jordanTriple_left_identity x y z w u
  k_identity x y z w u := by
    simpa only [fktsK, jordanTripleK, matrixJordanTriple_apply, one_smul] using
      jordanTriple_K_identity x y z w u

/-- This concrete matrix triple is nonzero, witnessed by the repository's
raising and lowering matrices; hence the bundled example is not the zero
triple-system inhabitant. -/
theorem matrixJordanFKTS_nonzero :
    matrixJordanFKTS.triple J_plus J_minus J_plus ≠ 0 := by
  change jordanTriple J_plus J_minus J_plus ≠ 0
  dsimp [jordanTriple]
  intro h
  have hmul : J_plus * J_minus * J_plus + J_plus * J_minus * J_plus = 0 := h
  have hentry := congr_fun (congr_fun hmul 0) 1
  norm_num [J_plus, J_minus, Matrix.mul_apply, Fin.sum_univ_two] at hentry

/-- Concrete Jordan tripotent `c_jordan` in `Mat₂(ℂ)` satisfying `c_jordan^3 = (1/2) c_jordan`. -/
noncomputable def c_jordan : Mat2C := !![0, 1; (1 / 2 : ℂ), 0]

theorem matrixJordanFKTS_tripotent_c_jordan :
    matrixJordanFKTS.IsTripotent c_jordan := by
  change jordanTriple c_jordan c_jordan c_jordan = c_jordan
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jordanTriple, c_jordan] <;> norm_num

/-- For `matrixJordanFKTS` at `c_jordan`, `N_1 = 0` (`V_{1/2} = ⊥`) and `T_1 = 2 • 1`
(`V_0 = ⊥`, `V_1 = ⊤`), giving the pure-Jordan Peirce decomposition. -/
theorem matrixJordanFKTS_peirce_c_jordan :
    matrixJordanFKTS.peirceN c_jordan = 0 ∧
    matrixJordanFKTS.peirceT c_jordan = (2 : ℂ) • 1 ∧
    DirectSum.IsInternal (matrixJordanFKTS.peirceSubmodule c_jordan) := by
  have hN : matrixJordanFKTS.peirceN c_jordan = 0 := by
    ext x i j
    fin_cases i <;> fin_cases j <;>
      simp [FreudenthalKantorTripleSystem.peirceN, FreudenthalKantorTripleSystem.leftMulOp,
        FreudenthalKantorTripleSystem.rightMulOp, matrixJordanFKTS, jordanTriple, c_jordan,
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring
  have hT : matrixJordanFKTS.peirceT c_jordan = (2 : ℂ) • 1 := by
    ext x i j
    fin_cases i <;> fin_cases j <;>
      simp [FreudenthalKantorTripleSystem.peirceT, FreudenthalKantorTripleSystem.leftMulOp,
        FreudenthalKantorTripleSystem.rightMulOp, matrixJordanFKTS, jordanTriple, c_jordan,
        Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring
  have hN_comp : IsCompl (LinearMap.range (matrixJordanFKTS.peirceN c_jordan))
      (LinearMap.ker (matrixJordanFKTS.peirceN c_jordan)) := by
    rw [hN, LinearMap.range_zero, LinearMap.ker_zero]
    exact isCompl_bot_top
  have hT_comp : IsCompl (LinearMap.range (matrixJordanFKTS.peirceT c_jordan))
      (LinearMap.ker (matrixJordanFKTS.peirceT c_jordan)) := by
    have hrange : LinearMap.range (matrixJordanFKTS.peirceT c_jordan) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      refine ⟨(1 / 2 : ℂ) • x, ?_⟩
      rw [hT]
      simp [smul_smul]
    have hker : LinearMap.ker (matrixJordanFKTS.peirceT c_jordan) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [LinearMap.mem_ker, hT, LinearMap.smul_apply, Module.End.one_apply] at hx
      have h2 : ((2 : ℂ) : ℂ) ≠ 0 := by norm_num
      exact (Submodule.mem_bot ℂ).mpr ((smul_eq_zero.mp hx).resolve_left h2)
    rw [hrange, hker]
    exact isCompl_top_bot
  refine ⟨hN, hT, FreudenthalKantorTripleSystem.peirce_isInternal matrixJordanFKTS
    rfl (by norm_num [matrixJordanFKTS]) matrixJordanFKTS_tripotent_c_jordan hN_comp hT_comp⟩

/-- Pauli-Z conjugation automorphism on `Mat₂(ℂ)`. -/
def mat2ConjZ : Module.End ℂ Mat2C where
  toFun x := !![1, 0; 0, -1] * x * !![1, 0; 0, -1]
  map_add' x y := by rw [mul_add, add_mul]
  map_smul' r x := by rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc]; rfl

theorem mat2ConjZ_sq (x : Mat2C) : mat2ConjZ (mat2ConjZ x) = x := by
  ext i j
  dsimp [mat2ConjZ]
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp

theorem mat2ConjZ_triple_hom (a b c : Mat2C) :
    mat2ConjZ (matrixJordanFKTS.triple a b c) =
      matrixJordanFKTS.triple (mat2ConjZ a) (mat2ConjZ b) (mat2ConjZ c) := by
  ext i j
  dsimp [mat2ConjZ, matrixJordanFKTS, jordanTriple]
  simp only [Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- Lie triple system on `Mat₂(ℂ)` induced from `matrixJordanFKTS` and `P = 1`
(recovering `[x, y, z] = 2 • [[x, y], z]`). -/
def matrixJordanDeltaLTS : FreudenthalKantorTripleSystem.DeltaLieTripleSystem ℂ 1 Mat2C :=
  FreudenthalKantorTripleSystem.toDeltaLieTripleSystem matrixJordanFKTS
    (by norm_num [matrixJordanFKTS]) (by norm_num [matrixJordanFKTS]) 1
    (fun v => by simp [matrixJordanFKTS]) (fun a b c => rfl)

/-- Twisted Lie triple system on `Mat₂(ℂ)` induced by `P = mat2ConjZ` (`P^2 = 1`). -/
def matrixJordanConjZDeltaLTS : FreudenthalKantorTripleSystem.DeltaLieTripleSystem ℂ 1 Mat2C :=
  FreudenthalKantorTripleSystem.toDeltaLieTripleSystem matrixJordanFKTS
    (by norm_num [matrixJordanFKTS]) (by norm_num [matrixJordanFKTS]) mat2ConjZ
    (fun v => by simpa [matrixJordanFKTS] using mat2ConjZ_sq v)
    mat2ConjZ_triple_hom

/-- Standard dot product bilinear form on `ℝ^2` (`Fin 2 → ℝ`). -/
def vec2Dot : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y => x 0 * y 0 + x 1 * y 1
      map_add' := fun y₁ y₂ => by simp [mul_add]; ring
      map_smul' := fun r y => by simp; ring }
  map_add' x₁ x₂ := by ext y; simp [add_mul]; ring
  map_smul' r x := by ext y; simp; ring

theorem vec2Dot_symm (x y : Fin 2 → ℝ) : vec2Dot x y = vec2Dot y x := by
  dsimp [vec2Dot]
  ring

/-- Concrete non-Jordan `(-1, 1)`-FKTS on `ℝ^2`: `K ≠ 0` and `V_{1/2} ≠ ⊥`. -/
def vec2OrthFKTS : FreudenthalKantorTripleSystem (R := ℝ) (U := Fin 2 → ℝ) :=
  FreudenthalKantorTripleSystem.bilinearRankOneFKTS vec2Dot vec2Dot_symm 1 (by norm_num)

/-- Concrete non-Jordan `(-1, -1)`-FKTS on `ℝ^2`: `K ≠ 0` and `P = rot90` (`P^2 = -1`)
produces a genuine anti-Lie triple system (`δ = -1`). -/
def vec2SkewOrthFKTS : FreudenthalKantorTripleSystem (R := ℝ) (U := Fin 2 → ℝ) :=
  FreudenthalKantorTripleSystem.bilinearRankOneFKTS vec2Dot vec2Dot_symm (-1) (by norm_num)

theorem vec2OrthFKTS_nonJordan_and_peirce :
    vec2OrthFKTS.K ![1, 0] ![0, 1] ![0, 1] ≠ 0 ∧
    vec2OrthFKTS.peirceVHalf ![1, 0] ≠ ⊥ ∧
    vec2OrthFKTS.peirceV1 ![1, 0] ≠ ⊥ ∧
    DirectSum.IsInternal (vec2OrthFKTS.peirceSubmodule ![1, 0]) := by
  let c : Fin 2 → ℝ := ![1, 0]
  have hc : vec2OrthFKTS.IsTripotent c :=
    FreudenthalKantorTripleSystem.bilinearRankOneFKTS_tripotent vec2Dot vec2Dot_symm 1
      (by norm_num) (by simp [c, vec2Dot])
  have hK : vec2OrthFKTS.K ![1, 0] ![0, 1] ![0, 1] ≠ 0 := by
    intro h
    have h0 := congr_fun h 0
    norm_num [vec2OrthFKTS, FreudenthalKantorTripleSystem.bilinearRankOneFKTS,
      FreudenthalKantorTripleSystem.K, fktsK,
      FreudenthalKantorTripleSystem.bilinearRankOneTriple, vec2Dot] at h0
  have hN_ne : vec2OrthFKTS.peirceVHalf c ≠ ⊥ := by
    intro hbot
    have hmem : vec2OrthFKTS.peirceN c ![0, 1] ∈ vec2OrthFKTS.peirceVHalf c := ⟨![0, 1], rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    have h1 := congr_fun hmem 1
    norm_num [c, vec2OrthFKTS, FreudenthalKantorTripleSystem.peirceN,
      FreudenthalKantorTripleSystem.leftMulOp, FreudenthalKantorTripleSystem.rightMulOp,
      FreudenthalKantorTripleSystem.bilinearRankOneFKTS,
      FreudenthalKantorTripleSystem.bilinearRankOneTriple, vec2Dot] at h1
  have hT_ne : vec2OrthFKTS.peirceV1 c ≠ ⊥ := by
    intro hbot
    have hmem : vec2OrthFKTS.peirceT c c ∈ vec2OrthFKTS.peirceV1 c := ⟨c, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    have h0 := congr_fun hmem 0
    norm_num [c, vec2OrthFKTS, FreudenthalKantorTripleSystem.peirceT,
      FreudenthalKantorTripleSystem.leftMulOp, FreudenthalKantorTripleSystem.rightMulOp,
      FreudenthalKantorTripleSystem.bilinearRankOneFKTS,
      FreudenthalKantorTripleSystem.bilinearRankOneTriple, vec2Dot] at h0
  have hN_comp : IsCompl (LinearMap.range (vec2OrthFKTS.peirceN c))
      (LinearMap.ker (vec2OrthFKTS.peirceN c)) := by
    have hrange : LinearMap.range (vec2OrthFKTS.peirceN c) = Submodule.span ℝ {![0, 1]} := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        rw [Submodule.mem_span_singleton]
        refine ⟨-x 1, ?_⟩
        ext i; fin_cases i <;>
          simp [c, vec2OrthFKTS, FreudenthalKantorTripleSystem.peirceN,
            FreudenthalKantorTripleSystem.leftMulOp, FreudenthalKantorTripleSystem.rightMulOp,
            FreudenthalKantorTripleSystem.bilinearRankOneFKTS,
            FreudenthalKantorTripleSystem.bilinearRankOneTriple, vec2Dot]
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        refine ⟨![0, -1], ?_⟩
        ext i; fin_cases i <;>
          simp [c, vec2OrthFKTS, FreudenthalKantorTripleSystem.peirceN,
            FreudenthalKantorTripleSystem.leftMulOp, FreudenthalKantorTripleSystem.rightMulOp,
            FreudenthalKantorTripleSystem.bilinearRankOneFKTS,
            FreudenthalKantorTripleSystem.bilinearRankOneTriple, vec2Dot]
    have hker : LinearMap.ker (vec2OrthFKTS.peirceN c) = Submodule.span ℝ {c} := by
      apply le_antisymm
      · intro x hx
        rw [LinearMap.mem_ker] at hx
        have hx1 := congr_fun hx 1
        simp [c, vec2OrthFKTS, FreudenthalKantorTripleSystem.peirceN,
          FreudenthalKantorTripleSystem.leftMulOp, FreudenthalKantorTripleSystem.rightMulOp,
          FreudenthalKantorTripleSystem.bilinearRankOneFKTS,
          FreudenthalKantorTripleSystem.bilinearRankOneTriple, vec2Dot] at hx1
        rw [Submodule.mem_span_singleton]
        refine ⟨x 0, ?_⟩
        ext i; fin_cases i <;> simp [c, hx1]
      · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
        ext i; fin_cases i <;>
          simp [c, vec2OrthFKTS, FreudenthalKantorTripleSystem.peirceN,
            FreudenthalKantorTripleSystem.leftMulOp, FreudenthalKantorTripleSystem.rightMulOp,
            FreudenthalKantorTripleSystem.bilinearRankOneFKTS,
            FreudenthalKantorTripleSystem.bilinearRankOneTriple, vec2Dot]
    rw [hrange, hker, isCompl_iff]
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      intro x hx
      rcases Submodule.mem_span_singleton.mp hx.1 with ⟨a, ha⟩
      rcases Submodule.mem_span_singleton.mp hx.2 with ⟨b, hb⟩
      have hb1 := congr_fun (ha.trans hb.symm) 1
      have ha0 : a = 0 := by simpa [c] using hb1
      rw [← ha, ha0, zero_smul]
      exact Submodule.zero_mem _
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      rw [Submodule.mem_sup]
      refine ⟨x 1 • ![0, 1], Submodule.mem_span_singleton.mpr ⟨x 1, rfl⟩,
        x 0 • c, Submodule.mem_span_singleton.mpr ⟨x 0, rfl⟩, ?_⟩
      ext i; fin_cases i <;> simp [c]
  have hT_comp : IsCompl (LinearMap.range (vec2OrthFKTS.peirceT c))
      (LinearMap.ker (vec2OrthFKTS.peirceT c)) := by
    have hrange : LinearMap.range (vec2OrthFKTS.peirceT c) = Submodule.span ℝ {c} := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        rw [Submodule.mem_span_singleton]
        refine ⟨2 * x 0, ?_⟩
        ext i; fin_cases i <;>
          simp only [c, vec2OrthFKTS, FreudenthalKantorTripleSystem.peirceT,
            FreudenthalKantorTripleSystem.leftMulOp, FreudenthalKantorTripleSystem.rightMulOp,
            FreudenthalKantorTripleSystem.bilinearRankOneFKTS,
            FreudenthalKantorTripleSystem.bilinearRankOneTriple, vec2Dot,
            LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
            Module.End.one_apply, LinearMap.coe_mk, AddHom.coe_mk,
            Matrix.cons_val_zero, Matrix.cons_val_one,
            Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;> ring
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        refine ⟨(1 / 2 : ℝ) • c, ?_⟩
        ext i; fin_cases i <;>
          simp only [c, vec2OrthFKTS, FreudenthalKantorTripleSystem.peirceT,
            FreudenthalKantorTripleSystem.leftMulOp, FreudenthalKantorTripleSystem.rightMulOp,
            FreudenthalKantorTripleSystem.bilinearRankOneFKTS,
            FreudenthalKantorTripleSystem.bilinearRankOneTriple, vec2Dot,
            LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
            Module.End.one_apply, LinearMap.coe_mk, AddHom.coe_mk,
            Matrix.cons_val_zero, Matrix.cons_val_one,
            Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] <;> norm_num
    have hker : LinearMap.ker (vec2OrthFKTS.peirceT c) = Submodule.span ℝ {![0, 1]} := by
      apply le_antisymm
      · intro x hx
        rw [LinearMap.mem_ker] at hx
        have hx0 := congr_fun hx 0
        simp only [c, vec2OrthFKTS, FreudenthalKantorTripleSystem.peirceT,
          FreudenthalKantorTripleSystem.leftMulOp, FreudenthalKantorTripleSystem.rightMulOp,
          FreudenthalKantorTripleSystem.bilinearRankOneFKTS,
          FreudenthalKantorTripleSystem.bilinearRankOneTriple, vec2Dot,
          LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
          Module.End.one_apply, LinearMap.coe_mk, AddHom.coe_mk,
          Matrix.cons_val_zero, Matrix.cons_val_one,
          Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hx0
        have hx0' : x 0 = 0 := by linarith
        rw [Submodule.mem_span_singleton]
        refine ⟨x 1, ?_⟩
        ext i; fin_cases i <;> simp [hx0']
      · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
        ext i; fin_cases i <;>
          simp only [c, vec2OrthFKTS, FreudenthalKantorTripleSystem.peirceT,
            FreudenthalKantorTripleSystem.leftMulOp, FreudenthalKantorTripleSystem.rightMulOp,
            FreudenthalKantorTripleSystem.bilinearRankOneFKTS,
            FreudenthalKantorTripleSystem.bilinearRankOneTriple, vec2Dot,
            LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
            Module.End.one_apply, LinearMap.coe_mk, AddHom.coe_mk,
            Matrix.cons_val_zero, Matrix.cons_val_one,
            Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] <;> norm_num
    rw [hrange, hker, isCompl_iff]
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      intro x hx
      rcases Submodule.mem_span_singleton.mp hx.1 with ⟨a, ha⟩
      rcases Submodule.mem_span_singleton.mp hx.2 with ⟨b, hb⟩
      have hb0 := congr_fun (ha.trans hb.symm) 0
      have ha0 : a = 0 := by simpa [c] using hb0
      rw [← ha, ha0, zero_smul]
      exact Submodule.zero_mem _
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      rw [Submodule.mem_sup]
      refine ⟨x 0 • c, Submodule.mem_span_singleton.mpr ⟨x 0, rfl⟩,
        x 1 • ![0, 1], Submodule.mem_span_singleton.mpr ⟨x 1, rfl⟩, ?_⟩
      ext i; fin_cases i <;> simp [c]
  exact ⟨hK, hN_ne, hT_ne, FreudenthalKantorTripleSystem.peirce_isInternal vec2OrthFKTS
    rfl (by norm_num [vec2OrthFKTS, FreudenthalKantorTripleSystem.bilinearRankOneFKTS])
    hc hN_comp hT_comp⟩

/-- 90-degree rotation on `ℝ^2` (`P^2 = -1`), generating a genuine anti-Lie triple system
(`δ = -1`) from `vec2SkewOrthFKTS`. -/
def vec2Rot90 : Module.End ℝ (Fin 2 → ℝ) where
  toFun x := ![-x 1, x 0]
  map_add' x y := by ext i; fin_cases i <;> simp; ring
  map_smul' r x := by ext i; fin_cases i <;> simp

def vec2AntiLieTripleSystem :
    FreudenthalKantorTripleSystem.DeltaLieTripleSystem ℝ (-1) (Fin 2 → ℝ) :=
  FreudenthalKantorTripleSystem.toDeltaLieTripleSystem vec2SkewOrthFKTS
    (by norm_num [vec2SkewOrthFKTS, FreudenthalKantorTripleSystem.bilinearRankOneFKTS])
    (by norm_num [vec2SkewOrthFKTS, FreudenthalKantorTripleSystem.bilinearRankOneFKTS])
    vec2Rot90
    (fun v => by
      ext i; fin_cases i <;>
        simp [vec2Rot90, vec2SkewOrthFKTS, FreudenthalKantorTripleSystem.bilinearRankOneFKTS])
    (fun a b c => by
      change vec2Rot90 ((vec2Dot b c) • a) =
        (vec2Dot (vec2Rot90 b) (vec2Rot90 c)) • vec2Rot90 a
      rw [map_smul]
      congr 1
      have hdot : ∀ u v : Fin 2 → ℝ, vec2Dot u v = u 0 * v 0 + u 1 * v 1 := fun _ _ => rfl
      have hrot : ∀ u : Fin 2 → ℝ, vec2Rot90 u = ![-u 1, u 0] := fun _ => rfl
      rw [hdot, hrot, hrot, hdot]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring)

end ConcreteMatrixFKTS

end InfoGeometry.Algebra
