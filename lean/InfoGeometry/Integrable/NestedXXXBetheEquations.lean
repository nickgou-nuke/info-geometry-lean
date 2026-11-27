/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.ConnesLottYangBaxterPoset
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Instances.Complex

/-!
# Nested rational $SU(r+1)$ XXX Bethe ansatz equations and non-commutative RTT

Formalization of the twisted rational XXX Bethe ansatz equations and their
quantum integrability structure from Shu, Zhao, Zhu, and Zou,
*Bethe-state counting and Witten index*, SciPost Phys. 15, 103 (2023)
(Eqs. 1, 2, 7):

1. `NestedXXXBetheData`, `BetheRoots`, explicit denominator non-collision
   (`NonCollisionDenominators`, `NonCollisionAll`), rational system
   `NestedXXXBetheSystem` (Eq. 7 with verified inter-level shift `Complex.I / 2`),
   cleared-denominator polynomial system `NestedXXXBethePolySystem`, and exact
   equivalence `nestedXXXBetheSystem_iff_poly`.
2. Exact specializations to the rank-1 twisted inhomogeneous XXX Bethe
   equations `TwistedXXXBetheSystem` (Eq. 2) and the standard untwisted
   spin-`1/2` Heisenberg XXX Bethe equations `HeisenbergXXXBetheSystem` (Eq. 1).
3. Constructive non-vacuous solution witnesses (vacuum `M = 0`, rank-1 twisted
   single-site `t = π i`, Heisenberg `L = 2, M = 1, λ = 0`, and genuine nested
   `SU(3)` `M = (1, 1)` solution) and exact symmetries (spectral shift, root
   permutation, `2πi` twist periodicity, negation-conjugation, and negation).
4. Non-commutative RTT and transfer-matrix integrability:
   - Reuse of `InfoGeometry.Algebra.ConnesLottYangBaxterPoset` for `SU(2)` 2-site
     RTT intertwining (`su2_twoSite_rtt_from_poset`) and transfer commutativity
     (`su2_twoSite_twistedTransfer_comm`).
   - General `N = r + 1` rational Yang `R`-matrix `yangRMatrix`, 3-space
     Yang–Baxter equation `yangRMatrix_ybe`, `L`-site quantum operator algebra
     `QuantumOp L N`, `siteLax`, `xxxMonodromy`, inductive `xxxMonodromy_rtt`,
     unconditional twisted transfer commutativity `twistedTransferMatrix_comm`,
     and explicit `T16` non-commutativity witnesses.
-/

namespace InfoGeometry.Integrable.NestedXXXBetheEquations

open Filter
open scoped BigOperators Topology

noncomputable section

/-! ### 1. Nested `SU(r + 1)` Rational XXX Bethe Equations (Eqs. 1, 2, 7) -/

/-- Data for the twisted nested `SU(r + 1)` rational XXX Bethe ansatz equations
(Shu–Zhao–Zhu–Zou 2023, Eqs. 1, 2, 7). -/
structure NestedXXXBetheData (r : ℕ) where
  /-- Chain length `L`. -/
  numSites : ℕ
  /-- Site spins `s_α ∈ ℚ` (standard spin-`1/2` has `spin α = 1 / 2`). -/
  spin : Fin numSites → ℚ
  /-- Site inhomogeneities `ν_α ∈ ℂ`. -/
  inhomog : Fin numSites → ℂ
  /-- Diagonal boundary twist parameters `t_a ∈ ℂ` for `a = 1, ..., r`. -/
  twist : Fin r → ℂ
  /-- Magnon numbers `M_a ∈ ℕ` at each nesting level `a = 1, ..., r`. -/
  magnonCount : Fin r → ℕ

/-- T17 constructive inhabitant: empty `0`-site vacuum data for every rank `r`. -/
instance (r : ℕ) : Inhabited (NestedXXXBetheData r) :=
  ⟨⟨0, Fin.elim0, Fin.elim0, fun _ => 0, fun _ => 0⟩⟩

/-- T17 concrete witness for `NestedXXXBetheData 2`. -/
def witnessNestedXXXBetheData : NestedXXXBetheData 2 :=
  ⟨1, fun _ => 1 / 2, fun _ => 0, fun _ => 0, fun _ => 1⟩

/-- Convenience constructor for uniform half-integer spin `twoS / 2` chains. -/
def uniformSpinData (r L twoS : ℕ) (ν : Fin L → ℂ) (t : Fin r → ℂ)
    (M : Fin r → ℕ) : NestedXXXBetheData r where
  numSites := L
  spin := fun _ => (twoS : ℚ) / 2
  inhomog := ν
  twist := t
  magnonCount := M

/-- Rapidities `λ_k^{(a)}` for `a : Fin r`, `k : Fin (D.magnonCount a)`. -/
def BetheRoots {r : ℕ} (D : NestedXXXBetheData r) : Type :=
  (a : Fin r) → Fin (D.magnonCount a) → ℂ

/-- Explicit non-collision of all denominators in Eq. (7):
1. At level `a = 0`: `λ_k^{(1)} - ν_α - i s_α ≠ 0`.
2. At every level `a`: `λ_k^{(a)} - λ_j^{(a)} - i ≠ 0` for `j ≠ k`.
3. Between adjacent levels `a` and `a ± 1`: `λ_k^{(a)} - λ_j^{(a±1)} + i/2 ≠ 0`. -/
def NonCollisionDenominators {r : ℕ} (D : NestedXXXBetheData r)
    (lam : BetheRoots D) : Prop :=
  (∀ (h0 : 0 < r) (k : Fin (D.magnonCount ⟨0, h0⟩)) (α : Fin D.numSites),
    lam ⟨0, h0⟩ k - D.inhomog α - Complex.I * (D.spin α : ℂ) ≠ 0) ∧
  (∀ (a : Fin r) (k j : Fin (D.magnonCount a)), j ≠ k →
    lam a k - lam a j - Complex.I ≠ 0) ∧
  (∀ (a : Fin r) (hprev : 0 < a.val) (k : Fin (D.magnonCount a))
      (j : Fin (D.magnonCount ⟨a.val - 1, by omega⟩)),
    lam a k - lam ⟨a.val - 1, by omega⟩ j + Complex.I / 2 ≠ 0) ∧
  (∀ (a : Fin r) (hnext : a.val + 1 < r) (k : Fin (D.magnonCount a))
      (j : Fin (D.magnonCount ⟨a.val + 1, hnext⟩)),
    lam a k - lam ⟨a.val + 1, hnext⟩ j + Complex.I / 2 ≠ 0)

/-- Symmetric non-collision (both `+` and `-` shifts nonzero), used for direct
rational inversion under `(λ, ν, t) ↦ (-λ, -ν, -t)`. -/
def NonCollisionAll {r : ℕ} (D : NestedXXXBetheData r) (lam : BetheRoots D) : Prop :=
  NonCollisionDenominators D lam ∧
  (∀ (h0 : 0 < r) (k : Fin (D.magnonCount ⟨0, h0⟩)) (α : Fin D.numSites),
    lam ⟨0, h0⟩ k - D.inhomog α + Complex.I * (D.spin α : ℂ) ≠ 0) ∧
  (∀ (a : Fin r) (k j : Fin (D.magnonCount a)), j ≠ k →
    lam a k - lam a j + Complex.I ≠ 0) ∧
  (∀ (a : Fin r) (hprev : 0 < a.val) (k : Fin (D.magnonCount a))
      (j : Fin (D.magnonCount ⟨a.val - 1, by omega⟩)),
    lam a k - lam ⟨a.val - 1, by omega⟩ j - Complex.I / 2 ≠ 0) ∧
  (∀ (a : Fin r) (hnext : a.val + 1 < r) (k : Fin (D.magnonCount a))
      (j : Fin (D.magnonCount ⟨a.val + 1, hnext⟩)),
    lam a k - lam ⟨a.val + 1, hnext⟩ j - Complex.I / 2 ≠ 0)

/-- Left-hand side of Eq. (7) at node `a`, root `k` (site product for `a = 0`, `1` for `a ≥ 1`). -/
def nestedLHS {r : ℕ} (D : NestedXXXBetheData r) (lam : BetheRoots D)
    (a : Fin r) (k : Fin (D.magnonCount a)) : ℂ :=
  if _ha : a.val = 0 then
    ∏ α : Fin D.numSites,
      (lam a k - D.inhomog α + Complex.I * (D.spin α : ℂ)) /
      (lam a k - D.inhomog α - Complex.I * (D.spin α : ℂ))
  else 1

/-- Right-hand side of Eq. (7) at node `a`, root `k`:
`exp(-t_a) * prod_{prev} * prod_{same, j ≠ k} * prod_{next}`. -/
def nestedRHS {r : ℕ} (D : NestedXXXBetheData r) (lam : BetheRoots D)
    (a : Fin r) (k : Fin (D.magnonCount a)) : ℂ :=
  let prevProd : ℂ :=
    if hprev : 0 < a.val then
      ∏ j : Fin (D.magnonCount ⟨a.val - 1, by omega⟩),
        (lam a k - lam ⟨a.val - 1, by omega⟩ j - Complex.I / 2) /
        (lam a k - lam ⟨a.val - 1, by omega⟩ j + Complex.I / 2)
    else 1
  let sameProd : ℂ :=
    ∏ j : Fin (D.magnonCount a),
      if j = k then 1
      else (lam a k - lam a j + Complex.I) / (lam a k - lam a j - Complex.I)
  let nextProd : ℂ :=
    if hnext : a.val + 1 < r then
      ∏ j : Fin (D.magnonCount ⟨a.val + 1, hnext⟩),
        (lam a k - lam ⟨a.val + 1, hnext⟩ j - Complex.I / 2) /
        (lam a k - lam ⟨a.val + 1, hnext⟩ j + Complex.I / 2)
    else 1
  Complex.exp (-D.twist a) * prevProd * sameProd * nextProd

/-- Rational nested `SU(r + 1)` XXX Bethe ansatz system (Source #5 Eq. 7). -/
def NestedXXXBetheSystem {r : ℕ} (D : NestedXXXBetheData r) (lam : BetheRoots D) : Prop :=
  ∀ (a : Fin r) (k : Fin (D.magnonCount a)), nestedLHS D lam a k = nestedRHS D lam a k

/-- Cleared-denominator polynomial LHS of Eq. (7). -/
def nestedPolyLHS {r : ℕ} (D : NestedXXXBetheData r) (lam : BetheRoots D)
    (a : Fin r) (k : Fin (D.magnonCount a)) : ℂ :=
  let siteNum : ℂ :=
    if _ha : a.val = 0 then
      ∏ α : Fin D.numSites, (lam a k - D.inhomog α + Complex.I * (D.spin α : ℂ))
    else 1
  let prevDen : ℂ :=
    if hprev : 0 < a.val then
      ∏ j : Fin (D.magnonCount ⟨a.val - 1, by omega⟩),
        (lam a k - lam ⟨a.val - 1, by omega⟩ j + Complex.I / 2)
    else 1
  let sameDen : ℂ :=
    ∏ j : Fin (D.magnonCount a), if j = k then 1 else (lam a k - lam a j - Complex.I)
  let nextDen : ℂ :=
    if hnext : a.val + 1 < r then
      ∏ j : Fin (D.magnonCount ⟨a.val + 1, hnext⟩),
        (lam a k - lam ⟨a.val + 1, hnext⟩ j + Complex.I / 2)
    else 1
  siteNum * prevDen * sameDen * nextDen

/-- Cleared-denominator polynomial RHS of Eq. (7). -/
def nestedPolyRHS {r : ℕ} (D : NestedXXXBetheData r) (lam : BetheRoots D)
    (a : Fin r) (k : Fin (D.magnonCount a)) : ℂ :=
  let siteDen : ℂ :=
    if _ha : a.val = 0 then
      ∏ α : Fin D.numSites, (lam a k - D.inhomog α - Complex.I * (D.spin α : ℂ))
    else 1
  let prevNum : ℂ :=
    if hprev : 0 < a.val then
      ∏ j : Fin (D.magnonCount ⟨a.val - 1, by omega⟩),
        (lam a k - lam ⟨a.val - 1, by omega⟩ j - Complex.I / 2)
    else 1
  let sameNum : ℂ :=
    ∏ j : Fin (D.magnonCount a), if j = k then 1 else (lam a k - lam a j + Complex.I)
  let nextNum : ℂ :=
    if hnext : a.val + 1 < r then
      ∏ j : Fin (D.magnonCount ⟨a.val + 1, hnext⟩),
        (lam a k - lam ⟨a.val + 1, hnext⟩ j - Complex.I / 2)
    else 1
  Complex.exp (-D.twist a) * siteDen * prevNum * sameNum * nextNum

/-- Cleared-denominator polynomial form of Eq. (7). -/
def NestedXXXBethePolySystem {r : ℕ} (D : NestedXXXBetheData r) (lam : BetheRoots D) : Prop :=
  ∀ (a : Fin r) (k : Fin (D.magnonCount a)), nestedPolyLHS D lam a k = nestedPolyRHS D lam a k

/-- Under `NonCollisionDenominators`, the rational Eq. (7) and its cleared-denominator
polynomial system are logically equivalent. -/
theorem nestedXXXBetheSystem_iff_poly {r : ℕ} (D : NestedXXXBetheData r)
    (lam : BetheRoots D) (h_nc : NonCollisionDenominators D lam) :
    NestedXXXBetheSystem D lam ↔ NestedXXXBethePolySystem D lam := by
  rcases h_nc with ⟨hsite_nc, hsame_nc, hprev_nc, hnext_nc⟩
  have hsite_den_ne : ∀ (a : Fin r) (k : Fin (D.magnonCount a)),
      (if _ha : a.val = 0 then
          ∏ α : Fin D.numSites, (lam a k - D.inhomog α - Complex.I * (D.spin α : ℂ))
        else 1) ≠ 0 := by
    intro a k
    split_ifs with ha
    · have ha_eq : a = ⟨0, lt_of_le_of_lt (Nat.zero_le _) a.isLt⟩ := Fin.ext ha
      revert k
      rw [ha_eq]
      intro k
      exact Finset.prod_ne_zero_iff.mpr fun α _ =>
        hsite_nc (lt_of_le_of_lt (Nat.zero_le _) a.isLt) k α
    · exact one_ne_zero
  have hprev_den_ne : ∀ (a : Fin r) (k : Fin (D.magnonCount a)),
      (if hprev : 0 < a.val then
          ∏ j : Fin (D.magnonCount ⟨a.val - 1, by omega⟩),
            (lam a k - lam ⟨a.val - 1, by omega⟩ j + Complex.I / 2)
        else 1) ≠ 0 := by
    intro a k
    split_ifs with hprev
    · exact Finset.prod_ne_zero_iff.mpr fun j _ => hprev_nc a hprev k j
    · exact one_ne_zero
  have hsame_den_ne : ∀ (a : Fin r) (k : Fin (D.magnonCount a)),
      (∏ j : Fin (D.magnonCount a), if j = k then 1 else (lam a k - lam a j - Complex.I)) ≠ 0 := by
    intro a k
    refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    split_ifs with hj
    · exact one_ne_zero
    · exact hsame_nc a k j hj
  have hnext_den_ne : ∀ (a : Fin r) (k : Fin (D.magnonCount a)),
      (if hnext : a.val + 1 < r then
          ∏ j : Fin (D.magnonCount ⟨a.val + 1, hnext⟩),
            (lam a k - lam ⟨a.val + 1, hnext⟩ j + Complex.I / 2)
        else 1) ≠ 0 := by
    intro a k
    split_ifs with hnext
    · exact Finset.prod_ne_zero_iff.mpr fun j _ => hnext_nc a hnext k j
    · exact one_ne_zero
  have hLHS_eq : ∀ (a : Fin r) (k : Fin (D.magnonCount a)),
      nestedLHS D lam a k =
        (if _ha : a.val = 0 then
            ∏ α : Fin D.numSites, (lam a k - D.inhomog α + Complex.I * (D.spin α : ℂ))
          else 1) /
        (if _ha : a.val = 0 then
            ∏ α : Fin D.numSites, (lam a k - D.inhomog α - Complex.I * (D.spin α : ℂ))
          else 1) := by
    intro a k
    dsimp only [nestedLHS]
    split_ifs with ha
    · rw [Finset.prod_div_distrib]
    · simp
  have hRHS_eq : ∀ (a : Fin r) (k : Fin (D.magnonCount a)),
      nestedRHS D lam a k =
        Complex.exp (-D.twist a) *
          ((if hprev : 0 < a.val then
              ∏ j : Fin (D.magnonCount ⟨a.val - 1, by omega⟩),
                (lam a k - lam ⟨a.val - 1, by omega⟩ j - Complex.I / 2)
            else 1) /
          (if hprev : 0 < a.val then
              ∏ j : Fin (D.magnonCount ⟨a.val - 1, by omega⟩),
                (lam a k - lam ⟨a.val - 1, by omega⟩ j + Complex.I / 2)
            else 1)) *
          ((∏ j : Fin (D.magnonCount a), if j = k then 1 else (lam a k - lam a j + Complex.I)) /
          (∏ j : Fin (D.magnonCount a), if j = k then 1 else (lam a k - lam a j - Complex.I))) *
          ((if hnext : a.val + 1 < r then
              ∏ j : Fin (D.magnonCount ⟨a.val + 1, hnext⟩),
                (lam a k - lam ⟨a.val + 1, hnext⟩ j - Complex.I / 2)
            else 1) /
          (if hnext : a.val + 1 < r then
              ∏ j : Fin (D.magnonCount ⟨a.val + 1, hnext⟩),
                (lam a k - lam ⟨a.val + 1, hnext⟩ j + Complex.I / 2)
            else 1)) := by
    intro a k
    dsimp only [nestedRHS]
    congr 1
    · congr 1
      · congr 1
        split_ifs with hprev
        · rw [Finset.prod_div_distrib]
        · simp
      · rw [← Finset.prod_div_distrib]
        refine Finset.prod_congr rfl fun j _ => ?_
        split_ifs <;> simp
    · split_ifs with hnext
      · rw [Finset.prod_div_distrib]
      · simp
  refine ⟨fun h a k => ?_, fun h a k => ?_⟩
  · have heq := h a k
    rw [hLHS_eq, hRHS_eq] at heq
    dsimp only [nestedPolyLHS, nestedPolyRHS]
    set siteN := if _ha : a.val = 0 then ∏ α : Fin D.numSites, (lam a k - D.inhomog α + Complex.I * (D.spin α : ℂ)) else 1
    set siteD := if _ha : a.val = 0 then ∏ α : Fin D.numSites, (lam a k - D.inhomog α - Complex.I * (D.spin α : ℂ)) else 1
    set prevN := if hprev : 0 < a.val then ∏ j : Fin (D.magnonCount ⟨a.val - 1, by omega⟩), (lam a k - lam ⟨a.val - 1, by omega⟩ j - Complex.I / 2) else 1
    set prevD := if hprev : 0 < a.val then ∏ j : Fin (D.magnonCount ⟨a.val - 1, by omega⟩), (lam a k - lam ⟨a.val - 1, by omega⟩ j + Complex.I / 2) else 1
    set sameN := ∏ j : Fin (D.magnonCount a), if j = k then 1 else (lam a k - lam a j + Complex.I)
    set sameD := ∏ j : Fin (D.magnonCount a), if j = k then 1 else (lam a k - lam a j - Complex.I)
    set nextN := if hnext : a.val + 1 < r then ∏ j : Fin (D.magnonCount ⟨a.val + 1, hnext⟩), (lam a k - lam ⟨a.val + 1, hnext⟩ j - Complex.I / 2) else 1
    set nextD := if hnext : a.val + 1 < r then ∏ j : Fin (D.magnonCount ⟨a.val + 1, hnext⟩), (lam a k - lam ⟨a.val + 1, hnext⟩ j + Complex.I / 2) else 1
    have hsD : siteD ≠ 0 := hsite_den_ne a k
    have hpD : prevD ≠ 0 := hprev_den_ne a k
    have hsmD : sameD ≠ 0 := hsame_den_ne a k
    have hnD : nextD ≠ 0 := hnext_den_ne a k
    change siteN / siteD = Complex.exp (-D.twist a) * (prevN / prevD) * (sameN / sameD) * (nextN / nextD) at heq
    change siteN * prevD * sameD * nextD = Complex.exp (-D.twist a) * siteD * prevN * sameN * nextN
    field_simp [hsD, hpD, hsmD, hnD] at heq ⊢
    linear_combination heq
  · have heq := h a k
    dsimp only [nestedPolyLHS, nestedPolyRHS] at heq
    rw [hLHS_eq, hRHS_eq]
    set siteN := if _ha : a.val = 0 then ∏ α : Fin D.numSites, (lam a k - D.inhomog α + Complex.I * (D.spin α : ℂ)) else 1
    set siteD := if _ha : a.val = 0 then ∏ α : Fin D.numSites, (lam a k - D.inhomog α - Complex.I * (D.spin α : ℂ)) else 1
    set prevN := if hprev : 0 < a.val then ∏ j : Fin (D.magnonCount ⟨a.val - 1, by omega⟩), (lam a k - lam ⟨a.val - 1, by omega⟩ j - Complex.I / 2) else 1
    set prevD := if hprev : 0 < a.val then ∏ j : Fin (D.magnonCount ⟨a.val - 1, by omega⟩), (lam a k - lam ⟨a.val - 1, by omega⟩ j + Complex.I / 2) else 1
    set sameN := ∏ j : Fin (D.magnonCount a), if j = k then 1 else (lam a k - lam a j + Complex.I)
    set sameD := ∏ j : Fin (D.magnonCount a), if j = k then 1 else (lam a k - lam a j - Complex.I)
    set nextN := if hnext : a.val + 1 < r then ∏ j : Fin (D.magnonCount ⟨a.val + 1, hnext⟩), (lam a k - lam ⟨a.val + 1, hnext⟩ j - Complex.I / 2) else 1
    set nextD := if hnext : a.val + 1 < r then ∏ j : Fin (D.magnonCount ⟨a.val + 1, hnext⟩), (lam a k - lam ⟨a.val + 1, hnext⟩ j + Complex.I / 2) else 1
    have hsD : siteD ≠ 0 := hsite_den_ne a k
    have hpD : prevD ≠ 0 := hprev_den_ne a k
    have hsmD : sameD ≠ 0 := hsame_den_ne a k
    have hnD : nextD ≠ 0 := hnext_den_ne a k
    change siteN * prevD * sameD * nextD = Complex.exp (-D.twist a) * siteD * prevN * sameN * nextN at heq
    change siteN / siteD = Complex.exp (-D.twist a) * (prevN / prevD) * (sameN / sameD) * (nextN / nextD)
    field_simp [hsD, hpD, hsmD, hnD]
    linear_combination heq

/-! ### 2. Specializations to Rank-1 Twisted XXX (Eq. 2) & Heisenberg XXX (Eq. 1) -/

/-- Rank-1 twisted inhomogeneous XXX Bethe equations (Source #5 Eq. 2). -/
def TwistedXXXBetheSystem (L M : ℕ) (s : Fin L → ℚ) (ν : Fin L → ℂ)
    (t : ℂ) (lam : Fin M → ℂ) : Prop :=
  ∀ k : Fin M,
    (∏ α : Fin L, (lam k - ν α + Complex.I * (s α : ℂ)) /
                  (lam k - ν α - Complex.I * (s α : ℂ))) =
      Complex.exp (-t) *
        ∏ j : Fin M, if j = k then 1 else (lam k - lam j + Complex.I) / (lam k - lam j - Complex.I)

/-- Standard untwisted spin-`1/2` Heisenberg XXX Bethe equations (Source #5 Eq. 1). -/
def HeisenbergXXXBetheSystem (L M : ℕ) (lam : Fin M → ℂ) : Prop :=
  ∀ k : Fin M,
    ((lam k + Complex.I / 2) / (lam k - Complex.I / 2)) ^ L =
      ∏ j : Fin M, if j = k then 1 else (lam k - lam j + Complex.I) / (lam k - lam j - Complex.I)

/-- `NestedXXXBetheSystem` at rank `r = 1` is literally `TwistedXXXBetheSystem`. -/
theorem nestedXXXBetheSystem_rankOne_iff
    (L M : ℕ) (s : Fin L → ℚ) (ν : Fin L → ℂ) (t : ℂ) (lam : Fin M → ℂ) :
    NestedXXXBetheSystem
        ({ numSites := L, spin := s, inhomog := ν, twist := fun _ => t, magnonCount := fun _ => M } :
          NestedXXXBetheData 1)
        (fun _ => lam) ↔
      TwistedXXXBetheSystem L M s ν t lam := by
  refine ⟨fun h k => ?_, fun h a k => ?_⟩
  · have hk := h 0 k
    simpa [nestedLHS, nestedRHS] using hk
  · obtain rfl : a = 0 := Subsingleton.elim a 0
    simpa [nestedLHS, nestedRHS] using h k

/-- `NestedXXXBetheSystem` at `r = 1`, uniform spin `1/2`, `ν = 0`, `t = 0` is literally
the standard Heisenberg XXX system (Eq. 1). -/
theorem nestedXXXBetheSystem_heisenberg_iff (L M : ℕ) (lam : Fin M → ℂ) :
    NestedXXXBetheSystem
        (uniformSpinData 1 L 1 (fun _ => 0) (fun _ => 0) (fun _ => M))
        (fun _ => lam) ↔
      HeisenbergXXXBetheSystem L M lam := by
  let D1 : NestedXXXBetheData 1 :=
    { numSites := L, spin := fun _ => (1 : ℚ) / 2, inhomog := fun _ => 0,
      twist := fun _ => 0, magnonCount := fun _ => M }
  change NestedXXXBetheSystem D1 (fun _ => lam) ↔ HeisenbergXXXBetheSystem L M lam
  rw [nestedXXXBetheSystem_rankOne_iff L M (fun _ => (1 : ℚ) / 2) (fun _ => 0) 0 lam]
  unfold TwistedXXXBetheSystem HeisenbergXXXBetheSystem
  refine ⟨fun h k => ?_, fun h k => ?_⟩
  · have hk := h k
    simp only [sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow,
      neg_zero, Complex.exp_zero, one_mul] at hk ⊢
    push_cast at hk
    simpa [mul_div_assoc, div_eq_mul_inv] using hk
  · have hk := h k
    simp only [sub_zero, Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_pow,
      neg_zero, Complex.exp_zero, one_mul] at hk ⊢
    push_cast
    simpa [mul_div_assoc, div_eq_mul_inv] using hk

/-! ### 3. Constructive Non-Vacuous Solution Witnesses -/

/-- Vacuum solution (`M_a = 0` for all `a`). -/
theorem vacuum_is_solution (r L : ℕ) (s : Fin L → ℚ) (ν : Fin L → ℂ) (t : Fin r → ℂ) :
    let D : NestedXXXBetheData r :=
      { numSites := L, spin := s, inhomog := ν, twist := t, magnonCount := fun _ => 0 }
    NonCollisionDenominators D (fun _ => Fin.elim0) ∧
    NestedXXXBetheSystem D (fun _ => Fin.elim0) := by
  intro D
  refine ⟨⟨fun _ k => Fin.elim0 k, fun _ k => Fin.elim0 k,
      fun _ _ k => Fin.elim0 k, fun _ _ k => Fin.elim0 k⟩,
    fun _ k => Fin.elim0 k⟩

/-- Constructive rank-1 twisted single-site solution:
`r = 1, L = 1, M = 1, s = 1/2, ν = 0, t = π * I, λ_0 = 0`. -/
theorem singleSite_piI_solution :
    let D := uniformSpinData 1 1 1 (fun _ => 0) (fun _ => Real.pi * Complex.I) (fun _ => 1)
    let lam : BetheRoots D := fun _ _ => 0
    NonCollisionDenominators D lam ∧ NestedXXXBetheSystem D lam := by
  intro D lam
  refine ⟨⟨fun _ _ _ => ?_, fun a k j hj => ?_,
      fun a hprev => absurd hprev (by omega), fun a hnext => absurd hnext (by omega)⟩,
    fun a k => ?_⟩
  · simp [D, lam, uniformSpinData, Complex.I_ne_zero]
  · dsimp only [D, uniformSpinData] at k j hj
    exact False.elim (hj (Subsingleton.elim j k))
  · obtain rfl : a = 0 := Subsingleton.elim a 0
    dsimp only [D, uniformSpinData] at k
    obtain rfl : k = 0 := Subsingleton.elim k 0
    have hexp : Complex.exp (-(Real.pi * Complex.I)) = -1 := by
      rw [Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    dsimp only [nestedLHS, nestedRHS, D, lam, uniformSpinData]
    simp [hexp]

/-- Constructive untwisted Heisenberg XXX solution (`L = 2, M = 1, λ_0 = 0`, Eq. 1). -/
theorem heisenberg_L2_M1_zero_solution :
    let D := uniformSpinData 1 2 1 (fun _ => 0) (fun _ => 0) (fun _ => 1)
    let lam : BetheRoots D := fun _ _ => 0
    NonCollisionDenominators D lam ∧
    NestedXXXBetheSystem D lam ∧
    HeisenbergXXXBetheSystem 2 1 (fun _ => 0) := by
  intro D lam
  have hnc : NonCollisionDenominators D lam := by
    refine ⟨fun _ _ _ => ?_, fun a k j hj => ?_,
        fun a hprev => absurd hprev (by omega), fun a hnext => absurd hnext (by omega)⟩
    · simp [D, lam, uniformSpinData, Complex.I_ne_zero]
    · dsimp only [D, uniformSpinData] at k j hj
      exact False.elim (hj (Subsingleton.elim j k))
  have hheis : HeisenbergXXXBetheSystem 2 1 (fun _ => 0) := by
    intro k
    obtain rfl : k = 0 := Subsingleton.elim k 0
    simp
  refine ⟨hnc, (nestedXXXBetheSystem_heisenberg_iff 2 1 (fun _ => 0)).mpr hheis, hheis⟩

/-- Constructive genuine nested rank-2 `SU(3)` solution (`r = 2, L = 1, M = (1, 1), s = 1/2, ν = 0, t = (0, π i), λ = 0`, Eq. 7),
directly exercising the `± i / 2` inter-level coupling. -/
theorem su3_nested_M11_solution :
    let D := uniformSpinData 2 1 1 (fun _ => 0) ![0, Real.pi * Complex.I] ![1, 1]
    let lam : BetheRoots D := fun _ _ => 0
    NonCollisionDenominators D lam ∧ NestedXXXBetheSystem D lam := by
  intro D lam
  have hIhalf_pos_ne : (Complex.I / 2 : ℂ) ≠ 0 := by simp [Complex.I_ne_zero]
  refine ⟨⟨fun _ _ _ => ?_, fun a k j hj => ?_,
      fun _ _ _ _ => ?_, fun _ _ _ _ => ?_⟩,
    fun a k => ?_⟩
  · simp [D, lam, uniformSpinData, Complex.I_ne_zero]
  · dsimp only [D, uniformSpinData] at k j hj
    fin_cases a <;> exact False.elim (hj (Subsingleton.elim (α := Fin 1) j k))
  · simp [lam, hIhalf_pos_ne]
  · simp [lam, hIhalf_pos_ne]
  · fin_cases a
    · dsimp only [nestedLHS, nestedRHS, D, lam, uniformSpinData] at k ⊢
      rw [dif_pos rfl, dif_neg (by omega), dif_pos (by omega)]
      simp
      have hprod0 : (∏ j, if j = k then (1 : ℂ) else -1) = 1 := by
        rw [Finset.prod_eq_single k]
        · rw [if_pos rfl]
        · intro j _ hj
          exfalso; apply hj; ext
          have hjlt := j.isLt; have hklt := k.isLt; simp at hjlt hklt; omega
        · intro hkmem; exact absurd (Finset.mem_univ k) hkmem
      erw [hprod0, Finset.card_univ, Fintype.card_fin]
      simp
    · have hexp : Complex.exp (-(Real.pi * Complex.I)) = -1 := by
        rw [Complex.exp_neg, Complex.exp_pi_mul_I]
        norm_num
      dsimp only [nestedLHS, nestedRHS, D, lam, uniformSpinData] at k ⊢
      rw [dif_neg (by omega), dif_pos (by omega), dif_neg (by omega)]
      simp [hexp]
      have hprod1 : (∏ j, if j = k then (1 : ℂ) else -1) = 1 := by
        rw [Finset.prod_eq_single k]
        · rw [if_pos rfl]
        · intro j _ hj
          exfalso; apply hj; ext
          have hjlt := j.isLt; have hklt := k.isLt; simp at hjlt hklt; omega
        · intro hkmem; exact absurd (Finset.mem_univ k) hkmem
      erw [hprod1, Finset.card_univ, Fintype.card_fin]
      simp

/-! ### 4. Exact Symmetries of `NestedXXXBetheSystem` -/

/-- Spectral translation invariance: shifting `ν_α ↦ ν_α + c` and `λ_k^{(a)} ↦ λ_k^{(a)} + c`
preserves both `NonCollisionDenominators` and `NestedXXXBetheSystem`. -/
theorem nestedXXXBetheSystem_shift {r : ℕ} (D : NestedXXXBetheData r)
    (lam : BetheRoots D) (c : ℂ) :
    let D' : NestedXXXBetheData r := { D with inhomog := fun α => D.inhomog α + c }
    let lam' : BetheRoots D' := fun a k => lam a k + c
    (NonCollisionDenominators D' lam' ↔ NonCollisionDenominators D lam) ∧
    (NestedXXXBetheSystem D' lam' ↔ NestedXXXBetheSystem D lam) := by
  intro D' lam'
  have hsub1 : ∀ (a : Fin r) (k : Fin (D.magnonCount a)) (α : Fin D.numSites),
      lam' a k - D'.inhomog α = lam a k - D.inhomog α := by
    intro a k α; dsimp [D', lam']; ring
  have hsub2 : ∀ (a : Fin r) (k : Fin (D.magnonCount a)) (b : Fin r) (j : Fin (D.magnonCount b)),
      lam' a k - lam' b j = lam a k - lam b j := by
    intro a k b j; dsimp [lam']; ring
  refine ⟨?_, ?_⟩
  · constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0 k α; simpa [hsub1] using h1 h0 k α
    · intro a k j hj; simpa [hsub2] using h2 a k j hj
    · intro a hprev k j; simpa [hsub2] using h3 a hprev k j
    · intro a hnext k j; simpa [hsub2] using h4 a hnext k j
    · intro h0 k α; simpa [hsub1] using h1 h0 k α
    · intro a k j hj; simpa [hsub2] using h2 a k j hj
    · intro a hprev k j; simpa [hsub2] using h3 a hprev k j
    · intro a hnext k j; simpa [hsub2] using h4 a hnext k j
  · have hLHS : ∀ a k, nestedLHS D' lam' a k = nestedLHS D lam a k := by
      intro a k
      dsimp [nestedLHS]
      split_ifs
      · refine Finset.prod_congr rfl fun α _ => ?_
        rw [hsub1]
      · rfl
    have hRHS : ∀ a k, nestedRHS D' lam' a k = nestedRHS D lam a k := by
      intro a k
      dsimp [nestedRHS]
      have htwist : D'.twist a = D.twist a := rfl
      rw [htwist]
      congr 1
      · congr 1
        · congr 1
          split_ifs
          · exact Finset.prod_congr rfl fun j _ => by rw [hsub2]
          · rfl
        · refine Finset.prod_congr rfl fun j _ => ?_
          split_ifs
          · rfl
          · rw [hsub2]
      · split_ifs
        · exact Finset.prod_congr rfl fun j _ => by rw [hsub2]
        · rfl
    exact ⟨fun h a k => by rw [← hLHS, ← hRHS]; exact h a k,
      fun h a k => by rw [hLHS, hRHS]; exact h a k⟩

/-- Root permutation invariance at each nesting level `a`. -/
theorem nestedXXXBetheSystem_perm {r : ℕ} (D : NestedXXXBetheData r)
    (lam : BetheRoots D) (σ : (a : Fin r) → Equiv.Perm (Fin (D.magnonCount a))) :
    let lam' : BetheRoots D := fun a k => lam a (σ a k)
    (NonCollisionDenominators D lam' ↔ NonCollisionDenominators D lam) ∧
    (NestedXXXBetheSystem D lam' ↔ NestedXXXBetheSystem D lam) := by
  intro lam'
  have hLHS_eq : ∀ a k, nestedLHS D lam' a k = nestedLHS D lam a (σ a k) := by
    intro a k; rfl
  have hRHS_eq : ∀ a k, nestedRHS D lam' a k = nestedRHS D lam a (σ a k) := by
    intro a k
    dsimp [nestedRHS]
    congr 1
    · congr 1
      · congr 1
        split_ifs with hprev
        · exact Fintype.prod_equiv (σ ⟨a.val - 1, by omega⟩) _ _ fun _ => rfl
        · rfl
      · refine Fintype.prod_equiv (σ a) _ _ fun j => ?_
        by_cases hj : j = k
        · subst hj; simp
        · have hne : σ a j ≠ σ a k := fun h => hj ((σ a).injective h)
          simp [hj, hne, lam']
    · split_ifs with hnext
      · exact Fintype.prod_equiv (σ ⟨a.val + 1, hnext⟩) _ _ fun _ => rfl
      · rfl
  refine ⟨?_, ?_⟩
  · constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro h0 k α
        simpa [lam'] using h1 h0 ((σ ⟨0, h0⟩).symm k) α
      · intro a k j hj
        have hne : (σ a).symm j ≠ (σ a).symm k := fun h => hj ((σ a).symm.injective h)
        simpa [lam'] using h2 a ((σ a).symm k) ((σ a).symm j) hne
      · intro a hprev k j
        simpa [lam'] using h3 a hprev ((σ a).symm k) ((σ ⟨a.val - 1, by omega⟩).symm j)
      · intro a hnext k j
        simpa [lam'] using h4 a hnext ((σ a).symm k) ((σ ⟨a.val + 1, hnext⟩).symm j)
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro h0 k α
        exact h1 h0 (σ ⟨0, h0⟩ k) α
      · intro a k j hj
        exact h2 a (σ a k) (σ a j) (fun h => hj ((σ a).injective h))
      · intro a hprev k j
        exact h3 a hprev (σ a k) (σ ⟨a.val - 1, by omega⟩ j)
      · intro a hnext k j
        exact h4 a hnext (σ a k) (σ ⟨a.val + 1, hnext⟩ j)
  · constructor
    · intro h a k
      have hk := h a ((σ a).symm k)
      rw [hLHS_eq, hRHS_eq, Equiv.apply_symm_apply] at hk
      exact hk
    · intro h a k
      rw [hLHS_eq, hRHS_eq]
      exact h a (σ a k)

/-- Twist periodicity `t_a ↦ t_a + 2 π i n_a` (`n : Fin r → ℤ`). -/
theorem nestedXXXBetheSystem_twist_add_two_pi_I {r : ℕ} (D : NestedXXXBetheData r)
    (lam : BetheRoots D) (n : Fin r → ℤ) :
    let D' : NestedXXXBetheData r :=
      { D with twist := fun a => D.twist a + 2 * Real.pi * Complex.I * (n a : ℂ) }
    NestedXXXBetheSystem D' lam ↔ NestedXXXBetheSystem D lam := by
  intro D'
  have hexp : ∀ a : Fin r, Complex.exp (-D'.twist a) = Complex.exp (-D.twist a) := by
    intro a
    dsimp [D']
    have harg :
        -(D.twist a + 2 * Real.pi * Complex.I * (n a : ℂ)) =
          (-D.twist a) + ((-n a : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      ring
    rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hLHS : ∀ a k, nestedLHS D' lam a k = nestedLHS D lam a k := fun _ _ => rfl
  have hRHS : ∀ a k, nestedRHS D' lam a k = nestedRHS D lam a k := by
    intro a k
    dsimp [nestedRHS]
    rw [hexp a]
  exact ⟨fun h a k => by rw [← hLHS, ← hRHS]; exact h a k,
    fun h a k => by rw [hLHS, hRHS]; exact h a k⟩

/-- Negation-conjugation symmetry `(λ, ν, t) ↦ (-conj λ, -conj ν, conj t)`. -/
theorem nestedXXXBetheSystem_neg_conj {r : ℕ} (D : NestedXXXBetheData r)
    (lam : BetheRoots D) :
    let D' : NestedXXXBetheData r :=
      { D with
        inhomog := fun α => -star (D.inhomog α)
        twist := fun a => star (D.twist a) }
    let lam' : BetheRoots D' := fun a k => -star (lam a k)
    (NonCollisionDenominators D' lam' ↔ NonCollisionDenominators D lam) ∧
    (NestedXXXBetheSystem D' lam' ↔ NestedXXXBetheSystem D lam) := by
  intro D' lam'
  have hconj_spin : ∀ α : Fin D.numSites, starRingEnd ℂ (D.spin α : ℂ) = (D.spin α : ℂ) := by
    intro α; simp
  have hsite_num : ∀ a k α,
      lam' a k - D'.inhomog α + Complex.I * (D'.spin α : ℂ) =
        -star (lam a k - D.inhomog α + Complex.I * (D.spin α : ℂ)) := by
    intro a k α
    dsimp [D', lam']
    simp only [map_add, map_sub, map_mul, Complex.conj_I, hconj_spin]
    ring
  have hsite_den : ∀ a k α,
      lam' a k - D'.inhomog α - Complex.I * (D'.spin α : ℂ) =
        -star (lam a k - D.inhomog α - Complex.I * (D.spin α : ℂ)) := by
    intro a k α
    dsimp [D', lam']
    simp only [map_sub, map_mul, Complex.conj_I, hconj_spin]
    ring
  have hsame_num : ∀ a k j,
      lam' a k - lam' a j + Complex.I = -star (lam a k - lam a j + Complex.I) := by
    intro a k j
    dsimp [lam']
    simp only [map_add, map_sub, Complex.conj_I]
    ring
  have hsame_den : ∀ a k j,
      lam' a k - lam' a j - Complex.I = -star (lam a k - lam a j - Complex.I) := by
    intro a k j
    dsimp [lam']
    simp only [map_sub, Complex.conj_I]
    ring
  have hcross_num : ∀ (a : Fin r) k (b : Fin r) j,
      lam' a k - lam' b j - Complex.I / 2 = -star (lam a k - lam b j - Complex.I / 2) := by
    intro a k b j
    dsimp [lam']
    simp only [map_sub, map_div₀, Complex.conj_I, map_ofNat]
    ring
  have hcross_den : ∀ (a : Fin r) k (b : Fin r) j,
      lam' a k - lam' b j + Complex.I / 2 = -star (lam a k - lam b j + Complex.I / 2) := by
    intro a k b j
    dsimp [lam']
    simp only [map_add, map_sub, map_div₀, Complex.conj_I, map_ofNat]
    ring
  have hneg_conj_ne : ∀ z : ℂ, -star z ≠ 0 ↔ z ≠ 0 := by
    intro z
    simp [neg_eq_zero]
  refine ⟨?_, ?_⟩
  · constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0 k α; rw [← hneg_conj_ne, ← hsite_den]; exact h1 h0 k α
    · intro a k j hj; rw [← hneg_conj_ne, ← hsame_den]; exact h2 a k j hj
    · intro a hprev k j; rw [← hneg_conj_ne, ← hcross_den]; exact h3 a hprev k j
    · intro a hnext k j; rw [← hneg_conj_ne, ← hcross_den]; exact h4 a hnext k j
    · intro h0 k α; rw [hsite_den, hneg_conj_ne]; exact h1 h0 k α
    · intro a k j hj; rw [hsame_den, hneg_conj_ne]; exact h2 a k j hj
    · intro a hprev k j; rw [hcross_den, hneg_conj_ne]; exact h3 a hprev k j
    · intro a hnext k j; rw [hcross_den, hneg_conj_ne]; exact h4 a hnext k j
  · have hLHS : ∀ a k, nestedLHS D' lam' a k = star (nestedLHS D lam a k) := by
      intro a k
      dsimp [nestedLHS]
      split_ifs
      · rw [map_prod]
        refine Finset.prod_congr rfl fun α _ => ?_
        rw [hsite_num, hsite_den, neg_div_neg_eq]
        exact (map_div₀ (starRingEnd ℂ) _ _).symm
      · simp
    have hRHS : ∀ a k, nestedRHS D' lam' a k = star (nestedRHS D lam a k) := by
      intro a k
      dsimp [nestedRHS]
      have hexp_conj : Complex.exp (-D'.twist a) = star (Complex.exp (-D.twist a)) := by
        dsimp [D']
        rw [← Complex.exp_conj]
        simp
      rw [hexp_conj, map_mul, map_mul, map_mul]
      congr 1
      · congr 1
        · congr 1
          split_ifs
          · rw [map_prod]
            refine Finset.prod_congr rfl fun j _ => ?_
            rw [hcross_num, hcross_den, neg_div_neg_eq]
            exact (map_div₀ (starRingEnd ℂ) _ _).symm
          · simp
        · rw [map_prod]
          refine Finset.prod_congr rfl fun j _ => ?_
          split_ifs
          · simp
          · rw [hsame_num, hsame_den, neg_div_neg_eq]
            exact (map_div₀ (starRingEnd ℂ) _ _).symm
      · split_ifs
        · rw [map_prod]
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [hcross_num, hcross_den, neg_div_neg_eq]
          exact (map_div₀ (starRingEnd ℂ) _ _).symm
        · simp
    exact ⟨fun h a k => star_injective (by rw [← hLHS, ← hRHS]; exact h a k),
      fun h a k => by rw [hLHS, hRHS, h a k]⟩

/-- Unconditional negation symmetry of the polynomial system `(λ, ν, t) ↦ (-λ, -ν, -t)`. -/
theorem nestedXXXBethePolySystem_neg {r : ℕ} (D : NestedXXXBetheData r)
    (lam : BetheRoots D) :
    let D' : NestedXXXBetheData r :=
      { D with inhomog := fun α => -D.inhomog α, twist := fun a => -D.twist a }
    let lam' : BetheRoots D' := fun a k => -lam a k
    NestedXXXBethePolySystem D' lam' ↔ NestedXXXBethePolySystem D lam := by
  intro D' lam'
  have hneg_prod : ∀ {ι : Type} (s : Finset ι) (f : ι → ℂ),
      (∏ i ∈ s, -f i) = (-1 : ℂ) ^ s.card * ∏ i ∈ s, f i := by
    intro ι s f
    induction s using Finset.cons_induction with
    | empty => simp
    | cons x s hx ih =>
      rw [Finset.prod_cons, Finset.prod_cons, Finset.card_cons, ih]
      ring
  have hLHS_rel : ∀ a k,
      nestedPolyLHS D' lam' a k =
        (-1 : ℂ) ^ ((if a.val = 0 then D.numSites else 0) +
            (if hprev : 0 < a.val then D.magnonCount ⟨a.val - 1, by omega⟩ else 0) +
            (Finset.univ.filter (fun j : Fin (D.magnonCount a) => j ≠ k)).card +
            (if hnext : a.val + 1 < r then D.magnonCount ⟨a.val + 1, hnext⟩ else 0)) *
          nestedPolyRHS D lam a k * Complex.exp (D.twist a) := by
    intro a k
    dsimp [nestedPolyLHS, nestedPolyRHS, D', lam']
    have hsite :
        (if a.val = 0 then
            ∏ α : Fin D.numSites, (-lam a k - -D.inhomog α + Complex.I * (D.spin α : ℂ))
          else 1) =
        (-1 : ℂ) ^ (if a.val = 0 then D.numSites else 0) *
          (if a.val = 0 then
            ∏ α : Fin D.numSites, (lam a k - D.inhomog α - Complex.I * (D.spin α : ℂ))
          else 1) := by
      split_ifs with ha
      · have h1 : (∏ α : Fin D.numSites, (-lam a k - -D.inhomog α + Complex.I * (D.spin α : ℂ))) =
            ∏ α : Fin D.numSites, -(lam a k - D.inhomog α - Complex.I * (D.spin α : ℂ)) := by
          refine Finset.prod_congr rfl fun α _ => by ring
        rw [h1, hneg_prod]
        simp
      · simp
    have hprev :
        (if hprev : 0 < a.val then
            ∏ j : Fin (D.magnonCount ⟨a.val - 1, by omega⟩),
              (-lam a k - -lam ⟨a.val - 1, by omega⟩ j + Complex.I / 2)
          else 1) =
        (-1 : ℂ) ^ (if hprev : 0 < a.val then D.magnonCount ⟨a.val - 1, by omega⟩ else 0) *
          (if hprev : 0 < a.val then
            ∏ j : Fin (D.magnonCount ⟨a.val - 1, by omega⟩),
              (lam a k - lam ⟨a.val - 1, by omega⟩ j - Complex.I / 2)
          else 1) := by
      split_ifs with hp
      · have h1 :
            (∏ j : Fin (D.magnonCount ⟨a.val - 1, by omega⟩),
              (-lam a k - -lam ⟨a.val - 1, by omega⟩ j + Complex.I / 2)) =
            ∏ j : Fin (D.magnonCount ⟨a.val - 1, by omega⟩),
              -(lam a k - lam ⟨a.val - 1, by omega⟩ j - Complex.I / 2) := by
          refine Finset.prod_congr rfl fun j _ => by ring
        rw [h1, hneg_prod]
        simp
      · simp
    have hsame :
        (∏ j : Fin (D.magnonCount a), if j = k then 1 else (-lam a k - -lam a j - Complex.I)) =
        (-1 : ℂ) ^ (Finset.univ.filter (fun j : Fin (D.magnonCount a) => j ≠ k)).card *
          (∏ j : Fin (D.magnonCount a), if j = k then 1 else (lam a k - lam a j + Complex.I)) := by
      have hL :
          (∏ j : Fin (D.magnonCount a), if j = k then 1 else (-lam a k - -lam a j - Complex.I)) =
          ∏ j ∈ Finset.univ.filter (fun j : Fin (D.magnonCount a) => j ≠ k),
            -(lam a k - lam a j + Complex.I) := by
        rw [Finset.prod_filter]
        refine Finset.prod_congr rfl fun j _ => ?_
        by_cases hj : j = k <;> simp [hj] <;> ring
      have hR :
          (∏ j : Fin (D.magnonCount a), if j = k then 1 else (lam a k - lam a j + Complex.I)) =
          ∏ j ∈ Finset.univ.filter (fun j : Fin (D.magnonCount a) => j ≠ k),
            (lam a k - lam a j + Complex.I) := by
        rw [Finset.prod_filter]
        refine Finset.prod_congr rfl fun j _ => ?_
        by_cases hj : j = k <;> simp [hj]
      rw [hL, hR, hneg_prod]
    have hnext :
        (if hnext : a.val + 1 < r then
            ∏ j : Fin (D.magnonCount ⟨a.val + 1, hnext⟩),
              (-lam a k - -lam ⟨a.val + 1, hnext⟩ j + Complex.I / 2)
          else 1) =
        (-1 : ℂ) ^ (if hnext : a.val + 1 < r then D.magnonCount ⟨a.val + 1, hnext⟩ else 0) *
          (if hnext : a.val + 1 < r then
            ∏ j : Fin (D.magnonCount ⟨a.val + 1, hnext⟩),
              (lam a k - lam ⟨a.val + 1, hnext⟩ j - Complex.I / 2)
          else 1) := by
      split_ifs with hn
      · have h1 :
            (∏ j : Fin (D.magnonCount ⟨a.val + 1, hn⟩),
              (-lam a k - -lam ⟨a.val + 1, hn⟩ j + Complex.I / 2)) =
            ∏ j : Fin (D.magnonCount ⟨a.val + 1, hn⟩),
              -(lam a k - lam ⟨a.val + 1, hn⟩ j - Complex.I / 2) := by
          refine Finset.prod_congr rfl fun j _ => by ring
        rw [h1, hneg_prod]
        simp
      · simp
    rw [hsite, hprev, hsame, hnext]
    have hexp : Complex.exp (-D.twist a) * Complex.exp (D.twist a) = 1 := by
      rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
    set P1 := (-1 : ℂ) ^ (if a.val = 0 then D.numSites else 0)
    set P2 := (-1 : ℂ) ^ (if hprev : 0 < a.val then D.magnonCount ⟨a.val - 1, by omega⟩ else 0)
    set P3 := (-1 : ℂ) ^ (Finset.univ.filter (fun j : Fin (D.magnonCount a) => j ≠ k)).card
    set P4 := (-1 : ℂ) ^ (if hnext : a.val + 1 < r then D.magnonCount ⟨a.val + 1, hnext⟩ else 0)
    set S := if a.val = 0 then ∏ α : Fin D.numSites, (lam a k - D.inhomog α - Complex.I * (D.spin α : ℂ)) else 1
    set Pr := if hprev : 0 < a.val then ∏ j : Fin (D.magnonCount ⟨a.val - 1, by omega⟩), (lam a k - lam ⟨a.val - 1, by omega⟩ j - Complex.I / 2) else 1
    set Sm := ∏ j : Fin (D.magnonCount a), if j = k then 1 else (lam a k - lam a j + Complex.I)
    set Nx := if hnext : a.val + 1 < r then ∏ j : Fin (D.magnonCount ⟨a.val + 1, hnext⟩), (lam a k - lam ⟨a.val + 1, hnext⟩ j - Complex.I / 2) else 1
    calc
      (P1 * S) * (P2 * Pr) * (P3 * Sm) * (P4 * Nx)
        = (P1 * P2 * P3 * P4) * ((1 : ℂ) * S * Pr * Sm * Nx) := by ring
      _ = (P1 * P2 * P3 * P4) * ((Complex.exp (-D.twist a) * Complex.exp (D.twist a)) * S * Pr * Sm * Nx) := by
          rw [hexp]
      _ = (-1 : ℂ) ^ ((if a.val = 0 then D.numSites else 0) +
            (if hprev : 0 < a.val then D.magnonCount ⟨a.val - 1, by omega⟩ else 0) +
            (Finset.univ.filter (fun j : Fin (D.magnonCount a) => j ≠ k)).card +
            (if hnext : a.val + 1 < r then D.magnonCount ⟨a.val + 1, hnext⟩ else 0)) *
          (Complex.exp (-D.twist a) * S * Pr * Sm * Nx) * Complex.exp (D.twist a) := by
          simp only [pow_add]
          ring
  have hRHS_rel : ∀ a k,
      nestedPolyRHS D' lam' a k =
        (-1 : ℂ) ^ ((if a.val = 0 then D.numSites else 0) +
            (if hprev : 0 < a.val then D.magnonCount ⟨a.val - 1, by omega⟩ else 0) +
            (Finset.univ.filter (fun j : Fin (D.magnonCount a) => j ≠ k)).card +
            (if hnext : a.val + 1 < r then D.magnonCount ⟨a.val + 1, hnext⟩ else 0)) *
          nestedPolyLHS D lam a k * Complex.exp (D.twist a) := by
    intro a k
    dsimp [nestedPolyLHS, nestedPolyRHS, D', lam']
    have hsite :
        (if a.val = 0 then
            ∏ α : Fin D.numSites, (-lam a k - -D.inhomog α - Complex.I * (D.spin α : ℂ))
          else 1) =
        (-1 : ℂ) ^ (if a.val = 0 then D.numSites else 0) *
          (if a.val = 0 then
            ∏ α : Fin D.numSites, (lam a k - D.inhomog α + Complex.I * (D.spin α : ℂ))
          else 1) := by
      split_ifs with ha
      · have h1 : (∏ α : Fin D.numSites, (-lam a k - -D.inhomog α - Complex.I * (D.spin α : ℂ))) =
            ∏ α : Fin D.numSites, -(lam a k - D.inhomog α + Complex.I * (D.spin α : ℂ)) := by
          refine Finset.prod_congr rfl fun α _ => by ring
        rw [h1, hneg_prod]
        simp
      · simp
    have hprev :
        (if hprev : 0 < a.val then
            ∏ j : Fin (D.magnonCount ⟨a.val - 1, by omega⟩),
              (-lam a k - -lam ⟨a.val - 1, by omega⟩ j - Complex.I / 2)
          else 1) =
        (-1 : ℂ) ^ (if hprev : 0 < a.val then D.magnonCount ⟨a.val - 1, by omega⟩ else 0) *
          (if hprev : 0 < a.val then
            ∏ j : Fin (D.magnonCount ⟨a.val - 1, by omega⟩),
              (lam a k - lam ⟨a.val - 1, by omega⟩ j + Complex.I / 2)
          else 1) := by
      split_ifs with hp
      · have h1 :
            (∏ j : Fin (D.magnonCount ⟨a.val - 1, by omega⟩),
              (-lam a k - -lam ⟨a.val - 1, by omega⟩ j - Complex.I / 2)) =
            ∏ j : Fin (D.magnonCount ⟨a.val - 1, by omega⟩),
              -(lam a k - lam ⟨a.val - 1, by omega⟩ j + Complex.I / 2) := by
          refine Finset.prod_congr rfl fun j _ => by ring
        rw [h1, hneg_prod]
        simp
      · simp
    have hsame :
        (∏ j : Fin (D.magnonCount a), if j = k then 1 else (-lam a k - -lam a j + Complex.I)) =
        (-1 : ℂ) ^ (Finset.univ.filter (fun j : Fin (D.magnonCount a) => j ≠ k)).card *
          (∏ j : Fin (D.magnonCount a), if j = k then 1 else (lam a k - lam a j - Complex.I)) := by
      have hL :
          (∏ j : Fin (D.magnonCount a), if j = k then 1 else (-lam a k - -lam a j + Complex.I)) =
          ∏ j ∈ Finset.univ.filter (fun j : Fin (D.magnonCount a) => j ≠ k),
            -(lam a k - lam a j - Complex.I) := by
        rw [Finset.prod_filter]
        refine Finset.prod_congr rfl fun j _ => ?_
        by_cases hj : j = k <;> simp [hj] <;> ring
      have hR :
          (∏ j : Fin (D.magnonCount a), if j = k then 1 else (lam a k - lam a j - Complex.I)) =
          ∏ j ∈ Finset.univ.filter (fun j : Fin (D.magnonCount a) => j ≠ k),
            (lam a k - lam a j - Complex.I) := by
        rw [Finset.prod_filter]
        refine Finset.prod_congr rfl fun j _ => ?_
        by_cases hj : j = k <;> simp [hj]
      rw [hL, hR, hneg_prod]
    have hnext :
        (if hnext : a.val + 1 < r then
            ∏ j : Fin (D.magnonCount ⟨a.val + 1, hnext⟩),
              (-lam a k - -lam ⟨a.val + 1, hnext⟩ j - Complex.I / 2)
          else 1) =
        (-1 : ℂ) ^ (if hnext : a.val + 1 < r then D.magnonCount ⟨a.val + 1, hnext⟩ else 0) *
          (if hnext : a.val + 1 < r then
            ∏ j : Fin (D.magnonCount ⟨a.val + 1, hnext⟩),
              (lam a k - lam ⟨a.val + 1, hnext⟩ j + Complex.I / 2)
          else 1) := by
      split_ifs with hn
      · have h1 :
            (∏ j : Fin (D.magnonCount ⟨a.val + 1, hn⟩),
              (-lam a k - -lam ⟨a.val + 1, hn⟩ j - Complex.I / 2)) =
            ∏ j : Fin (D.magnonCount ⟨a.val + 1, hn⟩),
              -(lam a k - lam ⟨a.val + 1, hn⟩ j + Complex.I / 2) := by
          refine Finset.prod_congr rfl fun j _ => by ring
        rw [h1, hneg_prod]
        simp
      · simp
    rw [hsite, hprev, hsame, hnext]
    simp only [neg_neg, pow_add]
    ring
  constructor
  · intro h a k
    have heq := h a k
    rw [hLHS_rel, hRHS_rel] at heq
    have hexp_ne : Complex.exp (D.twist a) ≠ 0 := Complex.exp_ne_zero _
    have hpow_ne :
        (-1 : ℂ) ^ ((if a.val = 0 then D.numSites else 0) +
            (if hprev : 0 < a.val then D.magnonCount ⟨a.val - 1, by omega⟩ else 0) +
            (Finset.univ.filter (fun j : Fin (D.magnonCount a) => j ≠ k)).card +
            (if hnext : a.val + 1 < r then D.magnonCount ⟨a.val + 1, hnext⟩ else 0)) ≠ 0 :=
      pow_ne_zero _ (by norm_num)
    exact (mul_right_injective₀ hpow_ne (mul_left_injective₀ hexp_ne heq)).symm
  · intro h a k
    rw [hLHS_rel, hRHS_rel, h a k]

/-- Rational negation symmetry `(λ, ν, t) ↦ (-λ, -ν, -t)` under `NonCollisionAll`. -/
theorem nestedXXXBetheSystem_neg {r : ℕ} (D : NestedXXXBetheData r)
    (lam : BetheRoots D) (h_nc : NonCollisionAll D lam) :
    let D' : NestedXXXBetheData r :=
      { D with inhomog := fun α => -D.inhomog α, twist := fun a => -D.twist a }
    let lam' : BetheRoots D' := fun a k => -lam a k
    NestedXXXBetheSystem D' lam' ↔ NestedXXXBetheSystem D lam := by
  intro D' lam'
  have hnc_neg : NonCollisionDenominators D' lam' := by
    rcases h_nc with ⟨_, h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0 k α
      have h := h1 h0 k α
      have heq : lam' ⟨0, h0⟩ k - D'.inhomog α - Complex.I * (D'.spin α : ℂ) =
          -(lam ⟨0, h0⟩ k - D.inhomog α + Complex.I * (D.spin α : ℂ)) := by
        dsimp [D', lam']; ring
      rw [heq, neg_ne_zero]; exact h
    · intro a k j hj
      have h := h2 a k j hj
      have heq : lam' a k - lam' a j - Complex.I = -(lam a k - lam a j + Complex.I) := by
        dsimp [lam']; ring
      rw [heq, neg_ne_zero]; exact h
    · intro a hprev k j
      have h := h3 a hprev k j
      have heq : lam' a k - lam' ⟨a.val - 1, by omega⟩ j + Complex.I / 2 =
          -(lam a k - lam ⟨a.val - 1, by omega⟩ j - Complex.I / 2) := by
        dsimp [lam']; ring
      rw [heq, neg_ne_zero]; exact h
    · intro a hnext k j
      have h := h4 a hnext k j
      have heq : lam' a k - lam' ⟨a.val + 1, hnext⟩ j + Complex.I / 2 =
          -(lam a k - lam ⟨a.val + 1, hnext⟩ j - Complex.I / 2) := by
        dsimp [lam']; ring
      rw [heq, neg_ne_zero]; exact h
  rw [nestedXXXBetheSystem_iff_poly D' lam' hnc_neg,
      nestedXXXBetheSystem_iff_poly D lam h_nc.1]
  exact nestedXXXBethePolySystem_neg D lam

/-! ### 5. Non-Commutative RTT & Transfer-Matrix Integrability (`T16` & `T17`) -/

section SU2PosetReuse

open InfoGeometry.Algebra.ConnesLottYangBaxterPoset

/-- Reuse of `ConnesLottYangBaxterPoset`: 2-site `SU(2)` RTT intertwining relation. -/
theorem su2_twoSite_rtt_from_poset (u v : ℂ) :
    AuxMat4.mul
        (AuxMat4.mul (AuxMat4.R_ab (u - v) Complex.I)
          (AuxMat4.gaugedLax_ar u Complex.I Mat2.one))
        (AuxMat4.gaugedLax_br v Complex.I Mat2.one) =
      AuxMat4.mul
        (AuxMat4.mul (AuxMat4.gaugedLax_br v Complex.I Mat2.one)
          (AuxMat4.gaugedLax_ar u Complex.I Mat2.one))
        (AuxMat4.R_ab (u - v) Complex.I) :=
  (AuxMat4.archetype_M2_M3_braid_rtt_intertwining_and_corner_activation
    u v 0 0 Complex.I 1 0 0 Mat2.one Mat2.one Mat2.one Mat2.one).1

/-- Reuse of `ConnesLottYangBaxterPoset`: 2-site `SU(2)` twisted transfer-matrix
commutativity `[τ(u), τ(v)] = 0`. -/
theorem su2_twoSite_twistedTransfer_comm (u v : ℂ) (ν : Fin 2 → ℂ) (K : Mat2 ℂ) :
    Mat4.comm
        (AuxMat4.trAux K (AuxMat4.bareMonodromy u (ν 0) (ν 1) Complex.I))
        (AuxMat4.trAux K (AuxMat4.bareMonodromy v (ν 0) (ν 1) Complex.I)) =
      Mat4.zero :=
  AuxMat4.bare_two_factor_trace_comm u v (ν 0) (ν 1) Complex.I K

end SU2PosetReuse

/-! #### 5A. General `SU(N)` (`N = r + 1`) Rational Yang `R`-Matrix & 3-Space YBE -/

private lemma ybe_scalar_1 (u v : ℂ) : (u - v) * u * v = v * u * (u - v) := by ring
private lemma ybe_scalar_12 (u v η : ℂ) : η * u * v = v * u * η := by ring
private lemma ybe_scalar_13 (u v η : ℂ) : (u - v) * η * v + η ^ 3 = v * η * (u - v) + η ^ 3 := by
  ring
private lemma ybe_scalar_23 (u v η : ℂ) : (u - v) * u * η = η * u * (u - v) := by ring
private lemma ybe_scalar_cyc1 (u v η : ℂ) : (u - v) * η ^ 2 + η ^ 2 * v = η * u * η := by ring
private lemma ybe_scalar_cyc2 (u v η : ℂ) : η * u * η = v * η ^ 2 + η ^ 2 * (u - v) := by ring
private lemma inv_scalar_id (u η : ℂ) : u * u - η * η = u ^ 2 - η ^ 2 := by ring
private lemma inv_scalar_cross (u η : ℂ) : η * u - u * η = 0 := by ring

/-- Permutation swap operator on `Fin N × Fin N`. -/
def swapOp (N : ℕ) : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ :=
  Equiv.Perm.permMatrix ℂ (Equiv.prodComm (Fin N) (Fin N))

/-- General `SU(N)` rational Yang `R`-matrix `R(u) = u I + η P`. -/
def yangRMatrix (N : ℕ) (u η : ℂ) : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ :=
  u • (1 : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) + η • swapOp N

/-- Inversion identity `(u I + η P)(u I - η P) = (u² - η²) I`. -/
theorem yangRMatrix_inversion (N : ℕ) (u η : ℂ) :
    yangRMatrix N u η * (u • (1 : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) - η • swapOp N) =
      (u ^ 2 - η ^ 2) • (1 : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) := by
  have hP2 : swapOp N * swapOp N = 1 := by
    dsimp [swapOp]
    rw [← Matrix.permMatrix_mul]
    have hinv : (Equiv.prodComm (Fin N) (Fin N)) * (Equiv.prodComm (Fin N) (Fin N)) = 1 := by
      ext ⟨a, b⟩ <;> rfl
    rw [hinv, Matrix.permMatrix_one]
  dsimp [yangRMatrix]
  rw [add_mul, mul_sub, sub_eq_add_neg, mul_sub, smul_mul_smul_comm, smul_mul_smul_comm,
    smul_mul_smul_comm, smul_mul_smul_comm, one_mul, mul_one, one_mul, hP2]
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- `T16` non-commutativity witness for `Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ` when `2 ≤ N`. -/
theorem yangSpace2_noncommutative (N : ℕ) (hN : 2 ≤ N) :
    ∃ A B : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ, A * B ≠ B * A := by
  have h0lt : 0 < N := lt_of_lt_of_le (by decide) hN
  have h1lt : 1 < N := lt_of_lt_of_le (by decide) hN
  let i0 : Fin N × Fin N := (⟨0, h0lt⟩, ⟨0, h0lt⟩)
  let i1 : Fin N × Fin N := (⟨0, h0lt⟩, ⟨1, h1lt⟩)
  let A : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ := Matrix.single i0 i1 1
  let B : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ := Matrix.single i1 i0 1
  refine ⟨A, B, ?_⟩
  intro h
  have h00 : (A * B) i0 i0 = (B * A) i0 i0 := by rw [h]
  have hi01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  simp [A, B, Matrix.mul_apply, Matrix.single_apply, hi01.symm] at h00

private def swap12Equiv (N : ℕ) : Equiv.Perm (Fin N × Fin N × Fin N) where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun x := (x.2.1, (x.1, x.2.2))
  left_inv x := by rcases x with ⟨a, ⟨b, c⟩⟩; rfl
  right_inv x := by rcases x with ⟨a, ⟨b, c⟩⟩; rfl

private def swap23Equiv (N : ℕ) : Equiv.Perm (Fin N × Fin N × Fin N) where
  toFun x := (x.1, (x.2.2, x.2.1))
  invFun x := (x.1, (x.2.2, x.2.1))
  left_inv x := by rcases x with ⟨a, ⟨b, c⟩⟩; rfl
  right_inv x := by rcases x with ⟨a, ⟨b, c⟩⟩; rfl

private def swap13Equiv (N : ℕ) : Equiv.Perm (Fin N × Fin N × Fin N) where
  toFun x := (x.2.2, (x.2.1, x.1))
  invFun x := (x.2.2, (x.2.1, x.1))
  left_inv x := by rcases x with ⟨a, ⟨b, c⟩⟩; rfl
  right_inv x := by rcases x with ⟨a, ⟨b, c⟩⟩; rfl

def P12 (N : ℕ) : Matrix (Fin N × Fin N × Fin N) (Fin N × Fin N × Fin N) ℂ :=
  (swap12Equiv N).permMatrix ℂ

def P23 (N : ℕ) : Matrix (Fin N × Fin N × Fin N) (Fin N × Fin N × Fin N) ℂ :=
  (swap23Equiv N).permMatrix ℂ

def P13 (N : ℕ) : Matrix (Fin N × Fin N × Fin N) (Fin N × Fin N × Fin N) ℂ :=
  (swap13Equiv N).permMatrix ℂ

def R12 (N : ℕ) (u η : ℂ) : Matrix (Fin N × Fin N × Fin N) (Fin N × Fin N × Fin N) ℂ :=
  u • 1 + η • P12 N

def R13 (N : ℕ) (u η : ℂ) : Matrix (Fin N × Fin N × Fin N) (Fin N × Fin N × Fin N) ℂ :=
  u • 1 + η • P13 N

def R23 (N : ℕ) (u η : ℂ) : Matrix (Fin N × Fin N × Fin N) (Fin N × Fin N × Fin N) ℂ :=
  u • 1 + η • P23 N

private lemma P12_mul_P13_eq_P23_mul_P12 (N : ℕ) : P12 N * P13 N = P23 N * P12 N := by
  dsimp [P12, P13, P23]
  rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul]
  congr 1

private lemma P13_mul_P23_eq_P23_mul_P12 (N : ℕ) : P13 N * P23 N = P23 N * P12 N := by
  dsimp [P13, P23, P12]
  rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul]
  congr 1

private lemma P12_mul_P23_eq_P13_mul_P12 (N : ℕ) : P12 N * P23 N = P13 N * P12 N := by
  dsimp [P12, P23, P13]
  rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul]
  congr 1

private lemma P23_mul_P13_eq_P13_mul_P12 (N : ℕ) : P23 N * P13 N = P13 N * P12 N := by
  dsimp [P23, P13, P12]
  rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul]
  congr 1

private lemma P12_mul_P13_mul_P23_eq_P13 (N : ℕ) : P12 N * P13 N * P23 N = P13 N := by
  dsimp [P12, P13, P23]
  rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul]
  congr 1

private lemma P23_mul_P13_mul_P12_eq_P13 (N : ℕ) : P23 N * P13 N * P12 N = P13 N := by
  dsimp [P23, P13, P12]
  rw [← Matrix.permMatrix_mul, ← Matrix.permMatrix_mul]
  congr 1

/-- 3-space spectral Yang–Baxter equation for `yangRMatrix` in every dimension `N : ℕ`. -/
theorem yangRMatrix_ybe (N : ℕ) (u v η : ℂ) :
    R12 N (u - v) η * R13 N u η * R23 N v η =
      R23 N v η * R13 N u η * R12 N (u - v) η := by
  dsimp [R12, R13, R23]
  simp only [add_mul, mul_add, one_mul, mul_one, mul_smul_comm, smul_mul_assoc]
  rw [P12_mul_P13_mul_P23_eq_P13, P23_mul_P13_mul_P12_eq_P13,
      P13_mul_P23_eq_P23_mul_P12, P12_mul_P13_eq_P23_mul_P12,
      P12_mul_P23_eq_P13_mul_P12, P23_mul_P13_eq_P13_mul_P12]
  ext ⟨a, b, c⟩ ⟨d, e, f⟩
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- `T16` non-commutativity witness for `Matrix (Fin N × Fin N × Fin N) (Fin N × Fin N × Fin N) ℂ` when `2 ≤ N`. -/
theorem yangSpace3_noncommutative (N : ℕ) (hN : 2 ≤ N) :
    ∃ A B : Matrix (Fin N × Fin N × Fin N) (Fin N × Fin N × Fin N) ℂ, A * B ≠ B * A := by
  have h0lt : 0 < N := lt_of_lt_of_le (by decide) hN
  have h1lt : 1 < N := lt_of_lt_of_le (by decide) hN
  let i0 : Fin N × Fin N × Fin N := (⟨0, h0lt⟩, ⟨0, h0lt⟩, ⟨0, h0lt⟩)
  let i1 : Fin N × Fin N × Fin N := (⟨0, h0lt⟩, ⟨0, h0lt⟩, ⟨1, h1lt⟩)
  let A : Matrix (Fin N × Fin N × Fin N) (Fin N × Fin N × Fin N) ℂ := Matrix.single i0 i1 1
  let B : Matrix (Fin N × Fin N × Fin N) (Fin N × Fin N × Fin N) ℂ := Matrix.single i1 i0 1
  refine ⟨A, B, ?_⟩
  intro h
  have h00 : (A * B) i0 i0 = (B * A) i0 i0 := by rw [h]
  have hi01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  simp [A, B, Matrix.mul_apply, Matrix.single_apply, hi01.symm] at h00

/-! #### 5B. Genuine Non-Commutative `L`-Site Quantum Monodromy, RTT, and Twisted Transfer Matrix -/

/-- `L`-site `SU(N)` quantum operator ring `End((ℂ^N)^{⊗ L})`. -/
abbrev QuantumOp (L N : ℕ) : Type := Matrix (Fin L → Fin N) (Fin L → Fin N) ℂ

/-- Local Weyl matrix unit `E_{b, a}^{(α)}` acting at site `α` and as the identity elsewhere. -/
def siteE {L N : ℕ} (α : Fin L) (b a : Fin N) : QuantumOp L N :=
  Matrix.of fun x y =>
    if x α = b ∧ y α = a ∧ ∀ β : Fin L, β ≠ α → x β = y β then 1 else 0

/-- Site Weyl units at distinct sites commute. -/
theorem siteE_comm_ne {L N : ℕ} {α β : Fin L} (hne : α ≠ β) (b a d c : Fin N) :
    siteE (L := L) (N := N) α b a * siteE β d c = siteE β d c * siteE α b a := by
  ext x y
  simp only [Matrix.mul_apply, siteE, Matrix.of_apply]
  let P : Prop :=
    x α = b ∧ y α = a ∧ x β = d ∧ y β = c ∧ ∀ γ : Fin L, γ ≠ α → γ ≠ β → x γ = y γ
  have hLHS :
      (∑ z : Fin L → Fin N,
        (if x α = b ∧ z α = a ∧ ∀ γ, γ ≠ α → x γ = z γ then (1 : ℂ) else 0) *
        (if z β = d ∧ y β = c ∧ ∀ γ, γ ≠ β → z γ = y γ then 1 else 0)) =
      if P then 1 else 0 := by
    let z0 : Fin L → Fin N := Function.update x α a
    rw [Finset.sum_eq_single z0]
    · by_cases hP : P
      · rcases hP with ⟨hxα, hyα, hxβ, hyβ, hrest⟩
        have h1 : x α = b ∧ z0 α = a ∧ ∀ γ, γ ≠ α → x γ = z0 γ :=
          ⟨hxα, by simp [z0], fun γ hγα => by simp [z0, Function.update_of_ne hγα]⟩
        have h2 : z0 β = d ∧ y β = c ∧ ∀ γ, γ ≠ β → z0 γ = y γ := by
          refine ⟨by simpa [z0, Function.update_of_ne hne.symm] using hxβ, hyβ, fun γ hγβ => ?_⟩
          by_cases hγα : γ = α
          · subst hγα; simp [z0, hyα]
          · simp [z0, Function.update_of_ne hγα, hrest γ hγα hγβ]
        rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h2),
          ite_eq_left_of_eq_true _ _ (eq_true ⟨hxα, hyα, hxβ, hyβ, hrest⟩), mul_one]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hP)]
        by_contra hnz
        have hmul := mul_ne_zero_iff.mp hnz
        split_ifs at hmul with h1 h2
        · apply hP
          rcases h1 with ⟨hxα, _, _⟩
          rcases h2 with ⟨hz0β, hyβ, h2rest⟩
          have hxβ : x β = d := by simpa [z0, Function.update_of_ne hne.symm] using hz0β
          have hyα : y α = a := by simpa [z0] using (h2rest α hne).symm
          refine ⟨hxα, hyα, hxβ, hyβ, fun γ hγα hγβ => ?_⟩
          simpa [z0, Function.update_of_ne hγα] using h2rest γ hγβ
        · simp at hmul
        · simp at hmul
        · simp at hmul
    · intro z _ hz
      by_contra hnz
      have hmul := mul_ne_zero_iff.mp hnz
      split_ifs at hmul with h1 h2
      · apply hz
        ext γ
        by_cases hγα : γ = α
        · subst hγα; simp [z0, h1.2.1]
        · simp [z0, Function.update_of_ne hγα, (h1.2.2 γ hγα).symm]
      · simp at hmul
      · simp at hmul
      · simp at hmul
    · intro hmem; exact absurd (Finset.mem_univ z0) hmem
  have hRHS :
      (∑ z : Fin L → Fin N,
        (if x β = d ∧ z β = c ∧ ∀ γ, γ ≠ β → x γ = z γ then (1 : ℂ) else 0) *
        (if z α = b ∧ y α = a ∧ ∀ γ, γ ≠ α → z γ = y γ then 1 else 0)) =
      if P then 1 else 0 := by
    let z1 : Fin L → Fin N := Function.update x β c
    rw [Finset.sum_eq_single z1]
    · by_cases hP : P
      · rcases hP with ⟨hxα, hyα, hxβ, hyβ, hrest⟩
        have h1 : x β = d ∧ z1 β = c ∧ ∀ γ, γ ≠ β → x γ = z1 γ :=
          ⟨hxβ, by simp [z1], fun γ hγβ => by simp [z1, Function.update_of_ne hγβ]⟩
        have h2 : z1 α = b ∧ y α = a ∧ ∀ γ, γ ≠ α → z1 γ = y γ := by
          refine ⟨by simpa [z1, Function.update_of_ne hne] using hxα, hyα, fun γ hγα => ?_⟩
          by_cases hγβ : γ = β
          · subst hγβ; simp [z1, hyβ]
          · simp [z1, Function.update_of_ne hγβ, hrest γ hγα hγβ]
        rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h2),
          ite_eq_left_of_eq_true _ _ (eq_true ⟨hxα, hyα, hxβ, hyβ, hrest⟩), mul_one]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hP)]
        by_contra hnz
        have hmul := mul_ne_zero_iff.mp hnz
        split_ifs at hmul with h1 h2
        · apply hP
          rcases h1 with ⟨hxβ, _, _⟩
          rcases h2 with ⟨hz1α, hyα, h2rest⟩
          have hxα : x α = b := by simpa [z1, Function.update_of_ne hne] using hz1α
          have hyβ : y β = c := by simpa [z1] using (h2rest β hne.symm).symm
          refine ⟨hxα, hyα, hxβ, hyβ, fun γ hγα hγβ => ?_⟩
          simpa [z1, Function.update_of_ne hγβ] using h2rest γ hγα
        · simp at hmul
        · simp at hmul
        · simp at hmul
    · intro z _ hz
      by_contra hnz
      have hmul := mul_ne_zero_iff.mp hnz
      split_ifs at hmul with h1 h2
      · apply hz
        ext γ
        by_cases hγβ : γ = β
        · subst hγβ; simp [z1, h1.2.1]
        · simp [z1, Function.update_of_ne hγβ, (h1.2.2 γ hγβ).symm]
      · simp at hmul
      · simp at hmul
      · simp at hmul
    · intro hmem; exact absurd (Finset.mem_univ z1) hmem
  rw [hLHS, hRHS]

/-- Same-site Weyl unit multiplication: `E_{b,a}^{(α)} E_{d,c}^{(α)} = δ_{a,d} E_{b,c}^{(α)}`. -/
theorem siteE_mul_same {L N : ℕ} (α : Fin L) (b a d c : Fin N) :
    siteE (L := L) (N := N) α b a * siteE α d c = if a = d then siteE α b c else 0 := by
  ext x y
  simp only [Matrix.mul_apply, siteE, Matrix.of_apply]
  let z0 : Fin L → Fin N := Function.update x α a
  rw [Finset.sum_eq_single z0]
  · by_cases had : a = d
    · subst had
      by_cases hcond : x α = b ∧ y α = c ∧ ∀ γ : Fin L, γ ≠ α → x γ = y γ
      · rcases hcond with ⟨hxα, hyα, hrest⟩
        have h1 : x α = b ∧ z0 α = a ∧ ∀ γ, γ ≠ α → x γ = z0 γ :=
          ⟨hxα, by simp [z0], fun γ hγα => by simp [z0, Function.update_of_ne hγα]⟩
        have h2 : z0 α = a ∧ y α = c ∧ ∀ γ, γ ≠ α → z0 γ = y γ :=
          ⟨by simp [z0], hyα, fun γ hγα => by simp [z0, Function.update_of_ne hγα, hrest γ hγα]⟩
        rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h2),
          ite_eq_left_of_eq_true _ _ (eq_true rfl), Matrix.of_apply,
          ite_eq_left_of_eq_true _ _ (eq_true ⟨hxα, hyα, hrest⟩), mul_one]
      · simp only [↓reduceIte, Matrix.of_apply]
        rw [ite_eq_right_of_eq_false _ _ (eq_false hcond)]
        by_contra hnz
        have hmul := mul_ne_zero_iff.mp hnz
        split_ifs at hmul with h1 h2
        · apply hcond
          refine ⟨h1.1, h2.2.1, fun γ hγα => ?_⟩
          have := h2.2.2 γ hγα
          simpa [z0, Function.update_of_ne hγα] using this
        · simp at hmul
        · simp at hmul
        · simp at hmul
    · rw [ite_eq_right_of_eq_false _ _ (eq_false had), Matrix.zero_apply]
      by_contra hnz
      have hmul := mul_ne_zero_iff.mp hnz
      split_ifs at hmul with h1 h2
      · apply had
        have hz0 : z0 α = a := by simp [z0]
        rw [← hz0, h2.1]
      · simp at hmul
      · simp at hmul
      · simp at hmul
  · intro z _ hz
    by_contra hnz
    have hmul := mul_ne_zero_iff.mp hnz
    split_ifs at hmul with h1 h2
    · apply hz
      ext γ
      by_cases hγα : γ = α
      · subst hγα; simp [z0, h1.2.1]
      · simp [z0, Function.update_of_ne hγα, (h1.2.2 γ hγα).symm]
    · simp at hmul
    · simp at hmul
    · simp at hmul
  · intro hmem; exact absurd (Finset.mem_univ z0) hmem

/-- `T16` non-commutativity witness for `siteE` (and `QuantumOp L N`). -/
theorem siteE_noncommutative (r L : ℕ) (hr : 1 ≤ r) (hL : 0 < L) :
    let α : Fin L := ⟨0, hL⟩
    let e10 : QuantumOp L (r + 1) := siteE α ⟨1, Nat.lt_succ_of_le hr⟩ ⟨0, Nat.zero_lt_succ r⟩
    let e01 : QuantumOp L (r + 1) := siteE α ⟨0, Nat.zero_lt_succ r⟩ ⟨1, Nat.lt_succ_of_le hr⟩
    e10 * e01 ≠ e01 * e10 := by
  intro α e10 e01 h
  have hmul1 : e10 * e01 = siteE α ⟨1, Nat.lt_succ_of_le hr⟩ ⟨1, Nat.lt_succ_of_le hr⟩ := by
    dsimp [e10, e01]
    rw [siteE_mul_same]
    simp
  have hmul2 : e01 * e10 = siteE α ⟨0, Nat.zero_lt_succ r⟩ ⟨0, Nat.zero_lt_succ r⟩ := by
    dsimp [e10, e01]
    rw [siteE_mul_same]
    simp
  rw [hmul1, hmul2] at h
  let x : Fin L → Fin (r + 1) := fun _ => ⟨0, Nat.zero_lt_succ r⟩
  have hx := congr_fun (congr_fun h x) x
  have hL_zero : siteE α ⟨1, Nat.lt_succ_of_le hr⟩ ⟨1, Nat.lt_succ_of_le hr⟩ x x = 0 := by
    simp only [siteE, Matrix.of_apply, x]
    exact if_neg fun hcond => by
      have : (0 : ℕ) = 1 := congrArg Fin.val hcond.1
      omega
  have hR_one : siteE α ⟨0, Nat.zero_lt_succ r⟩ ⟨0, Nat.zero_lt_succ r⟩ x x = 1 := by
    dsimp [siteE, Matrix.of_apply, x]
    rw [if_pos ⟨rfl, rfl, fun _ _ => rfl⟩]
  rw [hL_zero, hR_one] at hx
  exact zero_ne_one hx

/-- `T16` existential non-commutativity witness on `QuantumOp L N` for `2 ≤ N, 1 ≤ L`. -/
theorem quantumOp_noncommutative (L N : ℕ) (hL : 0 < L) (hN : 2 ≤ N) :
    ∃ A B : QuantumOp L N, A * B ≠ B * A := by
  have h0lt : 0 < N := lt_of_lt_of_le (by decide) hN
  have h1lt : 1 < N := lt_of_lt_of_le (by decide) hN
  let α : Fin L := ⟨0, hL⟩
  let A : QuantumOp L N := siteE α ⟨1, h1lt⟩ ⟨0, h0lt⟩
  let B : QuantumOp L N := siteE α ⟨0, h0lt⟩ ⟨1, h1lt⟩
  refine ⟨A, B, ?_⟩
  intro h
  have h1 : A * B = siteE α ⟨1, h1lt⟩ ⟨1, h1lt⟩ := by
    dsimp [A, B]; rw [siteE_mul_same]; simp
  have h2 : B * A = siteE α ⟨0, h0lt⟩ ⟨0, h0lt⟩ := by
    dsimp [A, B]; rw [siteE_mul_same]; simp
  rw [h1, h2] at h
  let x : Fin L → Fin N := fun _ => ⟨0, h0lt⟩
  have hx := congr_fun (congr_fun h x) x
  dsimp [siteE, Matrix.of_apply, x] at hx
  simp only [Fin.ext_iff] at hx
  have hx' : (if (1 : ℕ) = 0 ∧ (fun _ : Fin L => (0 : ℕ)) = fun _ => 0 then (1 : ℂ) else 0) =
      if (0 : ℕ) = 0 ∧ (fun _ : Fin L => (0 : ℕ)) = fun _ => 0 then 1 else 0 := by
    simpa using hx
  simp at hx'

/-- `T16` existential non-commutativity witness on `Matrix (Fin N) (Fin N) (QuantumOp L N)` for `2 ≤ N`. -/
theorem auxQuantumMatrix_noncommutative (L N : ℕ) (hN : 2 ≤ N) :
    ∃ A B : Matrix (Fin N) (Fin N) (QuantumOp L N), A * B ≠ B * A := by
  have h0lt : 0 < N := lt_of_lt_of_le (by decide) hN
  have h1lt : 1 < N := lt_of_lt_of_le (by decide) hN
  let A : Matrix (Fin N) (Fin N) (QuantumOp L N) := Matrix.single ⟨0, h0lt⟩ ⟨1, h1lt⟩ 1
  let B : Matrix (Fin N) (Fin N) (QuantumOp L N) := Matrix.single ⟨1, h1lt⟩ ⟨0, h0lt⟩ 1
  refine ⟨A, B, ?_⟩
  intro h
  have h00 : (A * B) ⟨0, h0lt⟩ ⟨0, h0lt⟩ = (B * A) ⟨0, h0lt⟩ ⟨0, h0lt⟩ := by rw [h]
  have h01 : (⟨0, h0lt⟩ : Fin N) ≠ ⟨1, h1lt⟩ := by simp [Fin.ext_iff]
  simp [A, B, Matrix.mul_apply, Matrix.single_apply, h01.symm] at h00
  have hcon := congr_fun (congr_fun h00 (fun _ => ⟨0, h0lt⟩)) (fun _ => ⟨0, h0lt⟩)
  simp at hcon

/-- `T16` existential non-commutativity witness on `Matrix (Fin N × Fin N) (Fin N × Fin N) (QuantumOp L N)` for `2 ≤ N`. -/
theorem aux2QuantumMatrix_noncommutative (L N : ℕ) (hN : 2 ≤ N) :
    ∃ A B : Matrix (Fin N × Fin N) (Fin N × Fin N) (QuantumOp L N), A * B ≠ B * A := by
  have h0lt : 0 < N := lt_of_lt_of_le (by decide) hN
  have h1lt : 1 < N := lt_of_lt_of_le (by decide) hN
  let i0 : Fin N × Fin N := (⟨0, h0lt⟩, ⟨0, h0lt⟩)
  let i1 : Fin N × Fin N := (⟨0, h0lt⟩, ⟨1, h1lt⟩)
  let A : Matrix (Fin N × Fin N) (Fin N × Fin N) (QuantumOp L N) := Matrix.single i0 i1 1
  let B : Matrix (Fin N × Fin N) (Fin N × Fin N) (QuantumOp L N) := Matrix.single i1 i0 1
  refine ⟨A, B, ?_⟩
  intro h
  have h00 : (A * B) i0 i0 = (B * A) i0 i0 := by rw [h]
  have hi01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  simp [A, B, Matrix.mul_apply, Matrix.single_apply, hi01.symm] at h00
  have hcon := congr_fun (congr_fun h00 (fun _ => ⟨0, h0lt⟩)) (fun _ => ⟨0, h0lt⟩)
  simp at hcon

/-- 1-site rational Lax operator at site `α`:
`(L_α(u))_{a,b} = δ_{a,b} (u - ν) • 1 + η • E_{b,a}^{(α)}`. -/
def siteLax (L N : ℕ) (α : Fin L) (ν u η : ℂ) : Matrix (Fin N) (Fin N) (QuantumOp L N) :=
  Matrix.of fun a b => (if a = b then (u - ν) • (1 : QuantumOp L N) else 0) + η • siteE α b a

/-- `L`-site monodromy matrix `T(u) = L_0(u) L_1(u) ⋯ L_{L-1}(u)`. -/
def xxxMonodromy (L N : ℕ) (ν : Fin L → ℂ) (u η : ℂ) : Matrix (Fin N) (Fin N) (QuantumOp L N) :=
  (List.finRange L).foldl (fun acc α => acc * siteLax L N α (ν α) u η) 1

/-- Embed an auxiliary matrix `A` into the first factor of `V_1 ⊗ V_2`. -/
def auxEmbed1 {L N : ℕ} (A : Matrix (Fin N) (Fin N) (QuantumOp L N)) :
    Matrix (Fin N × Fin N) (Fin N × Fin N) (QuantumOp L N) :=
  Matrix.of fun p q => if p.2 = q.2 then A p.1 q.1 else 0

/-- Embed an auxiliary matrix `B` into the second factor of `V_1 ⊗ V_2`. -/
def auxEmbed2 {L N : ℕ} (B : Matrix (Fin N) (Fin N) (QuantumOp L N)) :
    Matrix (Fin N × Fin N) (Fin N × Fin N) (QuantumOp L N) :=
  Matrix.of fun p q => if p.1 = q.1 then B p.2 q.2 else 0

/-- Lift the scalar Yang `R`-matrix into `Matrix (Fin N × Fin N) (Fin N × Fin N) (QuantumOp L N)`. -/
def liftR (N L : ℕ) (w η : ℂ) : Matrix (Fin N × Fin N) (Fin N × Fin N) (QuantumOp L N) :=
  (yangRMatrix N w η).map (algebraMap ℂ (QuantumOp L N))

private lemma auxEmbed1_mul {L N : ℕ} (A B : Matrix (Fin N) (Fin N) (QuantumOp L N)) :
    auxEmbed1 (A * B) = auxEmbed1 A * auxEmbed1 B := by
  ext ⟨i', j'⟩ ⟨i, j⟩
  simp only [auxEmbed1, Matrix.of_apply, Matrix.mul_apply]
  have hsum :
      (∑ x : Fin N × Fin N, (if j' = x.2 then A i' x.1 else 0) * (if x.2 = j then B x.1 i else 0)) =
        ∑ k : Fin N, (if j' = j then A i' k * B k i else 0) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single j']
    · by_cases hjj : j' = j <;> simp [hjj]
    · intro l _ hl; simp [hl.symm]
    · intro hmem; exact absurd (Finset.mem_univ j') hmem
  rw [hsum]
  by_cases hjj : j' = j <;> simp [hjj]

private lemma auxEmbed2_mul {L N : ℕ} (A B : Matrix (Fin N) (Fin N) (QuantumOp L N)) :
    auxEmbed2 (A * B) = auxEmbed2 A * auxEmbed2 B := by
  ext ⟨i', j'⟩ ⟨i, j⟩
  simp only [auxEmbed2, Matrix.of_apply, Matrix.mul_apply]
  have hsum :
      (∑ x : Fin N × Fin N, (if i' = x.1 then A j' x.2 else 0) * (if x.1 = i then B x.2 j else 0)) =
        ∑ k : Fin N, (if i' = i then A j' k * B k j else 0) := by
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single i']
    · by_cases hii : i' = i <;> simp [hii]
    · intro l _ hl; simp [hl.symm]
    · intro hmem; exact absurd (Finset.mem_univ i') hmem
  rw [hsum]
  by_cases hii : i' = i <;> simp [hii]

private lemma auxEmbed1_mul_auxEmbed2 {L N : ℕ}
    (A B : Matrix (Fin N) (Fin N) (QuantumOp L N)) (i' j' i j : Fin N) :
    (auxEmbed1 A * auxEmbed2 B) (i', j') (i, j) = A i' i * B j' j := by
  simp only [auxEmbed1, auxEmbed2, Matrix.mul_apply, Matrix.of_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j']
    · simp
    · intro l _ hl; simp [hl.symm]
    · intro hmem; exact absurd (Finset.mem_univ j') hmem
  · intro k _ hk
    refine Finset.sum_eq_zero fun l _ => ?_
    simp [hk]
  · intro hmem; exact absurd (Finset.mem_univ i) hmem

private lemma auxEmbed2_mul_auxEmbed1 {L N : ℕ}
    (A B : Matrix (Fin N) (Fin N) (QuantumOp L N)) (i' j' i j : Fin N) :
    (auxEmbed2 B * auxEmbed1 A) (i', j') (i, j) = B j' j * A i' i := by
  simp only [auxEmbed1, auxEmbed2, Matrix.mul_apply, Matrix.of_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i']
  · rw [Finset.sum_eq_single j]
    · simp
    · intro l _ hl; simp [hl]
    · intro hmem; exact absurd (Finset.mem_univ j) hmem
  · intro k _ hk
    refine Finset.sum_eq_zero fun l _ => ?_
    simp [hk.symm]
  · intro hmem; exact absurd (Finset.mem_univ i') hmem

private lemma liftR_apply {N L : ℕ} (w η : ℂ) (p q : Fin N × Fin N) :
    liftR N L w η p q =
      (if p = q then w • (1 : QuantumOp L N) else 0) +
        (if p = (q.2, q.1) then η • (1 : QuantumOp L N) else 0) := by
  simp only [liftR, Matrix.map_apply, yangRMatrix, swapOp, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
    Option.mem_def, Option.some.injEq, map_add, Algebra.algebraMap_eq_smul_one, smul_eq_mul,
    Equiv.prodComm_apply]
  have hcomm : (p.2, p.1) = q ↔ p = (q.2, q.1) := by
    rcases p with ⟨p1, p2⟩
    rcases q with ⟨q1, q2⟩
    simp [Prod.ext_iff, eq_comm, and_comm]
  change (w * if p = q then 1 else 0) • 1 + (η * if (p.2, p.1) = q then 1 else 0) • 1 = _
  simp only [hcomm]
  split_ifs <;> simp

private lemma liftR_mul_apply {N L : ℕ} (w η : ℂ)
    (M : Matrix (Fin N × Fin N) (Fin N × Fin N) (QuantumOp L N)) (i' j' i j : Fin N) :
    (liftR N L w η * M) (i', j') (i, j) =
      w • M (i', j') (i, j) + η • M (j', i') (i, j) := by
  rw [Matrix.mul_apply]
  simp_rw [liftR_apply, add_mul]
  rw [Finset.sum_add_distrib]
  have h1 :
      (∑ x : Fin N × Fin N,
        (if (i', j') = x then w • (1 : QuantumOp L N) else 0) * M x (i, j)) =
      w • M (i', j') (i, j) := by
    rw [Finset.sum_eq_single (i', j')]
    · simp
    · intro x _ hx; simp [hx.symm]
    · intro hmem; exact absurd (Finset.mem_univ (i', j')) hmem
  have h2 :
      (∑ x : Fin N × Fin N,
        (if (i', j') = (x.2, x.1) then η • (1 : QuantumOp L N) else 0) * M x (i, j)) =
      η • M (j', i') (i, j) := by
    rw [Finset.sum_eq_single (j', i')]
    · simp
    · intro x _ hx
      have hne : (i', j') ≠ (x.2, x.1) := by
        intro heq; apply hx
        exact Prod.ext (congrArg Prod.snd heq).symm (congrArg Prod.fst heq).symm
      simp [hne]
    · intro hmem; exact absurd (Finset.mem_univ (j', i')) hmem
  rw [h1, h2]

private lemma mul_liftR_apply {N L : ℕ} (w η : ℂ)
    (M : Matrix (Fin N × Fin N) (Fin N × Fin N) (QuantumOp L N)) (i' j' i j : Fin N) :
    (M * liftR N L w η) (i', j') (i, j) =
      w • M (i', j') (i, j) + η • M (i', j') (j, i) := by
  rw [Matrix.mul_apply]
  simp_rw [liftR_apply, mul_add]
  rw [Finset.sum_add_distrib]
  have h1 :
      (∑ x : Fin N × Fin N,
        M (i', j') x * (if x = (i, j) then w • (1 : QuantumOp L N) else 0)) =
      w • M (i', j') (i, j) := by
    rw [Finset.sum_eq_single (i, j)]
    · simp
    · intro x _ hx; simp [hx]
    · intro hmem; exact absurd (Finset.mem_univ (i, j)) hmem
  have h2 :
      (∑ x : Fin N × Fin N,
        M (i', j') x * (if x = (j, i) then η • (1 : QuantumOp L N) else 0)) =
      η • M (i', j') (j, i) := by
    rw [Finset.sum_eq_single (j, i)]
    · simp
    · intro x _ hx; simp [hx]
    · intro hmem; exact absurd (Finset.mem_univ (j, i)) hmem
  rw [h1, h2]

private lemma siteLax_rtt_coeff_1 (u' v' η dii djj dji dij : ℂ) :
    (u' - v') * ((u' * dii) * (v' * djj)) + η * ((u' * dji) * (v' * dij)) =
      (u' - v') * ((v' * djj) * (u' * dii)) + η * ((v' * dji) * (u' * dij)) := by ring

private lemma siteLax_rtt_coeff_Eii' (u' v' η d1 : ℂ) :
    (u' - v') * (η * (v' * d1)) + η * (η * (η * d1)) =
      (u' - v') * ((v' * d1) * η) + η * (η * (η * d1)) := by ring

private lemma siteLax_rtt_coeff_Ejj' (u' v' η d1 : ℂ) :
    (u' - v') * ((u' * d1) * η) = (u' - v') * (η * (u' * d1)) := by ring

private lemma siteLax_rtt_coeff_Eij' (u' v' η d1 : ℂ) :
    (u' - v') * (η * (η * d1)) + η * (η * (v' * d1)) = η * (η * (u' * d1)) := by ring

private lemma siteLax_rtt_coeff_Eji' (u' v' η d1 : ℂ) :
    η * ((u' * d1) * η) = (u' - v') * (η * (η * d1)) + η * ((v' * d1) * η) := by ring

private lemma siteLax_entry_split {L N : ℕ} (α : Fin L) (ν u η : ℂ) (a b : Fin N) :
    siteLax L N α ν u η a b =
      ((u - ν) * (if a = b then (1 : ℂ) else 0)) • (1 : QuantumOp L N) + η • siteE α b a := by
  dsimp [siteLax]
  split_ifs with h
  · simp [h]
  · simp

/-- Single-site RTT intertwining relation for `siteLax`. -/
theorem siteLax_rtt (L N : ℕ) (α : Fin L) (ν u v η : ℂ) :
    liftR N L (u - v) η * auxEmbed1 (siteLax L N α ν u η) * auxEmbed2 (siteLax L N α ν v η) =
      auxEmbed2 (siteLax L N α ν v η) * auxEmbed1 (siteLax L N α ν u η) * liftR N L (u - v) η := by
  ext ⟨i', j'⟩ ⟨i, j⟩
  rw [Matrix.mul_assoc, liftR_mul_apply, mul_liftR_apply,
      auxEmbed1_mul_auxEmbed2, auxEmbed1_mul_auxEmbed2,
      auxEmbed2_mul_auxEmbed1, auxEmbed2_mul_auxEmbed1]
  simp_rw [siteLax_entry_split]
  set u' : ℂ := u - ν
  set v' : ℂ := v - ν
  have huv : u - v = u' - v' := by simp [u', v']
  rw [huv]
  set δii : ℂ := if i' = i then 1 else 0
  set δjj : ℂ := if j' = j then 1 else 0
  set δji : ℂ := if j' = i then 1 else 0
  set δij : ℂ := if i' = j then 1 else 0
  have h1 :
      (u' - v') • (((u' * δii) • (1 : QuantumOp L N) + η • siteE α i i') *
          ((v' * δjj) • (1 : QuantumOp L N) + η • siteE α j j')) +
        η • (((u' * δji) • (1 : QuantumOp L N) + η • siteE α i j') *
          ((v' * δij) • (1 : QuantumOp L N) + η • siteE α j i')) =
      ((u' - v') * ((u' * δii) * (v' * δjj)) + η * ((u' * δji) * (v' * δij))) •
          (1 : QuantumOp L N) +
        ((u' - v') * (η * (v' * δjj)) + η * (η * (η * δjj))) • siteE α i i' +
        ((u' - v') * ((u' * δii) * η)) • siteE α j j' +
        ((u' - v') * (η * (η * δij)) + η * (η * (v' * δij))) • siteE α i j' +
        (η * ((u' * δji) * η)) • siteE α j i' := by
    simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, siteE_mul_same,
      smul_add, smul_smul]
    have hEij : (if i' = j then siteE (L := L) (N := N) α i j' else 0) = δij • siteE α i j' := by
      dsimp [δij]; split_ifs <;> simp
    have hEii : (if j' = j then siteE (L := L) (N := N) α i i' else 0) = δjj • siteE α i i' := by
      dsimp [δjj]; split_ifs <;> simp
    rw [hEij, hEii, smul_smul, smul_smul]
    simp only [add_smul, mul_assoc]
    abel
  have h2 :
      (u' - v') • (((v' * δjj) • (1 : QuantumOp L N) + η • siteE α j j') *
          ((u' * δii) • (1 : QuantumOp L N) + η • siteE α i i')) +
        η • (((v' * δji) • (1 : QuantumOp L N) + η • siteE α i j') *
          ((u' * δij) • (1 : QuantumOp L N) + η • siteE α j i')) =
      ((u' - v') * ((v' * δjj) * (u' * δii)) + η * ((v' * δji) * (u' * δij))) •
          (1 : QuantumOp L N) +
        ((u' - v') * ((v' * δjj) * η) + η * (η * (η * δjj))) • siteE α i i' +
        ((u' - v') * (η * (u' * δii))) • siteE α j j' +
        (η * (η * (u' * δij))) • siteE α i j' +
        ((u' - v') * (η * (η * δji)) + η * ((v' * δji) * η)) • siteE α j i' := by
    simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, siteE_mul_same,
      smul_add, smul_smul]
    have hEji : (if j' = i then siteE (L := L) (N := N) α j i' else 0) = δji • siteE α j i' := by
      dsimp [δji]; split_ifs <;> simp
    have hEii : (if j' = j then siteE (L := L) (N := N) α i i' else 0) = δjj • siteE α i i' := by
      dsimp [δjj]; split_ifs <;> simp
    rw [hEji, hEii, smul_smul, smul_smul]
    simp only [add_smul, mul_assoc]
    abel
  rw [h1, h2,
      siteLax_rtt_coeff_1 u' v' η δii δjj δji δij,
      siteLax_rtt_coeff_Eii' u' v' η δjj,
      siteLax_rtt_coeff_Ejj' u' v' η δii,
      siteLax_rtt_coeff_Eij' u' v' η δij,
      siteLax_rtt_coeff_Eji' u' v' η δji]

private def CommutesWithSite {L N : ℕ} (α : Fin L) (q : QuantumOp L N) : Prop :=
  ∀ b a : Fin N, q * siteE (L := L) (N := N) α b a = siteE α b a * q

private lemma commutesWithSite_one {L N : ℕ} (α : Fin L) :
    CommutesWithSite α (1 : QuantumOp L N) := fun _ _ => by simp

private lemma commutesWithSite_smul {L N : ℕ} (α : Fin L) (c : ℂ) {q : QuantumOp L N}
    (hq : CommutesWithSite α q) : CommutesWithSite α (c • q) := by
  intro b a
  rw [smul_mul_assoc, hq b a, mul_smul_comm]

private lemma commutesWithSite_add {L N : ℕ} (α : Fin L) {q1 q2 : QuantumOp L N}
    (h1 : CommutesWithSite α q1) (h2 : CommutesWithSite α q2) :
    CommutesWithSite α (q1 + q2) := by
  intro b a
  rw [add_mul, mul_add, h1 b a, h2 b a]

private lemma commutesWithSite_mul {L N : ℕ} (α : Fin L) {q1 q2 : QuantumOp L N}
    (h1 : CommutesWithSite α q1) (h2 : CommutesWithSite α q2) :
    CommutesWithSite α (q1 * q2) := by
  intro b a
  rw [mul_assoc, h2 b a, ← mul_assoc, h1 b a, mul_assoc]

private lemma commutesWithSite_siteLax {L N : ℕ} {α β : Fin L} (hne : β ≠ α)
    (ν u η : ℂ) (i j : Fin N) :
    CommutesWithSite α (siteLax L N β ν u η i j) := by
  dsimp [siteLax]
  apply commutesWithSite_add
  · split_ifs
    · exact commutesWithSite_smul α _ (commutesWithSite_one α)
    · intro b a; simp
  · exact commutesWithSite_smul α η (fun b a => siteE_comm_ne hne j i b a)

private lemma commutesWith_siteLax_of_commutesWithSite {L N : ℕ} (α : Fin L)
    (q : QuantumOp L N) (hq : CommutesWithSite α q) (ν u η : ℂ) (i j : Fin N) :
    q * siteLax L N α ν u η i j = siteLax L N α ν u η i j * q := by
  dsimp [siteLax]
  rw [mul_add, add_mul]
  congr 1
  · split_ifs <;> simp [mul_smul_comm, smul_mul_assoc]
  · rw [mul_smul_comm, smul_mul_assoc, hq j i]

private lemma auxEmbed1_comm_auxEmbed2_of_entries {L N : ℕ}
    (A B : Matrix (Fin N) (Fin N) (QuantumOp L N))
    (hcomm : ∀ i j k l : Fin N, A i j * B k l = B k l * A i j) :
    auxEmbed1 A * auxEmbed2 B = auxEmbed2 B * auxEmbed1 A := by
  ext ⟨i', j'⟩ ⟨i, j⟩
  rw [auxEmbed1_mul_auxEmbed2, auxEmbed2_mul_auxEmbed1, hcomm]

private lemma listFoldl_rtt {L N : ℕ} (xs : List (Fin L)) (hnodup : xs.Nodup)
    (ν : Fin L → ℂ) (u v η : ℂ)
    (accU accV : Matrix (Fin N) (Fin N) (QuantumOp L N))
    (hrtt : liftR N L (u - v) η * auxEmbed1 accU * auxEmbed2 accV =
      auxEmbed2 accV * auxEmbed1 accU * liftR N L (u - v) η)
    (hcommU : ∀ γ ∈ xs, ∀ i j : Fin N, CommutesWithSite γ (accU i j))
    (hcommV : ∀ γ ∈ xs, ∀ i j : Fin N, CommutesWithSite γ (accV i j)) :
    liftR N L (u - v) η *
        auxEmbed1 (xs.foldl (fun acc α => acc * siteLax L N α (ν α) u η) accU) *
        auxEmbed2 (xs.foldl (fun acc α => acc * siteLax L N α (ν α) v η) accV) =
      auxEmbed2 (xs.foldl (fun acc α => acc * siteLax L N α (ν α) v η) accV) *
        auxEmbed1 (xs.foldl (fun acc α => acc * siteLax L N α (ν α) u η) accU) *
        liftR N L (u - v) η := by
  induction xs generalizing accU accV with
  | nil => exact hrtt
  | cons α xs' ih =>
    simp only [List.foldl_cons]
    have hnodup' : xs'.Nodup := (List.nodup_cons.mp hnodup).2
    have hnotmem : α ∉ xs' := (List.nodup_cons.mp hnodup).1
    have hrtt_step :
        liftR N L (u - v) η *
            auxEmbed1 (accU * siteLax L N α (ν α) u η) *
            auxEmbed2 (accV * siteLax L N α (ν α) v η) =
          auxEmbed2 (accV * siteLax L N α (ν α) v η) *
            auxEmbed1 (accU * siteLax L N α (ν α) u η) *
            liftR N L (u - v) η := by
      have hcomm1 :
          auxEmbed1 (siteLax L N α (ν α) u η) * auxEmbed2 accV =
            auxEmbed2 accV * auxEmbed1 (siteLax L N α (ν α) u η) :=
        auxEmbed1_comm_auxEmbed2_of_entries _ _ fun i j k l =>
          (commutesWith_siteLax_of_commutesWithSite α (accV k l)
            (hcommV α (List.mem_cons_self) k l) (ν α) u η i j).symm
      have hcomm2 :
          auxEmbed1 accU * auxEmbed2 (siteLax L N α (ν α) v η) =
            auxEmbed2 (siteLax L N α (ν α) v η) * auxEmbed1 accU :=
        auxEmbed1_comm_auxEmbed2_of_entries _ _ fun i j k l =>
          commutesWith_siteLax_of_commutesWithSite α (accU i j)
            (hcommU α (List.mem_cons_self) i j) (ν α) v η k l
      rw [auxEmbed1_mul, auxEmbed2_mul]
      calc
        liftR N L (u - v) η * (auxEmbed1 accU * auxEmbed1 (siteLax L N α (ν α) u η)) *
            (auxEmbed2 accV * auxEmbed2 (siteLax L N α (ν α) v η))
          = liftR N L (u - v) η * auxEmbed1 accU *
              (auxEmbed1 (siteLax L N α (ν α) u η) * auxEmbed2 accV) *
              auxEmbed2 (siteLax L N α (ν α) v η) := by simp only [Matrix.mul_assoc]
        _ = (liftR N L (u - v) η * auxEmbed1 accU * auxEmbed2 accV) *
              auxEmbed1 (siteLax L N α (ν α) u η) *
              auxEmbed2 (siteLax L N α (ν α) v η) := by
            rw [hcomm1]
            simp only [Matrix.mul_assoc]
        _ = (auxEmbed2 accV * auxEmbed1 accU * liftR N L (u - v) η) *
              auxEmbed1 (siteLax L N α (ν α) u η) *
              auxEmbed2 (siteLax L N α (ν α) v η) := by rw [hrtt]
        _ = auxEmbed2 accV * auxEmbed1 accU *
              (liftR N L (u - v) η * auxEmbed1 (siteLax L N α (ν α) u η) *
                auxEmbed2 (siteLax L N α (ν α) v η)) := by simp only [Matrix.mul_assoc]
        _ = auxEmbed2 accV * auxEmbed1 accU *
              (auxEmbed2 (siteLax L N α (ν α) v η) * auxEmbed1 (siteLax L N α (ν α) u η) *
                liftR N L (u - v) η) := by rw [siteLax_rtt]
        _ = auxEmbed2 accV * (auxEmbed1 accU * auxEmbed2 (siteLax L N α (ν α) v η)) *
              auxEmbed1 (siteLax L N α (ν α) u η) * liftR N L (u - v) η := by
            simp only [Matrix.mul_assoc]
        _ = auxEmbed2 accV * (auxEmbed2 (siteLax L N α (ν α) v η) * auxEmbed1 accU) *
              auxEmbed1 (siteLax L N α (ν α) u η) * liftR N L (u - v) η := by rw [hcomm2]
        _ = (auxEmbed2 accV * auxEmbed2 (siteLax L N α (ν α) v η)) *
              (auxEmbed1 accU * auxEmbed1 (siteLax L N α (ν α) u η)) *
              liftR N L (u - v) η := by simp only [Matrix.mul_assoc]
    refine ih hnodup' _ _ hrtt_step ?_ ?_
    · intro γ hγ i j
      have hne : α ≠ γ := fun heq => hnotmem (heq ▸ hγ)
      simp only [Matrix.mul_apply]
      clear hrtt hrtt_step
      have hsum : ∀ (s : Finset (Fin N)) (f : Fin N → QuantumOp L N),
          (∀ k ∈ s, CommutesWithSite γ (f k)) → CommutesWithSite γ (∑ k ∈ s, f k) := by
        intro s f hf
        induction s using Finset.cons_induction with
        | empty => intro b a; simp
        | cons x s hx ihs =>
          rw [Finset.sum_cons]
          exact commutesWithSite_add γ (hf x (Finset.mem_cons_self _ _))
            (ihs fun k hk => hf k (Finset.mem_cons_of_mem hk))
      exact hsum Finset.univ _ fun k _ =>
        commutesWithSite_mul γ (hcommU γ (List.mem_cons_of_mem _ hγ) i k)
          (commutesWithSite_siteLax hne (ν α) u η k j)
    · intro γ hγ i j
      have hne : α ≠ γ := fun heq => hnotmem (heq ▸ hγ)
      simp only [Matrix.mul_apply]
      clear hrtt hrtt_step
      have hsum : ∀ (s : Finset (Fin N)) (f : Fin N → QuantumOp L N),
          (∀ k ∈ s, CommutesWithSite γ (f k)) → CommutesWithSite γ (∑ k ∈ s, f k) := by
        intro s f hf
        induction s using Finset.cons_induction with
        | empty => intro b a; simp
        | cons x s hx ihs =>
          rw [Finset.sum_cons]
          exact commutesWithSite_add γ (hf x (Finset.mem_cons_self _ _))
            (ihs fun k hk => hf k (Finset.mem_cons_of_mem hk))
      exact hsum Finset.univ _ fun k _ =>
        commutesWithSite_mul γ (hcommV γ (List.mem_cons_of_mem _ hγ) i k)
          (commutesWithSite_siteLax hne (ν α) v η k j)

/-- Full `L`-site `SU(N)` rational XXX RTT relation:
`R_{12}(u - v) T_1(u) T_2(v) = T_2(v) T_1(u) R_{12}(u - v)`. -/
theorem xxxMonodromy_rtt (L N : ℕ) (ν : Fin L → ℂ) (u v η : ℂ) :
    liftR N L (u - v) η * auxEmbed1 (xxxMonodromy L N ν u η) * auxEmbed2 (xxxMonodromy L N ν v η) =
      auxEmbed2 (xxxMonodromy L N ν v η) * auxEmbed1 (xxxMonodromy L N ν u η) * liftR N L (u - v) η := by
  unfold xxxMonodromy
  refine listFoldl_rtt (List.finRange L) (List.nodup_finRange L) ν u v η 1 1 ?_ ?_ ?_
  · have h1 : auxEmbed1 (1 : Matrix (Fin N) (Fin N) (QuantumOp L N)) = 1 := by
      ext ⟨i', j'⟩ ⟨i, j⟩
      simp only [auxEmbed1, Matrix.of_apply, Matrix.one_apply, Prod.ext_iff]
      split_ifs <;> simp_all
    have h2 : auxEmbed2 (1 : Matrix (Fin N) (Fin N) (QuantumOp L N)) = 1 := by
      ext ⟨i', j'⟩ ⟨i, j⟩
      simp only [auxEmbed2, Matrix.of_apply, Matrix.one_apply, Prod.ext_iff]
      split_ifs <;> simp_all
    rw [h1, h2, mul_one, mul_one, one_mul, one_mul]
  · intro γ _ i j
    by_cases hij : i = j
    · subst hij; simpa using commutesWithSite_one γ
    · intro b a; simp [hij]
  · intro γ _ i j
    by_cases hij : i = j
    · subst hij; simpa using commutesWithSite_one γ
    · intro b a; simp [hij]

/-- Twisted quantum transfer matrix `τ(u) = tr_aux(K T(u))` in `QuantumOp L N`. -/
def twistedTransferMatrix (L N : ℕ) (ν : Fin L → ℂ)
    (K : Matrix (Fin N) (Fin N) ℂ) (u η : ℂ) : QuantumOp L N :=
  Matrix.trace (K.map (algebraMap ℂ (QuantumOp L N)) * xxxMonodromy L N ν u η)

private lemma yangRMatrix_inv_mul (N : ℕ) (u η : ℂ) :
    (u • (1 : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) - η • swapOp N) * yangRMatrix N u η =
      (u ^ 2 - η ^ 2) • (1 : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) := by
  have hP2 : swapOp N * swapOp N = 1 := by
    dsimp [swapOp]
    rw [← Matrix.permMatrix_mul]
    have hinv : (Equiv.prodComm (Fin N) (Fin N)) * (Equiv.prodComm (Fin N) (Fin N)) = 1 := by
      ext ⟨a, b⟩ <;> rfl
    rw [hinv, Matrix.permMatrix_one]
  dsimp [yangRMatrix]
  rw [sub_mul, mul_add, mul_add, smul_mul_smul_comm, smul_mul_smul_comm,
    smul_mul_smul_comm, smul_mul_smul_comm, one_mul, mul_one, one_mul, hP2]
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

private lemma trace_auxEmbed1_mul_auxEmbed2 {L N : ℕ}
    (A B : Matrix (Fin N) (Fin N) (QuantumOp L N)) :
    Matrix.trace (auxEmbed1 A * auxEmbed2 B) = Matrix.trace A * Matrix.trace B := by
  simp only [Matrix.trace, Matrix.diag]
  rw [Fintype.sum_prod_type]
  simp_rw [auxEmbed1_mul_auxEmbed2]
  rw [Finset.sum_mul_sum]

private lemma trace_auxEmbed2_mul_auxEmbed1 {L N : ℕ}
    (A B : Matrix (Fin N) (Fin N) (QuantumOp L N)) :
    Matrix.trace (auxEmbed2 B * auxEmbed1 A) = Matrix.trace B * Matrix.trace A := by
  simp only [Matrix.trace, Matrix.diag]
  rw [Fintype.sum_prod_type]
  simp_rw [auxEmbed2_mul_auxEmbed1]
  rw [Finset.sum_mul_sum, Finset.sum_comm]

private lemma trace_scalarMatrix_conj {N L : ℕ}
    (R1 R2 : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ)
    (hinv : R2 * R1 = 1)
    (M : Matrix (Fin N × Fin N) (Fin N × Fin N) (QuantumOp L N)) :
    Matrix.trace (R1.map (algebraMap ℂ (QuantumOp L N)) * M *
        R2.map (algebraMap ℂ (QuantumOp L N))) =
      Matrix.trace M := by
  ext x y
  simp only [Matrix.trace, Matrix.diag, Matrix.sum_apply]
  have hentry : ∀ p : Fin N × Fin N,
      (R1.map (algebraMap ℂ (QuantumOp L N)) * M *
          R2.map (algebraMap ℂ (QuantumOp L N))) p p x y =
        ∑ q : Fin N × Fin N, ∑ s : Fin N × Fin N, (R1 p q * R2 s p) * M q s x y := by
    intro p
    have hmat :
        (R1.map (algebraMap ℂ (QuantumOp L N)) * M *
            R2.map (algebraMap ℂ (QuantumOp L N))) p p =
          ∑ q : Fin N × Fin N, ∑ s : Fin N × Fin N, (R1 p q * R2 s p) • M q s := by
      simp only [Matrix.mul_apply, Matrix.map_apply, Algebra.algebraMap_eq_smul_one,
        Finset.sum_mul, Finset.mul_sum, Finset.smul_sum, smul_mul_assoc, one_mul, mul_smul_comm,
        mul_one, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun s _ => ?_
      rw [mul_comm (R2 s p) (R1 p q)]
    rw [hmat]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [hentry]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_comm]
  calc
    ∑ s : Fin N × Fin N, ∑ p : Fin N × Fin N, (R1 p q * R2 s p) * M q s x y
      = ∑ s : Fin N × Fin N, (∑ p : Fin N × Fin N, R2 s p * R1 p q) * M q s x y := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun p _ => by ring
    _ = ∑ s : Fin N × Fin N, (if s = q then (1 : ℂ) else 0) * M q s x y := by
          refine Finset.sum_congr rfl fun s _ => ?_
          have h := congr_fun (congr_fun hinv s) q
          simpa [Matrix.mul_apply, Matrix.one_apply] using congrArg (· * M q s x y) h
    _ = M q q x y := by simp

private lemma liftR_comm_auxEmbed_K {N L : ℕ} (w η : ℂ) (K : Matrix (Fin N) (Fin N) ℂ) :
    let KL := K.map (algebraMap ℂ (QuantumOp L N))
    liftR N L w η * (auxEmbed1 KL * auxEmbed2 KL) =
      (auxEmbed1 KL * auxEmbed2 KL) * liftR N L w η := by
  intro KL
  ext ⟨i', j'⟩ ⟨i, j⟩
  rw [liftR_mul_apply, mul_liftR_apply, auxEmbed1_mul_auxEmbed2, auxEmbed1_mul_auxEmbed2,
      auxEmbed1_mul_auxEmbed2]
  simp only [KL, Matrix.map_apply, Algebra.algebraMap_eq_smul_one, smul_mul_smul_comm, one_mul,
    smul_smul]
  have h1 : w * (K i' i * K j' j) = w * (K i' i * K j' j) := rfl
  have h2 : η * (K j' i * K i' j) = η * (K i' j * K j' i) := by rw [mul_comm (K j' i) (K i' j)]
  rw [h2]

private lemma auxEmbed1_K_mul_T {L N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    (T1 T2 : Matrix (Fin N) (Fin N) (QuantumOp L N)) :
    let KL := K.map (algebraMap ℂ (QuantumOp L N))
    auxEmbed1 (KL * T1) * auxEmbed2 (KL * T2) =
      (auxEmbed1 KL * auxEmbed2 KL) * (auxEmbed1 T1 * auxEmbed2 T2) ∧
    auxEmbed2 (KL * T2) * auxEmbed1 (KL * T1) =
      (auxEmbed1 KL * auxEmbed2 KL) * (auxEmbed2 T2 * auxEmbed1 T1) := by
  intro KL
  have hcomm : auxEmbed2 KL * auxEmbed1 T1 = auxEmbed1 T1 * auxEmbed2 KL := by
    symm
    apply auxEmbed1_comm_auxEmbed2_of_entries _ _ ?_
    intro i j k l
    simp only [KL, Matrix.map_apply, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one]
  have hcomm' : auxEmbed1 KL * auxEmbed2 KL = auxEmbed2 KL * auxEmbed1 KL := by
    apply auxEmbed1_comm_auxEmbed2_of_entries
    intro i j k l
    simp only [KL, Matrix.map_apply, Algebra.algebraMap_eq_smul_one, smul_mul_smul_comm, one_mul]
    rw [mul_comm (K i j) (K k l)]
  constructor
  · rw [auxEmbed1_mul, auxEmbed2_mul]
    calc
      (auxEmbed1 KL * auxEmbed1 T1) * (auxEmbed2 KL * auxEmbed2 T2)
        = auxEmbed1 KL * (auxEmbed1 T1 * auxEmbed2 KL) * auxEmbed2 T2 := by
            simp only [Matrix.mul_assoc]
      _ = auxEmbed1 KL * (auxEmbed2 KL * auxEmbed1 T1) * auxEmbed2 T2 := by rw [← hcomm]
      _ = (auxEmbed1 KL * auxEmbed2 KL) * (auxEmbed1 T1 * auxEmbed2 T2) := by
            simp only [Matrix.mul_assoc]
  · rw [auxEmbed1_mul, auxEmbed2_mul]
    calc
      (auxEmbed2 KL * auxEmbed2 T2) * (auxEmbed1 KL * auxEmbed1 T1)
        = auxEmbed2 KL * (auxEmbed2 T2 * auxEmbed1 KL) * auxEmbed1 T1 := by
            simp only [Matrix.mul_assoc]
      _ = auxEmbed2 KL * (auxEmbed1 KL * auxEmbed2 T2) * auxEmbed1 T1 := by
            have hcomm2 : auxEmbed2 T2 * auxEmbed1 KL = auxEmbed1 KL * auxEmbed2 T2 := by
              symm
              apply auxEmbed1_comm_auxEmbed2_of_entries
              intro i j k l
              simp only [KL, Matrix.map_apply, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
                mul_smul_comm, one_mul, mul_one]
            rw [hcomm2]
      _ = (auxEmbed2 KL * auxEmbed1 KL) * (auxEmbed2 T2 * auxEmbed1 T1) := by
            simp only [Matrix.mul_assoc]
      _ = (auxEmbed1 KL * auxEmbed2 KL) * (auxEmbed2 T2 * auxEmbed1 T1) := by rw [← hcomm']

private lemma twistedTransferMatrix_comm_of_ne (L N : ℕ) (ν : Fin L → ℂ)
    (K : Matrix (Fin N) (Fin N) ℂ) (u v η : ℂ) (hne : (u - v) ^ 2 - η ^ 2 ≠ 0) :
    twistedTransferMatrix L N ν K u η * twistedTransferMatrix L N ν K v η =
      twistedTransferMatrix L N ν K v η * twistedTransferMatrix L N ν K u η := by
  dsimp [twistedTransferMatrix]
  rw [← trace_auxEmbed1_mul_auxEmbed2, ← trace_auxEmbed2_mul_auxEmbed1]
  set R1 : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ := yangRMatrix N (u - v) η
  set R2 : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ :=
    ((u - v) ^ 2 - η ^ 2)⁻¹ •
      ((u - v) • (1 : Matrix (Fin N × Fin N) (Fin N × Fin N) ℂ) - η • swapOp N)
  have hR12 : R1 * R2 = 1 := by
    dsimp [R1, R2]
    rw [mul_smul_comm, yangRMatrix_inversion, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hR21 : R2 * R1 = 1 := by
    dsimp [R1, R2]
    rw [smul_mul_assoc, yangRMatrix_inv_mul, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hR1_map : R1.map (algebraMap ℂ (QuantumOp L N)) = liftR N L (u - v) η := rfl
  have hR12_map :
      R1.map (algebraMap ℂ (QuantumOp L N)) * R2.map (algebraMap ℂ (QuantumOp L N)) = 1 := by
    ext p q a b
    simp only [Matrix.mul_apply, Matrix.map_apply, Algebra.algebraMap_eq_smul_one,
      smul_mul_smul_comm, one_mul]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    have h := congr_fun (congr_fun hR12 p) q
    simp only [Matrix.mul_apply] at h
    rw [← Finset.sum_mul, h]
    simp only [Matrix.one_apply]
    split_ifs <;> simp [Matrix.one_apply, *]
  set KL := K.map (algebraMap ℂ (QuantumOp L N))
  set T1 := xxxMonodromy L N ν u η
  set T2 := xxxMonodromy L N ν v η
  have hrtt_KT :
      R1.map (algebraMap ℂ (QuantumOp L N)) * (auxEmbed1 (KL * T1) * auxEmbed2 (KL * T2)) =
        (auxEmbed2 (KL * T2) * auxEmbed1 (KL * T1)) * R1.map (algebraMap ℂ (QuantumOp L N)) := by
    rw [hR1_map, (auxEmbed1_K_mul_T K T1 T2).1, (auxEmbed1_K_mul_T K T1 T2).2]
    calc
      liftR N L (u - v) η * ((auxEmbed1 KL * auxEmbed2 KL) * (auxEmbed1 T1 * auxEmbed2 T2))
        = (liftR N L (u - v) η * (auxEmbed1 KL * auxEmbed2 KL)) *
            (auxEmbed1 T1 * auxEmbed2 T2) := by simp only [Matrix.mul_assoc]
      _ = ((auxEmbed1 KL * auxEmbed2 KL) * liftR N L (u - v) η) *
            (auxEmbed1 T1 * auxEmbed2 T2) := by rw [liftR_comm_auxEmbed_K]
      _ = (auxEmbed1 KL * auxEmbed2 KL) *
            (liftR N L (u - v) η * auxEmbed1 T1 * auxEmbed2 T2) := by
          simp only [Matrix.mul_assoc]
      _ = (auxEmbed1 KL * auxEmbed2 KL) *
            (auxEmbed2 T2 * auxEmbed1 T1 * liftR N L (u - v) η) := by
          rw [xxxMonodromy_rtt]
      _ = (auxEmbed1 KL * auxEmbed2 KL) * (auxEmbed2 T2 * auxEmbed1 T1) *
            liftR N L (u - v) η := by simp only [Matrix.mul_assoc]
  rw [← trace_scalarMatrix_conj R1 R2 hR21 (auxEmbed1 (KL * T1) * auxEmbed2 (KL * T2)),
      hrtt_KT, Matrix.mul_assoc, hR12_map, Matrix.mul_one]

private lemma continuous_twistedTransferMatrix (L N : ℕ) (ν : Fin L → ℂ)
    (K : Matrix (Fin N) (Fin N) ℂ) (η : ℂ) :
    Continuous (fun u : ℂ => twistedTransferMatrix L N ν K u η) := by
  have hsite : ∀ α : Fin L, Continuous (fun u : ℂ => siteLax L N α (ν α) u η) := by
    intro α
    refine continuous_matrix fun a b => ?_
    dsimp [siteLax]
    split_ifs
    · exact ((continuous_id.sub continuous_const).smul continuous_const).add continuous_const
    · exact continuous_const
  have hfold : ∀ (xs : List (Fin L))
      (acc : ℂ → Matrix (Fin N) (Fin N) (QuantumOp L N)), Continuous acc →
      Continuous (fun u => xs.foldl (fun a α => a * siteLax L N α (ν α) u η) (acc u)) := by
    intro xs
    induction xs with
    | nil => intro acc hacc; exact hacc
    | cons α xs' ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      exact ih _ (hacc.mul (hsite α))
  have hmono : Continuous (fun u : ℂ => xxxMonodromy L N ν u η) :=
    hfold (List.finRange L) (fun _ => 1) continuous_const
  have hprod : Continuous (fun u : ℂ => K.map (algebraMap ℂ (QuantumOp L N)) * xxxMonodromy L N ν u η) :=
    continuous_const.mul hmono
  dsimp [twistedTransferMatrix]
  exact continuous_finsetSum Finset.univ fun i _ =>
    (continuous_apply i).comp ((continuous_apply i).comp hprod)

/-- Unconditional commutativity of twisted `SU(N)` transfer matrices `[τ(u), τ(v)] = 0`
for all spectral parameters `u, v, η : ℂ` and arbitrary twist matrix `K`. -/
theorem twistedTransferMatrix_comm (L N : ℕ) (ν : Fin L → ℂ)
    (K : Matrix (Fin N) (Fin N) ℂ) (u v η : ℂ) :
    twistedTransferMatrix L N ν K u η * twistedTransferMatrix L N ν K v η =
      twistedTransferMatrix L N ν K v η * twistedTransferMatrix L N ν K u η := by
  let seq : ℕ → ℂ := fun n => u + (((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ))
  have hseq_inj : Function.Injective seq := by
    intro m n hmn
    have h1 : (((((m + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) = (((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) :=
      add_left_cancel hmn
    have h2 : (((m + 1 : ℕ) : ℝ)⁻¹) = (((n + 1 : ℕ) : ℝ)⁻¹) := Complex.ofReal_injective h1
    have h3 : ((m + 1 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) := inv_injective h2
    have h4 : m + 1 = n + 1 := Nat.cast_injective h3
    omega
  have htend : Tendsto seq atTop (𝓝 u) := by
    have hreal : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    have hcpx : Tendsto (fun n : ℕ => ((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) :=
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hreal).mono_right (by simp)
    have hadd := tendsto_const_nhds (x := u).add hcpx
    simpa [seq, add_zero] using hadd
  have havoid : ∀ c : ℂ, ∃ N0 : ℕ, ∀ n ≥ N0, seq n ≠ c := by
    intro c
    by_cases hc : ∃ m : ℕ, seq m = c
    · rcases hc with ⟨m, hm⟩
      refine ⟨m + 1, fun n hn hne => ?_⟩
      have hnm : n = m := hseq_inj (hne.trans hm.symm)
      omega
    · refine ⟨0, fun n _ hne => hc ⟨n, hne⟩⟩
  obtain ⟨N1, hN1⟩ := havoid (v + η)
  obtain ⟨N2, hN2⟩ := havoid (v - η)
  have hev : ∀ᶠ n in atTop,
      twistedTransferMatrix L N ν K (seq n) η * twistedTransferMatrix L N ν K v η =
        twistedTransferMatrix L N ν K v η * twistedTransferMatrix L N ν K (seq n) η := by
    refine eventually_atTop.mpr ⟨max N1 N2, fun n hn => ?_⟩
    have hn1 : seq n ≠ v + η := hN1 n (le_trans (le_max_left _ _) hn)
    have hn2 : seq n ≠ v - η := hN2 n (le_trans (le_max_right _ _) hn)
    have hne : (seq n - v) ^ 2 - η ^ 2 ≠ 0 := by
      intro hz
      have hsq : (seq n - v) ^ 2 = η ^ 2 := sub_eq_zero.mp hz
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
      · exact hn1 (eq_add_of_sub_eq' h)
      · exact hn2 (by linear_combination h)
    exact twistedTransferMatrix_comm_of_ne L N ν K (seq n) v η hne
  have hcont : Continuous (fun w : ℂ => twistedTransferMatrix L N ν K w η) :=
    continuous_twistedTransferMatrix L N ν K η
  have hLHS : Tendsto (fun n => twistedTransferMatrix L N ν K (seq n) η *
      twistedTransferMatrix L N ν K v η) atTop
      (𝓝 (twistedTransferMatrix L N ν K u η * twistedTransferMatrix L N ν K v η)) :=
    (hcont.continuousAt.tendsto.comp htend).mul tendsto_const_nhds
  have hRHS : Tendsto (fun n => twistedTransferMatrix L N ν K v η *
      twistedTransferMatrix L N ν K (seq n) η) atTop
      (𝓝 (twistedTransferMatrix L N ν K v η * twistedTransferMatrix L N ν K u η)) :=
    tendsto_const_nhds.mul (hcont.continuousAt.tendsto.comp htend)
  exact tendsto_nhds_unique (hLHS.congr' hev) hRHS

/-- Explicit `T16` non-commutativity witness on `xxxMonodromy` entries (`r ≥ 1`). -/
theorem xxxMonodromy_noncommutative (r : ℕ) (hr : 1 ≤ r) (ν : Fin 1 → ℂ) (u v : ℂ) :
    xxxMonodromy 1 (r + 1) ν u Complex.I ⟨0, Nat.zero_lt_succ r⟩ ⟨1, Nat.lt_succ_of_le hr⟩ *
      xxxMonodromy 1 (r + 1) ν v Complex.I ⟨1, Nat.lt_succ_of_le hr⟩ ⟨0, Nat.zero_lt_succ r⟩ ≠
    xxxMonodromy 1 (r + 1) ν v Complex.I ⟨1, Nat.lt_succ_of_le hr⟩ ⟨0, Nat.zero_lt_succ r⟩ *
      xxxMonodromy 1 (r + 1) ν u Complex.I ⟨0, Nat.zero_lt_succ r⟩ ⟨1, Nat.lt_succ_of_le hr⟩ := by
  have hfold : ∀ w : ℂ, xxxMonodromy 1 (r + 1) ν w Complex.I =
      siteLax 1 (r + 1) 0 (ν 0) w Complex.I := by
    intro w
    have hfr : List.finRange 1 = [0] := rfl
    simp [xxxMonodromy, hfr]
  rw [hfold u, hfold v]
  have h01 : (⟨0, Nat.zero_lt_succ r⟩ : Fin (r + 1)) ≠ ⟨1, Nat.lt_succ_of_le hr⟩ := by
    simp [Fin.ext_iff]
  have h10 : (⟨1, Nat.lt_succ_of_le hr⟩ : Fin (r + 1)) ≠ ⟨0, Nat.zero_lt_succ r⟩ := h01.symm
  simp only [siteLax, Matrix.of_apply, h01, h10, ↓reduceIte, zero_add, smul_mul_smul_comm]
  have hE10 : siteE (L := 1) (N := r + 1) 0 ⟨1, Nat.lt_succ_of_le hr⟩ ⟨0, Nat.zero_lt_succ r⟩ *
      siteE (L := 1) (N := r + 1) 0 ⟨0, Nat.zero_lt_succ r⟩ ⟨1, Nat.lt_succ_of_le hr⟩ =
      siteE 0 ⟨1, Nat.lt_succ_of_le hr⟩ ⟨1, Nat.lt_succ_of_le hr⟩ := by
    rw [siteE_mul_same]; simp
  have hE01 : siteE (L := 1) (N := r + 1) 0 ⟨0, Nat.zero_lt_succ r⟩ ⟨1, Nat.lt_succ_of_le hr⟩ *
      siteE (L := 1) (N := r + 1) 0 ⟨1, Nat.lt_succ_of_le hr⟩ ⟨0, Nat.zero_lt_succ r⟩ =
      siteE 0 ⟨0, Nat.zero_lt_succ r⟩ ⟨0, Nat.zero_lt_succ r⟩ := by
    rw [siteE_mul_same]; simp
  rw [hE10, hE01, Complex.I_mul_I]
  intro h
  let x : Fin 1 → Fin (r + 1) := fun _ => ⟨0, Nat.zero_lt_succ r⟩
  have hx := congr_fun (congr_fun h x) x
  dsimp [siteE, Matrix.of_apply, Matrix.smul_apply, x] at hx
  have hx' : (-1 : ℂ) * (if (1 : ℕ) = 0 then (1 : ℂ) else 0) =
      (-1 : ℂ) * (if (0 : ℕ) = 0 then (1 : ℂ) else 0) := by
    simpa [Fin.ext_iff] using hx
  norm_num at hx'

end

end InfoGeometry.Integrable.NestedXXXBetheEquations

