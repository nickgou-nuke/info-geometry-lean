/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic.NoncommRing
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornKitaevMajoranaChain
import InfoGeometry.OperatorAlgebra.PeirceSpine.IdempotentZornChainArchetypes

/-!
# Three-corner Zorn path: native ring identities for two directed links

This module proves the finite associative-ring algebra of the path and its
edge composites. “Majorana” here means the sum/difference construction only;
no involution, CAR representation, Hamiltonian spectrum, or topological phase
is inferred from these identities.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.ZornKitaevMajoranaChainFull

open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornKitaevMajoranaChain
open InfoGeometry.OperatorAlgebra.PeirceSpine.IdempotentZornChainArchetypes

variable {B : Type*} [Ring B]

def e1 (P₁ : B) : B := P₁
def e2 (P₁ P₂ : B) : B := P₂ - P₁
def e3 (P₂ : B) : B := 1 - P₂

def n12 (P₁ P₂ A : B) : B := e1 P₁ * A * e2 P₁ P₂
def n21 (P₁ P₂ C : B) : B := e2 P₁ P₂ * C * e1 P₁
def n23 (P₁ P₂ A : B) : B := e2 P₁ P₂ * A * e3 P₂
def n32 (P₁ P₂ C : B) : B := e3 P₂ * C * e2 P₁ P₂

def phi12 (P₁ P₂ A C : B) : B := n12 P₁ P₂ A + n21 P₁ P₂ C
def j12 (P₁ P₂ A C : B) : B := n12 P₁ P₂ A - n21 P₁ P₂ C
def v12 (P₁ P₂ A C : B) : B :=
  n12 P₁ P₂ A * n21 P₁ P₂ C + n21 P₁ P₂ C * n12 P₁ P₂ A
def sig12 (P₁ P₂ A C : B) : B :=
  n12 P₁ P₂ A * n21 P₁ P₂ C - n21 P₁ P₂ C * n12 P₁ P₂ A

def phi23 (P₁ P₂ A C : B) : B := n23 P₁ P₂ A + n32 P₁ P₂ C
def j23 (P₁ P₂ A C : B) : B := n23 P₁ P₂ A - n32 P₁ P₂ C
def v23 (P₁ P₂ A C : B) : B :=
  n23 P₁ P₂ A * n32 P₁ P₂ C + n32 P₁ P₂ C * n23 P₁ P₂ A
def sig23 (P₁ P₂ A C : B) : B :=
  n23 P₁ P₂ A * n32 P₁ P₂ C - n32 P₁ P₂ C * n23 P₁ P₂ A

def n13 (P₁ P₂ A₁ A₂ : B) : B := n12 P₁ P₂ A₁ * n23 P₁ P₂ A₂
def n31 (P₁ P₂ C₁ C₂ : B) : B := n32 P₁ P₂ C₂ * n21 P₁ P₂ C₁
def phi13 (P₁ P₂ A₁ C₁ A₂ C₂ : B) : B :=
  n13 P₁ P₂ A₁ A₂ + n31 P₁ P₂ C₁ C₂
def j13 (P₁ P₂ A₁ C₁ A₂ C₂ : B) : B :=
  n13 P₁ P₂ A₁ A₂ - n31 P₁ P₂ C₁ C₂
def v13 (P₁ P₂ A₁ C₁ A₂ C₂ : B) : B :=
  n13 P₁ P₂ A₁ A₂ * n31 P₁ P₂ C₁ C₂ + n31 P₁ P₂ C₁ C₂ * n13 P₁ P₂ A₁ A₂
def sig13 (P₁ P₂ A₁ C₁ A₂ C₂ : B) : B :=
  n13 P₁ P₂ A₁ A₂ * n31 P₁ P₂ C₁ C₂ - n31 P₁ P₂ C₁ C₂ * n13 P₁ P₂ A₁ A₂

def bulk (P₁ P₂ X : B) : B := e2 P₁ P₂ * X * e2 P₁ P₂

def chainPhi (P₁ P₂ A₁ C₁ A₂ C₂ : B) : B :=
  phi12 P₁ P₂ A₁ C₁ + phi23 P₁ P₂ A₂ C₂
def chainJ (P₁ P₂ A₁ C₁ A₂ C₂ : B) : B :=
  j12 P₁ P₂ A₁ C₁ + j23 P₁ P₂ A₂ C₂

def defect (x : B) : B := x * x - x
def comm (x y : B) : B := x * y - y * x
def anticomm (x y : B) : B := x * y + y * x

theorem three_corner_laws {P₁ P₂ : B}
    (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂)
    (h₁₂ : P₁ * P₂ = P₁) (h₂₁ : P₂ * P₁ = P₁) :
    e1 P₁ * e1 P₁ = e1 P₁ ∧ e2 P₁ P₂ * e2 P₁ P₂ = e2 P₁ P₂ ∧
    e3 P₂ * e3 P₂ = e3 P₂ ∧
    e1 P₁ * e2 P₁ P₂ = 0 ∧ e2 P₁ P₂ * e1 P₁ = 0 ∧
    e1 P₁ * e3 P₂ = 0 ∧ e3 P₂ * e1 P₁ = 0 ∧
    e2 P₁ P₂ * e3 P₂ = 0 ∧ e3 P₂ * e2 P₁ P₂ = 0 ∧
    e1 P₁ + e2 P₁ P₂ + e3 P₂ = 1 := by
  dsimp [e1, e2, e3]
  repeat' constructor
  all_goals noncomm_ring [h₁, h₂, h₁₂, h₂₁]

/-- Each link is square-zero in its two directed corners and has the exact
sum/difference tetraktys identities. -/
theorem link_tetraktys {P₁ P₂ A₁ C₁ A₂ C₂ : B}
    (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂)
    (h₁₂ : P₁ * P₂ = P₁) (h₂₁ : P₂ * P₁ = P₁) :
    n12 P₁ P₂ A₁ * n12 P₁ P₂ A₁ = 0 ∧
    n21 P₁ P₂ C₁ * n21 P₁ P₂ C₁ = 0 ∧
    phi12 P₁ P₂ A₁ C₁ * phi12 P₁ P₂ A₁ C₁ = v12 P₁ P₂ A₁ C₁ ∧
    j12 P₁ P₂ A₁ C₁ * j12 P₁ P₂ A₁ C₁ = -v12 P₁ P₂ A₁ C₁ ∧
    anticomm (phi12 P₁ P₂ A₁ C₁) (j12 P₁ P₂ A₁ C₁) = 0 ∧
    j12 P₁ P₂ A₁ C₁ * phi12 P₁ P₂ A₁ C₁ = sig12 P₁ P₂ A₁ C₁ ∧
    n23 P₁ P₂ A₂ * n23 P₁ P₂ A₂ = 0 ∧
    n32 P₁ P₂ C₂ * n32 P₁ P₂ C₂ = 0 ∧
    phi23 P₁ P₂ A₂ C₂ * phi23 P₁ P₂ A₂ C₂ = v23 P₁ P₂ A₂ C₂ ∧
    j23 P₁ P₂ A₂ C₂ * j23 P₁ P₂ A₂ C₂ = -v23 P₁ P₂ A₂ C₂ ∧
    anticomm (phi23 P₁ P₂ A₂ C₂) (j23 P₁ P₂ A₂ C₂) = 0 ∧
    j23 P₁ P₂ A₂ C₂ * phi23 P₁ P₂ A₂ C₂ = sig23 P₁ P₂ A₂ C₂ := by
  rcases three_corner_laws h₁ h₂ h₁₂ h₂₁ with
    ⟨he1, he2, he3, h12, h21, h13, h31, h23, h32, hsum⟩
  have hxx : n12 P₁ P₂ A₁ * n12 P₁ P₂ A₁ = 0 := by
    change root12 (e1 P₁) (e2 P₁ P₂) A₁ * root12 (e1 P₁) (e2 P₁ P₂) A₁ = 0
    exact corner_arrows_mul_zero (e := e1 P₁) (f := e2 P₁ P₂)
      (g := e1 P₁) (h := e2 P₁ P₂) (a := A₁) (b := A₁) h21
  have hyy : n21 P₁ P₂ C₁ * n21 P₁ P₂ C₁ = 0 := by
    change root21 (e2 P₁ P₂) (e1 P₁) C₁ * root21 (e2 P₁ P₂) (e1 P₁) C₁ = 0
    exact corner_arrows_mul_zero (e := e2 P₁ P₂) (f := e1 P₁)
      (g := e2 P₁ P₂) (h := e1 P₁) (a := C₁) (b := C₁) h12
  have huu : n23 P₁ P₂ A₂ * n23 P₁ P₂ A₂ = 0 := by
    change root23 (e2 P₁ P₂) (e3 P₂) A₂ * root23 (e2 P₁ P₂) (e3 P₂) A₂ = 0
    exact corner_arrows_mul_zero (e := e2 P₁ P₂) (f := e3 P₂)
      (g := e2 P₁ P₂) (h := e3 P₂) (a := A₂) (b := A₂) h32
  have hvv : n32 P₁ P₂ C₂ * n32 P₁ P₂ C₂ = 0 := by
    change root32 (e3 P₂) (e2 P₁ P₂) C₂ * root32 (e3 P₂) (e2 P₁ P₂) C₂ = 0
    exact corner_arrows_mul_zero (e := e3 P₂) (f := e2 P₁ P₂)
      (g := e3 P₂) (h := e2 P₁ P₂) (a := C₂) (b := C₂) h23
  have hp12 := directed_majorana_pair_laws hxx hyy
  have hp23 := directed_majorana_pair_laws huu hvv
  refine ⟨hxx, hyy, ?_, ?_, ?_, ?_, huu, hvv, ?_, ?_, ?_, ?_⟩
  · simpa [phi12, v12, n12, n21, e1, e2, root12, root21] using hp12.1
  · simpa [j12, v12, n12, n21, e1, e2, root12, root21] using hp12.2.1
  · simpa [anticomm, phi12, j12, n12, n21, e1, e2, root12, root21] using hp12.2.2.1
  · simpa [sig12, j12, phi12, n12, n21, e1, e2, root12, root21] using hp12.2.2.2
  · simpa [phi23, v23, n23, n32, e2, e3, root23, root32] using hp23.1
  · simpa [j23, v23, n23, n32, e2, e3, root23, root32] using hp23.2.1
  · simpa [anticomm, phi23, j23, n23, n32, e2, e3, root23, root32] using hp23.2.2.1
  · simpa [sig23, j23, phi23, n23, n32, e2, e3, root23, root32] using hp23.2.2.2

/-- The four non-composable mixed products vanish, and the surviving two-hop
products are exactly the endpoint arrows. -/
theorem interlink_cancellation {P₁ P₂ A₁ C₁ A₂ C₂ : B}
    (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂)
    (h₁₂ : P₁ * P₂ = P₁) (h₂₁ : P₂ * P₁ = P₁) :
    n21 P₁ P₂ C₁ * n23 P₁ P₂ A₂ = 0 ∧
    n12 P₁ P₂ A₁ * n32 P₁ P₂ C₂ = 0 ∧
    n21 P₁ P₂ C₁ * n32 P₁ P₂ C₂ = 0 ∧
    phi12 P₁ P₂ A₁ C₁ * phi23 P₁ P₂ A₂ C₂ = n13 P₁ P₂ A₁ A₂ ∧
    phi23 P₁ P₂ A₂ C₂ * phi12 P₁ P₂ A₁ C₁ = n31 P₁ P₂ C₁ C₂ := by
  rcases three_corner_laws h₁ h₂ h₁₂ h₂₁ with
    ⟨he1, he2, he3, h12, h21, h13, h31, h23, h32, hsum⟩
  have hyu : n21 P₁ P₂ C₁ * n23 P₁ P₂ A₂ = 0 := by
    change root21 (e2 P₁ P₂) (e1 P₁) C₁ * root23 (e2 P₁ P₂) (e3 P₂) A₂ = 0
    exact corner_arrows_mul_zero (e := e2 P₁ P₂) (f := e1 P₁)
      (g := e2 P₁ P₂) (h := e3 P₂) (a := C₁) (b := A₂) h12
  have hxv : n12 P₁ P₂ A₁ * n32 P₁ P₂ C₂ = 0 := by
    change root12 (e1 P₁) (e2 P₁ P₂) A₁ * root32 (e3 P₂) (e2 P₁ P₂) C₂ = 0
    exact corner_arrows_mul_zero (e := e1 P₁) (f := e2 P₁ P₂)
      (g := e3 P₂) (h := e2 P₁ P₂) (a := A₁) (b := C₂) h23
  have hyv : n21 P₁ P₂ C₁ * n32 P₁ P₂ C₂ = 0 := by
    change root21 (e2 P₁ P₂) (e1 P₁) C₁ * root32 (e3 P₂) (e2 P₁ P₂) C₂ = 0
    exact corner_arrows_mul_zero (e := e2 P₁ P₂) (f := e1 P₁)
      (g := e3 P₂) (h := e2 P₁ P₂) (a := C₁) (b := C₂) h13
  have hux : n23 P₁ P₂ A₂ * n12 P₁ P₂ A₁ = 0 := by
    change root23 (e2 P₁ P₂) (e3 P₂) A₂ * root12 (e1 P₁) (e2 P₁ P₂) A₁ = 0
    exact corner_arrows_mul_zero (e := e2 P₁ P₂) (f := e3 P₂)
      (g := e1 P₁) (h := e2 P₁ P₂) (a := A₂) (b := A₁) h31
  have hvx : n32 P₁ P₂ C₂ * n12 P₁ P₂ A₁ = 0 := by
    change root32 (e3 P₂) (e2 P₁ P₂) C₂ * root12 (e1 P₁) (e2 P₁ P₂) A₁ = 0
    exact corner_arrows_mul_zero (e := e3 P₂) (f := e2 P₁ P₂)
      (g := e1 P₁) (h := e2 P₁ P₂) (a := C₂) (b := A₁) h21
  have huy : n23 P₁ P₂ A₂ * n21 P₁ P₂ C₁ = 0 := by
    change root23 (e2 P₁ P₂) (e3 P₂) A₂ * root21 (e2 P₁ P₂) (e1 P₁) C₁ = 0
    exact corner_arrows_mul_zero (e := e2 P₁ P₂) (f := e3 P₂)
      (g := e2 P₁ P₂) (h := e1 P₁) (a := A₂) (b := C₁) h32
  have hProducts := zorn_interlink_majorana_products
    (A := A₁) (Bc := C₁) (C := A₂) (D := C₂)
    h12 h21 h13 h31 h23 h32
  refine ⟨hyu, hxv, hyv, ?_, ?_⟩
  · simpa [phi12, phi23, n13, n12, n21, n23, n32, e1, e2, e3,
      majoranaPhi12, majoranaPhi23, edgeRoot13, root12, root21, root23, root32]
      using hProducts.1
  · simpa [phi12, phi23, n31, n12, n21, n23, n32, e1, e2, e3,
      majoranaPhi12, majoranaPhi23, edgeRoot31, root12, root21, root23, root32]
      using hProducts.2.1

/-- The alternating parity of the three-corner Zorn decomposition acts on
single-link Majorana sums by the oriented signs `(+,-)` and fixes the
two-hop endpoint bridge. This is the concrete Zorn-chain realization of the
abstract three-corner parity law; it asserts no CAR or spectral structure. -/
theorem zorn_plabic_parity_majorana_chain_laws {P₁ P₂ A₁ C₁ A₂ C₂ : B}
    (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂)
    (h₁₂ : P₁ * P₂ = P₁) (h₂₁ : P₂ * P₁ = P₁) :
    let S := plabicParity (e1 P₁) (e2 P₁ P₂) (e3 P₂)
    S * S = 1 ∧
    S * phi12 P₁ P₂ A₁ C₁ = j12 P₁ P₂ A₁ C₁ ∧
    S * j12 P₁ P₂ A₁ C₁ = phi12 P₁ P₂ A₁ C₁ ∧
    antibracket S (phi12 P₁ P₂ A₁ C₁) = 0 ∧
    S * phi23 P₁ P₂ A₂ C₂ = -j23 P₁ P₂ A₂ C₂ ∧
    S * j23 P₁ P₂ A₂ C₂ = -phi23 P₁ P₂ A₂ C₂ ∧
    antibracket S (phi23 P₁ P₂ A₂ C₂) = 0 ∧
    S * phi13 P₁ P₂ A₁ C₁ A₂ C₂ = phi13 P₁ P₂ A₁ C₁ A₂ C₂ ∧
    phi13 P₁ P₂ A₁ C₁ A₂ C₂ * S = phi13 P₁ P₂ A₁ C₁ A₂ C₂ ∧
    S * j13 P₁ P₂ A₁ C₁ A₂ C₂ = j13 P₁ P₂ A₁ C₁ A₂ C₂ ∧
    j13 P₁ P₂ A₁ C₁ A₂ C₂ * S = j13 P₁ P₂ A₁ C₁ A₂ C₂ := by
  rcases three_corner_laws h₁ h₂ h₁₂ h₂₁ with
    ⟨he1, he2, he3, h12, h21, h13, h31, h23, h32, hsum⟩
  let S := plabicParity (e1 P₁) (e2 P₁ P₂) (e3 P₂)
  have hpar := plabic_parity_three_corner_laws he1 he2 he3 h12 h21 h13 h31 h23 h32 hsum
  have hS1L : S * e1 P₁ = e1 P₁ := hpar.2.1
  have hS1R : e1 P₁ * S = e1 P₁ := hpar.2.2.1
  have hS2L : S * e2 P₁ P₂ = -(e2 P₁ P₂) := hpar.2.2.2.1
  have hS2R : e2 P₁ P₂ * S = -(e2 P₁ P₂) := hpar.2.2.2.2.1
  have hS3L : S * e3 P₂ = e3 P₂ := hpar.2.2.2.2.2.1
  have hS3R : e3 P₂ * S = e3 P₂ := hpar.2.2.2.2.2.2
  have parityLeft (e f x : B) (he : S * e = e) :
      S * (e * x * f) = e * x * f := by
    calc
      S * (e * x * f) = (S * e) * x * f := by noncomm_ring
      _ = e * x * f := by rw [he]
  have parityLeftNeg (e f x : B) (he : S * e = -e) :
      S * (e * x * f) = -(e * x * f) := by
    calc
      S * (e * x * f) = (S * e) * x * f := by noncomm_ring
      _ = (-e) * x * f := by rw [he]
      _ = -(e * x * f) := by noncomm_ring
  have parityRight (e f x : B) (hf : f * S = f) :
      (e * x * f) * S = e * x * f := by
    calc
      (e * x * f) * S = e * x * (f * S) := by noncomm_ring
      _ = e * x * f := by rw [hf]
  have parityRightNeg (e f x : B) (hf : f * S = -f) :
      (e * x * f) * S = -(e * x * f) := by
    calc
      (e * x * f) * S = e * x * (f * S) := by noncomm_ring
      _ = e * x * (-f) := by rw [hf]
      _ = -(e * x * f) := by noncomm_ring
  have h12L : S * n12 P₁ P₂ A₁ = n12 P₁ P₂ A₁ := by
    change S * (e1 P₁ * A₁ * e2 P₁ P₂) = e1 P₁ * A₁ * e2 P₁ P₂
    exact parityLeft _ _ _ hS1L
  have h21L : S * n21 P₁ P₂ C₁ = -(n21 P₁ P₂ C₁) := by
    change S * (e2 P₁ P₂ * C₁ * e1 P₁) = -(e2 P₁ P₂ * C₁ * e1 P₁)
    exact parityLeftNeg _ _ _ hS2L
  have h12R : n12 P₁ P₂ A₁ * S = -(n12 P₁ P₂ A₁) := by
    change (e1 P₁ * A₁ * e2 P₁ P₂) * S = -(e1 P₁ * A₁ * e2 P₁ P₂)
    exact parityRightNeg _ _ _ hS2R
  have h21R : n21 P₁ P₂ C₁ * S = n21 P₁ P₂ C₁ := by
    change (e2 P₁ P₂ * C₁ * e1 P₁) * S = e2 P₁ P₂ * C₁ * e1 P₁
    exact parityRight _ _ _ hS1R
  have h23L : S * n23 P₁ P₂ A₂ = -(n23 P₁ P₂ A₂) := by
    change S * (e2 P₁ P₂ * A₂ * e3 P₂) = -(e2 P₁ P₂ * A₂ * e3 P₂)
    exact parityLeftNeg _ _ _ hS2L
  have h32L : S * n32 P₁ P₂ C₂ = n32 P₁ P₂ C₂ := by
    change S * (e3 P₂ * C₂ * e2 P₁ P₂) = e3 P₂ * C₂ * e2 P₁ P₂
    exact parityLeft _ _ _ hS3L
  have h23R : n23 P₁ P₂ A₂ * S = n23 P₁ P₂ A₂ := by
    change (e2 P₁ P₂ * A₂ * e3 P₂) * S = e2 P₁ P₂ * A₂ * e3 P₂
    exact parityRight _ _ _ hS3R
  have h32R : n32 P₁ P₂ C₂ * S = -(n32 P₁ P₂ C₂) := by
    change (e3 P₂ * C₂ * e2 P₁ P₂) * S = -(e3 P₂ * C₂ * e2 P₁ P₂)
    exact parityRightNeg _ _ _ hS2R
  have h13L : S * n13 P₁ P₂ A₁ A₂ = n13 P₁ P₂ A₁ A₂ := by
    change S * (n12 P₁ P₂ A₁ * n23 P₁ P₂ A₂) =
      n12 P₁ P₂ A₁ * n23 P₁ P₂ A₂
    calc
      S * (n12 P₁ P₂ A₁ * n23 P₁ P₂ A₂) =
          (S * n12 P₁ P₂ A₁) * n23 P₁ P₂ A₂ := by rw [← mul_assoc]
      _ = n12 P₁ P₂ A₁ * n23 P₁ P₂ A₂ := by rw [h12L]
  have h13R : n13 P₁ P₂ A₁ A₂ * S = n13 P₁ P₂ A₁ A₂ := by
    change (n12 P₁ P₂ A₁ * n23 P₁ P₂ A₂) * S =
      n12 P₁ P₂ A₁ * n23 P₁ P₂ A₂
    calc
      (n12 P₁ P₂ A₁ * n23 P₁ P₂ A₂) * S =
          n12 P₁ P₂ A₁ * (n23 P₁ P₂ A₂ * S) := by rw [mul_assoc]
      _ = n12 P₁ P₂ A₁ * n23 P₁ P₂ A₂ := by rw [h23R]
  have h31L : S * n31 P₁ P₂ C₁ C₂ = n31 P₁ P₂ C₁ C₂ := by
    change S * (n32 P₁ P₂ C₂ * n21 P₁ P₂ C₁) =
      n32 P₁ P₂ C₂ * n21 P₁ P₂ C₁
    calc
      S * (n32 P₁ P₂ C₂ * n21 P₁ P₂ C₁) =
          (S * n32 P₁ P₂ C₂) * n21 P₁ P₂ C₁ := by rw [← mul_assoc]
      _ = n32 P₁ P₂ C₂ * n21 P₁ P₂ C₁ := by rw [h32L]
  have h31R : n31 P₁ P₂ C₁ C₂ * S = n31 P₁ P₂ C₁ C₂ := by
    change (n32 P₁ P₂ C₂ * n21 P₁ P₂ C₁) * S =
      n32 P₁ P₂ C₂ * n21 P₁ P₂ C₁
    calc
      (n32 P₁ P₂ C₂ * n21 P₁ P₂ C₁) * S =
          n32 P₁ P₂ C₂ * (n21 P₁ P₂ C₁ * S) := by rw [mul_assoc]
      _ = n32 P₁ P₂ C₂ * n21 P₁ P₂ C₁ := by rw [h21R]
  refine ⟨hpar.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change S * (n12 P₁ P₂ A₁ + n21 P₁ P₂ C₁) =
      n12 P₁ P₂ A₁ - n21 P₁ P₂ C₁
    rw [mul_add, h12L, h21L]
    abel
  · change S * (n12 P₁ P₂ A₁ - n21 P₁ P₂ C₁) =
      n12 P₁ P₂ A₁ + n21 P₁ P₂ C₁
    rw [mul_sub, h12L, h21L]
    abel
  · change S * (n12 P₁ P₂ A₁ + n21 P₁ P₂ C₁) +
      (n12 P₁ P₂ A₁ + n21 P₁ P₂ C₁) * S = 0
    rw [mul_add, add_mul, h12L, h21L, h12R, h21R]
    abel
  · change S * (n23 P₁ P₂ A₂ + n32 P₁ P₂ C₂) =
      -(n23 P₁ P₂ A₂ - n32 P₁ P₂ C₂)
    rw [mul_add, h23L, h32L]
    abel
  · change S * (n23 P₁ P₂ A₂ - n32 P₁ P₂ C₂) =
      -(n23 P₁ P₂ A₂ + n32 P₁ P₂ C₂)
    rw [mul_sub, h23L, h32L]
    abel
  · change S * (n23 P₁ P₂ A₂ + n32 P₁ P₂ C₂) +
      (n23 P₁ P₂ A₂ + n32 P₁ P₂ C₂) * S = 0
    rw [mul_add, add_mul, h23L, h32L, h23R, h32R]
    abel
  · change S * (n13 P₁ P₂ A₁ A₂ + n31 P₁ P₂ C₁ C₂) =
      n13 P₁ P₂ A₁ A₂ + n31 P₁ P₂ C₁ C₂
    rw [mul_add, h13L, h31L]
  · change (n13 P₁ P₂ A₁ A₂ + n31 P₁ P₂ C₁ C₂) * S =
      n13 P₁ P₂ A₁ A₂ + n31 P₁ P₂ C₁ C₂
    rw [add_mul, h13R, h31R]
  · change S * (n13 P₁ P₂ A₁ A₂ - n31 P₁ P₂ C₁ C₂) =
      n13 P₁ P₂ A₁ A₂ - n31 P₁ P₂ C₁ C₂
    rw [mul_sub, h13L, h31L]
  · change (n13 P₁ P₂ A₁ A₂ - n31 P₁ P₂ C₁ C₂) * S =
      n13 P₁ P₂ A₁ A₂ - n31 P₁ P₂ C₁ C₂
    rw [sub_mul, h13R, h31R]

/-- The edge bridge and phase have zero middle-corner support, so they commute
and anticommute with compressed bulk observables. Their metric and spin defect
operators also commute with the bulk corner; no anticommutator claim is made
for those even defect operators. -/
theorem edge_bulk_decoupling {P₁ P₂ A₁ C₁ A₂ C₂ X : B}
    (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂)
    (h₁₂ : P₁ * P₂ = P₁) (h₂₁ : P₂ * P₁ = P₁) :
    e2 P₁ P₂ * phi13 P₁ P₂ A₁ C₁ A₂ C₂ = 0 ∧
    phi13 P₁ P₂ A₁ C₁ A₂ C₂ * e2 P₁ P₂ = 0 ∧
    e2 P₁ P₂ * j13 P₁ P₂ A₁ C₁ A₂ C₂ = 0 ∧
    j13 P₁ P₂ A₁ C₁ A₂ C₂ * e2 P₁ P₂ = 0 ∧
    comm (phi13 P₁ P₂ A₁ C₁ A₂ C₂) (bulk P₁ P₂ X) = 0 ∧
    comm (j13 P₁ P₂ A₁ C₁ A₂ C₂) (bulk P₁ P₂ X) = 0 ∧
    anticomm (phi13 P₁ P₂ A₁ C₁ A₂ C₂) (bulk P₁ P₂ X) = 0 ∧
    anticomm (j13 P₁ P₂ A₁ C₁ A₂ C₂) (bulk P₁ P₂ X) = 0 ∧
    comm (v13 P₁ P₂ A₁ C₁ A₂ C₂) (bulk P₁ P₂ X) = 0 ∧
    comm (sig13 P₁ P₂ A₁ C₁ A₂ C₂) (bulk P₁ P₂ X) = 0 := by
  rcases three_corner_laws h₁ h₂ h₁₂ h₂₁ with
    ⟨he1, he2, he3, h12, h21, h13, h31, h23, h32, hsum⟩
  have hEdge := zorn_edge_modes_are_invisible_to_interior_corner
    (A := A₁) (Bc := C₁) (C := A₂) (D := C₂) (X := X)
    h12 h21 h23 h32
  have hPhiE2 : phi13 P₁ P₂ A₁ C₁ A₂ C₂ * e2 P₁ P₂ = 0 := by
    simpa [phi13, n13, n31, edgeMajoranaPhi13, edgeRoot13, edgeRoot31,
      n12, n23, n32, n21, e1, e2, e3, root12, root21, root23, root32]
      using hEdge.2.1
  have hE2Phi : e2 P₁ P₂ * phi13 P₁ P₂ A₁ C₁ A₂ C₂ = 0 := by
    simpa [phi13, n13, n31, edgeMajoranaPhi13, edgeRoot13, edgeRoot31,
      n12, n23, n32, n21, e1, e2, e3, root12, root21, root23, root32]
      using hEdge.1
  have hJE2 : j13 P₁ P₂ A₁ C₁ A₂ C₂ * e2 P₁ P₂ = 0 := by
    simpa [j13, n13, n31, edgeMajoranaJ13, edgeRoot13, edgeRoot31,
      n12, n23, n32, n21, e1, e2, e3, root12, root21, root23, root32]
      using hEdge.2.2.2.1
  have hE2J : e2 P₁ P₂ * j13 P₁ P₂ A₁ C₁ A₂ C₂ = 0 := by
    simpa [j13, n13, n31, edgeMajoranaJ13, edgeRoot13, edgeRoot31,
      n12, n23, n32, n21, e1, e2, e3, root12, root21, root23, root32]
      using hEdge.2.2.1
  have hPhiL : phi13 P₁ P₂ A₁ C₁ A₂ C₂ * bulk P₁ P₂ X = 0 := by
    calc
      phi13 P₁ P₂ A₁ C₁ A₂ C₂ * bulk P₁ P₂ X =
          (phi13 P₁ P₂ A₁ C₁ A₂ C₂ * e2 P₁ P₂) * X * e2 P₁ P₂ := by
            simp only [bulk]
            noncomm_ring
      _ = 0 := by rw [hPhiE2]; simp
  have hPhiR : bulk P₁ P₂ X * phi13 P₁ P₂ A₁ C₁ A₂ C₂ = 0 := by
    calc
      bulk P₁ P₂ X * phi13 P₁ P₂ A₁ C₁ A₂ C₂ =
          e2 P₁ P₂ * X * (e2 P₁ P₂ * phi13 P₁ P₂ A₁ C₁ A₂ C₂) := by
            simp only [bulk]
            noncomm_ring
      _ = 0 := by rw [hE2Phi]; simp
  have hJL : j13 P₁ P₂ A₁ C₁ A₂ C₂ * bulk P₁ P₂ X = 0 := by
    calc
      j13 P₁ P₂ A₁ C₁ A₂ C₂ * bulk P₁ P₂ X =
          (j13 P₁ P₂ A₁ C₁ A₂ C₂ * e2 P₁ P₂) * X * e2 P₁ P₂ := by
            simp only [bulk]
            noncomm_ring
      _ = 0 := by rw [hJE2]; simp
  have hJR : bulk P₁ P₂ X * j13 P₁ P₂ A₁ C₁ A₂ C₂ = 0 := by
    calc
      bulk P₁ P₂ X * j13 P₁ P₂ A₁ C₁ A₂ C₂ =
          e2 P₁ P₂ * X * (e2 P₁ P₂ * j13 P₁ P₂ A₁ C₁ A₂ C₂) := by
            simp only [bulk]
            noncomm_ring
      _ = 0 := by rw [hE2J]; simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [phi13, n13, n31, edgeMajoranaPhi13, edgeRoot13, edgeRoot31,
      n12, n23, n32, n21, e1, e2, e3, root12, root21, root23, root32]
      using hEdge.1
  · simpa [phi13, n13, n31, edgeMajoranaPhi13, edgeRoot13, edgeRoot31,
      n12, n23, n32, n21, e1, e2, e3, root12, root21, root23, root32]
      using hEdge.2.1
  · simpa [j13, n13, n31, edgeMajoranaJ13, edgeRoot13, edgeRoot31,
      n12, n23, n32, n21, e1, e2, e3, root12, root21, root23, root32]
      using hEdge.2.2.1
  · simpa [j13, n13, n31, edgeMajoranaJ13, edgeRoot13, edgeRoot31,
      n12, n23, n32, n21, e1, e2, e3, root12, root21, root23, root32]
      using hEdge.2.2.2.1
  · change ringComm (phi13 P₁ P₂ A₁ C₁ A₂ C₂) (bulk P₁ P₂ X) = 0
    simpa [phi13, n13, n31, bulk, edgeMajoranaPhi13, edgeRoot13, edgeRoot31,
      n12, n23, n32, n21, e1, e2, e3, root12, root21, root23, root32]
      using hEdge.2.2.2.2.1
  · change ringComm (j13 P₁ P₂ A₁ C₁ A₂ C₂) (bulk P₁ P₂ X) = 0
    simpa [j13, n13, n31, bulk, edgeMajoranaJ13, edgeRoot13, edgeRoot31,
      n12, n23, n32, n21, e1, e2, e3, root12, root21, root23, root32]
      using hEdge.2.2.2.2.2.1
  · simp [anticomm, hPhiL, hPhiR]
  · simp [anticomm, hJL, hJR]
  · change ringComm (v13 P₁ P₂ A₁ C₁ A₂ C₂) (bulk P₁ P₂ X) = 0
    simpa [v13, n13, n31, bulk, edgeMetric13, edgeRoot13, edgeRoot31,
      n12, n23, n32, n21, e1, e2, e3, root12, root21, root23, root32]
      using hEdge.2.2.2.2.2.2.1
  · change ringComm (sig13 P₁ P₂ A₁ C₁ A₂ C₂) (bulk P₁ P₂ X) = 0
    simpa [sig13, n13, n31, bulk, edgeSpin13, edgeRoot13, edgeRoot31,
      n12, n23, n32, n21, e1, e2, e3, root12, root21, root23, root32]
      using hEdge.2.2.2.2.2.2.2

/-- The end-to-end bridge does not automatically commute with the full
two-link chain. Its exact commutator is the difference of the two surviving
three-hop paths. Thus decoupling from the middle corner alone is insufficient
to assert a boundary zero mode for the full chain operator. -/
lemma two_link_repeated_products_vanish {x y u v : B}
    (hxx : x * x = 0) (hvv : v * v = 0)
    (hux : u * x = 0) (hvx : v * x = 0) (hxv : x * v = 0)
    (hyv : y * v = 0) :
    x * (x * u) = 0 ∧ u * (x * u) = 0 ∧ v * (x * u) = 0 ∧
    x * (v * y) = 0 ∧ y * (v * y) = 0 ∧ v * (v * y) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc x * (x * u) = (x * x) * u := by rw [← mul_assoc]
      _ = 0 := by rw [hxx]; simp
  · calc u * (x * u) = (u * x) * u := by rw [← mul_assoc]
      _ = 0 := by rw [hux]; simp
  · calc v * (x * u) = (v * x) * u := by rw [← mul_assoc]
      _ = 0 := by rw [hvx]; simp
  · calc x * (v * y) = (x * v) * y := by rw [← mul_assoc]
      _ = 0 := by rw [hxv]; simp
  · calc y * (v * y) = (y * v) * y := by rw [← mul_assoc]
      _ = 0 := by rw [hyv]; simp
  · calc v * (v * y) = (v * v) * y := by rw [← mul_assoc]
      _ = 0 := by rw [hvv]; simp

theorem two_link_edge_bridge_chain_commutator {x y u v : B}
    (hxx : x * x = 0) (hyy : y * y = 0)
    (huu : u * u = 0) (hvv : v * v = 0)
    (hxv : x * v = 0) (hyu : y * u = 0)
    (hux : u * x = 0) (huy : u * y = 0)
    (hvx : v * x = 0) (hyv : y * v = 0) :
    comm (x * u + v * y) (x + y + u + v) =
      (x * u * v + v * y * x) - (y * x * u + u * v * y) := by
  rcases two_link_repeated_products_vanish hxx hvv hux hvx hxv hyv with
    ⟨h1, h2, h3, h4, h5, h6⟩
  unfold comm
  noncomm_ring [hxx, hyy, huu, hvv, hxv, hyu, hux, huy, hvx, hyv, h1, h2, h3, h4, h5, h6]

/-- Four commutators of the two directed end-to-end composites with the
symmetric and alternating two-link operators. The surviving terms are the
oriented three-hop paths; no scalar or commutativity assumption is used. -/
theorem two_link_edge_chain_commutator_table {x y u v : B}
    (hxx : x * x = 0) (hyy : y * y = 0)
    (huu : u * u = 0) (hvv : v * v = 0)
    (hxv : x * v = 0) (hyu : y * u = 0)
    (hux : u * x = 0) (huy : u * y = 0)
    (hvx : v * x = 0) (hyv : y * v = 0) :
    comm (x * u + v * y) (x + y + u + v) =
      (x * u * v + v * y * x) - (y * x * u + u * v * y) ∧
    comm (x * u - v * y) (x + y + u + v) =
      (x * u * v - v * y * x) - (y * x * u - u * v * y) ∧
    comm (x * u + v * y) (x - y + u - v) =
      (-x * u * v + v * y * x) - (-y * x * u + u * v * y) ∧
    comm (x * u - v * y) (x - y + u - v) =
      (-x * u * v - v * y * x) - (-y * x * u - u * v * y) := by
  rcases two_link_repeated_products_vanish hxx hvv hux hvx hxv hyv with
    ⟨h1, h2, h3, h4, h5, h6⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (unfold comm; noncomm_ring [hxx, hyy, huu, hvv, hxv, hyu, hux, huy, hvx, hyv,
      h1, h2, h3, h4, h5, h6])

/-- Specialization of the path formula to the idempotent Zorn chain. The
edge Majorana bridge is conserved by the full chain exactly when its two
three-hop return paths agree; orthogonality by itself does not imply this. -/
theorem zorn_edge_bridge_chain_commutator {P₁ P₂ A₁ C₁ A₂ C₂ : B}
    (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂)
    (h₁₂ : P₁ * P₂ = P₁) (h₂₁ : P₂ * P₁ = P₁) :
    comm (phi13 P₁ P₂ A₁ C₁ A₂ C₂) (chainPhi P₁ P₂ A₁ C₁ A₂ C₂) =
      (n13 P₁ P₂ A₁ A₂ * n32 P₁ P₂ C₂ +
        n31 P₁ P₂ C₁ C₂ * n12 P₁ P₂ A₁) -
      (n21 P₁ P₂ C₁ * n13 P₁ P₂ A₁ A₂ +
        n23 P₁ P₂ A₂ * n31 P₁ P₂ C₁ C₂) := by
  rcases three_corner_laws h₁ h₂ h₁₂ h₂₁ with
    ⟨_, _, _, h12, h21, h13, h31, h23, h32, _⟩
  have hxx : n12 P₁ P₂ A₁ * n12 P₁ P₂ A₁ = 0 :=
    corner_arrows_mul_zero (a := A₁) (b := A₁) h21
  have hyy : n21 P₁ P₂ C₁ * n21 P₁ P₂ C₁ = 0 :=
    corner_arrows_mul_zero (a := C₁) (b := C₁) h12
  have huu : n23 P₁ P₂ A₂ * n23 P₁ P₂ A₂ = 0 :=
    corner_arrows_mul_zero (a := A₂) (b := A₂) h32
  have hvv : n32 P₁ P₂ C₂ * n32 P₁ P₂ C₂ = 0 :=
    corner_arrows_mul_zero (a := C₂) (b := C₂) h23
  have hxv : n12 P₁ P₂ A₁ * n32 P₁ P₂ C₂ = 0 :=
    corner_arrows_mul_zero (a := A₁) (b := C₂) h23
  have hyu : n21 P₁ P₂ C₁ * n23 P₁ P₂ A₂ = 0 :=
    corner_arrows_mul_zero (a := C₁) (b := A₂) h12
  have hux : n23 P₁ P₂ A₂ * n12 P₁ P₂ A₁ = 0 :=
    corner_arrows_mul_zero (a := A₂) (b := A₁) h31
  have huy : n23 P₁ P₂ A₂ * n21 P₁ P₂ C₁ = 0 :=
    corner_arrows_mul_zero (a := A₂) (b := C₁) h32
  have hvx : n32 P₁ P₂ C₂ * n12 P₁ P₂ A₁ = 0 :=
    corner_arrows_mul_zero (a := C₂) (b := A₁) h21
  have hyv : n21 P₁ P₂ C₁ * n32 P₁ P₂ C₂ = 0 :=
    corner_arrows_mul_zero (a := C₁) (b := C₂) h13
  simpa [phi13, chainPhi, phi12, phi23, n13, n31, add_assoc, mul_assoc] using
    (two_link_edge_bridge_chain_commutator hxx hyy huu hvv hxv hyu
      hux huy hvx hyv)

/-- Full-chain conservation of the Zorn edge bridge is equivalent to balance
of its two directed three-hop return paths. -/
theorem zorn_edge_bridge_is_chain_zero_mode_iff_path_balance
    {P₁ P₂ A₁ C₁ A₂ C₂ : B}
    (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂)
    (h₁₂ : P₁ * P₂ = P₁) (h₂₁ : P₂ * P₁ = P₁) :
    comm (phi13 P₁ P₂ A₁ C₁ A₂ C₂) (chainPhi P₁ P₂ A₁ C₁ A₂ C₂) = 0 ↔
      n13 P₁ P₂ A₁ A₂ * n32 P₁ P₂ C₂ +
        n31 P₁ P₂ C₁ C₂ * n12 P₁ P₂ A₁ =
      n21 P₁ P₂ C₁ * n13 P₁ P₂ A₁ A₂ +
        n23 P₁ P₂ A₂ * n31 P₁ P₂ C₁ C₂ := by
  rw [zorn_edge_bridge_chain_commutator h₁ h₂ h₁₂ h₂₁]
  exact sub_eq_zero

/-- Exact squares and anticommutator of the total two-link sum/difference.
The total commutator formula is intentionally stated separately with its
correct cancellation: the two mixed commutators cancel each other. -/
theorem total_chain_squares_and_anticommutator {P₁ P₂ A₁ C₁ A₂ C₂ : B}
    (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂)
    (h₁₂ : P₁ * P₂ = P₁) (h₂₁ : P₂ * P₁ = P₁) :
    chainPhi P₁ P₂ A₁ C₁ A₂ C₂ * chainPhi P₁ P₂ A₁ C₁ A₂ C₂ =
      v12 P₁ P₂ A₁ C₁ + v23 P₁ P₂ A₂ C₂ + phi13 P₁ P₂ A₁ C₁ A₂ C₂ ∧
    chainJ P₁ P₂ A₁ C₁ A₂ C₂ * chainJ P₁ P₂ A₁ C₁ A₂ C₂ =
      -(v12 P₁ P₂ A₁ C₁ + v23 P₁ P₂ A₂ C₂) + phi13 P₁ P₂ A₁ C₁ A₂ C₂ ∧
    anticomm (chainPhi P₁ P₂ A₁ C₁ A₂ C₂) (chainJ P₁ P₂ A₁ C₁ A₂ C₂) =
      (2 : ℤ) • j13 P₁ P₂ A₁ C₁ A₂ C₂ ∧
    comm (chainJ P₁ P₂ A₁ C₁ A₂ C₂) (chainPhi P₁ P₂ A₁ C₁ A₂ C₂) =
      (2 : ℤ) • (sig12 P₁ P₂ A₁ C₁ + sig23 P₁ P₂ A₂ C₂) := by
  rcases three_corner_laws h₁ h₂ h₁₂ h₂₁ with
    ⟨he1, he2, he3, h12, h21, h13, h31, h23, h32, hsum⟩
  have hxx : n12 P₁ P₂ A₁ * n12 P₁ P₂ A₁ = 0 :=
    corner_arrows_mul_zero (a := A₁) (b := A₁) h21
  have hyy : n21 P₁ P₂ C₁ * n21 P₁ P₂ C₁ = 0 :=
    corner_arrows_mul_zero (a := C₁) (b := C₁) h12
  have huu : n23 P₁ P₂ A₂ * n23 P₁ P₂ A₂ = 0 :=
    corner_arrows_mul_zero (a := A₂) (b := A₂) h32
  have hvv : n32 P₁ P₂ C₂ * n32 P₁ P₂ C₂ = 0 :=
    corner_arrows_mul_zero (a := C₂) (b := C₂) h23
  have hxv : n12 P₁ P₂ A₁ * n32 P₁ P₂ C₂ = 0 :=
    corner_arrows_mul_zero (a := A₁) (b := C₂) h23
  have hyu : n21 P₁ P₂ C₁ * n23 P₁ P₂ A₂ = 0 :=
    corner_arrows_mul_zero (a := C₁) (b := A₂) h12
  have hux : n23 P₁ P₂ A₂ * n12 P₁ P₂ A₁ = 0 :=
    corner_arrows_mul_zero (a := A₂) (b := A₁) h31
  have huy : n23 P₁ P₂ A₂ * n21 P₁ P₂ C₁ = 0 :=
    corner_arrows_mul_zero (a := A₂) (b := C₁) h32
  have hvx : n32 P₁ P₂ C₂ * n12 P₁ P₂ A₁ = 0 :=
    corner_arrows_mul_zero (a := C₂) (b := A₁) h21
  have hyv : n21 P₁ P₂ C₁ * n32 P₁ P₂ C₂ = 0 :=
    corner_arrows_mul_zero (a := C₁) (b := C₂) h13
  have hsquares := directed_two_link_square_laws hxx hyy huu hvv
    hxv hyu hux huy hvx hyv
  have hbrackets := directed_edge_defect_laws hxx hyy huu hvv
    hxv hyu hux huy hvx hyv
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hsquares.1
    dsimp [chainPhi, phi12, phi23, n12, n21, n23, n32, e1, e2, e3,
      root12, root21, root23, root32] at h ⊢
    rw [h]
    simp only [v12, v23, phi13, n13, n31]
    abel
  · have h := hsquares.2
    dsimp [chainJ, j12, j23, n12, n21, n23, n32, e1, e2, e3,
      root12, root21, root23, root32] at h ⊢
    rw [h]
    simp only [v12, v23, phi13, n13, n31]
    abel
  · have h := hbrackets.2
    dsimp [chainPhi, chainJ, phi12, j12, phi23, j23] at h ⊢
    change
      (n12 P₁ P₂ A₁ + n21 P₁ P₂ C₁ + (n23 P₁ P₂ A₂ + n32 P₁ P₂ C₂)) *
          (n12 P₁ P₂ A₁ - n21 P₁ P₂ C₁ + (n23 P₁ P₂ A₂ - n32 P₁ P₂ C₂)) +
        (n12 P₁ P₂ A₁ - n21 P₁ P₂ C₁ + (n23 P₁ P₂ A₂ - n32 P₁ P₂ C₂)) *
          (n12 P₁ P₂ A₁ + n21 P₁ P₂ C₁ + (n23 P₁ P₂ A₂ + n32 P₁ P₂ C₂)) =
        (2 : ℤ) • j13 P₁ P₂ A₁ C₁ A₂ C₂
    rw [h]
    simp only [j13, n13, n31]
  · dsimp [chainPhi, chainJ, comm, phi12, j12, phi23, j23, sig12, sig23]
    noncomm_ring [hxx, hyy, huu, hvv, hxv, hyu, hux, huy, hvx, hyv]

/-- The idempotency defects of the total two-link operators retain both the
end-to-end bridge and the linear term in `δ(T) = T² - T`. -/
theorem total_chain_idempotency_defect_readout {P₁ P₂ A₁ C₁ A₂ C₂ : B}
    (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂)
    (h₁₂ : P₁ * P₂ = P₁) (h₂₁ : P₂ * P₁ = P₁) :
    defect (chainPhi P₁ P₂ A₁ C₁ A₂ C₂) =
      v12 P₁ P₂ A₁ C₁ + v23 P₁ P₂ A₂ C₂ +
        phi13 P₁ P₂ A₁ C₁ A₂ C₂ - chainPhi P₁ P₂ A₁ C₁ A₂ C₂ ∧
    defect (chainJ P₁ P₂ A₁ C₁ A₂ C₂) =
      -(v12 P₁ P₂ A₁ C₁ + v23 P₁ P₂ A₂ C₂) +
        phi13 P₁ P₂ A₁ C₁ A₂ C₂ - chainJ P₁ P₂ A₁ C₁ A₂ C₂ := by
  rcases total_chain_squares_and_anticommutator h₁ h₂ h₁₂ h₂₁ with
    ⟨hPhi, hJ, _, _⟩
  constructor
  · unfold defect
    rw [hPhi]
  · unfold defect
    rw [hJ]

/-- Directed-arrow form of the two-link Plabic connection identities. The
proof only uses the square-zero arrows and the six non-composable products;
the nested idempotent shell calculation is kept out of this algebraic core. -/
theorem directed_plabic_twisted_connection_laws {x y u v : B}
    (hxx : x * x = 0) (hyy : y * y = 0)
    (huu : u * u = 0) (hvv : v * v = 0)
    (hxv : x * v = 0) (hyu : y * u = 0)
    (hux : u * x = 0) (huy : u * y = 0)
    (hvx : v * x = 0) (hyv : y * v = 0) :
    ((x - y) - (u - v)) * ((x + y) + (u + v)) =
      (x * y - y * x) - (u * v - v * u) + (x * u + v * y) ∧
    comm ((x - y) - (u - v)) ((x + y) + (u + v)) =
      (2 : ℤ) • ((x * y - y * x) - (u * v - v * u) + (x * u + v * y)) ∧
    anticomm ((x - y) - (u - v)) ((x + y) + (u + v)) = 0 ∧
    comm ((x + y) - (u + v)) ((x + y) + (u + v)) =
      (2 : ℤ) • (x * u - v * y) ∧
    anticomm ((x + y) - (u + v)) ((x + y) + (u + v)) =
      (2 : ℤ) • ((x * y + y * x) - (u * v + v * u)) ∧
    comm ((x - y) - (u - v)) ((x + y) - (u + v)) =
      (2 : ℤ) • ((x * y - y * x) + (u * v - v * u)) ∧
    comm ((x - y) + (u - v)) ((x + y) + (u + v)) =
      (2 : ℤ) • ((x * y - y * x) + (u * v - v * u)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [comm, anticomm]) <;>
    noncomm_ring [hxx, hyy, huu, hvv, hxv, hyu, hux, huy, hvx, hyv]

/-- The two oriented spin generators act on the endpoint arrows by the sum
and difference of their link metrics. These are exact identities in an
arbitrary associative ring under the directed-corner annihilation laws. -/
theorem directed_plabic_spin_connection_actions {x y u v : B}
    (hxx : x * x = 0) (hyy : y * y = 0)
    (huu : u * u = 0) (hvv : v * v = 0)
    (hxv : x * v = 0) (hyu : y * u = 0)
    (hux : u * x = 0) (huy : u * y = 0)
    (hvx : v * x = 0) (hyv : y * v = 0) :
    comm ((x * y - y * x) + (u * v - v * u)) (x * u) =
        (x * y + y * x) * (x * u) + (x * u) * (u * v + v * u) ∧
    comm ((x * y - y * x) - (u * v - v * u)) (x * u) =
        (x * y + y * x) * (x * u) - (x * u) * (u * v + v * u) ∧
    comm ((x * y - y * x) + (u * v - v * u)) (v * y) =
        -((u * v + v * u) * (v * y) + (v * y) * (x * y + y * x)) ∧
    comm ((x * y - y * x) - (u * v - v * u)) (v * y) =
        (u * v + v * u) * (v * y) - (v * y) * (x * y + y * x) := by
  have hxxu : x * (x * u) = 0 := by rw [← mul_assoc, hxx, zero_mul]
  have hvxu : v * (x * u) = 0 := by rw [← mul_assoc, hvx, zero_mul]
  have huxu : u * (x * u) = 0 := by rw [← mul_assoc, hux, zero_mul]
  have huxy : u * (x * y) = 0 := by rw [← mul_assoc, hux, zero_mul]
  have huyx : u * (y * x) = 0 := by rw [← mul_assoc, huy, zero_mul]
  have huuv : u * (u * v) = 0 := by rw [← mul_assoc, huu, zero_mul]
  have hyv_y : y * (v * y) = 0 := by rw [← mul_assoc, hyv, zero_mul]
  have hxv_y : x * (v * y) = 0 := by rw [← mul_assoc, hxv, zero_mul]
  have hvv_y : v * (v * y) = 0 := by rw [← mul_assoc, hvv, zero_mul]
  have hyyx : y * (y * x) = 0 := by rw [← mul_assoc, hyy, zero_mul]
  have hyuv : y * (u * v) = 0 := by rw [← mul_assoc, hyu, zero_mul]
  have hyv_u : y * (v * u) = 0 := by rw [← mul_assoc, hyv, zero_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold comm
    noncomm_ring [hxxu, hvxu, huxu, huxy, huyx, huuv,
      hyv_y, hxv_y, hvv_y, hyyx, hyuv, hyv_u]
  · unfold comm
    noncomm_ring [hxxu, hvxu, huxu, huxy, huyx, huuv,
      hyv_y, hxv_y, hvv_y, hyyx, hyuv, hyv_u]
  · unfold comm
    noncomm_ring [hxxu, hvxu, huxu, huxy, huyx, huuv,
      hyv_y, hxv_y, hvv_y, hyyx, hyuv, hyv_u]
  · unfold comm
    noncomm_ring [hxxu, hvxu, huxu, huxy, huyx, huuv,
      hyv_y, hxv_y, hvv_y, hyyx, hyuv, hyv_u]

/-- The three-corner Peirce chain realizes the directed spin-connection
actions on both endpoint arrows. The sum connection adds the two link
metrics; the parity-twisted connection takes their difference. -/
theorem zorn_plabic_spin_connection_actions
    {P₁ P₂ A₁ C₁ A₂ C₂ : B}
    (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂)
    (h₁₂ : P₁ * P₂ = P₁) (h₂₁ : P₂ * P₁ = P₁) :
    comm (sig12 P₁ P₂ A₁ C₁ + sig23 P₁ P₂ A₂ C₂)
        (n13 P₁ P₂ A₁ A₂) =
      v12 P₁ P₂ A₁ C₁ * n13 P₁ P₂ A₁ A₂ +
        n13 P₁ P₂ A₁ A₂ * v23 P₁ P₂ A₂ C₂ ∧
    comm (sig12 P₁ P₂ A₁ C₁ - sig23 P₁ P₂ A₂ C₂)
        (n13 P₁ P₂ A₁ A₂) =
      v12 P₁ P₂ A₁ C₁ * n13 P₁ P₂ A₁ A₂ -
        n13 P₁ P₂ A₁ A₂ * v23 P₁ P₂ A₂ C₂ ∧
    comm (sig12 P₁ P₂ A₁ C₁ + sig23 P₁ P₂ A₂ C₂)
        (n31 P₁ P₂ C₁ C₂) =
      -((v23 P₁ P₂ A₂ C₂ * n31 P₁ P₂ C₁ C₂) +
        (n31 P₁ P₂ C₁ C₂ * v12 P₁ P₂ A₁ C₁)) ∧
    comm (sig12 P₁ P₂ A₁ C₁ - sig23 P₁ P₂ A₂ C₂)
        (n31 P₁ P₂ C₁ C₂) =
      v23 P₁ P₂ A₂ C₂ * n31 P₁ P₂ C₁ C₂ -
        n31 P₁ P₂ C₁ C₂ * v12 P₁ P₂ A₁ C₁ := by
  rcases three_corner_laws h₁ h₂ h₁₂ h₂₁ with
    ⟨_, _, _, h12, h21, h13, h31, h23, h32, _⟩
  let x := n12 P₁ P₂ A₁
  let y := n21 P₁ P₂ C₁
  let u := n23 P₁ P₂ A₂
  let v := n32 P₁ P₂ C₂
  have hxx : x * x = 0 := by
    change root12 (e1 P₁) (e2 P₁ P₂) A₁ * root12 (e1 P₁) (e2 P₁ P₂) A₁ = 0
    exact corner_arrows_mul_zero (a := A₁) (b := A₁) h21
  have hyy : y * y = 0 := by
    change root21 (e2 P₁ P₂) (e1 P₁) C₁ * root21 (e2 P₁ P₂) (e1 P₁) C₁ = 0
    exact corner_arrows_mul_zero (a := C₁) (b := C₁) h12
  have huu : u * u = 0 := by
    change root23 (e2 P₁ P₂) (e3 P₂) A₂ * root23 (e2 P₁ P₂) (e3 P₂) A₂ = 0
    exact corner_arrows_mul_zero (a := A₂) (b := A₂) h32
  have hvv : v * v = 0 := by
    change root32 (e3 P₂) (e2 P₁ P₂) C₂ * root32 (e3 P₂) (e2 P₁ P₂) C₂ = 0
    exact corner_arrows_mul_zero (a := C₂) (b := C₂) h23
  have hxv : x * v = 0 := by
    change root12 (e1 P₁) (e2 P₁ P₂) A₁ * root32 (e3 P₂) (e2 P₁ P₂) C₂ = 0
    exact corner_arrows_mul_zero (a := A₁) (b := C₂) h23
  have hyu : y * u = 0 := by
    change root21 (e2 P₁ P₂) (e1 P₁) C₁ * root23 (e2 P₁ P₂) (e3 P₂) A₂ = 0
    exact corner_arrows_mul_zero (a := C₁) (b := A₂) h12
  have hux : u * x = 0 := by
    change root23 (e2 P₁ P₂) (e3 P₂) A₂ * root12 (e1 P₁) (e2 P₁ P₂) A₁ = 0
    exact corner_arrows_mul_zero (a := A₂) (b := A₁) h31
  have huy : u * y = 0 := by
    change root23 (e2 P₁ P₂) (e3 P₂) A₂ * root21 (e2 P₁ P₂) (e1 P₁) C₁ = 0
    exact corner_arrows_mul_zero (a := A₂) (b := C₁) h32
  have hvx : v * x = 0 := by
    change root32 (e3 P₂) (e2 P₁ P₂) C₂ * root12 (e1 P₁) (e2 P₁ P₂) A₁ = 0
    exact corner_arrows_mul_zero (a := C₂) (b := A₁) h21
  have hyv : y * v = 0 := by
    change root21 (e2 P₁ P₂) (e1 P₁) C₁ * root32 (e3 P₂) (e2 P₁ P₂) C₂ = 0
    exact corner_arrows_mul_zero (a := C₁) (b := C₂) h13
  have hActions := directed_plabic_spin_connection_actions
    hxx hyy huu hvv hxv hyu hux huy hvx hyv
  simpa [sig12, sig23, v12, v23, n13, n31, x, y, u, v, comm] using hActions

/-- The spin connections act on the endpoint Majorana pair by adding or
subtracting the already established actions on its two directed arrows. -/
theorem zorn_plabic_spin_connection_actions_on_boundary_pair
    {P₁ P₂ A₁ C₁ A₂ C₂ : B}
    (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂)
    (h₁₂ : P₁ * P₂ = P₁) (h₂₁ : P₂ * P₁ = P₁) :
    comm (sig12 P₁ P₂ A₁ C₁ + sig23 P₁ P₂ A₂ C₂)
        (phi13 P₁ P₂ A₁ C₁ A₂ C₂) =
      v12 P₁ P₂ A₁ C₁ * n13 P₁ P₂ A₁ A₂ +
        n13 P₁ P₂ A₁ A₂ * v23 P₁ P₂ A₂ C₂ -
        v23 P₁ P₂ A₂ C₂ * n31 P₁ P₂ C₁ C₂ -
        n31 P₁ P₂ C₁ C₂ * v12 P₁ P₂ A₁ C₁ ∧
    comm (sig12 P₁ P₂ A₁ C₁ - sig23 P₁ P₂ A₂ C₂)
        (phi13 P₁ P₂ A₁ C₁ A₂ C₂) =
      v12 P₁ P₂ A₁ C₁ * n13 P₁ P₂ A₁ A₂ -
        n13 P₁ P₂ A₁ A₂ * v23 P₁ P₂ A₂ C₂ +
        v23 P₁ P₂ A₂ C₂ * n31 P₁ P₂ C₁ C₂ -
        n31 P₁ P₂ C₁ C₂ * v12 P₁ P₂ A₁ C₁ ∧
    comm (sig12 P₁ P₂ A₁ C₁ + sig23 P₁ P₂ A₂ C₂)
        (j13 P₁ P₂ A₁ C₁ A₂ C₂) =
      v12 P₁ P₂ A₁ C₁ * n13 P₁ P₂ A₁ A₂ +
        n13 P₁ P₂ A₁ A₂ * v23 P₁ P₂ A₂ C₂ +
        v23 P₁ P₂ A₂ C₂ * n31 P₁ P₂ C₁ C₂ +
        n31 P₁ P₂ C₁ C₂ * v12 P₁ P₂ A₁ C₁ ∧
    comm (sig12 P₁ P₂ A₁ C₁ - sig23 P₁ P₂ A₂ C₂)
        (j13 P₁ P₂ A₁ C₁ A₂ C₂) =
      v12 P₁ P₂ A₁ C₁ * n13 P₁ P₂ A₁ A₂ -
        n13 P₁ P₂ A₁ A₂ * v23 P₁ P₂ A₂ C₂ -
        v23 P₁ P₂ A₂ C₂ * n31 P₁ P₂ C₁ C₂ +
        n31 P₁ P₂ C₁ C₂ * v12 P₁ P₂ A₁ C₁ := by
  rcases zorn_plabic_spin_connection_actions h₁ h₂ h₁₂ h₂₁ with
    ⟨h13sum, h13diff, h31sum, h31diff⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · change comm (sig12 P₁ P₂ A₁ C₁ + sig23 P₁ P₂ A₂ C₂)
      (n13 P₁ P₂ A₁ A₂ + n31 P₁ P₂ C₁ C₂) = _
    have hExpand : comm (sig12 P₁ P₂ A₁ C₁ + sig23 P₁ P₂ A₂ C₂)
        (n13 P₁ P₂ A₁ A₂ + n31 P₁ P₂ C₁ C₂) =
        comm (sig12 P₁ P₂ A₁ C₁ + sig23 P₁ P₂ A₂ C₂) (n13 P₁ P₂ A₁ A₂) +
        comm (sig12 P₁ P₂ A₁ C₁ + sig23 P₁ P₂ A₂ C₂) (n31 P₁ P₂ C₁ C₂) := by
      unfold comm
      noncomm_ring
    rw [hExpand, h13sum, h31sum]
    noncomm_ring
  · change comm (sig12 P₁ P₂ A₁ C₁ - sig23 P₁ P₂ A₂ C₂)
      (n13 P₁ P₂ A₁ A₂ + n31 P₁ P₂ C₁ C₂) = _
    have hExpand : comm (sig12 P₁ P₂ A₁ C₁ - sig23 P₁ P₂ A₂ C₂)
        (n13 P₁ P₂ A₁ A₂ + n31 P₁ P₂ C₁ C₂) =
        comm (sig12 P₁ P₂ A₁ C₁ - sig23 P₁ P₂ A₂ C₂) (n13 P₁ P₂ A₁ A₂) +
        comm (sig12 P₁ P₂ A₁ C₁ - sig23 P₁ P₂ A₂ C₂) (n31 P₁ P₂ C₁ C₂) := by
      unfold comm
      noncomm_ring
    rw [hExpand, h13diff, h31diff]
    noncomm_ring
  · change comm (sig12 P₁ P₂ A₁ C₁ + sig23 P₁ P₂ A₂ C₂)
      (n13 P₁ P₂ A₁ A₂ - n31 P₁ P₂ C₁ C₂) = _
    have hExpand : comm (sig12 P₁ P₂ A₁ C₁ + sig23 P₁ P₂ A₂ C₂)
        (n13 P₁ P₂ A₁ A₂ - n31 P₁ P₂ C₁ C₂) =
        comm (sig12 P₁ P₂ A₁ C₁ + sig23 P₁ P₂ A₂ C₂) (n13 P₁ P₂ A₁ A₂) -
        comm (sig12 P₁ P₂ A₁ C₁ + sig23 P₁ P₂ A₂ C₂) (n31 P₁ P₂ C₁ C₂) := by
      unfold comm
      noncomm_ring
    rw [hExpand, h13sum, h31sum]
    noncomm_ring
  · change comm (sig12 P₁ P₂ A₁ C₁ - sig23 P₁ P₂ A₂ C₂)
      (n13 P₁ P₂ A₁ A₂ - n31 P₁ P₂ C₁ C₂) = _
    have hExpand : comm (sig12 P₁ P₂ A₁ C₁ - sig23 P₁ P₂ A₂ C₂)
        (n13 P₁ P₂ A₁ A₂ - n31 P₁ P₂ C₁ C₂) =
        comm (sig12 P₁ P₂ A₁ C₁ - sig23 P₁ P₂ A₂ C₂) (n13 P₁ P₂ A₁ A₂) -
        comm (sig12 P₁ P₂ A₁ C₁ - sig23 P₁ P₂ A₂ C₂) (n31 P₁ P₂ C₁ C₂) := by
      unfold comm
      noncomm_ring
    rw [hExpand, h13diff, h31diff]
    noncomm_ring

/-- Algebraic contraction identity for a two-link path with middle corner `e`.
The hypotheses are precisely the corner support and non-composability laws
used by the concrete Zorn-chain instance below. -/
theorem directed_plabic_vertex_contraction {e x y u v : B}
    (hxe : x * e = x) (hve : v * e = v)
    (hey : e * y = y) (heu : e * u = u)
    (hxx : x * x = 0) (hvv : v * v = 0)
    (hxv : x * v = 0) (hvx : v * x = 0)
    (hyy : y * y = 0) (huu : u * u = 0)
    (hyu : y * u = 0) (huy : u * y = 0) :
    (1 - x - v) * (e + x + y + u + v) * (1 - y - u) =
      e - (x * y + v * u) - (x * u + v * y) := by
  have hLeft : (x + v) * e = x + v := by rw [add_mul, hxe, hve]
  have hRight : e * (y + u) = y + u := by rw [mul_add, hey, heu]
  have hFirst : (x + v) * (e + x + y + u + v) =
      x + v + (x * y + x * u + v * y + v * u) := by
    calc
      (x + v) * (e + x + y + u + v) =
          (x + v) * e + (x + v) * (x + y + u + v) := by noncomm_ring
      _ = x + v + (x * y + x * u + v * y + v * u) := by
          rw [hLeft]
          noncomm_ring [hxx, hvv, hxv, hvx]
  have hLast : (x * y + x * u + v * y + v * u) * (y + u) = 0 := by
    noncomm_ring [hyy, huu, hyu, huy]
  have hMiddle : (e + y + u - (x * y + x * u + v * y + v * u)) * (y + u) =
      y + u := by
    calc
      (e + y + u - (x * y + x * u + v * y + v * u)) * (y + u) =
          (e + y + u) * (y + u) -
            (x * y + x * u + v * y + v * u) * (y + u) := by noncomm_ring
      _ = (e + y + u) * (y + u) := by rw [hLast]; simp
      _ = e * (y + u) := by noncomm_ring [hyy, huu, hyu, huy]
      _ = y + u := hRight
  calc
    (1 - x - v) * (e + x + y + u + v) * (1 - y - u) =
        (e + y + u - (x * y + x * u + v * y + v * u)) * (1 - y - u) := by
          have hLM : (1 - x - v) * (e + x + y + u + v) =
              e + y + u - (x * y + x * u + v * y + v * u) := by
            calc
              (1 - x - v) * (e + x + y + u + v) =
                  e + x + y + u + v -
                    (x + v) * (e + x + y + u + v) := by noncomm_ring
              _ = e + y + u - (x * y + x * u + v * y + v * u) := by
                  rw [hFirst]
                  noncomm_ring
          rw [hLM]
    _ = e - (x * y + v * u) - (x * u + v * y) := by
          calc
            (e + y + u - (x * y + x * u + v * y + v * u)) * (1 - y - u) =
                e + y + u - (x * y + x * u + v * y + v * u) - (y + u) := by
                  calc
                    _ = (e + y + u - (x * y + x * u + v * y + v * u)) -
                        (e + y + u - (x * y + x * u + v * y + v * u)) * (y + u) := by
                          noncomm_ring
                    _ = _ := by rw [hMiddle]
            _ = e - (x * y + v * u) - (x * u + v * y) := by
              noncomm_ring

/-- Signed version of the directed contraction. Its bridge term is the
symmetric endpoint sum `x*u + v*y`; this sign is fixed by the order and
orientation of the two return strippers. -/
theorem directed_plabic_signed_vertex_contraction {e x y u v : B}
    (hxe : x * e = x) (hve : v * e = v)
    (hey : e * y = y) (heu : e * u = u)
    (hxx : x * x = 0) (hvv : v * v = 0)
    (hxv : x * v = 0) (hvx : v * x = 0)
    (hyy : y * y = 0) (huu : u * u = 0)
    (hyu : y * u = 0) (huy : u * y = 0) :
    (1 - x + v) * (e + x - y + u - v) * (1 + y - u) =
      e + (x * y + v * u) - (x * u + v * y) := by
  have hve' : (-v) * e = -v := by
    calc
      (-v) * e = -(v * e) := by noncomm_ring
      _ = -v := congrArg Neg.neg hve
  have hey' : e * (-y) = -y := by
    calc
      e * (-y) = -(e * y) := by noncomm_ring
      _ = -y := congrArg Neg.neg hey
  have hvv' : (-v) * (-v) = 0 := by simp [hvv]
  have hxv' : x * (-v) = 0 := by simp [hxv]
  have hvx' : (-v) * x = 0 := by simp [hvx]
  have hyy' : (-y) * (-y) = 0 := by simp [hyy]
  have hyu' : (-y) * u = 0 := by simp [hyu]
  have huy' : u * (-y) = 0 := by simp [huy]
  have h := directed_plabic_vertex_contraction hxe hve' hey' heu
    hxx hvv' hxv' hvx' hyy' huu hyu' huy'
  calc
    (1 - x + v) * (e + x - y + u - v) * (1 + y - u) =
        e - (-(x * y) + -(v * u)) - (x * u + v * y) := by
          simpa [sub_eq_add_neg] using h
    _ = e + (x * y + v * u) - (x * u + v * y) := by noncomm_ring

/-- The left and right edge strippers in the three-corner Zorn chain are
two-sided inverses of their opposite-sign unipotent factors. -/
theorem zorn_plabic_edge_strippers_are_invertible
    {P₁ P₂ A₁ C₁ A₂ C₂ : B}
    (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂)
    (h₁₂ : P₁ * P₂ = P₁) (h₂₁ : P₂ * P₁ = P₁) :
    (1 - n12 P₁ P₂ A₁ - n32 P₁ P₂ C₂) *
        (1 + n12 P₁ P₂ A₁ + n32 P₁ P₂ C₂) = 1 ∧
    (1 + n12 P₁ P₂ A₁ + n32 P₁ P₂ C₂) *
        (1 - n12 P₁ P₂ A₁ - n32 P₁ P₂ C₂) = 1 ∧
    (1 - n21 P₁ P₂ C₁ - n23 P₁ P₂ A₂) *
        (1 + n21 P₁ P₂ C₁ + n23 P₁ P₂ A₂) = 1 ∧
    (1 + n21 P₁ P₂ C₁ + n23 P₁ P₂ A₂) *
        (1 - n21 P₁ P₂ C₁ - n23 P₁ P₂ A₂) = 1 := by
  rcases three_corner_laws h₁ h₂ h₁₂ h₂₁ with
    ⟨_, _, _, h12, h21, h13, h31, h23, h32, _⟩
  have hxx : n12 P₁ P₂ A₁ * n12 P₁ P₂ A₁ = 0 := by
    change root12 (e1 P₁) (e2 P₁ P₂) A₁ * root12 (e1 P₁) (e2 P₁ P₂) A₁ = 0
    exact corner_arrows_mul_zero (a := A₁) (b := A₁) h21
  have hvv : n32 P₁ P₂ C₂ * n32 P₁ P₂ C₂ = 0 := by
    change root32 (e3 P₂) (e2 P₁ P₂) C₂ * root32 (e3 P₂) (e2 P₁ P₂) C₂ = 0
    exact corner_arrows_mul_zero (a := C₂) (b := C₂) h23
  have hxv : n12 P₁ P₂ A₁ * n32 P₁ P₂ C₂ = 0 := by
    change root12 (e1 P₁) (e2 P₁ P₂) A₁ * root32 (e3 P₂) (e2 P₁ P₂) C₂ = 0
    exact corner_arrows_mul_zero (a := A₁) (b := C₂) h23
  have hvx : n32 P₁ P₂ C₂ * n12 P₁ P₂ A₁ = 0 := by
    change root32 (e3 P₂) (e2 P₁ P₂) C₂ * root12 (e1 P₁) (e2 P₁ P₂) A₁ = 0
    exact corner_arrows_mul_zero (a := C₂) (b := A₁) h21
  have hyy : n21 P₁ P₂ C₁ * n21 P₁ P₂ C₁ = 0 := by
    change root21 (e2 P₁ P₂) (e1 P₁) C₁ * root21 (e2 P₁ P₂) (e1 P₁) C₁ = 0
    exact corner_arrows_mul_zero (a := C₁) (b := C₁) h12
  have huu : n23 P₁ P₂ A₂ * n23 P₁ P₂ A₂ = 0 := by
    change root23 (e2 P₁ P₂) (e3 P₂) A₂ * root23 (e2 P₁ P₂) (e3 P₂) A₂ = 0
    exact corner_arrows_mul_zero (a := A₂) (b := A₂) h32
  have hyu : n21 P₁ P₂ C₁ * n23 P₁ P₂ A₂ = 0 := by
    change root21 (e2 P₁ P₂) (e1 P₁) C₁ * root23 (e2 P₁ P₂) (e3 P₂) A₂ = 0
    exact corner_arrows_mul_zero (a := C₁) (b := A₂) h12
  have huy : n23 P₁ P₂ A₂ * n21 P₁ P₂ C₁ = 0 := by
    change root23 (e2 P₁ P₂) (e3 P₂) A₂ * root21 (e2 P₁ P₂) (e1 P₁) C₁ = 0
    exact corner_arrows_mul_zero (a := A₂) (b := C₁) h32
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one] <;>
    noncomm_ring [hxx, hvv, hxv, hvx, hyy, huu, hyu, huy]

/-- The untwisted three-corner Plabic contraction is the middle idempotent
minus the two link-return terms and the two-hop endpoint bridge. -/
theorem zorn_plabic_vertex_contraction
    {P₁ P₂ A₁ C₁ A₂ C₂ : B}
    (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂)
    (h₁₂ : P₁ * P₂ = P₁) (h₂₁ : P₂ * P₁ = P₁) :
    (1 - n12 P₁ P₂ A₁ - n32 P₁ P₂ C₂) *
        (e2 P₁ P₂ + chainPhi P₁ P₂ A₁ C₁ A₂ C₂) *
        (1 - n21 P₁ P₂ C₁ - n23 P₁ P₂ A₂) =
      e2 P₁ P₂ -
        (n12 P₁ P₂ A₁ * n21 P₁ P₂ C₁ +
          n32 P₁ P₂ C₂ * n23 P₁ P₂ A₂) -
        phi13 P₁ P₂ A₁ C₁ A₂ C₂ ∧
    (1 - n12 P₁ P₂ A₁ + n32 P₁ P₂ C₂) *
        (e2 P₁ P₂ + j12 P₁ P₂ A₁ C₁ + j23 P₁ P₂ A₂ C₂) *
        (1 + n21 P₁ P₂ C₁ - n23 P₁ P₂ A₂) =
      e2 P₁ P₂ +
        (n12 P₁ P₂ A₁ * n21 P₁ P₂ C₁ +
          n32 P₁ P₂ C₂ * n23 P₁ P₂ A₂) -
        phi13 P₁ P₂ A₁ C₁ A₂ C₂ := by
  rcases three_corner_laws h₁ h₂ h₁₂ h₂₁ with
    ⟨_, he2, _, h12, h21, h13, h31, h23, h32, _⟩
  have hxe : n12 P₁ P₂ A₁ * e2 P₁ P₂ = n12 P₁ P₂ A₁ := by
    dsimp [n12, e1]
    calc
      (P₁ * A₁ * e2 P₁ P₂) * e2 P₁ P₂ =
          P₁ * A₁ * (e2 P₁ P₂ * e2 P₁ P₂) := by noncomm_ring
      _ = P₁ * A₁ * e2 P₁ P₂ := by rw [he2]
  have hve : n32 P₁ P₂ C₂ * e2 P₁ P₂ = n32 P₁ P₂ C₂ := by
    dsimp [n32, e3]
    calc
      ((1 - P₂) * C₂ * e2 P₁ P₂) * e2 P₁ P₂ =
          (1 - P₂) * C₂ * (e2 P₁ P₂ * e2 P₁ P₂) := by noncomm_ring
      _ = (1 - P₂) * C₂ * e2 P₁ P₂ := by rw [he2]
  have hey : e2 P₁ P₂ * n21 P₁ P₂ C₁ = n21 P₁ P₂ C₁ := by
    dsimp [n21, e1, e2]
    calc
      (P₂ - P₁) * ((P₂ - P₁) * C₁ * P₁) =
          (e2 P₁ P₂ * e2 P₁ P₂) * C₁ * P₁ := by dsimp [e2]; noncomm_ring
      _ = (P₂ - P₁) * C₁ * P₁ := by simpa [e2] using congrArg (fun z : B => z * C₁ * P₁) he2
  have heu : e2 P₁ P₂ * n23 P₁ P₂ A₂ = n23 P₁ P₂ A₂ := by
    dsimp [n23, e2, e3]
    calc
      (P₂ - P₁) * ((P₂ - P₁) * A₂ * (1 - P₂)) =
          (e2 P₁ P₂ * e2 P₁ P₂) * A₂ * (1 - P₂) := by dsimp [e2]; noncomm_ring
      _ = (P₂ - P₁) * A₂ * (1 - P₂) := by
        simpa [e2] using congrArg (fun z : B => z * A₂ * (1 - P₂)) he2
  have hxx : n12 P₁ P₂ A₁ * n12 P₁ P₂ A₁ = 0 := by
    change root12 (e1 P₁) (e2 P₁ P₂) A₁ * root12 (e1 P₁) (e2 P₁ P₂) A₁ = 0
    exact corner_arrows_mul_zero (a := A₁) (b := A₁) h21
  have hvv : n32 P₁ P₂ C₂ * n32 P₁ P₂ C₂ = 0 := by
    change root32 (e3 P₂) (e2 P₁ P₂) C₂ * root32 (e3 P₂) (e2 P₁ P₂) C₂ = 0
    exact corner_arrows_mul_zero (a := C₂) (b := C₂) h23
  have hxv : n12 P₁ P₂ A₁ * n32 P₁ P₂ C₂ = 0 := by
    change root12 (e1 P₁) (e2 P₁ P₂) A₁ * root32 (e3 P₂) (e2 P₁ P₂) C₂ = 0
    exact corner_arrows_mul_zero (a := A₁) (b := C₂) h23
  have hvx : n32 P₁ P₂ C₂ * n12 P₁ P₂ A₁ = 0 := by
    change root32 (e3 P₂) (e2 P₁ P₂) C₂ * root12 (e1 P₁) (e2 P₁ P₂) A₁ = 0
    exact corner_arrows_mul_zero (a := C₂) (b := A₁) h21
  have hyy : n21 P₁ P₂ C₁ * n21 P₁ P₂ C₁ = 0 := by
    change root21 (e2 P₁ P₂) (e1 P₁) C₁ * root21 (e2 P₁ P₂) (e1 P₁) C₁ = 0
    exact corner_arrows_mul_zero (a := C₁) (b := C₁) h12
  have huu : n23 P₁ P₂ A₂ * n23 P₁ P₂ A₂ = 0 := by
    change root23 (e2 P₁ P₂) (e3 P₂) A₂ * root23 (e2 P₁ P₂) (e3 P₂) A₂ = 0
    exact corner_arrows_mul_zero (a := A₂) (b := A₂) h32
  have hyu : n21 P₁ P₂ C₁ * n23 P₁ P₂ A₂ = 0 := by
    change root21 (e2 P₁ P₂) (e1 P₁) C₁ * root23 (e2 P₁ P₂) (e3 P₂) A₂ = 0
    exact corner_arrows_mul_zero (a := C₁) (b := A₂) h12
  have huy : n23 P₁ P₂ A₂ * n21 P₁ P₂ C₁ = 0 := by
    change root23 (e2 P₁ P₂) (e3 P₂) A₂ * root21 (e2 P₁ P₂) (e1 P₁) C₁ = 0
    exact corner_arrows_mul_zero (a := A₂) (b := C₁) h32
  have hPath := directed_plabic_vertex_contraction hxe hve hey heu
    hxx hvv hxv hvx hyy huu hyu huy
  have hDual := directed_plabic_signed_vertex_contraction hxe hve hey heu
    hxx hvv hxv hvx hyy huu hyu huy
  constructor
  · simpa only [chainPhi, phi12, phi23, phi13, n13, n31, add_assoc] using hPath
  · simpa only [j12, j23, add_assoc, sub_eq_add_neg, neg_add, neg_neg,
      phi13, n13, n31] using hDual

/-- Corrected A114 connection split for the Kasteleyn-oriented two-link
operators. The source packet's mixed brackets have sign errors: the direct
product carries `+Φ₁₃`, its commutator carries `2 Φ₁₃`, and its
anticommutator vanishes. The other twisted bridge is `J₁₃`, not `Φ₁₃`. -/
theorem corrected_plabic_twisted_connection_split
    {P₁ P₂ A₁ C₁ A₂ C₂ : B}
    (h₁ : P₁ * P₁ = P₁) (h₂ : P₂ * P₂ = P₂)
    (h₁₂ : P₁ * P₂ = P₁) (h₂₁ : P₂ * P₁ = P₁) :
    (j12 P₁ P₂ A₁ C₁ - j23 P₁ P₂ A₂ C₂) *
        chainPhi P₁ P₂ A₁ C₁ A₂ C₂ =
      sig12 P₁ P₂ A₁ C₁ - sig23 P₁ P₂ A₂ C₂ +
        phi13 P₁ P₂ A₁ C₁ A₂ C₂ ∧
    comm (j12 P₁ P₂ A₁ C₁ - j23 P₁ P₂ A₂ C₂)
        (chainPhi P₁ P₂ A₁ C₁ A₂ C₂) =
      (2 : ℤ) • (sig12 P₁ P₂ A₁ C₁ - sig23 P₁ P₂ A₂ C₂ +
        phi13 P₁ P₂ A₁ C₁ A₂ C₂) ∧
    anticomm (j12 P₁ P₂ A₁ C₁ - j23 P₁ P₂ A₂ C₂)
        (chainPhi P₁ P₂ A₁ C₁ A₂ C₂) = 0 ∧
    comm (phi12 P₁ P₂ A₁ C₁ - phi23 P₁ P₂ A₂ C₂)
        (chainPhi P₁ P₂ A₁ C₁ A₂ C₂) =
      (2 : ℤ) • j13 P₁ P₂ A₁ C₁ A₂ C₂ ∧
    anticomm (phi12 P₁ P₂ A₁ C₁ - phi23 P₁ P₂ A₂ C₂)
        (chainPhi P₁ P₂ A₁ C₁ A₂ C₂) =
      (2 : ℤ) • (v12 P₁ P₂ A₁ C₁ - v23 P₁ P₂ A₂ C₂) ∧
    comm (j12 P₁ P₂ A₁ C₁ - j23 P₁ P₂ A₂ C₂)
        (phi12 P₁ P₂ A₁ C₁ - phi23 P₁ P₂ A₂ C₂) =
      (2 : ℤ) • (sig12 P₁ P₂ A₁ C₁ + sig23 P₁ P₂ A₂ C₂) ∧
    comm (chainJ P₁ P₂ A₁ C₁ A₂ C₂)
        (chainPhi P₁ P₂ A₁ C₁ A₂ C₂) =
      (2 : ℤ) • (sig12 P₁ P₂ A₁ C₁ + sig23 P₁ P₂ A₂ C₂) := by
  rcases three_corner_laws h₁ h₂ h₁₂ h₂₁ with
    ⟨he1, he2, he3, h12, h21, h13, h31, h23, h32, hsum⟩
  let x := n12 P₁ P₂ A₁
  let y := n21 P₁ P₂ C₁
  let u := n23 P₁ P₂ A₂
  let v := n32 P₁ P₂ C₂
  have hxx : x * x = 0 := by
    change root12 (e1 P₁) (e2 P₁ P₂) A₁ * root12 (e1 P₁) (e2 P₁ P₂) A₁ = 0
    exact corner_arrows_mul_zero (a := A₁) (b := A₁) h21
  have hyy : y * y = 0 := by
    change root21 (e2 P₁ P₂) (e1 P₁) C₁ * root21 (e2 P₁ P₂) (e1 P₁) C₁ = 0
    exact corner_arrows_mul_zero (a := C₁) (b := C₁) h12
  have huu : u * u = 0 := by
    change root23 (e2 P₁ P₂) (e3 P₂) A₂ * root23 (e2 P₁ P₂) (e3 P₂) A₂ = 0
    exact corner_arrows_mul_zero (a := A₂) (b := A₂) h32
  have hvv : v * v = 0 := by
    change root32 (e3 P₂) (e2 P₁ P₂) C₂ * root32 (e3 P₂) (e2 P₁ P₂) C₂ = 0
    exact corner_arrows_mul_zero (a := C₂) (b := C₂) h23
  have hxv : x * v = 0 := by
    change root12 (e1 P₁) (e2 P₁ P₂) A₁ * root32 (e3 P₂) (e2 P₁ P₂) C₂ = 0
    exact corner_arrows_mul_zero (a := A₁) (b := C₂) h23
  have hyu : y * u = 0 := by
    change root21 (e2 P₁ P₂) (e1 P₁) C₁ * root23 (e2 P₁ P₂) (e3 P₂) A₂ = 0
    exact corner_arrows_mul_zero (a := C₁) (b := A₂) h12
  have hux : u * x = 0 := by
    change root23 (e2 P₁ P₂) (e3 P₂) A₂ * root12 (e1 P₁) (e2 P₁ P₂) A₁ = 0
    exact corner_arrows_mul_zero (a := A₂) (b := A₁) h31
  have huy : u * y = 0 := by
    change root23 (e2 P₁ P₂) (e3 P₂) A₂ * root21 (e2 P₁ P₂) (e1 P₁) C₁ = 0
    exact corner_arrows_mul_zero (a := A₂) (b := C₁) h32
  have hvx : v * x = 0 := by
    change root32 (e3 P₂) (e2 P₁ P₂) C₂ * root12 (e1 P₁) (e2 P₁ P₂) A₁ = 0
    exact corner_arrows_mul_zero (a := C₂) (b := A₁) h21
  have hyv : y * v = 0 := by
    change root21 (e2 P₁ P₂) (e1 P₁) C₁ * root32 (e3 P₂) (e2 P₁ P₂) C₂ = 0
    exact corner_arrows_mul_zero (a := C₁) (b := C₂) h13
  have hDirected := directed_plabic_twisted_connection_laws
    hxx hyy huu hvv hxv hyu hux huy hvx hyv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ((x - y) - (u - v)) * ((x + y) + (u + v)) = _
    simpa [sig12, sig23, phi13, n13, n31, x, y, u, v] using hDirected.1
  · change comm ((x - y) - (u - v)) ((x + y) + (u + v)) = _
    simpa [comm, sig12, sig23, phi13, n13, n31, x, y, u, v] using hDirected.2.1
  · change anticomm ((x - y) - (u - v)) ((x + y) + (u + v)) = 0
    simpa [anticomm, x, y, u, v] using hDirected.2.2.1
  · change comm ((x + y) - (u + v)) ((x + y) + (u + v)) = _
    simpa [comm, j13, n13, n31, x, y, u, v] using hDirected.2.2.2.1
  · change anticomm ((x + y) - (u + v)) ((x + y) + (u + v)) = _
    simpa [anticomm, v12, v23, x, y, u, v] using hDirected.2.2.2.2.1
  · change comm ((x - y) - (u - v)) ((x + y) - (u + v)) = _
    simpa [comm, sig12, sig23, x, y, u, v] using hDirected.2.2.2.2.2.1
  · change comm ((x - y) + (u - v)) ((x + y) + (u + v)) = _
    simpa [comm, sig12, sig23, chainJ, chainPhi, phi12, j12, phi23, j23,
      x, y, u, v] using hDirected.2.2.2.2.2.2

end InfoGeometry.OperatorAlgebra.PeirceSpine.ZornKitaevMajoranaChainFull
