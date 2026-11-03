/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Tactic.NoncommRing

/-!
# Finite Zorn-chain corner algebra and Majorana-style composites

This file records the associative-ring identities for a three-corner path.
The word “Majorana-style” refers only to the displayed sum/difference
operators; no involution, CAR representation, Hamiltonian dynamics, spectral
gap, or topological phase is assumed here.
-/

namespace InfoGeometry.OperatorAlgebra.PeirceSpine.ZornKitaevMajoranaChain

variable {B : Type*} [Ring B]

def bracket (x y : B) : B := x * y - y * x
def antibracket (x y : B) : B := x * y + y * x

def phi (n m : B) : B := n + m
def jop (n m : B) : B := n - m
def metric (n m : B) : B := antibracket n m
def spin (n m : B) : B := bracket n m

def edgePhi (a b : B) : B := a + b
def edgeJ (a b : B) : B := a - b

def chainPhi (a b c d : B) : B := a + b + c + d
def chainJ (a b c d : B) : B := a - b + c - d

/-- The alternating parity element on a three-corner decomposition. -/
def plabicParity (e f g : B) : B := e - f + g

/-- On an orthogonal three-idempotent partition, the alternating parity is an
involution and acts with signs `(+1,-1,+1)` from both sides. -/
theorem plabic_parity_three_corner_laws {e f g : B}
    (he : e * e = e) (hf : f * f = f) (hg : g * g = g)
    (hef : e * f = 0) (hfe : f * e = 0)
    (heg : e * g = 0) (hge : g * e = 0)
    (hfg : f * g = 0) (hgf : g * f = 0)
    (hsum : e + f + g = 1) :
    plabicParity e f g * plabicParity e f g = 1 ∧
    plabicParity e f g * e = e ∧ e * plabicParity e f g = e ∧
    plabicParity e f g * f = -f ∧ f * plabicParity e f g = -f ∧
    plabicParity e f g * g = g ∧ g * plabicParity e f g = g := by
  dsimp [plabicParity]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      (e - f + g) * (e - f + g) = e + f + g := by
        noncomm_ring [he, hf, hg, hef, hfe, heg, hge, hfg, hgf]
      _ = 1 := hsum
  · noncomm_ring [he, hf, hg, hef, hfe, heg, hge, hfg, hgf]
  · noncomm_ring [he, hf, hg, hef, hfe, heg, hge, hfg, hgf]
  · noncomm_ring [he, hf, hg, hef, hfe, heg, hge, hfg, hgf]
  · noncomm_ring [he, hf, hg, hef, hfe, heg, hge, hfg, hgf]
  · noncomm_ring [he, hf, hg, hef, hfe, heg, hge, hfg, hgf]
  · noncomm_ring [he, hf, hg, hef, hfe, heg, hge, hfg, hgf]

/-- One square-zero directed corner pair gives the split-signature
sum/difference identities; `n*m` and `m*n` are retained as operators. -/
theorem directed_pair_tetraktys {n m : B}
    (hn : n * n = 0) (hm : m * m = 0) :
    phi n m * phi n m = metric n m ∧
    jop n m * jop n m = -metric n m ∧
    antibracket (phi n m) (jop n m) = 0 ∧
    jop n m * phi n m = spin n m := by
  dsimp [phi, jop, metric, spin, antibracket, bracket]
  constructor
  · noncomm_ring [hn, hm]
  constructor
  · noncomm_ring [hn, hm]
  constructor
  · noncomm_ring [hn, hm]
  · noncomm_ring [hn, hm]

/-- The exact four-corner cancellation hypotheses for two consecutive
oriented links. They are precisely the vanishing mixed products; the two
composable products `n*o` and `p*m` are not assumed zero. -/
theorem adjacent_link_products {n m o p : B}
    (hnp : n * p = 0) (hmo : m * o = 0) (hmp : m * p = 0)
    (hon : o * n = 0) (hom : o * m = 0) (hpn : p * n = 0) :
    phi n m * phi o p = n * o + m * p ∧
    jop n m * jop o p = n * o + m * p ∧
    phi o p * phi n m = p * m + o * m ∧
    jop o p * jop n m = p * m + o * m ∧
    antibracket (phi n m) (phi o p) = edgePhi (n * o) (p * m) ∧
    bracket (phi n m) (phi o p) = edgeJ (n * o) (p * m) ∧
    bracket (phi n m) (jop o p) = edgePhi (n * o) (p * m) ∧
    antibracket (phi n m) (jop o p) = edgeJ (n * o) (p * m) := by
  dsimp [phi, jop, edgePhi, edgeJ, antibracket, bracket]
  repeat' constructor <;> noncomm_ring [hnp, hmo, hmp, hon, hom, hpn] <;> simp

/-- The two-link sum/difference operators separate the local corner metrics
from the directed end-to-end products. This identity uses explicit corner
cancellation laws and makes no CAR normalization or spectral claim. -/
theorem two_link_chain_quadratic_split {n m o p : B}
    (hnn : n * n = 0) (hmm : m * m = 0)
    (hoo : o * o = 0) (hpp : p * p = 0)
    (hnp : n * p = 0) (hmo : m * o = 0) (hmp : m * p = 0)
    (hon : o * n = 0) (hom : o * m = 0) (hpn : p * n = 0) :
    chainPhi n m o p * chainPhi n m o p =
        metric n m + metric o p + edgePhi (n * o) (p * m) ∧
    chainJ n m o p * chainJ n m o p =
        -(metric n m + metric o p) + edgePhi (n * o) (p * m) ∧
    antibracket (chainPhi n m o p) (chainJ n m o p) =
        (2 : ℤ) • edgeJ (n * o) (p * m) := by
  dsimp [chainPhi, chainJ, metric, edgePhi, edgeJ, antibracket]
  refine ⟨?_, ?_, ?_⟩ <;>
    noncomm_ring [hnn, hmm, hoo, hpp, hnp, hmo, hmp, hon, hom, hpn]

/-- A parity element acting with opposite signs on the two supporting corners
anticommutes with every operator between those corners. -/
theorem corner_parity_anticommutes {s e f x : B}
    (hleft : s * e = e) (hright : f * s = -f) :
    antibracket s (e * x * f) = 0 := by
  dsimp [antibracket]
  have hl : s * (e * x * f) = e * x * f := by
    calc
      s * (e * x * f) = (s * e) * x * f := by noncomm_ring
      _ = e * x * f := by rw [hleft]
  have hr : (e * x * f) * s = -(e * x * f) := by
    calc
      (e * x * f) * s = e * x * (f * s) := by noncomm_ring
      _ = e * x * (-f) := by rw [hright]
      _ = -(e * x * f) := by noncomm_ring
  rw [hl, hr]
  simp

/-- An operator supported between two corners on which parity has the same
left and right eigenvalue is fixed under parity multiplication on both sides.
This covers the two-end bridge when both endpoints have even parity. -/
theorem corner_parity_fixes_bridge {s e f x : B}
    (hleft : s * e = e) (hright : f * s = f) :
    s * (e * x * f) = e * x * f ∧ (e * x * f) * s = e * x * f := by
  constructor
  · calc
      s * (e * x * f) = (s * e) * x * f := by noncomm_ring
      _ = e * x * f := by rw [hleft]
  · calc
      (e * x * f) * s = e * x * (f * s) := by noncomm_ring
      _ = e * x * f := by rw [hright]

end InfoGeometry.OperatorAlgebra.PeirceSpine.ZornKitaevMajoranaChain
