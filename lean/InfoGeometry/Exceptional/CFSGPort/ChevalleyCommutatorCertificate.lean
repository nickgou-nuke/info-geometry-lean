/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Local Lean 4.34.1 adaptation of the finite root-cone certificate interface
from `CFSG.LieType.Chevalley.RootOps.Poly`. This first slice ports the G₂
commutator factor table and checks its sparse operator-polynomial identity.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleySparsePolynomial
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootOperatorTables
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootOperatorMirror
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyFastWeylTables
public import InfoGeometry.Exceptional.CFSGPort.ChevalleyCommutatorData

public section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

@[expose] def nilpE (τ : Tag) (g : ℕ) (C : ℤ) (ea eb : ℕ) : List PEntry :=
  [1, 2, 3].flatMap fun k => (entries τ g k).map fun e =>
    ((k * ea, k * eb), (e.1, e.2.1, C ^ k * e.2.2))

@[expose] def factorsN (τ : Tag) : List PEntry → List Factor → List PEntry
  | acc, [] => acc
  | acc, f :: fs =>
      factorsN τ (mul1 acc (nilpE τ f.2.2.1 f.2.2.2 f.1 f.2.1)) fs

@[expose] def coneOk (τ : Tag) (a b : ℕ) (f : Factor) : Bool :=
  Nat.blt f.2.2.1 τ.rootCertificate.roots.length &&
    Nat.ble 1 f.1 && Nat.ble 1 f.2.1 &&
    Mirror.vecBEq (τ.rootCertificate.root f.2.2.1)
      (f.1 • τ.rootCertificate.root a + f.2.1 • τ.rootCertificate.root b)

@[expose] def repCheck (τ : Tag) (a b : ℕ) (fs : List Factor) : Bool :=
  Nat.blt a τ.rootCertificate.roots.length &&
    Nat.blt b τ.rootCertificate.roots.length &&
    fs.all (coneOk τ a b) &&
    pEqCheck (mul1 (nilpE τ a 1 1 0) (nilpE τ b 1 0 1))
      (mul1 (mul1 (factorsN τ [] fs) (nilpE τ b 1 0 1))
        (nilpE τ a 1 1 0))

@[expose] def reps : Tag → List (ℕ × ℕ × List Factor)
  | .G2 => g2Reps
  | .F4 => f4Reps
  | .D4 => d4Reps
  | .E6 => e6Reps
  | .E7 => e7Reps
  | .E8 => e8Reps

@[expose] def cover : Tag → List ℕ
  | .G2 => g2Cover
  | .F4 => f4Cover
  | .D4 => d4Cover
  | .E6 => e6Cover
  | .E7 => e7Cover
  | .E8 => e8Cover

@[expose] def walkPair (τ : Tag) (w : List (Fin τ.rank)) (p : ℕ × ℕ) : ℕ × ℕ :=
  w.foldr (fun s x => (imgPar τ s x.1 / 2, imgPar τ s x.2 / 2)) p

@[expose] def walkRoot (τ : Tag) (w : List (Fin τ.rank))
    (α : Fin τ.rank → ℤ) : Fin τ.rank → ℤ :=
  w.foldr (fun i v => reflect τ i v) α

variable {τ : Tag}

theorem walkPair_root_spec (htab : tabCheck τ = true) (w : List (Fin τ.rank))
    {a : ℕ} (ha : a < τ.rootCertificate.roots.length)
    {b : ℕ} (hb : b < τ.rootCertificate.roots.length) :
    (walkPair τ w (a, b)).1 < τ.rootCertificate.roots.length ∧
      (walkPair τ w (a, b)).2 < τ.rootCertificate.roots.length ∧
      τ.rootCertificate.root (walkPair τ w (a, b)).1 =
        walkRoot τ w (τ.rootCertificate.root a) ∧
      τ.rootCertificate.root (walkPair τ w (a, b)).2 =
        walkRoot τ w (τ.rootCertificate.root b) := by
  induction w with
  | nil => simpa [walkPair, walkRoot] using ⟨ha, hb⟩
  | cons i w ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      simp only [walkPair, List.foldr_cons, walkRoot, List.foldr_cons] at h1 h2 h3 h4 ⊢
      rw [imgPar_div_two htab h1, imgPar_div_two htab h2]
      exact ⟨rootCertificate_image_lt h1 i, rootCertificate_image_lt h2 i,
        (rootCertificate_root_image h1 i).trans (congrArg (reflect τ i) h3),
        (rootCertificate_root_image h2 i).trans (congrArg (reflect τ i) h4)⟩

@[expose] def decodeWord (τ : Tag) : ℕ → ℕ → List (Fin τ.rank)
  | 0, _ => []
  | fuel + 1, code =>
      if code = 0 then []
      else if h : code % 16 - 1 < τ.rank then
        ⟨code % 16 - 1, h⟩ :: decodeWord τ fuel (code / 16)
      else decodeWord τ fuel (code / 16)

@[expose] def neededPairs (τ : Tag) : List (ℕ × ℕ) :=
  (List.finRange τ.rank).flatMap fun i =>
    (List.range τ.rootCertificate.roots.length).filterMap fun m =>
      if decide (0 < height (τ.rootCertificate.root m)) && !(m == (i : ℕ)) then
        some ((i : ℕ), m) else none

@[expose] def coverPair (e : ℕ) : ℕ × ℕ := (e % 16, e / 16 % 256)

@[expose] def coverRep (e : ℕ) : ℕ := e / 4096 % 16

@[expose] def coverWord (e : ℕ) : ℕ := e / 65536

@[expose] def repPair (rs : List (ℕ × ℕ × List Factor)) (r : ℕ) : ℕ × ℕ :=
  ((rs.getD r (0, 0, [])).1, (rs.getD r (0, 0, [])).2.1)

@[expose] def coverCheck (τ : Tag) (rs : List (ℕ × ℕ × List Factor))
    (cs : List ℕ) : Bool :=
  cs.map coverPair == neededPairs τ &&
    cs.all fun e => Nat.blt (coverRep e) rs.length &&
      walkPair τ (decodeWord τ 64 (coverWord e)) (repPair rs (coverRep e)) == coverPair e

@[expose] def repsCheck (τ : Tag) (rs : List (ℕ × ℕ × List Factor)) : Bool :=
  rs.all fun r => repCheck τ r.1 r.2.1 r.2.2

theorem exceptional_coverCheck (τ : Tag) : coverCheck τ (reps τ) (cover τ) = true := by
  cases τ <;> decide +kernel

theorem f4_repsCheck :
    f4Reps.all (fun r => repCheck .F4 r.1 r.2.1 r.2.2) = true := by
  decide +kernel

theorem d4_repsCheck :
    d4Reps.all (fun r => repCheck .D4 r.1 r.2.1 r.2.2) = true := by
  decide +kernel

theorem e6_repsCheck :
    e6Reps.all (fun r => repCheck .E6 r.1 r.2.1 r.2.2) = true := by
  decide +kernel

theorem e7_repsCheck :
    e7Reps.all (fun r => repCheck .E7 r.1 r.2.1 r.2.2) = true := by
  decide +kernel

theorem e8_repsCheck :
    e8Reps.all (fun r => repCheck .E8 r.1 r.2.1 r.2.2) = true := by
  decide +kernel

theorem g2_coneCheck :
    g2Reps.all (fun r => r.2.2.all (coneOk .G2 r.1 r.2.1)) = true := by
  decide +kernel

theorem g2_polynomialCheck :
    g2Reps.all (fun r =>
      pEqCheck
        (mul1 (nilpE .G2 r.1 1 1 0) (nilpE .G2 r.2.1 1 0 1))
        (mul1 (mul1 (factorsN .G2 [] r.2.2) (nilpE .G2 r.2.1 1 0 1))
          (nilpE .G2 r.1 1 1 0))) = true := by
  decide +kernel

theorem g2_repsCheck :
    g2Reps.all (fun r => repCheck .G2 r.1 r.2.1 r.2.2) = true := by
  decide +kernel

theorem exceptional_repsCheck (τ : Tag) :
    repsCheck τ (reps τ) = true := by
  cases τ with
  | G2 => simpa only [reps, repsCheck] using g2_repsCheck
  | F4 => simpa only [reps, repsCheck] using f4_repsCheck
  | D4 => simpa only [reps, repsCheck] using d4_repsCheck
  | E6 => simpa only [reps, repsCheck] using e6_repsCheck
  | E7 => simpa only [reps, repsCheck] using e7_repsCheck
  | E8 => simpa only [reps, repsCheck] using e8_repsCheck

theorem operator_polynomial_commutation_of_repCheck {τ : Tag} {a b : ℕ}
    {fs : List Factor} (hrep : repCheck τ a b fs = true)
    {R : Type*} [CommRing R] (s t : R) :
    pOp τ R (mul1 (nilpE τ a 1 1 0) (nilpE τ b 1 0 1)) s t =
      pOp τ R (mul1 (mul1 (factorsN τ [] fs) (nilpE τ b 1 0 1))
        (nilpE τ a 1 1 0)) s t := by
  have hpoly :
      pEqCheck
        (mul1 (nilpE τ a 1 1 0) (nilpE τ b 1 0 1))
        (mul1 (mul1 (factorsN τ [] fs) (nilpE τ b 1 0 1))
          (nilpE τ a 1 1 0)) = true := by
    have hfields := hrep
    simp only [repCheck, Bool.and_eq_true] at hfields
    exact hfields.2
  exact pOp_eq_of_pEqCheck (τ := τ) hpoly s t

end InfoGeometry.Exceptional.CFSGPort.Chevalley.RootOps

end
