/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.SuperGrassmannian.GraphChartTransition
import InfoGeometry.Topology.KleinBrillouinBase
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Tactic

/-!
# Null operators, signed graph inversion and the Klein cover

The inverse chart is a chart on actual submodules, not a totalized scalar
reciprocal. Signed exchange has square -I on vectors but acts involutively
on submodules. Nonzero square-zero operators leave the graph chart. The
existing Klein glide is lifted with its translation and fiber sign kept
separate. This is an explicit transport law, not a Pin-bundle classification.
-/

noncomputable section
namespace InfoGeometry.OperatorAlgebra.ProjectiveNullInversion

open InfoGeometry.SuperGrassmannian.GraphChartTransition

section Graphs
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

def signedSwap : (V × V) ≃ₗ[R] (V × V) where
  toFun z := (-z.2, z.1)
  invFun z := (z.2, -z.1)
  left_inv z := by simp
  right_inv z := by simp
  map_add' z w := by simp [add_comm]
  map_smul' c z := by simp

@[simp] theorem signedSwap_apply (z : V × V) : signedSwap (R := R) z = (-z.2, z.1) := rfl

theorem signedSwap_square (z : V × V) :
    signedSwap (R := R) (signedSwap (R := R) z) = -z := rfl

/-- Only passage to submodules forgets the central vector sign. -/
theorem signedSwap_map_twice (S : Submodule R (V × V)) :
    (S.map (signedSwap (R := R)).toLinearMap).map
      (signedSwap (R := R)).toLinearMap = S := by
  ext z
  constructor
  · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    change -y ∈ S
    exact S.neg_mem hy
  · intro hz
    refine ⟨signedSwap (-z), ⟨-z, S.neg_mem hz, rfl⟩, ?_⟩
    change -(-z) = z
    exact neg_neg z

/-- The ordered inverse of an operator, on its genuine invertible chart. -/
theorem signedSwap_graph_inverse (u : V ≃ₗ[R] V) :
    u.toLinearMap.graph.map (signedSwap (R := R)).toLinearMap =
      (-u.symm.toLinearMap).graph := by
  apply (map_graph_eq_iff _ _ _).mpr
  constructor
  · intro x
    change x = -u.symm (-u x)
    simp
  · intro y
    refine ⟨u.symm (-y), ?_⟩
    change -(u (u.symm (-y))) = y
    simp

theorem signedSwap_graph_chart_iff (f : Module.End R V) :
    (∃ g : Module.End R V,
        f.graph.map (signedSwap (R := R)).toLinearMap = g.graph) ↔
      Function.Bijective f := by
  rw [exists_map_graph_iff _ (signedSwap (R := R)).injective]
  change Function.Bijective (fun x => -f x) ↔ Function.Bijective f
  constructor
  · rintro ⟨hi, hs⟩
    constructor
    · intro x y h
      exact hi (congrArg Neg.neg h)
    · intro y
      obtain ⟨x, hx⟩ := hs (-y)
      exact ⟨x, neg_injective hx⟩
  · rintro ⟨hi, hs⟩
    constructor
    · intro x y h
      exact hi (neg_injective h)
    · intro y
      obtain ⟨x, hx⟩ := hs (-y)
      exact ⟨x, by simp [hx]⟩

/-- A nonzero nilpotent channel is an inverse-chart boundary. -/
theorem square_zero_exits_graph_chart (f : Module.End R V)
    (hf : f ≠ 0) (hsq : f * f = 0) (g : Module.End R V) :
    f.graph.map (signedSwap (R := R)).toLinearMap ≠ g.graph := by
  intro h
  have hi := ((signedSwap_graph_chart_iff f).mp ⟨g, h⟩).1
  apply hf
  ext x
  have hx : f (f x) = f 0 := by
    have hh := LinearMap.congr_fun hsq x
    simpa using hh
  exact hi hx

theorem zero_graph_to_vertical :
    (0 : Module.End R V).graph.map signedSwap.toLinearMap =
      LinearMap.ker (LinearMap.fst R V V) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x.2 = (0 : Module.End R V) x.1 at hx
    change -x.2 = 0
    simp [hx]
  · intro hz
    change z.1 = 0 at hz
    refine ⟨(z.2, 0), rfl, ?_⟩
    exact Prod.ext (by simpa using hz.symm) rfl

end Graphs

section Clifford
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- A named Clifford generator, used to state the graded anticommutation law. -/
def cliffordGenerator (Q : QuadraticForm R V) (v : V) : CliffordAlgebra Q :=
  CliffordAlgebra.ι Q v

/-- Orthogonal Clifford generators anticommute; this is the explicit noncommutative
operator relation available without assuming that every quadratic form is nondegenerate. -/
theorem cliffordGenerators_orthogonal_anticommute :
    ∀ (Q : QuadraticForm R V) (v w : V),
      QuadraticMap.polar Q v w = 0 →
        cliffordGenerator Q v * cliffordGenerator Q w +
          cliffordGenerator Q w * cliffordGenerator Q v = 0 := by
  intro Q v w hpolar
  have h := CliffordAlgebra.ι_mul_ι_add_swap (Q := Q) v w
  rw [hpolar, map_zero] at h
  simpa [cliffordGenerator] using h

/-- The anticommutator law as a carrier-level witness for pairs of orthogonal generators. -/
theorem orthogonal_generator_pair_anticommutes :
    ∀ (Q : QuadraticForm R V) (a b : CliffordAlgebra Q),
      (∃ v w, a = cliffordGenerator Q v ∧ b = cliffordGenerator Q w ∧
        QuadraticMap.polar Q v w = 0) → a * b + b * a = 0 := by
  rintro Q a b ⟨v, w, rfl, rfl, hpolar⟩
  exact cliffordGenerators_orthogonal_anticommute Q v w hpolar

/-- Left multiplication by a native Clifford generator on the Clifford algebra. -/
def cliffordLeft (Q : QuadraticForm R V) (v : V) : Module.End R (CliffordAlgebra Q) where
  toFun a := CliffordAlgebra.ι Q v * a
  map_add' a b := mul_add _ _ _
  map_smul' c a := by simp [mul_smul_comm]

theorem cliffordLeft_square (Q : QuadraticForm R V) (v : V) :
    cliffordLeft Q v * cliffordLeft Q v = (Q v) • (1 : Module.End R (CliffordAlgebra Q)) := by
  ext a
  change CliffordAlgebra.ι Q v * (CliffordAlgebra.ι Q v * a) = (Q v) • a
  rw [← mul_assoc, CliffordAlgebra.ι_sq_scalar, Algebra.smul_def]

theorem cliffordLeft_ne_zero (Q : QuadraticForm R V) (v : V)
    (hv : CliffordAlgebra.ι Q v ≠ 0) : cliffordLeft Q v ≠ 0 := by
  intro h
  have hh := LinearMap.congr_fun h 1
  exact hv (by simpa [cliffordLeft] using hh)

/-- The null cone maps into the square-zero cone of an operator algebra. -/
theorem clifford_null_graph_boundary (Q : QuadraticForm R V) (v : V)
    (hQ : Q v = 0) (hv : CliffordAlgebra.ι Q v ≠ 0)
    (g : Module.End R (CliffordAlgebra Q)) :
    (cliffordLeft Q v).graph.map (signedSwap (R := R)).toLinearMap ≠ g.graph := by
  apply square_zero_exits_graph_chart _ (cliffordLeft_ne_zero Q v hv)
  rw [cliffordLeft_square, hQ, zero_smul]

end Clifford

section KleinCover
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
open KleinBrillouinBase

/-- Lift the existing affine glide to the doubled operator-module carrier. -/
def signedGlide (p : Cover × (V × V)) : Cover × (V × V) :=
  (glide p.1, signedSwap (R := R) p.2)

/-- The axial translation survives; the fiber independently acquires a minus sign. -/
theorem signedGlide_square (p : Cover × (V × V)) :
    signedGlide (R := R) (signedGlide (R := R) p) = (tx p.1, -p.2) := by
  change (glide (glide p.1), signedSwap (R := R) (signedSwap p.2)) = _
  rw [glide_sq, signedSwap_square (R := R)]

/-- Equivariance is across base points, not a pointwise parity eigenvector. -/
theorem equivariant_translation_sign (ψ : Cover → V × V)
    (hψ : ∀ k, ψ (glide k) = signedSwap (R := R) (ψ k)) (k : Cover) :
    ψ (tx k) = -ψ k := by
  rw [← glide_sq, hψ, hψ, signedSwap_square (R := R)]

/-- A globally pure sector cannot satisfy a sector-exchanging glide law. -/
theorem equivariant_pure_sector_zero (ψ : Cover → V × V)
    (hψ : ∀ k, ψ (glide k) = signedSwap (R := R) (ψ k))
    (hpure : ∀ k, (ψ k).2 = 0) : ψ = 0 := by
  funext k
  apply Prod.ext
  · have hh := congrArg Prod.snd (hψ k)
    change (ψ (glide k)).2 = (ψ k).1 at hh
    exact hh.symm.trans (hpure (glide k))
  · exact hpure k

end KleinCover

end InfoGeometry.OperatorAlgebra.ProjectiveNullInversion
