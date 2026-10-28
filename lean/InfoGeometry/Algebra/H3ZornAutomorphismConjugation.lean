/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.BaezF4H3Zorn
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Conjugation on the split Albert derivation algebra

Every existing `H3ZornJordanAut` acts on the full endomorphism algebra through
Mathlib's `LinearEquiv.lieConj`.  Product preservation identifies the conjugates
of left Jordan multiplication and its commutators.  It also preserves every
Leibniz derivation, so conjugation restricts to a native Lie equivalence of the
existing `H3ZornF4Derivations`.

The operator bracket here is the left-composition convention `[D,E] = DE - ED`.
All assertions use the full real split Albert algebra `H3Zorn ℝ`.
-/

noncomputable section

namespace InfoGeometry.Algebra

open H3Zorn

attribute [local instance 100] LieRing.ofAssociativeRing

namespace H3ZornJordanAut

/-- A Jordan automorphism conjugates left multiplication by `x` to left
multiplication by its image. -/
@[simp] theorem lieConj_jordanLmul (g : H3ZornJordanAut) (x : H3Zorn ℝ) :
    g.toLinearEquiv.lieConj (jordanLmul (R := ℝ) x) =
      jordanLmul (R := ℝ) (g x) := by
  apply LinearMap.ext
  intro y
  change g (x * g.toLinearEquiv.symm y) = g x * y
  rw [g.map_mul]
  change g x * g.toLinearEquiv (g.toLinearEquiv.symm y) = g x * y
  rw [g.toLinearEquiv.apply_symm_apply]

/-- The actual noncommutative commutator of two left multiplication operators
transforms covariantly under every Jordan automorphism. -/
@[simp] theorem lieConj_jordanInnerDerivation
    (g : H3ZornJordanAut) (a b : H3Zorn ℝ) :
    g.toLinearEquiv.lieConj (jordanInnerDerivation (R := ℝ) a b) =
      jordanInnerDerivation (R := ℝ) (g a) (g b) := by
  change g.toLinearEquiv.lieConj
      ⁅jordanLmul (R := ℝ) a, jordanLmul (R := ℝ) b⁆ =
    ⁅jordanLmul (R := ℝ) (g a), jordanLmul (R := ℝ) (g b)⁆
  rw [LieEquiv.map_lie, lieConj_jordanLmul, lieConj_jordanLmul]

/-- Conjugation transports the already bundled split-Albert inner derivation. -/
@[simp] theorem lieConj_h3ZornJordanInnerDerivation
    (g : H3ZornJordanAut) (a b : H3Zorn ℝ) :
    g.toLinearEquiv.lieConj
        (h3ZornJordanInnerDerivation a b : Module.End ℝ (H3Zorn ℝ)) =
      (h3ZornJordanInnerDerivation (g a) (g b) : Module.End ℝ (H3Zorn ℝ)) :=
  lieConj_jordanInnerDerivation g a b

/-- Conjugating a Leibniz derivation by a Jordan automorphism again satisfies
the Leibniz rule for the actual split-Albert product. -/
theorem lieConj_mem_F4 (g : H3ZornJordanAut)
    {D : Module.End ℝ (H3Zorn ℝ)} (hD : D ∈ H3ZornF4Derivations) :
    g.toLinearEquiv.lieConj D ∈ H3ZornF4Derivations := by
  intro x y
  obtain ⟨a, rfl⟩ := g.toLinearEquiv.surjective x
  obtain ⟨b, rfl⟩ := g.toLinearEquiv.surjective y
  have hmul : g.toLinearEquiv a * g.toLinearEquiv b =
      g.toLinearEquiv (a * b) := (g.map_mul a b).symm
  rw [hmul]
  simp only [LinearEquiv.lieConj_apply, LinearEquiv.conj_apply_apply,
    LinearEquiv.symm_apply_apply]
  rw [hD a b, map_add]
  change g (D a * b) + g (a * D b) =
    g (D a) * g b + g a * g (D b)
  rw [g.map_mul, g.map_mul]

/-- Derivation membership is equivalent before and after conjugation. -/
@[simp] theorem lieConj_mem_F4_iff (g : H3ZornJordanAut)
    (D : Module.End ℝ (H3Zorn ℝ)) :
    g.toLinearEquiv.lieConj D ∈ H3ZornF4Derivations ↔
      D ∈ H3ZornF4Derivations := by
  constructor
  · intro hD
    have h := lieConj_mem_F4 g⁻¹ hD
    change g.toLinearEquiv.lieConj.symm
      (g.toLinearEquiv.lieConj D) ∈ H3ZornF4Derivations at h
    simpa only [LieEquiv.symm_apply_apply] using h
  · exact lieConj_mem_F4 g

/-- The image of the existing derivation Lie subalgebra under conjugation is
exactly that same subalgebra. -/
theorem map_F4_lieConj (g : H3ZornJordanAut) :
    H3ZornF4Derivations.map g.toLinearEquiv.lieConj.toLieHom =
      H3ZornF4Derivations := by
  ext D
  rw [LieSubalgebra.mem_map]
  constructor
  · rintro ⟨E, hE, rfl⟩
    exact lieConj_mem_F4 g hE
  · intro hD
    refine ⟨g.toLinearEquiv.lieConj.symm D, ?_, ?_⟩
    · apply (lieConj_mem_F4_iff g _).mp
      simpa only [LieEquiv.apply_symm_apply] using hD
    · exact g.toLinearEquiv.lieConj.apply_symm_apply D

/-- The native Lie equivalence on the full split-Albert derivation algebra
induced by a Jordan automorphism. -/
def derivationLieEquiv (g : H3ZornJordanAut) :
    H3ZornF4Derivations ≃ₗ⁅ℝ⁆ H3ZornF4Derivations :=
  g.toLinearEquiv.lieConj.ofSubalgebras
    H3ZornF4Derivations H3ZornF4Derivations (map_F4_lieConj g)

@[simp] theorem derivationLieEquiv_apply
    (g : H3ZornJordanAut) (D : H3ZornF4Derivations) :
    (derivationLieEquiv g D : Module.End ℝ (H3Zorn ℝ)) =
      g.toLinearEquiv.lieConj (D : Module.End ℝ (H3Zorn ℝ)) := rfl

@[simp] theorem derivationLieEquiv_symm_apply
    (g : H3ZornJordanAut) (D : H3ZornF4Derivations) :
    ((derivationLieEquiv g).symm D : Module.End ℝ (H3Zorn ℝ)) =
      g.toLinearEquiv.lieConj.symm (D : Module.End ℝ (H3Zorn ℝ)) := rfl

/-- The restricted Lie equivalence sends each actual bundled inner derivation
to the inner derivation of the transported pair. -/
@[simp] theorem derivationLieEquiv_inner
    (g : H3ZornJordanAut) (a b : H3Zorn ℝ) :
    derivationLieEquiv g
        ⟨(h3ZornJordanInnerDerivation a b : Module.End ℝ (H3Zorn ℝ)),
          h3ZornJordanInnerDerivation_mem_F4 a b⟩ =
      ⟨(h3ZornJordanInnerDerivation (g a) (g b) : Module.End ℝ (H3Zorn ℝ)),
        h3ZornJordanInnerDerivation_mem_F4 (g a) (g b)⟩ := by
  apply Subtype.ext
  exact lieConj_h3ZornJordanInnerDerivation g a b

end H3ZornJordanAut

end InfoGeometry.Algebra
