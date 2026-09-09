import InfoGeometry.Analysis.BipolarMonodromyDeckReadout
import Mathlib.Topology.Homotopy.Lifting

/-!
# Fundamental-group monodromy of the exponential covering

The exponential covering gives a genuine permutation representation of the
fundamental group on each fiber.  This is the native topological replacement
for an unproved identification of arbitrary loops with a winding lattice.
-/

noncomputable section

namespace InfoGeometry.Analysis.BipolarFundamentalMonodromy

open CategoryTheory Complex Topology

abbrev NonzeroComplex := {z : ℂ // z ≠ 0}
abbrev ExpFiber (x : NonzeroComplex) :=
  (fun z : ℂ => (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : NonzeroComplex)) ⁻¹' {x}

noncomputable def expMonodromyEquiv {x : NonzeroComplex}
    (γ : FundamentalGroup NonzeroComplex x) : ExpFiber x ≃ ExpFiber x :=
  Equiv.ofBijective
    (Complex.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ))
    (Complex.isCoveringMap_exp.monodromy_bijective (FundamentalGroup.toPath γ))

theorem expMonodromyEquiv_apply {x : NonzeroComplex}
    (γ : FundamentalGroup NonzeroComplex x) (e : ExpFiber x) :
    (expMonodromyEquiv γ e : ℂ) =
      (Complex.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ) e : ℂ) := rfl

noncomputable def expMonodromyRepresentation (x : NonzeroComplex) :
    FundamentalGroup NonzeroComplex x →* Equiv.Perm (ExpFiber x) where
  toFun := expMonodromyEquiv
  map_one' := by
    ext e
    dsimp [expMonodromyEquiv]
    change (Complex.isCoveringMap_exp.monodromy
        (FundamentalGroup.toPath (1 : FundamentalGroup NonzeroComplex x)) e : ℂ) =
      (e : ℂ)
    rw [show FundamentalGroup.toPath (1 : FundamentalGroup NonzeroComplex x) =
      Path.Homotopic.Quotient.refl x by rfl]
    rw [Complex.isCoveringMap_exp.monodromy_refl]
    rfl
  map_mul' := by
    intro γ δ
    ext e
    dsimp [expMonodromyEquiv]
    change Complex.isCoveringMap_exp.monodromy
        (FundamentalGroup.toPath (γ * δ)) e =
      (Complex.isCoveringMap_exp.monodromy (FundamentalGroup.toPath γ)
        (Complex.isCoveringMap_exp.monodromy (FundamentalGroup.toPath δ) e) : ℂ)
    rw [show FundamentalGroup.toPath (γ * δ) =
      (FundamentalGroup.toPath δ).trans (FundamentalGroup.toPath γ) by rfl]
    rw [Complex.isCoveringMap_exp.monodromy_trans_apply]

theorem expMonodromyRepresentation_apply (x : NonzeroComplex)
    (γ : FundamentalGroup NonzeroComplex x) (e : ExpFiber x) :
    expMonodromyRepresentation x γ e = expMonodromyEquiv γ e := rfl

/-- Reversing a loop gives the inverse permutation of its monodromy. -/
theorem expMonodromyRepresentation_inv (x : NonzeroComplex)
    (γ : FundamentalGroup NonzeroComplex x) :
    expMonodromyRepresentation x (γ⁻¹) =
      (expMonodromyRepresentation x γ)⁻¹ := by
  exact map_inv (expMonodromyRepresentation x) γ

end InfoGeometry.Analysis.BipolarFundamentalMonodromy
