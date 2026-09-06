import proofs.KleinOperatorAlgebraQuotient
import proofs.KleinBottleOrbitQuotient
import Mathlib.Topology.FiberBundle.Basic

/-!
# Certified FiberBundleCore packaging

This file packages the operator fibre over the literal Klein orbit base as a
FiberBundleCore.  The core is the honest trivial core; the separate orbit
quotient and descent action are retained in `KleinOperatorAlgebraQuotient`.
No unproved identification with the orbit quotient total space is asserted.
-/

noncomputable section
namespace KleinOperatorFiberBundle

open KleinBrillouinBase
open KleinBottleOrbitQuotient
open KleinOperatorAlgebraQuotient

abbrev Base := KleinBrillouinQuotient
abbrev Fibre := Operator

/-- The globally trivial operator core over the literal quotient base. -/
def trivialOperatorCore : FiberBundleCore Unit Base Fibre where
  baseSet := fun _ => Set.univ
  isOpen_baseSet := by intro i; exact isOpen_univ
  indexAt := fun _ => ()
  mem_baseSet_at := by intro x; exact Set.mem_univ x
  coordChange := fun _ _ _ v => v
  coordChange_self := by intro i x hx v; rfl
  continuousOn_coordChange := by
    intro i j
    simpa only [Function.comp_apply] using
      continuous_snd.continuousOn
  coordChange_comp := by intro i j k x hx v; rfl

@[simp] theorem trivialOperatorCore_baseSet (i : Unit) :
    (trivialOperatorCore.baseSet i) = Set.univ := rfl

@[simp] theorem trivialOperatorCore_coordChange
    (i j : Unit) (x : Base) (v : Fibre) :
    trivialOperatorCore.coordChange i j x v = v := rfl

/-- The core projection is the canonical total-space projection. -/
theorem trivialOperatorCore_projection_surjective :
    Function.Surjective (FiberBundleCore.proj trivialOperatorCore) := by
  intro x
  exact ⟨⟨x, (0 : Fibre)⟩, rfl⟩

end KleinOperatorFiberBundle
end noncomputable section
