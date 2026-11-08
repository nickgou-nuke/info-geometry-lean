import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.CyclotomicLatentQuotientTopological
import InfoGeometry.Topology.KleinBottleCubicRootInversionTopological

/-!
# Reflection on the finite cyclotomic latent chart

The orientation-reversing latent action is the product of cubic-root
inversion and negation of the two order-three Weyl residues.  This owner
constructs that finite reflection as a topological involution; it deliberately
does not assert a matrix-level conjugation law for the Weyl words.
-/

namespace InfoGeometry.Topology.CyclotomicLatentReflectionTopological

open InfoGeometry.Topology.CyclotomicLatentQuotientTopological
open InfoGeometry.Topology.KleinBottleCubicRootInversionTopological
open InfoGeometry.Topology.KleinBottleCubicRootMonodromyTopological

noncomputable section

/-- Negation of a finite order-three residue. -/
def residueReflection (i : Fin 3) : Fin 3 :=
  ⟨(3 - i.1) % 3, Nat.mod_lt _ (by norm_num)⟩

theorem residueReflection_involutive (i : Fin 3) :
    residueReflection (residueReflection i) = i := by
  fin_cases i <;> rfl

/-- Reflection of the two Weyl residue coordinates. -/
def residuePairReflection (r : Fin 3 × Fin 3) : Fin 3 × Fin 3 :=
  (residueReflection r.1, residueReflection r.2)

theorem residuePairReflection_involutive (r : Fin 3 × Fin 3) :
    residuePairReflection (residuePairReflection r) = r := by
  apply Prod.ext
  · exact residueReflection_involutive r.1
  · exact residueReflection_involutive r.2

abbrev LatentQuotient :=
  InfoGeometry.Topology.CyclotomicLatentQuotientTopological.LatentQuotient

/-- The finite reflection of the cyclotomic latent chart. -/
noncomputable def cyclotomicLatentReflection : LatentQuotient ≃ₜ LatentQuotient where
  toFun z :=
    (cubicRootInversion z.1, residuePairReflection z.2)
  invFun z :=
    (cubicRootInversion z.1, residuePairReflection z.2)
  left_inv z := by
    apply Prod.ext
    · exact cubicRootInversion.left_inv z.1
    · exact residuePairReflection_involutive z.2
  right_inv z := by
    apply Prod.ext
    · exact cubicRootInversion.right_inv z.1
    · exact residuePairReflection_involutive z.2
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

@[simp] theorem cyclotomicLatentReflection_apply_root
    (z : LatentQuotient) :
    (cyclotomicLatentReflection z).1 = cubicRootInversion z.1 := by
  rfl

@[simp] theorem cyclotomicLatentReflection_apply_residue
    (z : LatentQuotient) :
    (cyclotomicLatentReflection z).2 = residuePairReflection z.2 := by
  rfl

theorem cyclotomicLatentReflection_charge_readout
    (z : LatentQuotient) :
    cubicRootChargeReadout ((cyclotomicLatentReflection z).1) =
      (cubicRootChargeReadout z.1).comp (cubicRootChargeReadout z.1) := by
  rw [cyclotomicLatentReflection_apply_root]
  exact cubicRootChargeReadout_inversion z.1

theorem cyclotomicLatentReflection_involutive
    (z : LatentQuotient) :
    cyclotomicLatentReflection (cyclotomicLatentReflection z) = z := by
  exact (cyclotomicLatentReflection).left_inv z

end
end InfoGeometry.Topology.CyclotomicLatentReflectionTopological
