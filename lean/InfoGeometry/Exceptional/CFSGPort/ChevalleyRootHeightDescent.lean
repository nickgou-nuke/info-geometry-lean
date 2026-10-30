/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

/-
Local finite-certificate port of the positive-root height descent used by
CFSG.LieType.Chevalley.RootOps.CommAll. The statement is restricted to the six
exceptional root systems represented by the checked local root certificates.
-/
module

public import InfoGeometry.Exceptional.CFSGPort.ChevalleyRootTableAction

public section

namespace InfoGeometry.Exceptional.CFSGPort.Chevalley

/-- Every positive nonsimple root in one of the six certified exceptional
root systems has a simple reflection that keeps it positive and strictly
lowers its height. This finite certificate theorem supplies the induction
step used in the external all-positive-root commutator proof. -/
private theorem rootCertificate_height_descent :
    ∀ (τ : Tag) (k : Fin τ.rootCertificate.roots.length),
      0 < height (τ.rootCertificate.root k) →
      (∀ i : Fin τ.rank, τ.rootCertificate.root k ≠ Pi.single i 1) →
      ∃ i : Fin τ.rank,
        0 < height (reflect τ i (τ.rootCertificate.root k)) ∧
        height (reflect τ i (τ.rootCertificate.root k)) <
          height (τ.rootCertificate.root k) := by
  intro τ
  cases τ <;> decide +kernel

/-- Height descent for the inductively generated root predicate, transported
from the finite root certificate to the native root vector. -/
theorem exists_reflect_height_lt {τ : Tag} {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (hpos : 0 < height α)
    (hns : ∀ i : Fin τ.rank, α ≠ Pi.single i 1) :
    ∃ i : Fin τ.rank,
      IsRoot τ (reflect τ i α) ∧
      0 < height (reflect τ i α) ∧
      height (reflect τ i α) < height α := by
  obtain ⟨k, hk, hroot⟩ := RootCertificate.exists_root_eq τ.rootCertificate_check hα
  have hpos' : 0 < height (τ.rootCertificate.root k) := by
    rw [hroot]
    exact hpos
  have hns' : ∀ i : Fin τ.rank,
      τ.rootCertificate.root k ≠ Pi.single i 1 := by
    intro i hi
    exact hns i (hroot.symm.trans hi)
  obtain ⟨i, hiPos, hiLt⟩ :=
    rootCertificate_height_descent τ ⟨k, hk⟩ hpos' hns'
  exact ⟨i, IsRoot.reflect i hα, by simpa [hroot] using hiPos,
    by simpa [hroot] using hiLt⟩

end InfoGeometry.Exceptional.CFSGPort.Chevalley

end
