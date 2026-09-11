import InfoGeometry.Canonical.DikinFiniteOrbitColimit

/-!
# BKM Dikin Weyl Invariance Axiom Audit

Verifies that the concrete Weyl reflection operator L = -I, its involutive property,
its preservation of the BKM Dikin quadratic form bkmDikinQuadratic, the Dikin
ellipsoid isometric preimage, and radius-enlargement confinement rely strictly
on standard Lean 4 foundational axioms: `propext`, `Classical.choice`, and `Quot.sound`.
No custom axioms, no sorry, and no proxy certificate structures.
-/

namespace InfoGeometry.Canonical.DikinFiniteOrbitColimit.Audit

open SouriauOnsagerBKM
open InfoGeometry.Canonical.DikinFiniteOrbitColimit

variable {n : ℕ}

#print axioms weylReflection_involutive
#print axioms weylReflection_comp_self
#print axioms bkmDikinQuadratic_weylReflection
#print axioms bkmDikinQuadratic_weylIdentity
#print axioms bkmDikinEllipsoid_map_mono_radius_weylReflection
#print axioms inBkmDikinEllipsoid_weylReflection_iff
#print axioms inBkmDikinEllipsoidAt_weylReflection_iff
#print axioms weyl_dikin_synthesis

theorem weyl_dikin_audit_soundness
    (D : FaithfulDensityOperator n) (h : Continuous D.rpow)
    (A : SelfAdjointOperator n) {r s : ℝ}
    (hrs : r ^ 2 ≤ s ^ 2)
    (hA : InBkmDikinEllipsoid D h A r) :
    bkmDikinQuadratic D h (weylReflection n A) = bkmDikinQuadratic D h A ∧
    (weylReflection n (weylReflection n A) = A) ∧
    (InBkmDikinEllipsoid D h (weylReflection n A) r ↔ InBkmDikinEllipsoid D h A r) ∧
    InBkmDikinEllipsoid D h (weylReflection n A) s :=
  weyl_dikin_synthesis D h A hrs hA

#print axioms weyl_dikin_audit_soundness

end InfoGeometry.Canonical.DikinFiniteOrbitColimit.Audit
