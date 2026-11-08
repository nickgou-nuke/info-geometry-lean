/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.FibonacciGrothendieckRing

/-!
# Audit: Fibonacci Grothendieck Ring (`FibonacciK0 ≃+ FibonacciRingModel`)

Independent audit verifying that all theorems in
`InfoGeometry.Algebra.FibonacciGrothendieckRing` compile cleanly and depend
strictly on standard Core Lean 4 / Mathlib axioms (`[propext, Classical.choice, Quot.sound]`),
with zero `sorry`, zero `admit`, and zero custom axioms.
-/

namespace InfoGeometry.Algebra.FibonacciGrothendieckRingAudit

open InfoGeometry.Algebra.FibonacciGrothendieckRing

#print axioms k0ToModel_mk
#print axioms k0ToModel_injective
#print axioms k0ToModel_surjective
#print axioms fibonacciK0AddEquiv
#print axioms fibonacciK0AddEquiv_apply
#print axioms k0ToModel_fibonacciK0AddEquiv_symm
#print axioms fibonacciK0AddEquiv_symm_k0ToModel
#print axioms k0Mul
#print axioms k0ToModel_k0Mul
#print axioms k0Mul_tau_tau
#print axioms k0Mul_comm
#print axioms k0Mul_assoc
#print axioms one_k0Mul
#print axioms k0Mul_one
#print axioms k0Mul_left_distrib
#print axioms k0Mul_right_distrib
#print axioms k0ToModel_tensorTauK0
#print axioms tensorTauK0_eq_k0Mul_tau

end InfoGeometry.Algebra.FibonacciGrothendieckRingAudit
