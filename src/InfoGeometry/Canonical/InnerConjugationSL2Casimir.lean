/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.InnerConjugation
import InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset

/-!
# Inner-conjugation covariance of the associative-ring `sl₂` Casimir

The quadratic Casimir and its centrality are preserved when an `sl₂` triple
is transported by an inner automorphism.  This is an algebraic covariance
statement for unit conjugation; it does not assume a norm, a topology, or a
continuous one-parameter flow.
-/

namespace InfoGeometry.Canonical.InnerConjugationSL2Casimir

open InfoGeometry.OperatorAlgebra
open InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset

private abbrev opComm {A : Type*} [Ring A] (x y : A) : A :=
  InfoGeometry.OperatorAlgebra.PeirceSpine.ZornNambuDeRhamDiracKahlerPoset.comm x y

variable {A : Type*} [Ring A]

/-- Inner conjugation transports the division-free quadratic Casimir to the
Casimir formed from the conjugated generators. -/
theorem innerConjugation_map_sl2Casimir (u : Aˣ) (N M H : A) :
    innerConjugationRingEquiv u (casimir2 N M H) =
      casimir2 (innerConjugation u N) (innerConjugation u M)
        (innerConjugation u H) := by
  simp [casimir2, twoOp, innerConjugationRingEquiv, innerConjugation,
    map_add, map_mul]

private theorem innerConjugation_map_opComm (u : Aˣ) (x y : A) :
    opComm (innerConjugation u x) (innerConjugation u y) =
      innerConjugation u (opComm x y) := by
  change innerConjugation u x * innerConjugation u y -
      innerConjugation u y * innerConjugation u x =
    innerConjugation u (x * y - y * x)
  simpa only [innerConjugationRingEquiv_apply] using
    (innerConjugation_map_quadraticCommutator u x y).symm

private theorem innerConjugation_map_twoOp (u : Aˣ) (x : A) :
    innerConjugation u (twoOp x) = twoOp (innerConjugation u x) := by
  change innerConjugationRingEquiv u (x + x) = _
  exact map_add (innerConjugationRingEquiv u) x x

private theorem innerConjugation_map_neg_twoOp (u : Aˣ) (x : A) :
    innerConjugation u (-twoOp x) = -twoOp (innerConjugation u x) := by
  change innerConjugationRingEquiv u (-(x + x)) = _
  rw [map_neg, map_add]
  rfl

/-- An inner conjugate of an associative-ring `sl₂` triple is again an
`sl₂` triple, and its scaled quadratic Casimir remains central against all
three transported generators. -/
theorem innerConjugation_preserves_sl2_casimir_centrality
    (u : Aˣ) (N M H : A)
    (hHN : comm H N = twoOp N)
    (hHM : comm H M = -twoOp M)
    (hNM : comm N M = H) :
    opComm (innerConjugation u H) (innerConjugation u N) =
        twoOp (innerConjugation u N) ∧
      opComm (innerConjugation u H) (innerConjugation u M) =
        -twoOp (innerConjugation u M) ∧
      opComm (innerConjugation u N) (innerConjugation u M) =
        innerConjugation u H ∧
      opComm (casimir2 (innerConjugation u N) (innerConjugation u M)
        (innerConjugation u H)) (innerConjugation u N) = 0 ∧
      opComm (casimir2 (innerConjugation u N) (innerConjugation u M)
        (innerConjugation u H)) (innerConjugation u M) = 0 ∧
      opComm (casimir2 (innerConjugation u N) (innerConjugation u M)
        (innerConjugation u H)) (innerConjugation u H) = 0 := by
  have hHN' : opComm (innerConjugation u H) (innerConjugation u N) =
      twoOp (innerConjugation u N) := by
    calc
      opComm (innerConjugation u H) (innerConjugation u N) =
          innerConjugation u (opComm H N) := innerConjugation_map_opComm u H N
      _ = innerConjugation u (twoOp N) := congrArg (innerConjugation u) hHN
      _ = twoOp (innerConjugation u N) := innerConjugation_map_twoOp u N
  have hHM' : opComm (innerConjugation u H) (innerConjugation u M) =
      -twoOp (innerConjugation u M) := by
    calc
      opComm (innerConjugation u H) (innerConjugation u M) =
          innerConjugation u (opComm H M) := innerConjugation_map_opComm u H M
      _ = innerConjugation u (-twoOp M) := congrArg (innerConjugation u) hHM
      _ = -twoOp (innerConjugation u M) := innerConjugation_map_neg_twoOp u M
  have hNM' : opComm (innerConjugation u N) (innerConjugation u M) =
      innerConjugation u H := by
    calc
      opComm (innerConjugation u N) (innerConjugation u M) =
          innerConjugation u (opComm N M) := innerConjugation_map_opComm u N M
      _ = innerConjugation u H := congrArg (innerConjugation u) hNM
  obtain ⟨_, _, _, hC_H, hC_N, hC_M, _⟩ :=
    universal_sl2_casimir_centrality_any_index hHN' hHM' hNM'
  exact ⟨hHN', hHM', hNM', hC_N, hC_M, hC_H⟩

end InfoGeometry.Canonical.InnerConjugationSL2Casimir
