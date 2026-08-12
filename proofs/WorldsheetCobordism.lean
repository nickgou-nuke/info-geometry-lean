import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Hom.Defs

import proofs.Clifford55
import proofs.CuntzKTheoryMittagLeffler

noncomputable section

namespace WorldsheetCobordism

open Clifford55

-- 1. Define the Cl(1,1)^5 Clifford algebra structure
-- Cl(5,5) is canonically isomorphic to Cl(1,1) ⊗ ... ⊗ Cl(1,1) (5 times)
-- We use the Clifford55.Cl55 algebra representing this structure.
abbrev Cl11_5 := Cl55

-- 2. Structure the Pin(5,5) duality groups acting over the CleanVacuum
-- The vacuum carrier stores only the state value; defect-freeness is supplied
-- separately as the hypothesis required by the anomaly theorem below.
structure CleanVacuum where
  state : ℝ

-- Action of Pin(5,5) on CleanVacuum
def pin_action (_g : Pin55) (v : CleanVacuum) : CleanVacuum :=
  ⟨v.state⟩

-- 3. A conservative proof-carrying model of the Möbius-Witten anomaly

-- This file does not assert a global topological anomaly-cancellation theorem.
-- Instead, the anomaly functional is deliberately conservative: it returns zero
-- only for systems carrying the local defect-free evidence used in this model.
def moebius_witten_anomaly {G : Type*} [AddCommGroup G] (sys : InvSys G) : ℝ :=
  by
    classical
    exact if MittagLeffler sys ∧ Function.Surjective (shift_map sys) then 0 else 1

-- If the profinite K-theory supplies the explicit defect-free data used above
-- (Mittag-Leffler plus surjectivity of the Milnor shift map), this conservative
-- anomaly functional evaluates to zero by definition.
theorem anomaly_vanishes_of_defect_free {G : Type*} [AddCommGroup G] (sys : InvSys G)
  (h_ml : MittagLeffler sys)
  (h_surj : Function.Surjective (shift_map sys)) :
  moebius_witten_anomaly sys = 0 := by
  classical
  simp [moebius_witten_anomaly, h_ml, h_surj]

-- Application to the CleanVacuum established in previous files.
-- We use the constant_sys which models the profinite K-theory over finite abelian groups.
theorem moebius_witten_anomaly_vanishes_on_vacuum (n : ℕ) [Fact (n ≥ 2)] :
  moebius_witten_anomaly (constant_sys n) = 0 :=
  anomaly_vanishes_of_defect_free
    (constant_sys n)
    (mittag_leffler_constant_sys n)
    (milnor_defect_vanishes_constant n)

end WorldsheetCobordism
