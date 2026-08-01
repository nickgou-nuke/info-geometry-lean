import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Tactic.NoncommRing

noncomputable section

namespace InfoGeometry.Canonical.NativeMathlibCliffordBridge

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- **Theorem**: Definitional Equivalence between CliffordAlgebra (0) and ExteriorAlgebra R V.
    In Mathlib, ExteriorAlgebra R V is definitionally CliffordAlgebra (0 : QuadraticForm R V). -/
theorem clifford_zero_def_eq_exterior :
    CliffordAlgebra (0 : QuadraticForm R V) = ExteriorAlgebra R V :=
  rfl

/-- **Theorem**: General Clifford Algebra Anti-Commutation with Metric Polarization B(v1, v2).
    For any quadratic form Q : QuadraticForm R V and vectors v1 v2 : V,
    ι(v1) * ι(v2) + ι(v2) * ι(v1) = (polar Q v1 v2) • (1 : CliffordAlgebra Q).
    This encodes the Dirac Gamma Matrix relation γ^μ γ^ν + γ^ν γ^μ = 2 η^(μν) • I. -/
theorem clifford_anti_commute (Q : QuadraticForm R V) (v1 v2 : V) :
    CliffordAlgebra.ι Q v1 * CliffordAlgebra.ι Q v2 + CliffordAlgebra.ι Q v2 * CliffordAlgebra.ι Q v1 =
      algebraMap R (CliffordAlgebra Q) (QuadraticMap.polar Q v1 v2) :=
  CliffordAlgebra.ι_mul_ι_add_swap v1 v2

/-- **Theorem**: Native Mathlib Clifford Algebra Generator Square Scalar Law (ι(v)² = Q(v) • 1).
    Proves natively in Mathlib that for any vector v ∈ V and quadratic form Q,
    the generator ι(v) squared equals Q(v) • 1 in CliffordAlgebra Q. -/
theorem native_clifford_sq_scalar (Q : QuadraticForm R V) (v : V) :
    CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q v = algebraMap R (CliffordAlgebra Q) (Q v) :=
  CliffordAlgebra.ι_sq_scalar Q v

/-- **Theorem**: Native Mathlib Clifford Algebra Involute Involution (involute (involute c) = c).
    Proves natively in Mathlib that CliffordAlgebra.involute is an involution of order 2. -/
theorem native_clifford_involute_involution (Q : QuadraticForm R V) (c : CliffordAlgebra Q) :
    CliffordAlgebra.involute (CliffordAlgebra.involute c) = c :=
  CliffordAlgebra.involute_involute c

/-- **Theorem**: Native Mathlib Clifford Algebra Involute on Generator (involute (ι(v)) = - ι(v)). -/
theorem native_clifford_involute_ι (Q : QuadraticForm R V) (v : V) :
    CliffordAlgebra.involute (CliffordAlgebra.ι Q v) = - CliffordAlgebra.ι Q v :=
  CliffordAlgebra.involute_ι v


end InfoGeometry.Canonical.NativeMathlibCliffordBridge
