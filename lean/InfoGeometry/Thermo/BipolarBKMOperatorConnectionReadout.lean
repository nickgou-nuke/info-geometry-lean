import InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
import InfoGeometry.Thermo.SouriauOnsagerBKMOperatorForms
import Mathlib.Tactic

/-!
# BKM and curvature readouts of a bipolar operator connection

The same real tangent carrier `(dη,dθ)` can support an operator-valued one-form
with values in the repository's native finite C-star operator algebra. This
file keeps two readouts strictly separate:

* `bkmOperator1Form` is symmetric and nonnegative on the diagonal;
* `bkmProbeReadout` of the self-wedge is alternating and reads the operator
  commutator curvature term.

No identification of the BKM metric with the connection or curvature is made.
-/

noncomputable section

namespace InfoGeometry.Thermo.BipolarBKMOperatorConnectionReadout

open InfoGeometry.Canonical.BipolarTwoSheetOperatorConnectionBridge
open InfoGeometry.OperatorAlgebra.ExteriorAlgebra
open InfoGeometry.Thermo.SouriauOnsagerBKMOperatorForms
open SouriauOnsagerBKM

/-- Constant finite-operator-algebra connection on the bipolar tangent plane. -/
def finiteOperatorConnection {n : ℕ}
    (Kη Kθ : FiniteOperatorAlgebra n) :
    Op1Form ℝ Tangent2 (FiniteOperatorAlgebra n) where
  toFun v := v 0 • Kη + v 1 • Kθ
  map_add' u v := by
    simp [add_smul]
    abel
  map_smul' c v := by
    simp [mul_smul, smul_add]

@[simp] theorem finiteOperatorConnection_eta {n : ℕ}
    (Kη Kθ : FiniteOperatorAlgebra n) :
    finiteOperatorConnection Kη Kθ etaTangent = Kη := by
  simp [finiteOperatorConnection, etaTangent]

@[simp] theorem finiteOperatorConnection_theta {n : ℕ}
    (Kη Kθ : FiniteOperatorAlgebra n) :
    finiteOperatorConnection Kη Kθ thetaTangent = Kθ := by
  simp [finiteOperatorConnection, thetaTangent]

/-- The coordinate self-wedge is exactly the commutator of the two finite
operator coefficients. -/
theorem finiteOperatorConnection_wedge_eta_theta {n : ℕ}
    (Kη Kθ : FiniteOperatorAlgebra n) :
    wedge (finiteOperatorConnection Kη Kθ)
        (finiteOperatorConnection Kη Kθ) etaTangent thetaTangent =
      Kη * Kθ - Kθ * Kη := by
  rw [wedge_apply, finiteOperatorConnection_eta,
    finiteOperatorConnection_theta]

/-- Commuting connection coefficients have zero coordinate commutator
curvature. -/
theorem finiteOperatorConnection_wedge_zero_of_commute {n : ℕ}
    {Kη Kθ : FiniteOperatorAlgebra n} (h : Kη * Kθ = Kθ * Kη) :
    wedge (finiteOperatorConnection Kη Kθ)
        (finiteOperatorConnection Kη Kθ) etaTangent thetaTangent = 0 := by
  rw [finiteOperatorConnection_wedge_eta_theta, h, sub_self]

/-- The BKM response of two finite operator connections is symmetric at every
tangent vector. -/
theorem bkm_connection_swap {n : ℕ}
    (D : FaithfulDensityOperator n) (hD : Continuous D.rpow)
    (Kη Kθ Lη Lθ : FiniteOperatorAlgebra n) (v : Tangent2) :
    bkmOperator1Form D hD
        (finiteOperatorConnection Kη Kθ)
        (finiteOperatorConnection Lη Lθ) v =
      bkmOperator1Form D hD
        (finiteOperatorConnection Lη Lθ)
        (finiteOperatorConnection Kη Kθ) v := by
  exact bkmOperator1Form_swap D hD
    (finiteOperatorConnection Kη Kθ)
    (finiteOperatorConnection Lη Lθ) v

/-- The diagonal BKM response of a finite operator connection is nonnegative. -/
theorem bkm_connection_nonneg {n : ℕ}
    (D : FaithfulDensityOperator n) (hD : Continuous D.rpow)
    (Kη Kθ : FiniteOperatorAlgebra n) (v : Tangent2) :
    0 ≤ bkmOperator1Form D hD
      (finiteOperatorConnection Kη Kθ)
      (finiteOperatorConnection Kη Kθ) v := by
  exact bkmOperator1Form_nonneg D hD
    (finiteOperatorConnection Kη Kθ) v

/-- The probed self-wedge curvature readout is alternating in tangent
arguments. -/
theorem bkm_connection_curvature_skew {n : ℕ}
    (D : FaithfulDensityOperator n) (hD : Continuous D.rpow)
    (Q Kη Kθ : FiniteOperatorAlgebra n) (u v : Tangent2) :
    bkmProbeReadout D hD Q
        (wedge (finiteOperatorConnection Kη Kθ)
          (finiteOperatorConnection Kη Kθ)) u v =
      -bkmProbeReadout D hD Q
        (wedge (finiteOperatorConnection Kη Kθ)
          (finiteOperatorConnection Kη Kθ)) v u := by
  exact bkmProbeReadout_skew D hD Q
    (wedge (finiteOperatorConnection Kη Kθ)
      (finiteOperatorConnection Kη Kθ)) u v

/-- On the coordinate pair, the curvature probe reads the BKM pairing of the
operator commutator with the chosen probe. -/
theorem bkm_connection_curvature_coordinate {n : ℕ}
    (D : FaithfulDensityOperator n) (hD : Continuous D.rpow)
    (Q Kη Kθ : FiniteOperatorAlgebra n) :
    bkmProbeReadout D hD Q
        (wedge (finiteOperatorConnection Kη Kθ)
          (finiteOperatorConnection Kη Kθ)) etaTangent thetaTangent =
      D.bkmRealBilinForm hD (Kη * Kθ - Kθ * Kη) Q := by
  simpa using
    bkmProbeReadout_wedge_self D hD Q
      (finiteOperatorConnection Kη Kθ) etaTangent thetaTangent

/-- Compact separation theorem for the symmetric and alternating readouts. -/
theorem bipolar_BKM_curvature_separation_packet {n : ℕ}
    (D : FaithfulDensityOperator n) (hD : Continuous D.rpow)
    (Q Kη Kθ Lη Lθ : FiniteOperatorAlgebra n) (u v : Tangent2) :
    bkmOperator1Form D hD
        (finiteOperatorConnection Kη Kθ)
        (finiteOperatorConnection Lη Lθ) u =
      bkmOperator1Form D hD
        (finiteOperatorConnection Lη Lθ)
        (finiteOperatorConnection Kη Kθ) u ∧
    0 ≤ bkmOperator1Form D hD
      (finiteOperatorConnection Kη Kθ)
      (finiteOperatorConnection Kη Kθ) u ∧
    bkmProbeReadout D hD Q
        (wedge (finiteOperatorConnection Kη Kθ)
          (finiteOperatorConnection Kη Kθ)) u v =
      -bkmProbeReadout D hD Q
        (wedge (finiteOperatorConnection Kη Kθ)
          (finiteOperatorConnection Kη Kθ)) v u := by
  exact ⟨bkm_connection_swap D hD Kη Kθ Lη Lθ u,
    bkm_connection_nonneg D hD Kη Kθ u,
    bkm_connection_curvature_skew D hD Q Kη Kθ u v⟩

end InfoGeometry.Thermo.BipolarBKMOperatorConnectionReadout
