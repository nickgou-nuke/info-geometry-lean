import InfoGeometry.Canonical.UnifiedSuperchargeAlgebra
import InfoGeometry.Canonical.CentralChargeDiracMorphismBridge
import InfoGeometry.Physics.SuperPoincareOperatorCharges

noncomputable section

/-!
# Chiral supercharge / central-extension identification

The repository already owns the primitive chiral algebra and the Fredholm
central operator separately.  This file records the only extra datum needed
to connect them: an explicit equality identifying the CPT odd operator with a
sum of two nilpotent chiral charges.  No carrier identification is inferred
from notation alone.
-/

namespace InfoGeometry.Canonical.ChiralSuperchargeCentralExtension

open InfoGeometry.Canonical.SuperchargeCentralChargeClosure
open InfoGeometry.Canonical.SuperchargeCARCCRBridge
open InfoGeometry.Canonical.CentralChargeDiracMorphismBridge
open InfoGeometry.Canonical.OperatorialCentralCharge
open InfoGeometry.Physics.SuperPoincareOperatorCharges
open InfoGeometry.KK
open InfoGeometry.KK.RealSplitKreinKasparovCycle
open InfoGeometry.Krein

variable {A B E : Type}
variable [NormedRing A] [NormedRing B]
variable [NormedAlgebra ℝ A] [NormedAlgebra ℝ B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [KreinSpace (DoubledSpace E)] [KreinGradedModule (DoubledSpace E)]

local notation "H₂" => DoubledSpace E
local notation "EndH" => InfoGeometry.Canonical.BogoliubovFockSuper.FockEndomorphism E

/-- The chiral sum of two nilpotent odd endomorphisms has square equal to its
mixed anticommutator.  The equality `hSum` is the explicit CPT/chiral
identification contract. -/
theorem cpt_square_eq_chiral_anticommutator
    (Qplus Qminus : EndH)
    (hplus : Qplus * Qplus = 0)
    (hminus : Qminus * Qminus = 0)
    (hSum : cptSuperchargeOp (E := E) = Qplus + Qminus) :
    (cptSuperchargeOp (E := E)).comp (cptSuperchargeOp (E := E)) =
      anti Qplus Qminus := by
  rw [hSum]
  exact chiral_dirac_square_eq_momentum_operator hplus hminus

/-- Central extension after supplying the mixed-bracket readout. -/
theorem cpt_square_eq_kinetic_plus_diracCentralOperator
    (Qplus Qminus : EndH)
    (hplus : Qplus * Qplus = 0)
    (hminus : Qminus * Qminus = 0)
    (hSum : cptSuperchargeOp (E := E) = Qplus + Qminus)
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X)
    (hMixed : anti Qplus Qminus =
      cptSuperchargeKineticPart (A := A) (B := B) (E := E) X hX +
        integerCentralChargeMorphism (E := E)
          (operatorialCentralCharge (A := A) (B := B) (E := E) X hX)) :
    (cptSuperchargeOp (E := E)).comp (cptSuperchargeOp (E := E)) =
      cptSuperchargeKineticPart (A := A) (B := B) (E := E) X hX +
        integerCentralChargeMorphism (E := E)
          (operatorialCentralCharge (A := A) (B := B) (E := E) X hX) := by
  rw [cpt_square_eq_chiral_anticommutator Qplus Qminus hplus hminus hSum, hMixed]

/-- The Fredholm central readout commutes with every doubled-carrier operator. -/
theorem diracCentralOperator_commutes
    (X : RealSplitKreinDiracFredholmModule A B H₂)
    (hX : ChiralFredholmSurface X) (Y : EndH) :
    Commute
      (integerCentralChargeMorphism (E := E)
        (operatorialCentralCharge (A := A) (B := B) (E := E) X hX)) Y := by
  exact operatorialCentralChargeOperator_central (A := A) (B := B) (E := E) X hX Y

end InfoGeometry.Canonical.ChiralSuperchargeCentralExtension
