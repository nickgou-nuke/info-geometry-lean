import InfoGeometry.Canonical.CelikKocakCl11ConcretePacket
import InfoGeometry.Quantum.RealSplitClifford
import InfoGeometry.Clifford.RealDoubledHestenesAnchor
import InfoGeometry.Canonical.BilingualRealHestenesDictionary
import InfoGeometry.Clifford.Cl11Matrix

/-!
# InfoGeometry.Canonical.CelikKocakCl11DoubledDictionary

Finite `n = 1` dictionary from the concrete Çelik--Koçak `Cl(1,1)` matrix lane to
the repo's real doubled Hestenes/Krein carrier.

This file is intentionally narrow. It records only theorem-backed finite
readbacks already supported by existing owner lanes:

* matrix-side generators `Eplus`, `J1`, and the derived product `Eminus = Eplus * J1`;
* doubled-side operators `J`, `ε`, and the derived phase axis `K = J ∘ ε`;
* the split `Cl(1,1)` representation facts relating those generators.

This file does not claim:

* a Cantor walk/charge/Hestenes concrete instance;
* a Bogoliubov realization;
* a boundary-limit/Fock construction;
* or a full matrix equivalence into the doubled carrier.

It is a finite dictionary surface: concrete matrix words on one side, concrete
real doubled readbacks on the other.
-/

noncomputable section

namespace InfoGeometry.Canonical

open InfoGeometry.Clifford.Cl11Matrix
open InfoGeometry.Canonical.CelikKocakCl11ConcretePacket
open InfoGeometry.Quantum
open InfoGeometry.Quantum.RealSplitCl11Action

namespace CelikKocakCl11DoubledDictionary

namespace FiniteCl11DoubledDictionary

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Canonical finite dictionary: the `n = 1` Çelik--Koçak source packet read against
the canonical doubled-space split `Cl(1,1)` action.
-/
@[rep_depth operator]
def canonicalTarget :
    Quantum.RealSplitCl11Action (InfoGeometry.Krein.DoubledSpace E) :=
  Quantum.doubledSpaceCl11Action (E := E)

/-- Matrix-side first generator in the canonical finite source packet. -/
@[rep_depth operator]
theorem source_gamma_zero_eq_Eplus :
    CelikKocakCl11ConcretePacket.canonicalPauliGamma ⟨0, by decide⟩ = Eplus :=
  CelikKocakCl11ConcretePacket.canonical_psiGamma_zero

/-- Matrix-side second generator in the canonical finite source packet. -/
@[rep_depth operator]
theorem source_gamma_one_eq_J1 :
    CelikKocakCl11ConcretePacket.canonicalPauliGamma ⟨1, by decide⟩ = J1 :=
  CelikKocakCl11ConcretePacket.canonical_psiGamma_one

/-- The derived matrix phase generator is `Eminus = Eplus * J1`. -/
@[rep_depth operator]
theorem source_phase_eq_Eminus :
    CelikKocakCl11ConcretePacket.canonicalPauliGamma ⟨0, by decide⟩ *
        CelikKocakCl11ConcretePacket.canonicalPauliGamma ⟨1, by decide⟩ = Eminus := by
  rw [source_gamma_zero_eq_Eplus, source_gamma_one_eq_J1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Eplus, J1, Eminus, Matrix.mul_apply, Fin.sum_univ_two]

/-- The split left generator reads back to doubled `J`. -/
@[rep_depth krein]
theorem leftGenerator_readback :
    (canonicalTarget (E := E)).J =
      InfoGeometry.Krein.cl11Rep (E := E)
        (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0)) := by
  simpa using Quantum.doubledSpaceCl11Action_J_eq_cl11Rep_leftGenerator (E := E)

/-- The split pseudoscalar reads back to doubled `ε`. -/
@[rep_depth krein]
theorem pseudoscalar_readback :
    (canonicalTarget (E := E)).eps =
      InfoGeometry.Krein.cl11Rep (E := E)
        (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0) *
          CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1)) := by
  simpa using Quantum.doubledSpaceCl11Action_eps_eq_cl11Rep_pseudoscalar (E := E)

/-- The split right generator reads back to doubled `K = J ∘ ε`. -/
@[rep_depth krein]
theorem rightGenerator_readback :
    (canonicalTarget (E := E)).K =
      InfoGeometry.Krein.cl11Rep (E := E)
        (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1)) := by
  simpa using Quantum.doubledSpaceCl11Action_K_eq_cl11Rep_rightGenerator (E := E)

/-- The doubled phase axis squares to `-1`, matching the derived matrix phase channel. -/
@[rep_depth krein]
theorem target_phase_sq :
    ((canonicalTarget (E := E)).K).comp ((canonicalTarget (E := E)).K) =
      -(ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)) := by
  simpa using (canonicalTarget (E := E)).K_sq

/-- The doubled spectral involution squares to identity. -/
@[rep_depth krein]
theorem target_epsilon_sq :
    ((canonicalTarget (E := E)).eps).comp ((canonicalTarget (E := E)).eps) =
      ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E) := by
  simpa using (canonicalTarget (E := E)).eps_sq

/-- The doubled modular involution squares to identity. -/
@[rep_depth krein]
theorem target_J_sq :
    ((canonicalTarget (E := E)).J).comp ((canonicalTarget (E := E)).J) =
      ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E) := by
  simpa using (canonicalTarget (E := E)).J_sq

end FiniteCl11DoubledDictionary
end CelikKocakCl11DoubledDictionary

end InfoGeometry.Canonical
