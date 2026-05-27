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

@[rep_depth operator]
structure FiniteCl11DoubledDictionary
    (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] where
  source : CelikKocakCl11ConcretePacket
  target : Quantum.RealSplitCl11Action (InfoGeometry.Krein.DoubledSpace E)

namespace FiniteCl11DoubledDictionary

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
Canonical finite dictionary: the `n = 1` Çelik--Koçak source packet read against
the canonical doubled-space split `Cl(1,1)` action.
-/
@[rep_depth operator]
def canonical : FiniteCl11DoubledDictionary E where
  source := CelikKocakCl11ConcretePacket.canonical
  target := Quantum.doubledSpaceCl11Action (E := E)

/-- Matrix-side first generator in the canonical finite source packet. -/
@[rep_depth operator]
theorem source_gamma_zero_eq_Eplus :
    (canonical (E := E)).source.pauliBridge.psiGamma ⟨0, by decide⟩ = Eplus :=
  CelikKocakCl11ConcretePacket.canonical_psiGamma_zero

/-- Matrix-side second generator in the canonical finite source packet. -/
@[rep_depth operator]
theorem source_gamma_one_eq_J1 :
    (canonical (E := E)).source.pauliBridge.psiGamma ⟨1, by decide⟩ = J1 :=
  CelikKocakCl11ConcretePacket.canonical_psiGamma_one

/-- The derived matrix phase generator is `Eminus = Eplus * J1`. -/
@[rep_depth operator]
theorem source_phase_eq_Eminus :
    (canonical (E := E)).source.pauliBridge.psiGamma ⟨0, by decide⟩ *
        (canonical (E := E)).source.pauliBridge.psiGamma ⟨1, by decide⟩ = Eminus := by
  rw [source_gamma_zero_eq_Eplus (E := E), source_gamma_one_eq_J1 (E := E)]
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Eplus, J1, Eminus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Doubled-side first generator is the modular involution `J`. -/
@[rep_depth krein]
theorem target_leftGenerator_eq_modularJ :
    (canonical (E := E)).target.J = InfoGeometry.Krein.modular_j (E := E) := by
  rfl

/-- Doubled-side pseudoscalar is the spectral involution `ε`. -/
@[rep_depth krein]
theorem target_pseudoscalar_eq_spectralEpsilon :
    (canonical (E := E)).target.eps = InfoGeometry.Krein.spectral_epsilon (E := E) := by
  rfl

/-- Doubled-side derived phase axis is `K = J ∘ ε = complex_i`. -/
@[rep_depth krein]
theorem target_phase_eq_complexI :
    (canonical (E := E)).target.K = InfoGeometry.Krein.complex_i (E := E) := by
  rfl

/-- The split left generator reads back to doubled `J`. -/
@[rep_depth krein]
theorem leftGenerator_readback :
    (canonical (E := E)).target.J =
      InfoGeometry.Krein.cl11Rep (E := E)
        (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0)) := by
  simpa using Quantum.doubledSpaceCl11Action_J_eq_cl11Rep_leftGenerator (E := E)

/-- The split pseudoscalar reads back to doubled `ε`. -/
@[rep_depth krein]
theorem pseudoscalar_readback :
    (canonical (E := E)).target.eps =
      InfoGeometry.Krein.cl11Rep (E := E)
        (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0) *
          CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1)) := by
  simpa using Quantum.doubledSpaceCl11Action_eps_eq_cl11Rep_pseudoscalar (E := E)

/-- The split right generator reads back to doubled `K = J ∘ ε`. -/
@[rep_depth krein]
theorem rightGenerator_readback :
    (canonical (E := E)).target.K =
      InfoGeometry.Krein.cl11Rep (E := E)
        (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1)) := by
  simpa using Quantum.doubledSpaceCl11Action_K_eq_cl11Rep_rightGenerator (E := E)

/-- Matrix-side `J1` corresponds to the doubled spectral involution `ε`. -/
@[rep_depth krein]
theorem matrix_J1_to_doubledEpsilon :
    (canonical (E := E)).target.eps =
      InfoGeometry.Krein.cl11Rep (E := E)
        (CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (1, 0) *
          CliffordAlgebra.ι InfoGeometry.Clifford.splitQ11 (0, 1)) :=
  pseudoscalar_readback (E := E)

/-- The doubled phase axis squares to `-1`, matching the derived matrix phase channel. -/
@[rep_depth krein]
theorem target_phase_sq :
    ((canonical (E := E)).target.K).comp ((canonical (E := E)).target.K) =
      -(ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E)) := by
  simpa using (canonical (E := E)).target.K_sq

/-- The doubled spectral involution squares to identity. -/
@[rep_depth krein]
theorem target_epsilon_sq :
    ((canonical (E := E)).target.eps).comp ((canonical (E := E)).target.eps) =
      ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E) := by
  simpa using (canonical (E := E)).target.eps_sq

/-- The doubled modular involution squares to identity. -/
@[rep_depth krein]
theorem target_J_sq :
    ((canonical (E := E)).target.J).comp ((canonical (E := E)).target.J) =
      ContinuousLinearMap.id ℝ (InfoGeometry.Krein.DoubledSpace E) := by
  simpa using (canonical (E := E)).target.J_sq

end FiniteCl11DoubledDictionary
end CelikKocakCl11DoubledDictionary

end InfoGeometry.Canonical
