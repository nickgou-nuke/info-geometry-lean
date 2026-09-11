import InfoGeometry.Physics.NuclearCl55CartanParityDictionary
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.Cl55SpinorCartanFock

/-!
# Native soldering of the nuclear CAR interface to the Cl(5,5) carrier

The nuclear and Clifford files deliberately use different carriers.  This
file supplies the missing functorial edge: the already constructed five-mode
matrices `e` and `f` form an actual instance of the nuclear `QuasiparticleCAR`
interface.  No new generators or particle--hole representation are defined.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearCl55NativeSoldering

open InfoGeometry.Physics.NuclearQuasiparticleCAR
open InfoGeometry.Physics.NuclearQuasiparticleCAR.QuasiparticleCAR
open InfoGeometry.Physics.Cl55SpinorCartanFock
open InfoGeometry.Physics.NuclearCl55CartanParityDictionary
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.Canonical.Cl55WittLieRouting

/-- The existing Cl(5,5) Fock matrices, viewed through the nuclear CAR API. -/
def cl55CAR : QuasiparticleCAR (Fin 5) (MatStage 5) where
  a := f
  adag := e
  anticomm_a_a := f_anticomm
  anticomm_adag_adag := e_anticomm
  anticomm_a_adag := by
    intro i j
    have h := ef_car j i
    by_cases hij : i = j
    · subst j
      simpa [add_comm] using h
    · simpa [hij, Ne.symm hij, add_comm] using h

@[simp] theorem cl55CAR_a (i : Fin 5) : cl55CAR.a i = f i := rfl

@[simp] theorem cl55CAR_adag (i : Fin 5) : cl55CAR.adag i = e i := rfl

theorem cl55CAR_cartan_creation (i : Fin 5) :
    QuasiparticleCAR.comm (cl55CAR.centeredOccupationCartan i)
        (cl55CAR.adag i) = e i + e i := by
  exact cl55CAR.comm_centeredOccupationCartan_adag i

theorem cl55CAR_cartan_annihilation (i : Fin 5) :
    QuasiparticleCAR.comm (cl55CAR.centeredOccupationCartan i)
        (cl55CAR.a i) = -(f i + f i) := by
  exact cl55CAR.comm_centeredOccupationCartan_a i

theorem cl55CAR_cartan_creation_normalized (i : Fin 5) :
    bracket (normalizedCl55Cartan i) (e i) = (2 : ℝ) • e i := by
  exact normalizedCl55Cartan_creation i

theorem cl55CAR_cartan_annihilation_normalized (i : Fin 5) :
    bracket (normalizedCl55Cartan i) (f i) = (-2 : ℝ) • f i := by
  exact normalizedCl55Cartan_annihilation i

theorem cl55CAR_parity_and_chirality (i : Fin 5) :
    cl55CAR.fermionParity i * cl55CAR.fermionParity i = 1 ∧
      gammaChiral * gammaChiral = 1 := by
  exact nuclear_cl55_parity_shape_packet cl55CAR i

theorem cl55CAR_native_soldering_packet (i : Fin 5) :
    cl55CAR.a i * cl55CAR.a i = 0 ∧
      cl55CAR.adag i * cl55CAR.adag i = 0 ∧
      cl55CAR.adag i * cl55CAR.a i + cl55CAR.a i * cl55CAR.adag i = 1 ∧
      cl55CAR.fermionParity i * cl55CAR.fermionParity i = 1 := by
  refine ⟨cl55CAR.a_sq i, cl55CAR.adag_sq i, ?_, cl55CAR.fermionParity_sq i⟩
  simpa [cl55CAR_a, cl55CAR_adag] using (ef_car i i)

/-! ## Finite-mode Hamiltonian transport -/

/-- The free nuclear Hamiltonian interface on the native five-mode carrier. -/
def cl55FreeHamiltonian (s : Finset (Fin 5)) (eps : Fin 5 → ℝ) : MatStage 5 :=
  cl55CAR.freeQuasiparticleHamiltonian s eps

theorem cl55FreeHamiltonian_creation_weight
    (s : Finset (Fin 5)) (eps : Fin 5 → ℝ) (k : Fin 5) (hk : k ∈ s) :
    QuasiparticleCAR.comm (cl55FreeHamiltonian s eps) (e k) =
      (eps k) • e k := by
  exact cl55CAR.comm_freeQuasiparticleHamiltonian_adag s eps k hk

theorem cl55FreeHamiltonian_creation_weight_packet
    (s : Finset (Fin 5)) (eps : Fin 5 → ℝ) (k : Fin 5) (hk : k ∈ s) :
    QuasiparticleCAR.comm (cl55FreeHamiltonian s eps) (cl55CAR.adag k) =
        (eps k) • cl55CAR.adag k ∧
      cl55CAR.adag k * cl55CAR.a k + cl55CAR.a k * cl55CAR.adag k = 1 := by
  exact ⟨cl55FreeHamiltonian_creation_weight s eps k hk,
    by simpa using (ef_car k k)⟩

end InfoGeometry.Physics.NuclearCl55NativeSoldering
