import InfoGeometry.Canonical.BosonizationConstructiveCurrent
import InfoGeometry.Canonical.SplitCARCurrentSourceAdapter

/-!
# InfoGeometry.Canonical.EndomorphismCutoffCurrentAdapter

Endomorphism-valued cutoff current adapter binding `RawCARModeCompletion A`
to `Module.End 𝕜 V` via ring representation `ρ : A →+* Module.End 𝕜 V`.

This file bridges the gap between ring-valued cutoff current theorems
(`representedCutoffCurrent : ℕ → ℤ → A`) and module endomorphisms (`Module.End 𝕜 V`):

1. `endomorphismCutoffCurrent C ρ N m := ρ (representedCutoffCurrent C N m)`
2. Linearity: `endomorphismCutoffCurrent C ρ N m = ∑ k ∈ integerWindow N, ρ (C.matrixUnit k (k + m))`
3. Commutator Homomorphism: `[endomorphismCutoffCurrent N m, endomorphismCutoffCurrent M n] = ρ ([representedCutoffCurrent N m, representedCutoffCurrent M n])`
4. Complete constructive binding from raw CAR data to module endomorphisms.
-/

namespace InfoGeometry.Canonical.EndomorphismCutoffCurrentAdapter

open Filter
open InfoGeometry.Canonical.BosonizationConstructiveCurrent
open InfoGeometry.Canonical.SplitCARCurrentSourceAdapter

variable {𝕜 A V : Type*} [Field 𝕜] [CharZero 𝕜]
variable [Ring A] [AddCommGroup V] [Module 𝕜 V]

/--
Endomorphism-valued finite cutoff current:
Applies the representation `ρ : A →+* Module.End 𝕜 V` to the ring-valued normal-ordered cutoff current `representedCutoffCurrent C N m`.
-/
def endomorphismCutoffCurrent
    (C : RawCARModeCompletion A)
    (ρ : A →+* Module.End 𝕜 V)
    (N : ℕ) (m : Int) : Module.End 𝕜 V :=
  ρ (representedCutoffCurrent C N m)

/--
**Sum Distribution Theorem:**
The endomorphism cutoff current distributes over the sum of represented matrix units $\rho(E_{k,k+m})$.
-/
theorem endomorphismCutoffCurrent_eq_sum
    (C : RawCARModeCompletion A)
    (ρ : A →+* Module.End 𝕜 V)
    (N : ℕ) (m : Int) :
    endomorphismCutoffCurrent C ρ N m =
      ∑ k ∈ integerWindow N, ρ (C.matrixUnit k (k + m)) := by
  unfold endomorphismCutoffCurrent representedCutoffCurrent
  exact map_sum ρ (fun k => C.matrixUnit k (k + m)) (integerWindow N)

/--
**Commutator Homomorphism Theorem:**
The endomorphism commutator of two cutoff currents equals the image under $\rho$ of their ring-valued commutator in $A$.
-/
theorem endomorphismCutoffCurrent_commutator
    (C : RawCARModeCompletion A)
    (ρ : A →+* Module.End 𝕜 V)
    (N M : ℕ) (m n : Int) :
    (endomorphismCutoffCurrent C ρ N m).commutator
        (endomorphismCutoffCurrent C ρ M n) =
      ρ (comm (representedCutoffCurrent C N m) (representedCutoffCurrent C M n)) := by
  unfold endomorphismCutoffCurrent
  have hcomm : ∀ x y : A, ρ (comm x y) = (ρ x).commutator (ρ y) := by
    intro x y
    unfold comm LinearMap.commutator
    simp [map_sub, map_mul]
  rw [← hcomm]

/--
**Constructive Source Adapter Package:**
Given raw CAR data `C`, representation `ρ`, and a limit current family `J` with stabilization `eventually_eq`,
packages the data into a valid `AdapterData 𝕜 A V`.
-/
def makeSourceAdapter
    (C : RawCARModeCompletion A)
    (ρ : A →+* Module.End 𝕜 V)
    (J : Int → Module.End 𝕜 V)
    (eventually_eq : ∀ m v, ∀ᶠ L in atTop, endomorphismCutoffCurrent C ρ L m v = J m v)
    (trunc : ∀ v, ∀ᶠ l in atTop, J l v = 0)
    (comm : ∀ m n, (J m).commutator (J n) = if m + n = 0 then (m : 𝕜) • (1 : Module.End 𝕜 V) else 0) :
    AdapterData 𝕜 A V where
  source := C
  ρ := ρ
  cutoffCurrent := endomorphismCutoffCurrent C ρ
  J := J
  eventually_cutoffCurrent_eq := eventually_eq
  cutoffCurrent_eq_represented_rawCurrent := fun L m => rfl
  trunc := trunc
  comm := comm

end InfoGeometry.Canonical.EndomorphismCutoffCurrentAdapter
