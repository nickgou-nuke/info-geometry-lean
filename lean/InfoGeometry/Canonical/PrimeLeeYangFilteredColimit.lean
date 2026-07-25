import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Algebra.Colimit.Module
import InfoGeometry.Canonical.PrimePartitionPolynomials

/-!
# Filtered colimit of finite prime Lee--Yang stages

This file formalizes the algebraic front-end of the thermodynamic-limit
problem.  A compatible family of finite partition-polynomial stages determines
one class in Mathlib's module direct limit, and every compatible family of
linear readouts factors through that colimit.

No topology is placed on the colimit here.  Consequently this file does not
prove locally uniform convergence, Hurwitz zero transfer, analytic
continuation, or an identification with completed `xi`.
-/

noncomputable section

namespace InfoGeometry.Canonical.PrimeLeeYangFilteredColimit

open InfoGeometry.Canonical.PrimePartitionPolynomials

universe u v

variable {R : Type u} [Semiring R]
variable {Stage : ℕ → Type v}
variable [∀ n, AddCommMonoid (Stage n)] [∀ n, Module R (Stage n)]
variable
  (bond : ∀ i j : ℕ, i ≤ j → Stage i →ₗ[R] Stage j)
variable [DirectedSystem Stage bond]

/-- The algebraic filtered colimit of a sequence of module stages. -/
abbrev StageColimit :=
  DirectLimit Stage bond

/-- Canonical class of a finite-stage element in the filtered colimit. -/
def stageClass (n : ℕ) (x : Stage n) : StageColimit bond :=
  DirectLimit.Module.of R ℕ Stage bond n x

/-- A bonding map does not change the represented colimit class. -/
theorem stageClass_bond
    {i j : ℕ} (hij : i ≤ j) (x : Stage i) :
    stageClass bond j (bond i j hij x) = stageClass bond i x :=
  DirectLimit.Module.of_f

/--
A compatible family of finite-stage partition vectors represents one
stage-independent element of the filtered colimit.
-/
theorem compatible_stageClass_eq
    (Z : ∀ n, Stage n)
    (hZ : ∀ i j (hij : i ≤ j), bond i j hij (Z i) = Z j)
    {i j : ℕ} (hij : i ≤ j) :
    stageClass bond j (Z j) = stageClass bond i (Z i) := by
  rw [← hZ i j hij]
  exact stageClass_bond bond hij (Z i)

/-- Compatible linear readouts factor through the module direct limit. -/
def colimitReadout
    {Target : Type*} [AddCommMonoid Target] [Module R Target]
    (readout : ∀ n, Stage n →ₗ[R] Target)
    (hreadout :
      ∀ i j (hij : i ≤ j) (x : Stage i),
        readout j (bond i j hij x) = readout i x) :
    StageColimit bond →ₗ[R] Target :=
  DirectLimit.Module.lift R ℕ Stage bond readout hreadout

/-- The colimit readout agrees exactly with every finite-stage readout. -/
@[simp]
theorem colimitReadout_stageClass
    {Target : Type*} [AddCommMonoid Target] [Module R Target]
    (readout : ∀ n, Stage n →ₗ[R] Target)
    (hreadout :
      ∀ i j (hij : i ≤ j) (x : Stage i),
        readout j (bond i j hij x) = readout i x)
    (n : ℕ) (x : Stage n) :
    colimitReadout bond readout hreadout (stageClass bond n x) =
      readout n x :=
  DirectLimit.Module.lift_of readout hreadout x

section PrimePartitionFamily

variable
  (polyBond :
    ∀ i j : ℕ, i ≤ j →
      Polynomial ℂ →ₗ[ℂ] Polynomial ℂ)
variable [DirectedSystem (fun _ : ℕ => Polynomial ℂ) polyBond]

/-- Direct-limit class represented by the finite partition polynomial `Z_N`. -/
def primePartitionClass
    (F : PrimePartitionPolynomialFamily)
    (N : ℕ) :
    DirectLimit (fun _ : ℕ => Polynomial ℂ) polyBond :=
  stageClass polyBond N (F.Zpoly N)

/--
If the polynomial bonding maps carry each finite partition polynomial to every
later one, all finite volumes define the same colimit class.
-/
theorem primePartitionClass_eq_of_compatible
    (F : PrimePartitionPolynomialFamily)
    (hF :
      ∀ i j (hij : i ≤ j),
        polyBond i j hij (F.Zpoly i) = F.Zpoly j)
    {i j : ℕ} (hij : i ≤ j) :
    primePartitionClass polyBond F j =
      primePartitionClass polyBond F i :=
  compatible_stageClass_eq polyBond F.Zpoly hF hij

end PrimePartitionFamily

end InfoGeometry.Canonical.PrimeLeeYangFilteredColimit
