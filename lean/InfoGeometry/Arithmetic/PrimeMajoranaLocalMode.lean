import Mathlib.Tactic
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# InfoGeometry.Arithmetic.PrimeMajoranaLocalMode

Constructive local split-Majorana CAR mode.

This is the local real two-state Fock mode behind the prime-axis split-Majorana
picture. It is purely finite and real.

No infinite product, zeta identity, OPE, Pfaffian determinant theorem, or
Riemann-hypothesis statement is asserted here.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeMajoranaLocalMode

/--
One real local Fock mode.

A vector `(a₀, a₁)` means `a₀ |0⟩ + a₁ |1⟩`.
-/
abbrev LocalFock : Type :=
  ℝ × ℝ

/-- Vacuum state `|0⟩`. -/
def vacuum : LocalFock :=
  (1, 0)

/-- Occupied state `|1⟩`. -/
def occupied : LocalFock :=
  (0, 1)

/-- Endomorphisms of the local real Fock mode. -/
abbrev LocalEnd : Type :=
  LocalFock →ₗ[ℝ] LocalFock

/--
Creation/exterior operator `ε`.

`ε |0⟩ = |1⟩`, `ε |1⟩ = 0`.
-/
def epsilon : LocalFock →ₗ[ℝ] LocalFock where
  toFun := fun x => (0, x.1)
  map_add' := by
    intro x y
    ext <;> simp
  map_smul' := by
    intro a x
    ext <;> simp

/--
Annihilation/contraction operator `ι`.

`ι |1⟩ = |0⟩`, `ι |0⟩ = 0`.
-/
def iota : LocalFock →ₗ[ℝ] LocalFock where
  toFun := fun x => (x.2, 0)
  map_add' := by
    intro x y
    ext <;> simp
  map_smul' := by
    intro a x
    ext <;> simp

/-- Number projection `N = ε ∘ ι`. -/
def numberOp : LocalFock →ₗ[ℝ] LocalFock :=
  epsilon.comp iota

/-- Real split-Majorana bit-flipper `c = ε + ι`. -/
def cMajorana : LocalFock →ₗ[ℝ] LocalFock :=
  epsilon + iota

/-- Real split-Majorana hyperbolic partner `d = ε - ι`. -/
def dMajorana : LocalFock →ₗ[ℝ] LocalFock :=
  epsilon - iota

/-- Local parity operator `Π = c d`. -/
def parityOp : LocalEnd :=
  cMajorana.comp dMajorana

/-- Operator anticommutator `{A,B} = AB + BA`. -/
def anticommutator
    (A B : LocalEnd) : LocalEnd :=
  A.comp B + B.comp A

/-! ## Exterior / contraction CAR -/

/-- Creation squares to zero. -/
theorem epsilon_sq :
    epsilon.comp epsilon = 0 := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [epsilon]

/-- Contraction squares to zero. -/
theorem iota_sq :
    iota.comp iota = 0 := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [iota]

/-- The local CAR law `{ι, ε} = 1`. -/
theorem iota_epsilon_anticomm :
    iota.comp epsilon + epsilon.comp iota = 1 := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [epsilon, iota]

/-- Equivalent CAR orientation `{ε, ι} = 1`. -/
theorem epsilon_iota_anticomm :
    epsilon.comp iota + iota.comp epsilon = 1 := by
  rw [add_comm]
  exact iota_epsilon_anticomm

/-- The local CAR law in anticommutator form `{ε, ι} = 1`. -/
theorem epsilon_iota_anticomm' :
    anticommutator epsilon iota = 1 := by
  simpa [anticommutator] using epsilon_iota_anticomm

/-- The local CAR law in anticommutator form `{ι, ε} = 1`. -/
theorem iota_epsilon_anticomm' :
    anticommutator iota epsilon = 1 := by
  simpa [anticommutator] using iota_epsilon_anticomm

/-! ## Split-Majorana Clifford relations -/

/-- `c² = 1`. Hence `{c,c} = 2`. -/
theorem cMajorana_sq :
    cMajorana.comp cMajorana = 1 := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [cMajorana, epsilon, iota]

/-- `{c,c} = 2`. -/
theorem cMajorana_cMajorana_anticomm :
    anticommutator cMajorana cMajorana = (2 : ℝ) • (1 : LocalEnd) := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [anticommutator, cMajorana, epsilon, iota]
  · ring_nf
  · ring_nf

/-- `d² = -1`. Hence `{d,d} = -2`. -/
theorem dMajorana_sq :
    dMajorana.comp dMajorana = -1 := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [dMajorana, epsilon, iota]

/-- `{d,d} = -2`. -/
theorem dMajorana_dMajorana_anticomm :
    anticommutator dMajorana dMajorana = -((2 : ℝ) • (1 : LocalEnd)) := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [anticommutator, dMajorana, epsilon, iota]
  · ring_nf
  · ring_nf

/-- `c d + d c = 0`. -/
theorem cMajorana_dMajorana_anticomm :
    cMajorana.comp dMajorana + dMajorana.comp cMajorana = 0 := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [cMajorana, dMajorana, epsilon, iota]

/-- `d c + c d = 0`. -/
theorem dMajorana_cMajorana_anticomm :
    dMajorana.comp cMajorana + cMajorana.comp dMajorana = 0 := by
  rw [add_comm]
  exact cMajorana_dMajorana_anticomm

/-- Number operator acts as projection to the occupied component. -/
theorem numberOp_apply
    (x : LocalFock) :
    numberOp x = (0, x.2) := by
  rcases x with ⟨x0, x1⟩
  ext <;> simp [numberOp, epsilon, iota]

/-- Parity operator acts as `diag(1,-1)`. -/
theorem parityOp_apply
    (x : LocalFock) :
    parityOp x = (x.1, -x.2) := by
  rcases x with ⟨x0, x1⟩
  ext <;> simp [parityOp, cMajorana, dMajorana, epsilon, iota]

/-- `Π = cd = 1 - 2N`. -/
theorem parityOp_eq_one_sub_two_numberOp :
    parityOp = 1 - (2 : ℝ) • numberOp := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [parityOp_apply, numberOp_apply]
  ring

/--
Conjugation by local parity flips the split-Majorana bit-flipper.

This is the real local grading law:

`Π c Π = -c`.

It proves that the local Möbius/parity operator acts as the `ℤ₂` grading on
the Majorana generator.
-/
theorem parityOp_conj_cMajorana :
    parityOp.comp (cMajorana.comp parityOp) = -cMajorana := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [parityOp, cMajorana, dMajorana, epsilon, iota]

/--
Conjugation by local parity flips the hyperbolic split-Majorana partner.

`Π d Π = -d`.
-/
theorem parityOp_conj_dMajorana :
    parityOp.comp (dMajorana.comp parityOp) = -dMajorana := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [parityOp, cMajorana, dMajorana, epsilon, iota]

/-- `Π |0⟩ = |0⟩`. -/
@[simp]
theorem parityOp_vacuum :
    parityOp vacuum = vacuum := by
  ext <;> simp [parityOp_apply, vacuum]

/-- `Π |1⟩ = - |1⟩`. -/
@[simp]
theorem parityOp_occupied :
    parityOp occupied = -occupied := by
  ext <;> simp [parityOp_apply, occupied]

/-- `c |0⟩ = |1⟩`. -/
@[simp]
theorem cMajorana_vacuum :
    cMajorana vacuum = occupied := by
  ext <;> simp [cMajorana, epsilon, iota, vacuum, occupied]

/-- `c |1⟩ = |0⟩`. -/
@[simp]
theorem cMajorana_occupied :
    cMajorana occupied = vacuum := by
  ext <;> simp [cMajorana, epsilon, iota, vacuum, occupied]

/-- `d |0⟩ = |1⟩`. -/
@[simp]
theorem dMajorana_vacuum :
    dMajorana vacuum = occupied := by
  ext <;> simp [dMajorana, epsilon, iota, vacuum, occupied]

/-- `d |1⟩ = - |0⟩`. -/
@[simp]
theorem dMajorana_occupied :
    dMajorana occupied = -vacuum := by
  ext <;> simp [dMajorana, epsilon, iota, vacuum, occupied]

/-! ## 6. Parity as the local chiral grading -/

/--
The local parity/Möbius operator squares to the identity.

This proves that `Π = cd` is a genuine local `ℤ₂` grading operator.
-/
theorem parityOp_sq :
    parityOp.comp parityOp = (1 : LocalEnd) := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [parityOp, cMajorana, dMajorana, epsilon, iota]

/--
The local parity operator anticommutes with the split-Majorana bit-flipper `c`.

This is the concrete local grading law:

`Π c + c Π = 0`.
-/
theorem parityOp_cMajorana_anticomm :
    parityOp.comp cMajorana + cMajorana.comp parityOp = 0 := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [parityOp, cMajorana, dMajorana, epsilon, iota]

/--
The local parity operator anticommutes with the split-Majorana partner `d`.

This is the second local grading law:

`Π d + d Π = 0`.
-/
theorem parityOp_dMajorana_anticomm :
    parityOp.comp dMajorana + dMajorana.comp parityOp = 0 := by
  apply LinearMap.ext
  intro x
  rcases x with ⟨x0, x1⟩
  ext <;> simp [parityOp, cMajorana, dMajorana, epsilon, iota]

/--
Pointwise form of `Π c + c Π = 0`.
-/
theorem parityOp_cMajorana_apply
    (x : LocalFock) :
    parityOp (cMajorana x) = -cMajorana (parityOp x) := by
  have h :=
    congrArg (fun T : LocalEnd => T x) parityOp_cMajorana_anticomm
  have h0 : parityOp (cMajorana x) + cMajorana (parityOp x) = 0 := by
    simpa [LinearMap.add_apply] using h
  exact (eq_neg_iff_add_eq_zero).2 h0

/--
Pointwise form of `Π d + d Π = 0`.
-/
theorem parityOp_dMajorana_apply
    (x : LocalFock) :
    parityOp (dMajorana x) = -dMajorana (parityOp x) := by
  have h :=
    congrArg (fun T : LocalEnd => T x) parityOp_dMajorana_anticomm
  have h0 : parityOp (dMajorana x) + dMajorana (parityOp x) = 0 := by
    simpa [LinearMap.add_apply] using h
  exact (eq_neg_iff_add_eq_zero).2 h0

end InfoGeometry.Arithmetic.PrimeMajoranaLocalMode
