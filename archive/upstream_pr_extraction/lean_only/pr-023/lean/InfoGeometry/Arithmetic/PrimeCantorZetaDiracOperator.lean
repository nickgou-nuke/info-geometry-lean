import Mathlib
import InfoGeometry.Meta.Architecture
import InfoGeometry.Arithmetic.PrimeExteriorGraphDirac

/-!
# InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator

Finite Cantor--Dirac operator on the prime-indexed square-free/Fock carrier.

This module implements the finite operator surface behind the formal expression

  `D_C^ζ(s) = Q(s) + Q♯(s)`,

where `Q(s)` is the holonomy-weighted creation supercharge and `Q♯(s)` is the
dual holonomy-inverse annihilation supercharge.

The carrier is the existing finite exterior/Cantor state surface from
`PrimeExteriorGraphDirac`: vertices are finite square-free prime occupation
states, creation and annihilation are partial basis maps, and the Hamiltonian
readout is the finite prime-weighted number energy.

Analytic specializations such as `holonomy s p = p^(1/2 - s)` are intentionally
not hard-coded here. They belong to the analytic/socket layer.

No infinite Euler product.
No analytic continuation.
No Hilbert--Pólya operator.
No RH claim.
-/

noncomputable section

open scoped BigOperators

namespace InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator

open InfoGeometry.Arithmetic.PrimeExteriorGraphDirac

/-- A finite certified prime cutoff. -/
abbrev PrimeCutoff := PrimeExteriorGraphDirac.PrimeCutoff

/-- Prime mode inside a finite cutoff. -/
abbrev PrimeMode (P : PrimeCutoff) := PrimeExteriorGraphDirac.PrimeMode P

/-- Vertex of the finite prime Cantor/Fock lattice. -/
abbrev Vertex (P : PrimeCutoff) := PrimeExteriorGraphDirac.Vertex P

/-- Complex-valued fields on the finite prime Cantor/Fock lattice. -/
@[rep_depth thermo]
abbrev CantorField (P : PrimeCutoff) := Vertex P → ℂ

/-! ## 1. Partial creation/annihilation push-forwards -/

/-- Evaluate a field on an optional vertex, with `none` interpreted as zero. -/
@[rep_depth thermo]
def optionEval {P : PrimeCutoff}
    (f : CantorField P) : Option (Vertex P) → ℂ
  | none => 0
  | some v => f v

@[simp, rep_depth thermo]
theorem optionEval_none {P : PrimeCutoff} (f : CantorField P) :
    optionEval f none = 0 := rfl

@[simp, rep_depth thermo]
theorem optionEval_some {P : PrimeCutoff}
    (f : CantorField P) (v : Vertex P) :
    optionEval f (some v) = f v := rfl

/--
Creation push-forward along the prime axis.

At a basis state `S`, this evaluates the field at `ε_p S`, or returns zero
when creation is forbidden because `p` is already occupied.
-/
@[rep_depth thermo]
def creationPush {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P) : ℂ :=
  optionEval f (PrimeExteriorGraphDirac.create p S)

/--
Annihilation push-forward along the prime axis.

At a basis state `S`, this evaluates the field at `ι_p S`, or returns zero
when annihilation is forbidden because `p` is vacant.
-/
@[rep_depth thermo]
def annihilationPush {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P) : ℂ :=
  optionEval f (PrimeExteriorGraphDirac.annihilate p S)

@[simp, rep_depth thermo]
theorem creationPush_of_mem {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P)
    (hp : p ∈ S) :
    creationPush p f S = 0 := by
  simp [creationPush, PrimeExteriorGraphDirac.create, hp]

@[simp, rep_depth thermo]
theorem creationPush_of_not_mem {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P)
    (hp : p ∉ S) :
    creationPush p f S = f (insert p S) := by
  simp [creationPush, PrimeExteriorGraphDirac.create, hp]

@[simp, rep_depth thermo]
theorem annihilationPush_of_mem {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P)
    (hp : p ∈ S) :
    annihilationPush p f S = f (S.erase p) := by
  simp [annihilationPush, PrimeExteriorGraphDirac.annihilate, hp]

@[simp, rep_depth thermo]
theorem annihilationPush_of_not_mem {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P)
    (hp : p ∉ S) :
    annihilationPush p f S = 0 := by
  simp [annihilationPush, PrimeExteriorGraphDirac.annihilate, hp]

/-! ## 2. Kernel-level Cantor--Dirac readouts -/

/--
Single-prime creation kernel.

It is nonzero only when `T = ε_p S`.
-/
@[rep_depth thermo]
def creationKernel {P : PrimeCutoff}
    (amplitude holonomy : PrimeMode P → ℂ)
    (p : PrimeMode P) (S T : Vertex P) : ℂ :=
  if PrimeExteriorGraphDirac.create p S = some T then
    amplitude p * holonomy p
  else
    0

/--
Single-prime dual annihilation kernel.

It is nonzero only when `T = ι_p S`.
-/
@[rep_depth thermo]
def annihilationKernel {P : PrimeCutoff}
    (amplitude holonomy : PrimeMode P → ℂ)
    (p : PrimeMode P) (S T : Vertex P) : ℂ :=
  if PrimeExteriorGraphDirac.annihilate p S = some T then
    amplitude p * (holonomy p)⁻¹
  else
    0

/-- Total finite Cantor--Dirac kernel, summed over all prime axes. -/
@[rep_depth thermo]
def cantorDiracKernel {P : PrimeCutoff}
    (amplitude holonomy : PrimeMode P → ℂ)
    (S T : Vertex P) : ℂ :=
  Finset.sum (Finset.univ : Finset (PrimeMode P)) (fun p =>
    creationKernel amplitude holonomy p S T +
      annihilationKernel amplitude holonomy p S T)

@[simp, rep_depth thermo]
theorem creationKernel_of_create {P : PrimeCutoff}
    (amplitude holonomy : PrimeMode P → ℂ)
    (p : PrimeMode P) (S T : Vertex P)
    (h : PrimeExteriorGraphDirac.create p S = some T) :
    creationKernel amplitude holonomy p S T =
      amplitude p * holonomy p := by
  simp [creationKernel, h]

@[simp, rep_depth thermo]
theorem creationKernel_of_not_create {P : PrimeCutoff}
    (amplitude holonomy : PrimeMode P → ℂ)
    (p : PrimeMode P) (S T : Vertex P)
    (h : PrimeExteriorGraphDirac.create p S ≠ some T) :
    creationKernel amplitude holonomy p S T = 0 := by
  simp [creationKernel, h]

@[simp, rep_depth thermo]
theorem annihilationKernel_of_annihilate {P : PrimeCutoff}
    (amplitude holonomy : PrimeMode P → ℂ)
    (p : PrimeMode P) (S T : Vertex P)
    (h : PrimeExteriorGraphDirac.annihilate p S = some T) :
    annihilationKernel amplitude holonomy p S T =
      amplitude p * (holonomy p)⁻¹ := by
  simp [annihilationKernel, h]

@[simp, rep_depth thermo]
theorem annihilationKernel_of_not_annihilate {P : PrimeCutoff}
    (amplitude holonomy : PrimeMode P → ℂ)
    (p : PrimeMode P) (S T : Vertex P)
    (h : PrimeExteriorGraphDirac.annihilate p S ≠ some T) :
    annihilationKernel amplitude holonomy p S T = 0 := by
  simp [annihilationKernel, h]

/-! ## 3. Supercharges and finite Cantor--Dirac operator -/

/--
Holonomy-weighted creation supercharge.

`Q(s) = Σ_p amplitude_p * holonomy_p(s) * ε_p`.
-/
@[rep_depth thermo]
def creationSupercharge {P : PrimeCutoff}
    (amplitude holonomy : PrimeMode P → ℂ) :
    CantorField P → CantorField P :=
  fun f S =>
    Finset.sum (Finset.univ : Finset (PrimeMode P)) (fun p =>
      amplitude p * holonomy p * creationPush p f S)

/--
Dual holonomy-inverse annihilation supercharge.

`Q♯(s) = Σ_p amplitude_p * holonomy_p(s)⁻¹ * ι_p`.
-/
@[rep_depth thermo]
def dualAnnihilationSupercharge {P : PrimeCutoff}
    (amplitude holonomy : PrimeMode P → ℂ) :
    CantorField P → CantorField P :=
  fun f S =>
    Finset.sum (Finset.univ : Finset (PrimeMode P)) (fun p =>
      amplitude p * (holonomy p)⁻¹ * annihilationPush p f S)

/--
Finite Cantor--Dirac operator.

`D_C(s) = Q(s) + Q♯(s)`.
-/
@[rep_depth thermo]
def cantorDiracOperator {P : PrimeCutoff}
    (amplitude holonomy : PrimeMode P → ℂ) :
    CantorField P → CantorField P :=
  fun f S =>
    creationSupercharge amplitude holonomy f S +
      dualAnnihilationSupercharge amplitude holonomy f S

@[rep_depth thermo]
theorem cantorDiracOperator_eq_supercharge_sum {P : PrimeCutoff}
    (amplitude holonomy : PrimeMode P → ℂ)
    (f : CantorField P) (S : Vertex P) :
    cantorDiracOperator amplitude holonomy f S =
      creationSupercharge amplitude holonomy f S +
        dualAnnihilationSupercharge amplitude holonomy f S := rfl

/--
Basis delta field on the finite Cantor/Fock lattice.
-/
@[rep_depth thermo]
def basisDelta {P : PrimeCutoff} (T : Vertex P) : CantorField P :=
  fun S => if S = T then 1 else 0

@[simp, rep_depth thermo]
theorem basisDelta_self {P : PrimeCutoff} (T : Vertex P) :
    basisDelta T T = 1 := by
  simp [basisDelta]

@[simp, rep_depth thermo]
theorem basisDelta_of_ne {P : PrimeCutoff} {S T : Vertex P}
    (h : S ≠ T) :
    basisDelta T S = 0 := by
  simp [basisDelta, h]

/--
On an absent prime mode, the creation push-forward hits the inserted basis
state.
-/
@[simp, rep_depth thermo]
theorem creationPush_basis_insert_of_not_mem {P : PrimeCutoff}
    (p : PrimeMode P) (S : Vertex P) (hp : p ∉ S) :
    creationPush p (basisDelta (insert p S)) S = 1 := by
  simp [creationPush_of_not_mem, hp, basisDelta]

/--
On an occupied prime mode, the annihilation push-forward hits the erased basis
state.
-/
@[simp, rep_depth thermo]
theorem annihilationPush_basis_erase_of_mem {P : PrimeCutoff}
    (p : PrimeMode P) (S : Vertex P) (hp : p ∈ S) :
    annihilationPush p (basisDelta (S.erase p)) S = 1 := by
  simp [annihilationPush_of_mem, hp, basisDelta]

/-! ## 4. Bundled finite zeta-Cantor Dirac packet -/

/--
Finite zeta-Cantor Dirac packet.

`amplitude` is the prime-axis coefficient, e.g. a finite model may choose
`sqrt(log p)` or another normalized coefficient.

`holonomy s p` is the spectral twist. Analytically, the intended zeta model
uses `p^(1/2 - s)`, but this finite module keeps the holonomy abstract.
-/
@[rep_depth thermo]
structure FiniteCantorZetaDirac (P : PrimeCutoff) where
  amplitude : PrimeMode P → ℂ
  holonomy : ℂ → PrimeMode P → ℂ

namespace FiniteCantorZetaDirac

variable {P : PrimeCutoff}
variable (D : FiniteCantorZetaDirac P)

/-- Creation supercharge at spectral parameter `s`. -/
@[rep_depth thermo]
def Q (s : ℂ) : CantorField P → CantorField P :=
  creationSupercharge D.amplitude (D.holonomy s)

/-- Dual annihilation supercharge at spectral parameter `s`. -/
@[rep_depth thermo]
def Qsharp (s : ℂ) : CantorField P → CantorField P :=
  dualAnnihilationSupercharge D.amplitude (D.holonomy s)

/-- Finite Cantor--Dirac operator at spectral parameter `s`. -/
@[rep_depth thermo]
def op (s : ℂ) : CantorField P → CantorField P :=
  cantorDiracOperator D.amplitude (D.holonomy s)

/-- Kernel of the finite Cantor--Dirac operator at `s`. -/
@[rep_depth thermo]
def kernel (s : ℂ) (S T : Vertex P) : ℂ :=
  cantorDiracKernel D.amplitude (D.holonomy s) S T

@[rep_depth thermo]
theorem op_eq_Q_add_Qsharp
    (s : ℂ) (f : CantorField P) (S : Vertex P) :
    D.op s f S = D.Q s f S + D.Qsharp s f S := rfl

@[rep_depth thermo]
theorem kernel_eq_sum
    (s : ℂ) (S T : Vertex P) :
    D.kernel s S T =
      Finset.sum (Finset.univ : Finset (PrimeMode P)) (fun p =>
        creationKernel D.amplitude (D.holonomy s) p S T +
          annihilationKernel D.amplitude (D.holonomy s) p S T) := rfl

end FiniteCantorZetaDirac

end InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator
