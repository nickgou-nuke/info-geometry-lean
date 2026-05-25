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

/-- Creation push-forward is nilpotent on a fixed prime axis: `ε_p² = 0`. -/
@[simp, rep_depth thermo]
theorem creationPush_sq_zero {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P) :
    creationPush p (creationPush p f) S = 0 := by
  by_cases hp : p ∈ S
  · simp [hp]
  · have hmem : p ∈ insert p S := by simp
    simp [hp, hmem]

/-- Annihilation push-forward is nilpotent on a fixed prime axis: `ι_p² = 0`. -/
@[simp, rep_depth thermo]
theorem annihilationPush_sq_zero {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P) :
    annihilationPush p (annihilationPush p f) S = 0 := by
  by_cases hp : p ∈ S
  · have hnot : p ∉ S.erase p := by simp
    simp [hp, hnot]
  · simp [hp]

/--
Finite local CAR identity on Cantor fields:

`ε_p ι_p + ι_p ε_p = 1`.

This is a genuine operator lemma, not a certificate. It proves that the
creation/annihilation push-forwards close to the identity on each prime axis.
-/
@[rep_depth thermo]
theorem creation_annihilation_push_anticomm_identity {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P) :
    creationPush p (annihilationPush p f) S
      + annihilationPush p (creationPush p f) S
      =
    f S := by
  by_cases hp : p ∈ S
  · have hnot : p ∉ S.erase p := by simp
    have hins : insert p (S.erase p) = S := Finset.insert_erase hp
    simp [hp, hnot, hins]
  · have hmem : p ∈ insert p S := by simp
    have herase : (insert p S).erase p = S := by
      ext q
      by_cases hq : q = p
      · subst q
        simp [hp]
      · have hpq : p ≠ q := by
          intro h
          exact hq h.symm
        simp [Finset.mem_erase, hq]
    simp [hp, hmem, herase]

/--
Operator form of the local CAR identity on Cantor fields:
`ε_p ι_p + ι_p ε_p = 1` as an extensional equality of field transforms.
-/
@[rep_depth thermo]
theorem creation_annihilation_push_anticomm_identity_funext {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) :
    (fun S => creationPush p (annihilationPush p f) S
        + annihilationPush p (creationPush p f) S) = f := by
  funext S
  exact creation_annihilation_push_anticomm_identity p f S

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

/-! ## 3.5 Critical-line holonomy specialization (finite) -/

/--
Finite zeta-model holonomy specialization on a prime mode:
`h_p(s) = exp((1/2 - s) * log p)`.
-/
@[rep_depth thermo]
def zetaHolonomy {P : PrimeCutoff} (s : ℂ) (p : PrimeMode P) : ℂ :=
  Complex.exp (((1 / 2 : ℂ) - s) * Complex.log (p : ℂ))

/--
Norm readout for the finite zeta-model holonomy specialization.
-/
@[rep_depth thermo]
theorem norm_zetaHolonomy_eq {P : PrimeCutoff} (s : ℂ) (p : PrimeMode P) :
    ‖zetaHolonomy s p‖ = Real.exp ((1 / 2 - s.re) * Real.log (p : ℝ)) := by
  unfold zetaHolonomy
  rw [Complex.norm_exp]
  have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
    symm
    exact Complex.ofReal_log (by positivity)
  have hre : (Complex.log (p : ℂ)).re = Real.log (p : ℝ) := by
    exact congrArg Complex.re hlog
  have him : (Complex.log (p : ℂ)).im = 0 := by
    exact congrArg Complex.im hlog
  have hreS : ((1 / 2 : ℂ) - s).re = 1 / 2 - s.re := by
    simp
  rw [Complex.mul_re, hre, him, hreS]
  ring_nf

/--
For a prime mode, the zeta holonomy has unit norm exactly on the critical line.

`‖p^(1/2-s)‖ = 1 ↔ Re(s) = 1/2` in finite cutoff form.
-/
@[rep_depth thermo]
theorem norm_zetaHolonomy_eq_one_iff_re_eq_half
    {P : PrimeCutoff} (s : ℂ) (p : PrimeMode P) :
    ‖zetaHolonomy s p‖ = 1 ↔ s.re = 1 / 2 := by
  have hp1_nat : 1 < (p : ℕ) := Nat.Prime.one_lt (P.prime_mem p.1 p.2)
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp1_nat
  have hlog_pos : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hlog_ne : Real.log (p : ℝ) ≠ 0 := ne_of_gt hlog_pos

  rw [norm_zetaHolonomy_eq]
  constructor
  · intro h
    have hzero :
        (1 / 2 - s.re) * Real.log (p : ℝ) = 0 :=
      (Real.exp_eq_one_iff _).mp (by simpa using h)
    have hfactor : (1 / 2 - s.re) = 0 := by
      rcases mul_eq_zero.mp hzero with hfac | hlog
      · exact hfac
      · exact False.elim (hlog_ne hlog)
    linarith
  · intro hs
    rw [hs]
    simp

/--
Pointwise holonomy unitarity for the zeta specialization is equivalent to the
critical-line condition, provided the finite prime cutoff is nonempty.
-/
@[rep_depth thermo]
theorem zetaHolonomy_unitaryAt_iff_re_eq_half
    {P : PrimeCutoff} (hP : P.primes.Nonempty) (s : ℂ) :
    (∀ p : PrimeMode P, zetaHolonomy s p ≠ 0 ∧ (zetaHolonomy s p)⁻¹ = star (zetaHolonomy s p))
      ↔ s.re = 1 / 2 := by
  constructor
  · intro hU
    rcases hP with ⟨p0, hp0⟩
    let p : PrimeMode P := ⟨p0, hp0⟩
    have hpU : zetaHolonomy s p ≠ 0 ∧ (zetaHolonomy s p)⁻¹ = star (zetaHolonomy s p) := hU p
    have hnorm_one : ‖zetaHolonomy s p‖ = 1 := by
      rcases hpU with ⟨hp_ne, hp_inv⟩
      have hmul : zetaHolonomy s p * star (zetaHolonomy s p) = (1 : ℂ) := by
        rw [← hp_inv]
        exact mul_inv_cancel₀ hp_ne
      have hnorm_sq : ‖zetaHolonomy s p‖ * ‖star (zetaHolonomy s p)‖ = 1 := by
        have := congrArg norm hmul
        simpa [Complex.norm_mul] using this
      have hnorm_sq' : ‖zetaHolonomy s p‖ ^ 2 = 1 := by
        simpa [pow_two, Complex.norm_conj] using hnorm_sq
      have hnorm_nonneg : 0 ≤ ‖zetaHolonomy s p‖ := norm_nonneg _
      nlinarith
    exact (norm_zetaHolonomy_eq_one_iff_re_eq_half (s := s) (p := p)).1 hnorm_one
  · intro hs p
    refine ⟨?_, ?_⟩
    · unfold zetaHolonomy
      exact Complex.exp_ne_zero _
    · have hnorm : ‖zetaHolonomy s p‖ = 1 :=
        (norm_zetaHolonomy_eq_one_iff_re_eq_half (s := s) (p := p)).2 hs
      simpa using Complex.inv_eq_conj hnorm

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

open InfoGeometry.Arithmetic.PrimeExteriorGraphDirac

/--
The creation supercharge applied to a basis delta has matrix coefficient equal
to the creation kernel.

This is an actual kernel/operator compatibility lemma.
-/
theorem creationSupercharge_basisDelta_eq_kernel_sum {P : PrimeCutoff}
    (amplitude holonomy : PrimeMode P → ℂ)
    (S T : Vertex P) :
    creationSupercharge amplitude holonomy (basisDelta T) S =
      Finset.sum (Finset.univ : Finset (PrimeMode P))
        (fun p => creationKernel amplitude holonomy p S T) := by
  unfold creationSupercharge
  apply Finset.sum_congr rfl
  intro p hp
  unfold creationPush creationKernel optionEval basisDelta
  cases h : PrimeExteriorGraphDirac.create p S with
  | none =>
      simp
  | some U =>
      by_cases hUT : U = T
      · subst U
        simp
      · simp [hUT]

/--
The dual annihilation supercharge applied to a basis delta has matrix coefficient
equal to the annihilation kernel.

This is the annihilation half of the finite Cantor--Dirac kernel theorem.
-/
theorem dualAnnihilationSupercharge_basisDelta_eq_kernel_sum {P : PrimeCutoff}
    (amplitude holonomy : PrimeMode P → ℂ)
    (S T : Vertex P) :
    dualAnnihilationSupercharge amplitude holonomy (basisDelta T) S =
      Finset.sum (Finset.univ : Finset (PrimeMode P))
        (fun p => annihilationKernel amplitude holonomy p S T) := by
  unfold dualAnnihilationSupercharge
  apply Finset.sum_congr rfl
  intro p hp
  unfold annihilationPush annihilationKernel optionEval basisDelta
  cases h : PrimeExteriorGraphDirac.annihilate p S with
  | none =>
      simp
  | some U =>
      by_cases hUT : U = T
      · subst U
        simp
      · simp [hUT]

/--
The finite Cantor--Dirac kernel is the matrix coefficient of the finite
Cantor--Dirac operator on the basis delta.
-/
theorem cantorDiracOperator_basisDelta_eq_kernel {P : PrimeCutoff}
    (amplitude holonomy : PrimeMode P → ℂ)
    (S T : Vertex P) :
    cantorDiracOperator amplitude holonomy (basisDelta T) S =
      cantorDiracKernel amplitude holonomy S T := by
  unfold cantorDiracOperator cantorDiracKernel
  rw [creationSupercharge_basisDelta_eq_kernel_sum]
  rw [dualAnnihilationSupercharge_basisDelta_eq_kernel_sum]
  rw [Finset.sum_add_distrib]

namespace FiniteCantorZetaDirac

variable {P : PrimeCutoff}
variable (D : FiniteCantorZetaDirac P)

/--
Bundled specialization: the bundled kernel is the matrix coefficient of the
bundled operator on a basis delta.
-/
theorem op_basisDelta_eq_kernel
    (s : ℂ)
    (S T : Vertex P) :
    D.op s (basisDelta T) S = D.kernel s S T := by
  exact cantorDiracOperator_basisDelta_eq_kernel
    D.amplitude (D.holonomy s) S T

/-! ## 5. Finite adjoint pairing surface -/

/--
Pointwise holonomy unitarity at spectral parameter `s`:
`hol(s,p)⁻¹ = conj(hol(s,p))` with nonvanishing.
-/
@[rep_depth thermo]
def HolonomyUnitaryAt (s : ℂ) : Prop :=
  ∀ p : PrimeMode P, (D.holonomy s p) ≠ 0 ∧ (D.holonomy s p)⁻¹ = star (D.holonomy s p)

/--
Bundled critical-line criterion for pointwise holonomy unitarity under the
zeta holonomy specialization.
-/
@[rep_depth thermo]
theorem HolonomyUnitaryAt_iff_re_eq_half_of_zetaHolonomy
    (hP : P.primes.Nonempty) (s : ℂ)
    (hhol : D.holonomy s = zetaHolonomy (P := P) s) :
    D.HolonomyUnitaryAt s ↔ s.re = 1 / 2 := by
  unfold HolonomyUnitaryAt
  rw [hhol]
  exact zetaHolonomy_unitaryAt_iff_re_eq_half (P := P) hP s

/--
Under zeta holonomy specialization, critical-line real part implies pointwise
holonomy unitarity.
-/
@[rep_depth thermo]
theorem HolonomyUnitaryAt_of_re_eq_half_of_zetaHolonomy
    (hP : P.primes.Nonempty) (s : ℂ)
    (hhol : D.holonomy s = zetaHolonomy (P := P) s)
    (hs : s.re = 1 / 2) :
    D.HolonomyUnitaryAt s := by
  exact (D.HolonomyUnitaryAt_iff_re_eq_half_of_zetaHolonomy hP s hhol).2 hs

/--
Under zeta holonomy specialization, pointwise holonomy unitarity forces the
critical-line real part.
-/
@[rep_depth thermo]
theorem re_eq_half_of_HolonomyUnitaryAt_of_zetaHolonomy
    (hP : P.primes.Nonempty) (s : ℂ)
    (hhol : D.holonomy s = zetaHolonomy (P := P) s)
    (hU : D.HolonomyUnitaryAt s) :
    s.re = 1 / 2 := by
  exact (D.HolonomyUnitaryAt_iff_re_eq_half_of_zetaHolonomy hP s hhol).1 hU

/-- Finite sesquilinear pairing on Cantor fields. -/
@[rep_depth thermo]
def pairing (f g : CantorField P) : ℂ :=
  ∑ S : Vertex P, star (f S) * g S

/--
Adjoint-pair predicate for endomorphisms of the finite Cantor field.
-/
@[rep_depth thermo]
def IsAdjointPair
    (A B : CantorField P → CantorField P) : Prop :=
  ∀ f g : CantorField P, pairing (A f) g = pairing f (B g)

/--
Conjugate-transposed readout of an adjoint pair.

If `A` is adjoint to `B` under `pairing`, then
`star (pairing f (B g)) = pairing g (A f)`.
-/
@[rep_depth thermo]
theorem IsAdjointPair.conj_swap
    {A B : CantorField P → CantorField P}
    (hAB : IsAdjointPair (P := P) A B)
    (f g : CantorField P) :
    star (pairing f (B g)) = pairing g (A f) := by
  calc
    star (pairing f (B g))
        = star (pairing (A f) g) := by rw [hAB f g]
    _ = pairing g (A f) := by
      unfold pairing
      simp [mul_comm]

@[simp, rep_depth thermo]
theorem pairing_add_left (f₁ f₂ g : CantorField P) :
    pairing (f₁ + f₂) g = pairing f₁ g + pairing f₂ g := by
  simp [pairing, add_mul, Finset.sum_add_distrib]

@[simp, rep_depth thermo]
theorem pairing_add_right (f g₁ g₂ : CantorField P) :
    pairing f (g₁ + g₂) = pairing f g₁ + pairing f g₂ := by
  simp [pairing, mul_add, Finset.sum_add_distrib]

@[simp, rep_depth thermo]
theorem pairing_smul_left (c : ℂ) (f g : CantorField P) :
    pairing (c • f) g = (star c) * pairing f g := by
  simp [pairing, Finset.mul_sum, mul_left_comm, mul_comm]

@[simp, rep_depth thermo]
theorem pairing_smul_right (c : ℂ) (f g : CantorField P) :
    pairing f (c • g) = c * pairing f g := by
  simp [pairing, Finset.mul_sum, mul_assoc, mul_comm]

/--
Conjugate symmetry of the finite Cantor sesquilinear pairing.
-/
@[simp, rep_depth thermo]
theorem pairing_conj_symm (f g : CantorField P) :
    star (pairing f g) = pairing g f := by
  unfold pairing
  simp [mul_comm]

@[simp, rep_depth thermo]
theorem pairing_right_basisDelta (f : CantorField P) (T : Vertex P) :
    pairing f (basisDelta T) = star (f T) := by
  unfold pairing basisDelta
  simp

@[simp, rep_depth thermo]
theorem pairing_left_basisDelta (f : CantorField P) (T : Vertex P) :
    pairing (basisDelta T) f = f T := by
  unfold pairing basisDelta
  simp

@[simp, rep_depth thermo]
theorem pairing_sum_left (s : Finset (PrimeMode P))
    (F : PrimeMode P → CantorField P) (g : CantorField P) :
    pairing (Finset.sum s fun p => F p) g = Finset.sum s (fun p => pairing (F p) g) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      unfold pairing
      simp
  | @insert a s ha ih =>
      simp [ha, pairing_add_left, ih]

@[simp, rep_depth thermo]
theorem pairing_sum_right (f : CantorField P) (s : Finset (PrimeMode P))
    (G : PrimeMode P → CantorField P) :
    pairing f (Finset.sum s fun p => G p) = Finset.sum s (fun p => pairing f (G p)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      unfold pairing
      simp
  | @insert a s ha ih =>
      simp [ha, pairing_add_right, ih]

/--
If each prime-axis creation/annihilation channel is adjoint for the finite
pairing, and the holonomy is unitary with real amplitudes, then `Q♯` is the
adjoint partner of `Q`.

This is a theorem-level closure surface over existing finite operators.
-/
@[rep_depth thermo]
theorem Qsharp_isAdjointPair_of_unitary
    (s : ℂ)
    (hAdjMode :
      ∀ p : PrimeMode P,
        IsAdjointPair (P := P)
          (fun f S => D.amplitude p * D.holonomy s p * creationPush p f S)
          (fun f S => D.amplitude p * (D.holonomy s p)⁻¹ * annihilationPush p f S)) :
    IsAdjointPair (P := P) (D.Q s) (D.Qsharp s) := by
  intro f g
  unfold Q Qsharp creationSupercharge dualAnnihilationSupercharge
  have hQ :
      (fun S => ∑ p : PrimeMode P, D.amplitude p * D.holonomy s p * creationPush p f S)
        =
      (∑ p : PrimeMode P, fun S => D.amplitude p * D.holonomy s p * creationPush p f S) := by
    funext S
    simp
  have hQsharp :
      (fun S => ∑ p : PrimeMode P, D.amplitude p * (D.holonomy s p)⁻¹ * annihilationPush p g S)
        =
      (∑ p : PrimeMode P, fun S => D.amplitude p * (D.holonomy s p)⁻¹ * annihilationPush p g S) := by
    funext S
    simp
  rw [hQ, hQsharp]
  rw [pairing_sum_left (P := P)
      (s := (Finset.univ : Finset (PrimeMode P)))
      (F := fun p S => D.amplitude p * D.holonomy s p * creationPush p f S) g]
  rw [pairing_sum_right (P := P) f
      (s := (Finset.univ : Finset (PrimeMode P)))
      (G := fun p S => D.amplitude p * (D.holonomy s p)⁻¹ * annihilationPush p g S)]
  refine Finset.sum_congr rfl ?_
  intro p hp
  exact hAdjMode p f g

/--
Modewise reverse adjointness lifts to reverse adjointness of finite summed
supercharges.
-/
@[rep_depth thermo]
theorem Q_isAdjointPair_of_unitary
    (s : ℂ)
    (hAdjModeRev :
      ∀ p : PrimeMode P,
        IsAdjointPair (P := P)
          (fun f S => D.amplitude p * (D.holonomy s p)⁻¹ * annihilationPush p f S)
          (fun f S => D.amplitude p * D.holonomy s p * creationPush p f S)) :
    IsAdjointPair (P := P) (D.Qsharp s) (D.Q s) := by
  intro f g
  unfold Q Qsharp creationSupercharge dualAnnihilationSupercharge
  have hQ :
      (fun S => ∑ p : PrimeMode P, D.amplitude p * D.holonomy s p * creationPush p g S)
        =
      (∑ p : PrimeMode P, fun S => D.amplitude p * D.holonomy s p * creationPush p g S) := by
    funext S
    simp
  have hQsharp :
      (fun S => ∑ p : PrimeMode P, D.amplitude p * (D.holonomy s p)⁻¹ * annihilationPush p f S)
        =
      (∑ p : PrimeMode P, fun S => D.amplitude p * (D.holonomy s p)⁻¹ * annihilationPush p f S) := by
    funext S
    simp
  rw [hQsharp, hQ]
  rw [pairing_sum_left (P := P)
      (s := (Finset.univ : Finset (PrimeMode P)))
      (F := fun p S => D.amplitude p * (D.holonomy s p)⁻¹ * annihilationPush p f S) g]
  rw [pairing_sum_right (P := P) f
      (s := (Finset.univ : Finset (PrimeMode P)))
      (G := fun p S => D.amplitude p * D.holonomy s p * creationPush p g S)]
  refine Finset.sum_congr rfl ?_
  intro p hp
  exact hAdjModeRev p f g

/--
Finite pairing self-adjointness of `op` as a consequence of `Q/Q♯` adjointness.
-/
@[rep_depth thermo]
theorem op_isSelfAdjoint_of_unitary
    (s : ℂ)
    (hQQsharp : IsAdjointPair (P := P) (D.Q s) (D.Qsharp s))
    (hQsharpQ : IsAdjointPair (P := P) (D.Qsharp s) (D.Q s)) :
    IsAdjointPair (P := P) (D.op s) (D.op s) := by
  intro f g
  unfold op cantorDiracOperator
  have h1 := hQQsharp f g
  have h2 := hQsharpQ f g
  calc
    pairing (D.Q s f + D.Qsharp s f) g
        = pairing (D.Q s f) g + pairing (D.Qsharp s f) g := by
            simp [pairing_add_left]
    _ = pairing f (D.Qsharp s g) + pairing f (D.Q s g) := by simp [h1, h2]
    _ = pairing f (D.Qsharp s g + D.Q s g) := by
          simp [pairing_add_right]
    _ = pairing f (D.Q s g + D.Qsharp s g) := by abel_nf

/--
Direct finite self-adjointness corollary from modewise adjointness.

If each prime-mode channel is adjoint in both directions, then the finite
Cantor--Dirac operator `op = Q + Q♯` is self-adjoint for the finite pairing.
-/
@[rep_depth thermo]
theorem op_isSelfAdjoint_of_modewiseAdjoint
    (s : ℂ)
    (hAdjMode :
      ∀ p : PrimeMode P,
        IsAdjointPair (P := P)
          (fun f S => D.amplitude p * D.holonomy s p * creationPush p f S)
          (fun f S => D.amplitude p * (D.holonomy s p)⁻¹ * annihilationPush p f S))
    (hAdjModeRev :
      ∀ p : PrimeMode P,
        IsAdjointPair (P := P)
          (fun f S => D.amplitude p * (D.holonomy s p)⁻¹ * annihilationPush p f S)
          (fun f S => D.amplitude p * D.holonomy s p * creationPush p f S)) :
    IsAdjointPair (P := P) (D.op s) (D.op s) := by
  apply D.op_isSelfAdjoint_of_unitary (s := s)
  · exact D.Qsharp_isAdjointPair_of_unitary (s := s) hAdjMode
  · exact D.Q_isAdjointPair_of_unitary (s := s) hAdjModeRev

/--
Zeta-specialized finite self-adjointness of the Cantor--Dirac operator on the
critical line.

This theorem stays inside the existing owner lane: once modewise adjointness is
available and `D.holonomy` is specialized to `zetaHolonomy`, `Re(s)=1/2`
implies self-adjointness of `D.op s` for the finite pairing.
-/
@[rep_depth thermo]
theorem op_isSelfAdjoint_of_modewiseAdjoint_of_zetaHolonomy
    (hP : P.primes.Nonempty) (s : ℂ)
    (hhol : D.holonomy s = zetaHolonomy (P := P) s)
    (hs : s.re = 1 / 2)
    (hAdjMode :
      ∀ p : PrimeMode P,
        IsAdjointPair (P := P)
          (fun f S => D.amplitude p * D.holonomy s p * creationPush p f S)
          (fun f S => D.amplitude p * (D.holonomy s p)⁻¹ * annihilationPush p f S))
    (hAdjModeRev :
      ∀ p : PrimeMode P,
        IsAdjointPair (P := P)
          (fun f S => D.amplitude p * (D.holonomy s p)⁻¹ * annihilationPush p f S)
          (fun f S => D.amplitude p * D.holonomy s p * creationPush p f S)) :
    IsAdjointPair (P := P) (D.op s) (D.op s) := by
  have hU : D.HolonomyUnitaryAt s :=
    D.HolonomyUnitaryAt_of_re_eq_half_of_zetaHolonomy hP s hhol hs
  exact D.op_isSelfAdjoint_of_modewiseAdjoint s hAdjMode hAdjModeRev

/--
Zeta-specialized finite self-adjointness from pointwise holonomy unitarity.

This is the direct `HolonomyUnitaryAt` entrypoint: if the zeta-specialized
holonomy is unitary at `s`, then `D.op s` is self-adjoint once modewise
adjointness is provided.
-/
@[rep_depth thermo]
theorem op_isSelfAdjoint_of_modewiseAdjoint_of_HolonomyUnitaryAt_zetaHolonomy
    (hP : P.primes.Nonempty) (s : ℂ)
    (hhol : D.holonomy s = zetaHolonomy (P := P) s)
    (hU : D.HolonomyUnitaryAt s)
    (hAdjMode :
      ∀ p : PrimeMode P,
        IsAdjointPair (P := P)
          (fun f S => D.amplitude p * D.holonomy s p * creationPush p f S)
          (fun f S => D.amplitude p * (D.holonomy s p)⁻¹ * annihilationPush p f S))
    (hAdjModeRev :
      ∀ p : PrimeMode P,
        IsAdjointPair (P := P)
          (fun f S => D.amplitude p * (D.holonomy s p)⁻¹ * annihilationPush p f S)
          (fun f S => D.amplitude p * D.holonomy s p * creationPush p f S)) :
    IsAdjointPair (P := P) (D.op s) (D.op s) := by
  have hs : s.re = 1 / 2 :=
    D.re_eq_half_of_HolonomyUnitaryAt_of_zetaHolonomy hP s hhol hU
  exact D.op_isSelfAdjoint_of_modewiseAdjoint_of_zetaHolonomy
    hP s hhol hs hAdjMode hAdjModeRev

/--
Kernel Hermitian symmetry induced by finite self-adjointness:

`star (K(S,T)) = K(T,S)`.
-/
@[rep_depth thermo]
theorem kernel_conj_symm_of_op_isSelfAdjoint
    (s : ℂ)
    (hself : IsAdjointPair (P := P) (D.op s) (D.op s))
    (S T : Vertex P) :
    star (D.kernel s S T) = D.kernel s T S := by
  have hpair := hself (basisDelta T) (basisDelta S)
  have hL :
      pairing (D.op s (basisDelta T)) (basisDelta S) = star (D.kernel s S T) := by
    rw [pairing_right_basisDelta]
    simpa using congrArg star (D.op_basisDelta_eq_kernel (s := s) (S := S) (T := T))
  have hR :
      pairing (basisDelta T) (D.op s (basisDelta S)) = D.kernel s T S := by
    rw [pairing_left_basisDelta]
    simpa using (D.op_basisDelta_eq_kernel (s := s) (S := T) (T := S))
  rw [hL, hR] at hpair
  exact hpair

/--
Zeta-specialized kernel Hermitian symmetry on the critical line:

`star (K_s(S,T)) = K_s(T,S)`.
-/
@[rep_depth thermo]
theorem kernel_conj_symm_of_modewiseAdjoint_of_zetaHolonomy
    (hP : P.primes.Nonempty) (s : ℂ)
    (hhol : D.holonomy s = zetaHolonomy (P := P) s)
    (hs : s.re = 1 / 2)
    (hAdjMode :
      ∀ p : PrimeMode P,
        IsAdjointPair (P := P)
          (fun f S => D.amplitude p * D.holonomy s p * creationPush p f S)
          (fun f S => D.amplitude p * (D.holonomy s p)⁻¹ * annihilationPush p f S))
    (hAdjModeRev :
      ∀ p : PrimeMode P,
        IsAdjointPair (P := P)
          (fun f S => D.amplitude p * (D.holonomy s p)⁻¹ * annihilationPush p f S)
          (fun f S => D.amplitude p * D.holonomy s p * creationPush p f S))
    (S T : Vertex P) :
    star (D.kernel s S T) = D.kernel s T S := by
  have hself : IsAdjointPair (P := P) (D.op s) (D.op s) :=
    D.op_isSelfAdjoint_of_modewiseAdjoint_of_zetaHolonomy
      hP s hhol hs hAdjMode hAdjModeRev
  exact D.kernel_conj_symm_of_op_isSelfAdjoint s hself S T

end FiniteCantorZetaDirac

end InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator
