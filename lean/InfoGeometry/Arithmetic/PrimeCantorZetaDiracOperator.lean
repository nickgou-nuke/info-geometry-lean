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

/-! ## 1a. Split-Majorana operators from nilpotent creation/annihilation -/

/--
Split-Majorana plus operator:

  c_p = ε_p + ι_p.

This is the prime-axis bit-flip operator.
-/
@[rep_depth thermo]
def majoranaPlusPush {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P) : ℂ :=
  creationPush p f S + annihilationPush p f S

/--
Split-Majorana minus operator:

  d_p = ε_p - ι_p.

Together with `majoranaPlusPush`, this gives the split Clifford pair.
-/
@[rep_depth thermo]
def majoranaMinusPush {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P) : ℂ :=
  creationPush p f S - annihilationPush p f S

/--
The plus Majorana squares to the identity:

  (ε_p + ι_p)^2 = 1.

This is the concrete `Op² = 1` lemma.
-/
@[rep_depth thermo]
theorem majoranaPlusPush_sq_identity {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P) :
    majoranaPlusPush p (majoranaPlusPush p f) S = f S := by
  by_cases hp : p ∈ S
  · have hnot : p ∉ S.erase p := by
      simp
    have hins : insert p (S.erase p) = S := Finset.insert_erase hp
    simp [majoranaPlusPush, hp, hnot, hins]
  · have hmem : p ∈ insert p S := by
      simp
    have herase : (insert p S).erase p = S := by
      ext q
      by_cases hq : q = p
      · subst q
        simp [hp]
      · have hpq : p ≠ q := by
          intro h
          exact hq h.symm
        simp [Finset.mem_erase, hq]
    simp [majoranaPlusPush, hp, hmem, herase]

/--
The minus Majorana squares to negative identity:

  (ε_p - ι_p)^2 = -1.

This is the concrete `Op² = -1` lemma.
-/
@[rep_depth thermo]
theorem majoranaMinusPush_sq_neg_identity {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P) :
    majoranaMinusPush p (majoranaMinusPush p f) S = - f S := by
  by_cases hp : p ∈ S
  · have hnot : p ∉ S.erase p := by
      simp
    have hins : insert p (S.erase p) = S := Finset.insert_erase hp
    simp [majoranaMinusPush, hp, hnot, hins]
  · have hmem : p ∈ insert p S := by
      simp
    have herase : (insert p S).erase p = S := by
      ext q
      by_cases hq : q = p
      · subst q
        simp [hp]
      · have hpq : p ≠ q := by
          intro h
          exact hq h.symm
        simp [Finset.mem_erase, hq]
    simp [majoranaMinusPush, hp, hmem, herase]

/--
The split Majoranas anticommute:

  (ε_p + ι_p)(ε_p - ι_p) + (ε_p - ι_p)(ε_p + ι_p) = 0.

This is the concrete split-Clifford anticommutator lemma.
-/
@[rep_depth thermo]
theorem majoranaPlus_minus_anticomm {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P) :
    majoranaPlusPush p (majoranaMinusPush p f) S
      + majoranaMinusPush p (majoranaPlusPush p f) S = 0 := by
  by_cases hp : p ∈ S
  · have hnot : p ∉ S.erase p := by
      simp
    have hins : insert p (S.erase p) = S := Finset.insert_erase hp
    simp [majoranaPlusPush, majoranaMinusPush, hp, hnot, hins]
  · have hmem : p ∈ insert p S := by
      simp
    have herase : (insert p S).erase p = S := by
      ext q
      by_cases hq : q = p
      · subst q
        simp [hp]
      · have hpq : p ≠ q := by
          intro h
          exact hq h.symm
        simp [Finset.mem_erase, hq]
    simp [majoranaPlusPush, majoranaMinusPush, hp, hmem, herase]

/--
Operator form of the split-Majorana anticommutator:

`(c_p d_p + d_p c_p) f = 0` as an extensional equality of field transforms.
-/
@[rep_depth thermo]
theorem majoranaPlus_minus_anticomm_funext {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) :
    (fun S =>
      majoranaPlusPush p (majoranaMinusPush p f) S
        + majoranaMinusPush p (majoranaPlusPush p f) S)
      = (fun _ => (0 : ℂ)) := by
  funext S
  exact majoranaPlus_minus_anticomm p f S

/--
Operator commutation form of the split-Majorana anticommutator:

`c_p d_p = - d_p c_p` pointwise on fields.
-/
@[rep_depth thermo]
theorem majoranaPlus_comp_minus_eq_neg_minus_comp_plus
    {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P) :
    majoranaPlusPush p (majoranaMinusPush p f) S
      =
    - majoranaMinusPush p (majoranaPlusPush p f) S := by
  have h := majoranaPlus_minus_anticomm p f S
  exact eq_neg_of_add_eq_zero_left h

/--
Extensional operator form of `c_p d_p = - d_p c_p`.
-/
@[rep_depth thermo]
theorem majoranaPlus_comp_minus_eq_neg_minus_comp_plus_funext
    {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) :
    (fun S => majoranaPlusPush p (majoranaMinusPush p f) S)
      =
    (fun S => - majoranaMinusPush p (majoranaPlusPush p f) S) := by
  funext S
  exact majoranaPlus_comp_minus_eq_neg_minus_comp_plus p f S

/--
Local Witt-generator square-law closure on one prime mode:

`ε_p^2 = 0`, `ι_p^2 = 0`, `{ε_p, ι_p} = 1`
imply
`(ε_p + ι_p)^2 = 1` and `(ε_p - ι_p)^2 = -1`.
-/
@[rep_depth thermo]
theorem witt_square_law_closure {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P) :
    creationPush p (creationPush p f) S = 0 ∧
    annihilationPush p (annihilationPush p f) S = 0 ∧
    (creationPush p (annihilationPush p f) S
      + annihilationPush p (creationPush p f) S = f S) ∧
    majoranaPlusPush p (majoranaPlusPush p f) S = f S ∧
    majoranaMinusPush p (majoranaMinusPush p f) S = -f S := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact creationPush_sq_zero p f S
  · exact annihilationPush_sq_zero p f S
  · exact creation_annihilation_push_anticomm_identity p f S
  · exact majoranaPlusPush_sq_identity p f S
  · exact majoranaMinusPush_sq_neg_identity p f S

/--
Inverse coordinate formula:

`ε_p = (c_p + d_p)/2`, with `c_p = ε_p + ι_p`, `d_p = ε_p - ι_p`.
-/
@[rep_depth thermo]
theorem creationPush_eq_half_plus_majorana
    {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P) :
    creationPush p f S =
      (majoranaPlusPush p f S + majoranaMinusPush p f S) / 2 := by
  unfold majoranaPlusPush majoranaMinusPush
  ring

/--
Inverse coordinate formula:

`ι_p = (c_p - d_p)/2`, with `c_p = ε_p + ι_p`, `d_p = ε_p - ι_p`.
-/
@[rep_depth thermo]
theorem annihilationPush_eq_half_minus_majorana
    {P : PrimeCutoff}
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P) :
    annihilationPush p f S =
      (majoranaPlusPush p f S - majoranaMinusPush p f S) / 2 := by
  unfold majoranaPlusPush majoranaMinusPush
  ring

/--
Weighted plus-Majorana Dirac block:

  D_p = a c_p.
-/
@[rep_depth thermo]
def weightedMajoranaPlusPush {P : PrimeCutoff}
    (a : ℂ) (p : PrimeMode P) (f : CantorField P) (S : Vertex P) : ℂ :=
  a * majoranaPlusPush p f S

/--
Weighted minus-Majorana Dirac block:

  D'_p = a d_p.
-/
@[rep_depth thermo]
def weightedMajoranaMinusPush {P : PrimeCutoff}
    (a : ℂ) (p : PrimeMode P) (f : CantorField P) (S : Vertex P) : ℂ :=
  a * majoranaMinusPush p f S

/--
The weighted plus-Majorana Dirac block squares to scalar multiplication:

  `(a c_p)^2 = a^2`.
-/
@[rep_depth thermo]
theorem weightedMajoranaPlusPush_sq {P : PrimeCutoff}
    (a : ℂ) (p : PrimeMode P) (f : CantorField P) (S : Vertex P) :
    weightedMajoranaPlusPush a p (weightedMajoranaPlusPush a p f) S =
      (a * a) * f S := by
  by_cases hp : p ∈ S
  · have hnot : p ∉ S.erase p := by
      simp
    have hins : insert p (S.erase p) = S := Finset.insert_erase hp
    simp [weightedMajoranaPlusPush, majoranaPlusPush, hp, hnot, hins]
    ring
  · have hmem : p ∈ insert p S := by
      simp
    have herase : (insert p S).erase p = S := by
      ext q
      by_cases hq : q = p
      · subst q
        simp [hp]
      · simp [Finset.mem_erase, hq]
    simp [weightedMajoranaPlusPush, majoranaPlusPush, hp, hmem, herase]
    ring

/--
The weighted minus-Majorana Dirac block squares to negative scalar multiplication:

  `(a d_p)^2 = -a^2`.
-/
@[rep_depth thermo]
theorem weightedMajoranaMinusPush_sq {P : PrimeCutoff}
    (a : ℂ) (p : PrimeMode P) (f : CantorField P) (S : Vertex P) :
    weightedMajoranaMinusPush a p (weightedMajoranaMinusPush a p f) S =
      - ((a * a) * f S) := by
  by_cases hp : p ∈ S
  · have hnot : p ∉ S.erase p := by
      simp
    have hins : insert p (S.erase p) = S := Finset.insert_erase hp
    simp [weightedMajoranaMinusPush, majoranaMinusPush, hp, hnot, hins]
    ring
  · have hmem : p ∈ insert p S := by
      simp
    have herase : (insert p S).erase p = S := by
      ext q
      by_cases hq : q = p
      · subst q
        simp [hp]
      · simp [Finset.mem_erase, hq]
    simp [weightedMajoranaMinusPush, majoranaMinusPush, hp, hmem, herase]
    ring

/--
Weighted split-Majorana anticommutator:

`(a c_p)(a d_p) + (a d_p)(a c_p) = 0`.
-/
@[rep_depth thermo]
theorem weightedMajoranaPlus_minus_anticomm {P : PrimeCutoff}
    (a : ℂ) (p : PrimeMode P) (f : CantorField P) (S : Vertex P) :
    weightedMajoranaPlusPush a p (weightedMajoranaMinusPush a p f) S
      + weightedMajoranaMinusPush a p (weightedMajoranaPlusPush a p f) S = 0 := by
  by_cases hp : p ∈ S
  · have hnot : p ∉ S.erase p := by simp
    have hins : insert p (S.erase p) = S := Finset.insert_erase hp
    simp [weightedMajoranaPlusPush, weightedMajoranaMinusPush,
      majoranaPlusPush, majoranaMinusPush, hp, hnot, hins]
  · have hmem : p ∈ insert p S := by simp
    have herase : (insert p S).erase p = S := by
      ext q
      by_cases hq : q = p
      · subst q
        simp [hp]
      · simp [Finset.mem_erase, hq]
    simp [weightedMajoranaPlusPush, weightedMajoranaMinusPush,
      majoranaPlusPush, majoranaMinusPush, hp, hmem, herase]

/--
Extensional form of the weighted split-Majorana anticommutator.
-/
@[rep_depth thermo]
theorem weightedMajoranaPlus_minus_anticomm_funext {P : PrimeCutoff}
    (a : ℂ) (p : PrimeMode P) (f : CantorField P) :
    (fun S =>
      weightedMajoranaPlusPush a p (weightedMajoranaMinusPush a p f) S
        + weightedMajoranaMinusPush a p (weightedMajoranaPlusPush a p f) S)
      = (fun _ => (0 : ℂ)) := by
  funext S
  exact weightedMajoranaPlus_minus_anticomm a p f S

/-! ## 1b. Local Witt → projector/majorana algebra (no wrappers) -/

/--
From a local nilpotent CAR/Witt pair `ε, ι`, the number and hole operators
are idempotent:

* `N = ε*ι` with `N^2 = N`;
* `H = ι*ε` with `H^2 = H`.
-/
@[rep_depth thermo]
theorem projector_from_nilpotents
    {R : Type*} [Ring R]
    {ε ι : R}
    (hε : ε * ε = 0)
    (hι : ι * ι = 0)
    (hcar : ε * ι + ι * ε = 1) :
    (ε * ι) * (ε * ι) = ε * ι ∧
    (ι * ε) * (ι * ε) = ι * ε := by
  refine ⟨?_, ?_⟩
  · calc
      (ε * ι) * (ε * ι) = ε * (ι * ε) * ι := by
        noncomm_ring
      _ = ε * (1 - ε * ι) * ι := by
        have hιε : ι * ε = 1 - ε * ι := by
          rw [← hcar]
          noncomm_ring
        rw [hιε]
      _ = (ε * (1 - ε * ι)) * ι := by
        rw [mul_assoc]
      _ = (ε * 1 - ε * (ε * ι)) * ι := by
        rw [mul_sub]
      _ = (ε - (ε * ε) * ι) * ι := by
        rw [mul_one, mul_assoc]
      _ = (ε - 0 * ι) * ι := by
        rw [hε]
      _ = ε * ι := by
        simp
  · calc
      (ι * ε) * (ι * ε) = ι * (ε * ι) * ε := by
        noncomm_ring
      _ = ι * (1 - ι * ε) * ε := by
        have hει : ε * ι = 1 - ι * ε := by
          rw [← hcar]
          noncomm_ring
        rw [hει]
      _ = (ι * (1 - ι * ε)) * ε := by
        rw [mul_assoc]
      _ = (ι * 1 - ι * (ι * ε)) * ε := by
        rw [mul_sub]
      _ = (ι - (ι * ι) * ε) * ε := by
        rw [mul_one, mul_assoc]
      _ = (ι - 0 * ε) * ε := by
        rw [hι]
      _ = ι * ε := by
        simp

/--
For split Majoranas `c = ε + ι`, `d = ε - ι`, the product is parity:

`c*d = 1 - 2*(ε*ι)`.
-/
@[rep_depth thermo]
theorem parity_from_majorana_product
    {R : Type*} [Ring R]
    {ε ι : R}
    (hε : ε * ε = 0)
    (hι : ι * ι = 0)
    (hcar : ε * ι + ι * ε = 1) :
    (ε + ι) * (ε - ι) = 1 - (2 : R) * (ε * ι) := by
  calc
    (ε + ι) * (ε - ι)
        = ε * ε - ε * ι + ι * ε - ι * ι := by
            noncomm_ring
    _ = 0 - ε * ι + ι * ε - 0 := by
            rw [hε, hι]
    _ = ι * ε - ε * ι := by
            noncomm_ring
    _ = (1 - ε * ι) - ε * ι := by
            have hιε : ι * ε = 1 - ε * ι := by
              rw [← hcar]
              noncomm_ring
            rw [hιε]
    _ = 1 - (2 : R) * (ε * ι) := by
            noncomm_ring

/--
Local number operator idempotency:

`N_j := ε_j * ι_j` satisfies `N_j * N_j = N_j`.
-/
@[rep_depth thermo]
theorem localNumber_idempotent
    {R : Type*} [Ring R]
    {ε_j ι_j : R}
    (hε : ε_j * ε_j = 0)
    (hι : ι_j * ι_j = 0)
    (hcar : ε_j * ι_j + ι_j * ε_j = 1) :
    (ε_j * ι_j) * (ε_j * ι_j) = ε_j * ι_j := by
  exact (projector_from_nilpotents (ε := ε_j) (ι := ι_j) hε hι hcar).1

/--
Local parity/tilt identity:

`Π_j = 1 - 2 * N_j` for `Π_j := (ε_j + ι_j) * (ε_j - ι_j)` and
`N_j := ε_j * ι_j`.
-/
@[rep_depth thermo]
theorem localParity_eq_one_sub_two_number
    {R : Type*} [Ring R]
    {ε_j ι_j : R}
    (hε : ε_j * ε_j = 0)
    (hι : ι_j * ι_j = 0)
    (hcar : ε_j * ι_j + ι_j * ε_j = 1) :
    (ε_j + ι_j) * (ε_j - ι_j) = 1 - (2 : R) * (ε_j * ι_j) := by
  exact parity_from_majorana_product (ε := ε_j) (ι := ι_j) hε hι hcar

/--
Local vacuum projector idempotency:

`(1 - N_j)^2 = 1 - N_j` where `N_j := ε_j * ι_j`.
-/
@[rep_depth thermo]
theorem localVacuumProjector_idempotent
    {R : Type*} [Ring R]
    {ε_j ι_j : R}
    (hε : ε_j * ε_j = 0)
    (hι : ι_j * ι_j = 0)
    (hcar : ε_j * ι_j + ι_j * ε_j = 1) :
    (1 - ε_j * ι_j) * (1 - ε_j * ι_j) = 1 - ε_j * ι_j := by
  have hN : (ε_j * ι_j) * (ε_j * ι_j) = ε_j * ι_j :=
    localNumber_idempotent (ε_j := ε_j) (ι_j := ι_j) hε hι hcar
  calc
    (1 - ε_j * ι_j) * (1 - ε_j * ι_j)
        = 1 - (2 : R) * (ε_j * ι_j) + (ε_j * ι_j) * (ε_j * ι_j) := by
            noncomm_ring
    _ = 1 - (2 : R) * (ε_j * ι_j) + (ε_j * ι_j) := by
            rw [hN]
    _ = 1 - ε_j * ι_j := by
            noncomm_ring

/--
Orthogonality of vacuum and number projectors:

`(1 - N_j) * N_j = 0` where `N_j := ε_j * ι_j`.
-/
@[rep_depth thermo]
theorem localVacuum_mul_number_eq_zero
    {R : Type*} [Ring R]
    {ε_j ι_j : R}
    (hε : ε_j * ε_j = 0)
    (hι : ι_j * ι_j = 0)
    (hcar : ε_j * ι_j + ι_j * ε_j = 1) :
    (1 - ε_j * ι_j) * (ε_j * ι_j) = 0 := by
  have hN : (ε_j * ι_j) * (ε_j * ι_j) = ε_j * ι_j :=
    localNumber_idempotent (ε_j := ε_j) (ι_j := ι_j) hε hι hcar
  calc
    (1 - ε_j * ι_j) * (ε_j * ι_j)
        = ε_j * ι_j - (ε_j * ι_j) * (ε_j * ι_j) := by
            noncomm_ring
    _ = ε_j * ι_j - ε_j * ι_j := by
            rw [hN]
    _ = 0 := by
            simp

/--
Right-orthogonality of number and vacuum projectors:

`N_j * (1 - N_j) = 0` where `N_j := ε_j * ι_j`.
-/
@[rep_depth thermo]
theorem localNumber_mul_vacuum_eq_zero
    {R : Type*} [Ring R]
    {ε_j ι_j : R}
    (hε : ε_j * ε_j = 0)
    (hι : ι_j * ι_j = 0)
    (hcar : ε_j * ι_j + ι_j * ε_j = 1) :
    (ε_j * ι_j) * (1 - ε_j * ι_j) = 0 := by
  have hN : (ε_j * ι_j) * (ε_j * ι_j) = ε_j * ι_j :=
    localNumber_idempotent (ε_j := ε_j) (ι_j := ι_j) hε hι hcar
  calc
    (ε_j * ι_j) * (1 - ε_j * ι_j)
        = ε_j * ι_j - (ε_j * ι_j) * (ε_j * ι_j) := by
            noncomm_ring
    _ = ε_j * ι_j - ε_j * ι_j := by
            rw [hN]
    _ = 0 := by
            simp

/--
Local number/hole complement identity:

`N_j + H_j = 1` with `N_j := ε_j*ι_j` and `H_j := ι_j*ε_j`.
-/
@[rep_depth thermo]
theorem localNumber_hole_complement
    {R : Type*} [Ring R]
    {ε_j ι_j : R}
    (hcar : ε_j * ι_j + ι_j * ε_j = 1) :
    ε_j * ι_j + ι_j * ε_j = 1 := hcar

/--
Vacuum and number projectors sum to identity:

`(1 - N_j) + N_j = 1` where `N_j := ε_j*ι_j`.
-/
@[rep_depth thermo]
theorem localVacuum_add_number_eq_one
    {R : Type*} [Ring R]
    {ε_j ι_j : R} :
    (1 - ε_j * ι_j) + (ε_j * ι_j) = 1 := by
  noncomm_ring

/--
Number and vacuum projectors are complementary in both orders:

`(1 - N_j) + N_j = 1` and `N_j + (1 - N_j) = 1`.
-/
@[rep_depth thermo]
theorem localVacuum_number_complement_pair
    {R : Type*} [Ring R]
    {ε_j ι_j : R} :
    ((1 - ε_j * ι_j) + (ε_j * ι_j) = 1) ∧
    ((ε_j * ι_j) + (1 - ε_j * ι_j) = 1) := by
  refine ⟨?_, ?_⟩
  · exact localVacuum_add_number_eq_one (ε_j := ε_j) (ι_j := ι_j)
  · noncomm_ring

/--
Vacuum/number projectors annihilate each other in both orders.
-/
@[rep_depth thermo]
theorem localVacuum_number_annihilate_pair
    {R : Type*} [Ring R]
    {ε_j ι_j : R}
    (hε : ε_j * ε_j = 0)
    (hι : ι_j * ι_j = 0)
    (hcar : ε_j * ι_j + ι_j * ε_j = 1) :
    ((1 - ε_j * ι_j) * (ε_j * ι_j) = 0) ∧
    ((ε_j * ι_j) * (1 - ε_j * ι_j) = 0) := by
  refine ⟨?_, ?_⟩
  · exact localVacuum_mul_number_eq_zero (ε_j := ε_j) (ι_j := ι_j) hε hι hcar
  · exact localNumber_mul_vacuum_eq_zero (ε_j := ε_j) (ι_j := ι_j) hε hι hcar

/--
Orthogonality of the local number/hole projectors:

`(ε_j*ι_j)*(ι_j*ε_j) = 0` and `(ι_j*ε_j)*(ε_j*ι_j) = 0`.
-/
@[rep_depth thermo]
theorem localProjector_orthogonal
    {R : Type*} [Ring R]
    {ε_j ι_j : R}
    (hε : ε_j * ε_j = 0)
    (hι : ι_j * ι_j = 0) :
    (ε_j * ι_j) * (ι_j * ε_j) = 0 ∧
    (ι_j * ε_j) * (ε_j * ι_j) = 0 := by
  refine ⟨?_, ?_⟩
  · calc
      (ε_j * ι_j) * (ι_j * ε_j) = ε_j * (ι_j * ι_j) * ε_j := by
        noncomm_ring
      _ = 0 := by
        rw [hι]
        simp
  · calc
      (ι_j * ε_j) * (ε_j * ι_j) = ι_j * (ε_j * ε_j) * ι_j := by
        noncomm_ring
      _ = 0 := by
        rw [hε]
        simp

/--
CAR number/hole projectors resolve identity on the left:

`(N_j + H_j) * x = x` for all `x`, where
`N_j := ε_j*ι_j`, `H_j := ι_j*ε_j`, and `N_j + H_j = 1`.
-/
@[rep_depth thermo]
theorem localProjector_resolution_left
    {R : Type*} [Ring R]
    {ε_j ι_j x : R}
    (hcar : ε_j * ι_j + ι_j * ε_j = 1) :
    (ε_j * ι_j + ι_j * ε_j) * x = x := by
  calc
    (ε_j * ι_j + ι_j * ε_j) * x = (1 : R) * x := by
      rw [hcar]
    _ = x := by
      simp

/--
CAR projectors resolve identity on both sides:

`(N_j + H_j) * x = x` and `x * (N_j + H_j) = x`, where
`N_j := ε_j*ι_j`, `H_j := ι_j*ε_j`.
-/
@[rep_depth thermo]
theorem localProjector_resolution_two_sided
    {R : Type*} [Ring R]
    {ε_j ι_j x : R}
    (hcar : ε_j * ι_j + ι_j * ε_j = 1) :
    ((ε_j * ι_j + ι_j * ε_j) * x = x) ∧
    (x * (ε_j * ι_j + ι_j * ε_j) = x) := by
  refine ⟨?_, ?_⟩
  · exact localProjector_resolution_left (ε_j := ε_j) (ι_j := ι_j) (x := x) hcar
  · calc
      x * (ε_j * ι_j + ι_j * ε_j) = x * (1 : R) := by
        rw [hcar]
      _ = x := by
        simp

/--
Local parity involution:

`Π_j := 1 - 2*N_j` with `N_j := ε_j*ι_j` satisfies `Π_j^2 = 1`.
-/
@[rep_depth thermo]
theorem localParity_sq_identity
    {R : Type*} [Ring R]
    {ε_j ι_j : R}
    (hε : ε_j * ε_j = 0)
    (hι : ι_j * ι_j = 0)
    (hcar : ε_j * ι_j + ι_j * ε_j = 1) :
    (1 - (2 : R) * (ε_j * ι_j)) * (1 - (2 : R) * (ε_j * ι_j)) = 1 := by
  have hN : (ε_j * ι_j) * (ε_j * ι_j) = ε_j * ι_j :=
    localNumber_idempotent (ε_j := ε_j) (ι_j := ι_j) hε hι hcar
  calc
    (1 - (2 : R) * (ε_j * ι_j)) * (1 - (2 : R) * (ε_j * ι_j))
        = 1 - (4 : R) * (ε_j * ι_j) + (4 : R) * ((ε_j * ι_j) * (ε_j * ι_j)) := by
            noncomm_ring
    _ = 1 - (4 : R) * (ε_j * ι_j) + (4 : R) * (ε_j * ι_j) := by
            rw [hN]
    _ = 1 := by
            noncomm_ring

/--
If two local modes anticommute, the square of their sum is the sum of their
squares.

This is the local Clifford/Majorana cancellation mechanism.
-/
@[rep_depth thermo]
theorem square_add_of_anticomm
    {R : Type*} [Ring R]
    {x y wx wy : R}
    (hx : x * x = wx)
    (hy : y * y = wy)
    (hanti : x * y + y * x = 0) :
    (x + y) * (x + y) = wx + wy := by
  calc
    (x + y) * (x + y)
        = x * x + (x * y + y * x) + y * y := by
          noncomm_ring
    _ = wx + 0 + wy := by
          rw [hx, hy, hanti]
    _ = wx + wy := by
          simp

/--
A square-zero CAR pair generates the local `0 / +1 / -1` trichotomy.

`u² = v² = 0` are the chiral/spinor channels.
`u + v` is the Clifford involution.
`u - v` is the phase/clock axis.
-/
@[rep_depth thermo]
theorem squareZero_pair_gives_clifford_axes
    {R : Type*} [Ring R]
    {u v : R}
    (hu : u * u = 0)
    (hv : v * v = 0)
    (hcar : u * v + v * u = 1) :
    (u + v) * (u + v) = 1 ∧
    (u - v) * (u - v) = -(1 : R) := by
  constructor
  · calc
      (u + v) * (u + v)
          = u * u + (u * v + v * u) + v * v := by
            noncomm_ring
      _ = 0 + 1 + 0 := by
            rw [hu, hv, hcar]
      _ = 1 := by
            simp
  · calc
      (u - v) * (u - v)
          = u * u - (u * v + v * u) + v * v := by
            noncomm_ring
      _ = 0 - 1 + 0 := by
            rw [hu, hv, hcar]
      _ = -(1 : R) := by
            simp

/--
Nilpotent supercharges generate a Dirac operator whose square is the
super-Laplacian.

This is the algebraic core:

  D = Q + Q♯
  Δ = Q Q♯ + Q♯ Q
  D² = Δ
-/
@[rep_depth thermo]
theorem superDirac_sq_eq_superLaplacian
    {R : Type*} [Ring R]
    {Q Qsharp : R}
    (hQ : Q * Q = 0)
    (hQsharp : Qsharp * Qsharp = 0) :
    (Q + Qsharp) * (Q + Qsharp) =
      Q * Qsharp + Qsharp * Q := by
  calc
    (Q + Qsharp) * (Q + Qsharp)
        = Q * Q + (Q * Qsharp + Qsharp * Q) + Qsharp * Qsharp := by
          noncomm_ring
    _ = 0 + (Q * Qsharp + Qsharp * Q) + 0 := by
          rw [hQ, hQsharp]
    _ = Q * Qsharp + Qsharp * Q := by
          simp

/--
The left supercharge commutes with the super-Laplacian.

This is the abstract form of `[Q, Δ] = 0`.
-/
@[rep_depth thermo]
theorem supercharge_commutes_superLaplacian
    {R : Type*} [Ring R]
    {Q Qsharp : R}
    (hQ : Q * Q = 0) :
    Q * (Q * Qsharp + Qsharp * Q) =
      (Q * Qsharp + Qsharp * Q) * Q := by
  calc
    Q * (Q * Qsharp + Qsharp * Q)
        = (Q * Q) * Qsharp + Q * Qsharp * Q := by
          noncomm_ring
    _ = 0 * Qsharp + Q * Qsharp * Q := by
          rw [hQ]
    _ = Q * Qsharp * Q := by
          simp
    _ = Q * Qsharp * Q + Qsharp * (Q * Q) := by
          rw [hQ]
          simp
    _ = (Q * Qsharp + Qsharp * Q) * Q := by
          noncomm_ring

/--
The dual supercharge commutes with the super-Laplacian.

This is the abstract form of `[Q♯, Δ] = 0`.
-/
@[rep_depth thermo]
theorem dualSupercharge_commutes_superLaplacian
    {R : Type*} [Ring R]
    {Q Qsharp : R}
    (hQsharp : Qsharp * Qsharp = 0) :
    Qsharp * (Q * Qsharp + Qsharp * Q) =
      (Q * Qsharp + Qsharp * Q) * Qsharp := by
  calc
    Qsharp * (Q * Qsharp + Qsharp * Q)
        = Qsharp * Q * Qsharp + (Qsharp * Qsharp) * Q := by
          noncomm_ring
    _ = Qsharp * Q * Qsharp + 0 * Q := by
          rw [hQsharp]
    _ = Qsharp * Q * Qsharp := by
          simp
    _ = Q * (Qsharp * Qsharp) + Qsharp * Q * Qsharp := by
          rw [hQsharp]
          simp
    _ = (Q * Qsharp + Qsharp * Q) * Qsharp := by
          noncomm_ring

/--
The Dirac operator commutes with its Laplacian.

This is `[D, Δ] = 0` for `D = Q + Q♯`.
-/
@[rep_depth thermo]
theorem superDirac_commutes_superLaplacian
    {R : Type*} [Ring R]
    {Q Qsharp : R}
    (hQ : Q * Q = 0)
    (hQsharp : Qsharp * Qsharp = 0) :
    (Q + Qsharp) * (Q * Qsharp + Qsharp * Q) =
      (Q * Qsharp + Qsharp * Q) * (Q + Qsharp) := by
  calc
    (Q + Qsharp) * (Q * Qsharp + Qsharp * Q)
        =
      Q * (Q * Qsharp + Qsharp * Q) +
        Qsharp * (Q * Qsharp + Qsharp * Q) := by
          noncomm_ring
    _ =
      (Q * Qsharp + Qsharp * Q) * Q +
        (Q * Qsharp + Qsharp * Q) * Qsharp := by
          rw [
            supercharge_commutes_superLaplacian (Q := Q) (Qsharp := Qsharp) hQ,
            dualSupercharge_commutes_superLaplacian (Q := Q) (Qsharp := Qsharp) hQsharp
          ]
    _ =
      (Q * Qsharp + Qsharp * Q) * (Q + Qsharp) := by
          noncomm_ring

/--
Stage-`n` Dirac/Laplacian closure packaged as a pure theorem tuple.

This is the recurrence seed:
from nilpotent odd supercharges `Qn, Qn♯`, define
`Dn := Qn + Qn♯` and `Δn := Qn*Qn♯ + Qn♯*Qn`,
then obtain `Dn^2 = Δn` and commutation with `Δn`.
-/
@[rep_depth thermo]
theorem supergraded_stage_closure
    {R : Type*} [Ring R]
    {Qn Qnsharp : R}
    (hQn : Qn * Qn = 0)
    (hQnsharp : Qnsharp * Qnsharp = 0) :
    let Dn := Qn + Qnsharp
    let Δn := Qn * Qnsharp + Qnsharp * Qn
    (Dn * Dn = Δn) ∧
    (Qn * Δn = Δn * Qn) ∧
    (Qnsharp * Δn = Δn * Qnsharp) ∧
    (Dn * Δn = Δn * Dn) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact superDirac_sq_eq_superLaplacian (Q := Qn) (Qsharp := Qnsharp) hQn hQnsharp
  · exact supercharge_commutes_superLaplacian (Q := Qn) (Qsharp := Qnsharp) hQn
  · exact dualSupercharge_commutes_superLaplacian (Q := Qn) (Qsharp := Qnsharp) hQnsharp
  · exact superDirac_commutes_superLaplacian (Q := Qn) (Qsharp := Qnsharp) hQn hQnsharp

/--
Two-step recurrence closure.

If both stage-`n` and stage-`n+1` odd pairs are nilpotent, both induced
Dirac/Laplacian pairs satisfy the same closure laws. This is the direct
induction road for supergraded supercharge towers.
-/
@[rep_depth thermo]
theorem supergraded_two_step_recurrence_closure
    {R : Type*} [Ring R]
    {Qn Qnsharp Qnext Qnextsharp : R}
    (hQn : Qn * Qn = 0)
    (hQnsharp : Qnsharp * Qnsharp = 0)
    (hQnext : Qnext * Qnext = 0)
    (hQnextsharp : Qnextsharp * Qnextsharp = 0) :
    (let Dn := Qn + Qnsharp
     let Δn := Qn * Qnsharp + Qnsharp * Qn
     (Dn * Dn = Δn) ∧
     (Qn * Δn = Δn * Qn) ∧
     (Qnsharp * Δn = Δn * Qnsharp) ∧
     (Dn * Δn = Δn * Dn))
    ∧
    (let Dnext := Qnext + Qnextsharp
     let Δnext := Qnext * Qnextsharp + Qnextsharp * Qnext
     (Dnext * Dnext = Δnext) ∧
     (Qnext * Δnext = Δnext * Qnext) ∧
     (Qnextsharp * Δnext = Δnext * Qnextsharp) ∧
     (Dnext * Δnext = Δnext * Dnext)) := by
  refine ⟨?_, ?_⟩
  · exact supergraded_stage_closure (Qn := Qn) (Qnsharp := Qnsharp) hQn hQnsharp
  · exact supergraded_stage_closure (Qn := Qnext) (Qnsharp := Qnextsharp) hQnext hQnextsharp

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

/--
Single-axis creation action equals the corresponding single-axis kernel action.
-/
@[rep_depth thermo]
theorem creationPush_eq_creationKernel_sum {P : PrimeCutoff}
    (amplitude holonomy : PrimeMode P → ℂ)
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P) :
    amplitude p * holonomy p * creationPush p f S =
      Finset.sum (Finset.univ : Finset (Vertex P))
        (fun T => creationKernel amplitude holonomy p S T * f T) := by
  classical
  unfold creationPush creationKernel optionEval
  cases h : PrimeExteriorGraphDirac.create p S with
  | none =>
      simp [h]
  | some U =>
      simp [h, Finset.sum_ite_eq, Finset.sum_ite_irrel]

/--
Single-axis annihilation action equals the corresponding single-axis kernel action.
-/
@[rep_depth thermo]
theorem annihilationPush_eq_annihilationKernel_sum {P : PrimeCutoff}
    (amplitude holonomy : PrimeMode P → ℂ)
    (p : PrimeMode P) (f : CantorField P) (S : Vertex P) :
    amplitude p * (holonomy p)⁻¹ * annihilationPush p f S =
      Finset.sum (Finset.univ : Finset (Vertex P))
        (fun T => annihilationKernel amplitude holonomy p S T * f T) := by
  classical
  unfold annihilationPush annihilationKernel optionEval
  cases h : PrimeExteriorGraphDirac.annihilate p S with
  | none =>
      simp [h]
  | some U =>
      simp [h, Finset.sum_ite_eq, Finset.sum_ite_irrel]

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
Kernel-action form of the creation supercharge.
-/
@[rep_depth thermo]
theorem creationSupercharge_apply_eq_creationKernel_sum {P : PrimeCutoff}
    (amplitude holonomy : PrimeMode P → ℂ)
    (f : CantorField P) (S : Vertex P) :
    creationSupercharge amplitude holonomy f S =
      Finset.sum (Finset.univ : Finset (Vertex P))
        (fun T =>
          Finset.sum (Finset.univ : Finset (PrimeMode P))
            (fun p => creationKernel amplitude holonomy p S T * f T)) := by
  classical
  unfold creationSupercharge
  calc
    Finset.sum (Finset.univ : Finset (PrimeMode P))
      (fun p => amplitude p * holonomy p * creationPush p f S)
        =
      Finset.sum (Finset.univ : Finset (PrimeMode P))
        (fun p =>
          Finset.sum (Finset.univ : Finset (Vertex P))
            (fun T => creationKernel amplitude holonomy p S T * f T)) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          exact creationPush_eq_creationKernel_sum amplitude holonomy p f S
    _ =
      Finset.sum (Finset.univ : Finset (Vertex P))
        (fun T =>
          Finset.sum (Finset.univ : Finset (PrimeMode P))
            (fun p => creationKernel amplitude holonomy p S T * f T)) := by
          rw [Finset.sum_comm]

/--
Kernel-action form of the dual annihilation supercharge.
-/
@[rep_depth thermo]
theorem dualAnnihilationSupercharge_apply_eq_annihilationKernel_sum {P : PrimeCutoff}
    (amplitude holonomy : PrimeMode P → ℂ)
    (f : CantorField P) (S : Vertex P) :
    dualAnnihilationSupercharge amplitude holonomy f S =
      Finset.sum (Finset.univ : Finset (Vertex P))
        (fun T =>
          Finset.sum (Finset.univ : Finset (PrimeMode P))
            (fun p => annihilationKernel amplitude holonomy p S T * f T)) := by
  classical
  unfold dualAnnihilationSupercharge
  calc
    Finset.sum (Finset.univ : Finset (PrimeMode P))
      (fun p => amplitude p * (holonomy p)⁻¹ * annihilationPush p f S)
        =
      Finset.sum (Finset.univ : Finset (PrimeMode P))
        (fun p =>
          Finset.sum (Finset.univ : Finset (Vertex P))
            (fun T => annihilationKernel amplitude holonomy p S T * f T)) := by
          refine Finset.sum_congr rfl ?_
          intro p hp
          exact annihilationPush_eq_annihilationKernel_sum amplitude holonomy p f S
    _ =
      Finset.sum (Finset.univ : Finset (Vertex P))
        (fun T =>
          Finset.sum (Finset.univ : Finset (PrimeMode P))
            (fun p => annihilationKernel amplitude holonomy p S T * f T)) := by
          rw [Finset.sum_comm]

/-! ## Concrete normalized zeta holonomy -/

/--
Concrete finite normalized zeta holonomy in log-energy form.

For `E_p = log p`, this is

`exp(((1/2 - Re s) E_p)) * exp(-i (Im s) E_p)`,

i.e. the Lean-real-polar form of `p^(1/2 - s)`.
-/
@[rep_depth thermo]
def normalizedPrimeHolonomy {P : PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (s : ℂ) (p : PrimeMode P) : ℂ :=
  { re :=
      Real.exp (((1 : ℝ) / 2 - s.re) * logPrime p) *
        Real.cos (-(s.im * logPrime p)),
    im :=
      Real.exp (((1 : ℝ) / 2 - s.re) * logPrime p) *
        Real.sin (-(s.im * logPrime p)) }

/--
Norm-square of the concrete normalized zeta holonomy.

This is the finite-mode algebraic content of

`|p^(1/2-s)|^2 = p^(1-2 Re(s))`.
-/
@[rep_depth thermo]
theorem normalizedPrimeHolonomy_normSq {P : PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (s : ℂ) (p : PrimeMode P) :
    Complex.normSq (normalizedPrimeHolonomy logPrime s p) =
      (Real.exp (((1 : ℝ) / 2 - s.re) * logPrime p)) ^ 2 := by
  unfold normalizedPrimeHolonomy Complex.normSq
  set a : ℝ := ((1 : ℝ) / 2 - s.re) * logPrime p
  set θ : ℝ := -(s.im * logPrime p)
  simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
  have htrig : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    simpa [add_comm] using Real.cos_sq_add_sin_sq θ
  nlinarith [htrig]

/--
Single-mode critical-line criterion for the concrete normalized holonomy.

No infinite product. No RH claim.
-/
@[rep_depth thermo]
theorem normalizedPrimeHolonomy_normSq_eq_one_iff {P : PrimeCutoff}
    (logPrime : PrimeMode P → ℝ) (s : ℂ) (p : PrimeMode P)
    (hpos : 0 < logPrime p) :
    Complex.normSq (normalizedPrimeHolonomy logPrime s p) = 1
      ↔ s.re = (1 : ℝ) / 2 := by
  rw [normalizedPrimeHolonomy_normSq]
  set a : ℝ := ((1 : ℝ) / 2 - s.re) * logPrime p
  change (Real.exp a) ^ 2 = 1 ↔ s.re = (1 : ℝ) / 2
  constructor
  · intro hsq
    rcases sq_eq_one_iff.mp hsq with h1 | hneg
    · have ha : a = 0 := (Real.exp_eq_one_iff a).1 h1
      dsimp [a] at ha
      nlinarith [hpos]
    · have hgt : 0 < Real.exp a := Real.exp_pos a
      nlinarith
  · intro hs
    have ha : a = 0 := by
      dsimp [a]
      rw [hs]
      ring
    rw [ha, Real.exp_zero]
    ring

/--
Finite-cutoff version: all concrete normalized holonomies are unit-norm exactly
on the critical line.

The `Nonempty` assumption prevents the empty cutoff from making the left side
vacuously true.
-/
@[rep_depth thermo]
theorem normalizedPrimeHolonomy_all_normSq_eq_one_iff {P : PrimeCutoff}
    [Nonempty (PrimeMode P)]
    (logPrime : PrimeMode P → ℝ)
    (hpos : ∀ p : PrimeMode P, 0 < logPrime p)
    (s : ℂ) :
    (∀ p : PrimeMode P,
        Complex.normSq (normalizedPrimeHolonomy logPrime s p) = 1)
      ↔ s.re = (1 : ℝ) / 2 := by
  constructor
  · intro h
    rcases (inferInstance : Nonempty (PrimeMode P)) with ⟨p0⟩
    exact
      (normalizedPrimeHolonomy_normSq_eq_one_iff
        logPrime s p0 (hpos p0)).mp (h p0)
  · intro hs p
    exact
      (normalizedPrimeHolonomy_normSq_eq_one_iff
        logPrime s p (hpos p)).mpr hs

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
Finite critical-line predicate.
-/
@[rep_depth thermo]
def CriticalLine (s : ℂ) : Prop := s.re = 1 / 2

/--
Concrete normalized prime holonomy:
`h_p(s) = exp(((1/2)-s) * log p)`.
-/
@[rep_depth thermo]
def zetaNormalizedPrimeHolonomy {P : PrimeCutoff}
    (s : ℂ) (p : PrimeMode P) : ℂ :=
  Complex.exp ((((1 / 2 : ℝ) : ℂ) - s) * ((Real.log (p.1 : ℝ) : ℝ) : ℂ))

/--
Closed-form modulus of the normalized prime holonomy.
-/
@[rep_depth thermo]
def zetaNormalizedPrimeHolonomyNorm {P : PrimeCutoff}
    (s : ℂ) (p : PrimeMode P) : ℝ :=
  Real.exp (((1 / 2 : ℝ) - s.re) * Real.log (p.1 : ℝ))

/--
The normalized prime-holonomy norm is `1` exactly on the critical line.
-/
@[rep_depth thermo]
theorem zetaNormalizedPrimeHolonomyNorm_eq_one_iff_criticalLine
    {P : PrimeCutoff} (s : ℂ) (p : PrimeMode P) :
    zetaNormalizedPrimeHolonomyNorm s p = 1 ↔ CriticalLine s := by
  unfold zetaNormalizedPrimeHolonomyNorm CriticalLine
  rw [← norm_zetaHolonomy_eq (s := s) (p := p)]
  exact norm_zetaHolonomy_eq_one_iff_re_eq_half (s := s) (p := p)

/--
Finite all-modes unitary criterion via normalized holonomy norm.
-/
@[rep_depth thermo]
def ZetaHolonomyUnitaryAt {P : PrimeCutoff} (s : ℂ) : Prop :=
  ∀ p : PrimeMode P, zetaNormalizedPrimeHolonomyNorm s p = 1

/--
On a nonempty finite prime cutoff, all-mode normalized holonomy unitarity is
equivalent to the critical-line condition.
-/
@[rep_depth thermo]
theorem zetaHolonomyUnitaryAt_iff_criticalLine
    {P : PrimeCutoff} (hP : P.primes.Nonempty) (s : ℂ) :
    ZetaHolonomyUnitaryAt (P := P) s ↔ CriticalLine s := by
  constructor
  · intro hU
    rcases hP with ⟨p0, hp0⟩
    let p : PrimeMode P := ⟨p0, hp0⟩
    exact (zetaNormalizedPrimeHolonomyNorm_eq_one_iff_criticalLine (s := s) (p := p)).1 (hU p)
  · intro hs p
    exact (zetaNormalizedPrimeHolonomyNorm_eq_one_iff_criticalLine (s := s) (p := p)).2 hs

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

/-! ## 5a. Concrete critical-line holonomy modulus -/

/--
Modulus of the intended zeta holonomy

`p^(1/2 - s)`

written in real exponential/logarithmic form.

This is the norm readout only. It does not replace the abstract holonomy field
of `FiniteCantorZetaDirac`.
-/
@[rep_depth thermo]
def criticalLineHolonomyModulus
    (s : ℂ) (p : ℕ) : ℝ :=
  Real.exp (((1 / 2 : ℝ) - s.re) * Real.log (p : ℝ))

/--
For a real prime scale `p > 1`, the intended zeta-holonomy modulus is one
exactly on the critical line.

This is the finite concrete lemma:
`‖p^(1/2-s)‖ = 1 ↔ Re(s)=1/2`,
expressed without committing the whole operator packet to this holonomy.
-/
@[rep_depth thermo]
theorem criticalLineHolonomyModulus_eq_one_iff
    {p : ℕ} (hp : 1 < (p : ℝ)) (s : ℂ) :
    criticalLineHolonomyModulus s p = 1 ↔
      s.re = (1 / 2 : ℝ) := by
  unfold criticalLineHolonomyModulus
  have hlog_pos : 0 < Real.log (p : ℝ) := Real.log_pos hp
  constructor
  · intro h
    have hexp : Real.exp (((1 / 2 : ℝ) - s.re) * Real.log (p : ℝ)) = Real.exp 0 := by
      simpa using h
    have hmul : ((1 / 2 : ℝ) - s.re) * Real.log (p : ℝ) = 0 := by
      exact Real.exp_injective hexp
    rcases mul_eq_zero.mp hmul with hleft | hlog
    · linarith
    · exact False.elim (hlog_pos.ne' hlog)
  · intro hs
    simp [hs]

/--
Prime-mode version of the critical-line holonomy modulus criterion.
-/
@[rep_depth thermo]
theorem criticalLineHolonomyModulus_primeMode_eq_one_iff
    {P : PrimeCutoff} (p : PrimeMode P) (s : ℂ) :
    criticalLineHolonomyModulus s (p : ℕ) = 1 ↔
      s.re = (1 / 2 : ℝ) := by
  have hpPrime : Nat.Prime (p : ℕ) :=
    P.prime_mem (p : ℕ) p.property
  have hp : 1 < ((p : ℕ) : ℝ) := by
    exact_mod_cast hpPrime.one_lt
  exact criticalLineHolonomyModulus_eq_one_iff hp s

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

/-! ## 5A. Concrete critical-line holonomy norm -/

/--
Norm readout of the intended critical-line holonomy

`p^(1/2 - s) = exp((1/2 - s) log p)`.

We keep only the real norm readout here:

`exp((1/2 - Re s) log p)`.

This avoids hard-coding a full complex-power API while proving the real
critical-line criterion needed by the finite operator lane.
-/
@[rep_depth thermo]
def criticalLineHolonomyNorm
    (s : ℂ)
    (p : PrimeMode P) : ℝ :=
  Real.exp (((1 : ℝ) / 2 - s.re) * Real.log (p.1 : ℝ))

/--
The critical-line holonomy norm is positive.
-/
@[rep_depth thermo]
theorem criticalLineHolonomyNorm_pos
    (s : ℂ)
    (p : PrimeMode P) :
    0 < criticalLineHolonomyNorm (P := P) s p := by
  dsimp [criticalLineHolonomyNorm]
  positivity

/--
Concrete holonomy criterion for one prime mode:

`‖p^(1/2-s)‖ = 1` iff `Re(s)=1/2`.

This is the first finite critical-line theorem. It is independent of any
infinite Euler product or RH claim.
-/
@[rep_depth thermo]
theorem criticalLineHolonomyNorm_eq_one_iff
    (s : ℂ)
    (p : PrimeMode P)
    (hp : 1 < p.1) :
    criticalLineHolonomyNorm (P := P) s p = 1 ↔
      s.re = (1 : ℝ) / 2 := by
  have hlog_pos : 0 < Real.log (p.1 : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hp)

  constructor
  · intro h
    have hzero :
        ((1 : ℝ) / 2 - s.re) * Real.log (p.1 : ℝ) = 0 := by
      exact (Real.exp_eq_one_iff _).mp h

    have hleft :
        (1 : ℝ) / 2 - s.re = 0 := by
      rcases mul_eq_zero.mp hzero with hcoeff | hlog
      · exact hcoeff
      · exact False.elim (hlog_pos.ne' hlog)

    linarith

  · intro hs
    dsimp [criticalLineHolonomyNorm]
    have hzero :
        ((1 : ℝ) / 2 - s.re) * Real.log (p.1 : ℝ) = 0 := by
      rw [hs]
      ring
    rw [hzero]
    simp

/-- Log-norm readout for `p^(1/2-s)` in finite mode form. -/
@[rep_depth thermo]
def zetaCriticalHolonomyLogNorm (s : ℂ) (p : ℕ) : ℝ :=
  ((1 / 2 : ℝ) - s.re) * Real.log (p : ℝ)

/-- Real norm readout for `p^(1/2-s)` in finite mode form. -/
@[rep_depth thermo]
def zetaCriticalHolonomyNorm (s : ℂ) (p : ℕ) : ℝ :=
  Real.exp (zetaCriticalHolonomyLogNorm s p)

/--
Concrete finite-mode criterion:

`‖p^(1/2-s)‖ = 1 ↔ Re(s)=1/2`, for `p>1`.
-/
@[rep_depth thermo]
theorem zetaCriticalHolonomyNorm_eq_one_iff_re_eq_half
    {p : ℕ} (hp : 1 < p) (s : ℂ) :
    zetaCriticalHolonomyNorm s p = 1 ↔ s.re = 1 / 2 := by
  unfold zetaCriticalHolonomyNorm zetaCriticalHolonomyLogNorm
  rw [Real.exp_eq_one_iff]
  have hlog_pos : 0 < Real.log (p : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hp)
  have hlog_ne : Real.log (p : ℝ) ≠ 0 := hlog_pos.ne'
  constructor
  · intro hmul
    have hhalf : (1 / 2 : ℝ) - s.re = 0 := by
      rcases mul_eq_zero.mp hmul with hleft | hright
      · exact hleft
      · exact False.elim (hlog_ne hright)
    linarith
  · intro hs
    rw [hs]
    ring

/-- Prime-mode version of the zeta critical-line holonomy norm criterion. -/
@[rep_depth thermo]
theorem zetaCriticalHolonomyNorm_primeMode_eq_one_iff_re_eq_half
    (p : PrimeMode P) (s : ℂ) :
    zetaCriticalHolonomyNorm s (p : ℕ) = 1 ↔ s.re = 1 / 2 := by
  have hp_prime : Nat.Prime (p : ℕ) := P.prime_mem p.1 p.property
  exact zetaCriticalHolonomyNorm_eq_one_iff_re_eq_half hp_prime.one_lt s

/-- Finite-cutoff norm-unitarity predicate for the concrete zeta holonomy readout. -/
@[rep_depth thermo]
def ZetaCriticalHolonomyNormUnitaryAt (s : ℂ) : Prop :=
  ∀ p : PrimeMode P, zetaCriticalHolonomyNorm s (p : ℕ) = 1

/--
For nonempty finite cutoff, all-mode concrete zeta holonomy norm-unitarity is
equivalent to `Re(s)=1/2`.
-/
@[rep_depth thermo]
theorem zetaCriticalHolonomyNormUnitaryAt_iff_re_eq_half
    [Nonempty (PrimeMode P)] (s : ℂ) :
    ZetaCriticalHolonomyNormUnitaryAt (P := P) s ↔ s.re = 1 / 2 := by
  constructor
  · intro hunit
    rcases (inferInstance : Nonempty (PrimeMode P)) with ⟨p0⟩
    exact (zetaCriticalHolonomyNorm_primeMode_eq_one_iff_re_eq_half (P := P) p0 s).mp (hunit p0)
  · intro hs p
    exact (zetaCriticalHolonomyNorm_primeMode_eq_one_iff_re_eq_half (P := P) p s).mpr hs

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
Modewise finite adjointness on the Cantor/Fock pairing:
creation along a prime axis is adjoint to annihilation along the same axis.
-/
@[rep_depth thermo]
theorem creationPush_isAdjointPair_annihilationPush
    (p : PrimeMode P) :
    IsAdjointPair (P := P)
      (fun f S => creationPush p f S)
      (fun f S => annihilationPush p f S) := by
  classical
  intro f g
  unfold pairing
  have hL :
      (Finset.sum (Finset.univ : Finset (Vertex P))
        (fun S => star (creationPush p f S) * g S)) =
      Finset.sum ((Finset.univ : Finset (Vertex P)).filter (fun S => p ∉ S))
        (fun S => star (f (insert p S)) * g S) := by
    calc
      Finset.sum (Finset.univ : Finset (Vertex P))
          (fun S => star (creationPush p f S) * g S)
          =
          Finset.sum (Finset.univ : Finset (Vertex P))
            (fun S => if p ∉ S then star (f (insert p S)) * g S else 0) := by
              refine Finset.sum_congr rfl ?_
              intro S hS
              by_cases hpS : p ∈ S
              · simp [creationPush, PrimeExteriorGraphDirac.create, hpS]
              · simp [creationPush, PrimeExteriorGraphDirac.create, hpS]
      _ =
          Finset.sum ((Finset.univ : Finset (Vertex P)).filter (fun S => p ∉ S))
            (fun S => star (f (insert p S)) * g S) := by
              simpa [Finset.sum_filter] using
                (Finset.sum_filter (s := (Finset.univ : Finset (Vertex P)))
                  (p := fun S : Vertex P => p ∉ S)
                  (f := fun S => star (f (insert p S)) * g S)).symm
  have hR :
      (Finset.sum (Finset.univ : Finset (Vertex P))
        (fun S => star (f S) * annihilationPush p g S)) =
      Finset.sum ((Finset.univ : Finset (Vertex P)).filter (fun S => p ∈ S))
        (fun S => star (f S) * g (S.erase p)) := by
    calc
      Finset.sum (Finset.univ : Finset (Vertex P))
          (fun S => star (f S) * annihilationPush p g S)
          =
          Finset.sum (Finset.univ : Finset (Vertex P))
            (fun S => if p ∈ S then star (f S) * g (S.erase p) else 0) := by
              refine Finset.sum_congr rfl ?_
              intro S hS
              by_cases hpS : p ∈ S
              · simp [annihilationPush, PrimeExteriorGraphDirac.annihilate, hpS]
              · simp [annihilationPush, PrimeExteriorGraphDirac.annihilate, hpS]
      _ =
          Finset.sum ((Finset.univ : Finset (Vertex P)).filter (fun S => p ∈ S))
            (fun S => star (f S) * g (S.erase p)) := by
              simpa [Finset.sum_filter] using
                (Finset.sum_filter (s := (Finset.univ : Finset (Vertex P)))
                  (p := fun S : Vertex P => p ∈ S)
                  (f := fun S => star (f S) * g (S.erase p))).symm
  rw [hL, hR]
  refine Finset.sum_bij'
    (fun S _ => insert p S)
    (fun T _ => Finset.erase T p)
    (fun S hS => by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩)
    (fun T hT => by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp⟩)
    (fun S hS => by
      have hpS : p ∉ S := (Finset.mem_filter.mp hS).2
      simp [hpS])
    (fun T hT => by
      have hpT : p ∈ T := (Finset.mem_filter.mp hT).2
      simp [hpT])
    (fun S hS => by
      have hpS : p ∉ S := (Finset.mem_filter.mp hS).2
      simp [hpS])

/--
Modewise weighted adjointness for the creation-to-annihilation channel.

If amplitudes are self-adjoint scalars and holonomy is unitary at `s`, then
`a_p h_p ε_p` is adjoint to `a_p h_p⁻¹ ι_p` for each prime mode.
-/
@[rep_depth thermo]
theorem weighted_mode_isAdjointPair_of_unitary
    (s : ℂ)
    (hAmp : ∀ p : PrimeMode P, star (D.amplitude p) = D.amplitude p)
    (hU : D.HolonomyUnitaryAt s)
    (p : PrimeMode P) :
    IsAdjointPair (P := P)
      (fun f S => D.amplitude p * D.holonomy s p * creationPush p f S)
      (fun f S => D.amplitude p * (D.holonomy s p)⁻¹ * annihilationPush p f S) := by
  intro f g
  let c : ℂ := D.amplitude p * D.holonomy s p
  let d : ℂ := D.amplitude p * (D.holonomy s p)⁻¹
  have hbase := creationPush_isAdjointPair_annihilationPush (P := P) p f g
  have hcd : star c = d := by
    dsimp [c, d]
    have hhol : (D.holonomy s p)⁻¹ = star (D.holonomy s p) := (hU p).2
    calc
      star (D.amplitude p * D.holonomy s p)
          = star (D.holonomy s p) * star (D.amplitude p) := by
              simp [star_mul]
      _ = (D.holonomy s p)⁻¹ * D.amplitude p := by
              simp [hhol, hAmp p]
      _ = D.amplitude p * (D.holonomy s p)⁻¹ := by
              ring
  calc
    pairing ((fun f S => c * creationPush p f S) f) g
        = pairing (c • fun S => creationPush p f S) g := by
            rfl
    _ = star c * pairing (fun S => creationPush p f S) g := by
          simpa using pairing_smul_left (P := P) c (fun S => creationPush p f S) g
    _ = star c * pairing f (fun S => annihilationPush p g S) := by
          rw [hbase]
    _ = d * pairing f (fun S => annihilationPush p g S) := by
          rw [hcd]
    _ = pairing f (d • fun S => annihilationPush p g S) := by
          simpa using (pairing_smul_right (P := P) d f (fun S => annihilationPush p g S)).symm
    _ = pairing f ((fun f S => d * annihilationPush p f S) g) := by
          rfl

/--
Modewise weighted reverse adjointness for the annihilation-to-creation channel.

Derived from forward weighted adjointness plus conjugate symmetry of `pairing`.
-/
@[rep_depth thermo]
theorem weighted_mode_isAdjointPairRev_of_unitary
    (s : ℂ)
    (hAmp : ∀ p : PrimeMode P, star (D.amplitude p) = D.amplitude p)
    (hU : D.HolonomyUnitaryAt s)
    (p : PrimeMode P) :
    IsAdjointPair (P := P)
      (fun f S => D.amplitude p * (D.holonomy s p)⁻¹ * annihilationPush p f S)
      (fun f S => D.amplitude p * D.holonomy s p * creationPush p f S) := by
  intro f g
  have hfw :
      IsAdjointPair (P := P)
        (fun f S => D.amplitude p * D.holonomy s p * creationPush p f S)
        (fun f S => D.amplitude p * (D.holonomy s p)⁻¹ * annihilationPush p f S) :=
    weighted_mode_isAdjointPair_of_unitary (D := D) s hAmp hU p
  have hswap := IsAdjointPair.conj_swap (P := P) hfw g f
  calc
    pairing ((fun f S => D.amplitude p * (D.holonomy s p)⁻¹ * annihilationPush p f S) f) g
        = star (pairing g ((fun f S =>
            D.amplitude p * (D.holonomy s p)⁻¹ * annihilationPush p f S) f)) := by
            simpa using (pairing_conj_symm (P := P) g
              ((fun f S => D.amplitude p * (D.holonomy s p)⁻¹ * annihilationPush p f S) f)).symm
    _ = pairing f ((fun f S => D.amplitude p * D.holonomy s p * creationPush p f S) g) := by
          simpa using hswap

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
Kernel action formula: applying the finite Cantor--Dirac operator is the finite
matrix-kernel action on fields.
-/
@[rep_depth thermo]
theorem op_apply_eq_kernel_sum
    (s : ℂ) (f : CantorField P) (S : Vertex P) :
    D.op s f S =
      Finset.sum (Finset.univ : Finset (Vertex P))
        (fun T => D.kernel s S T * f T) := by
  calc
    D.op s f S
        = D.Q s f S + D.Qsharp s f S := by
            exact D.op_eq_Q_add_Qsharp s f S
    _ = creationSupercharge D.amplitude (D.holonomy s) f S +
          dualAnnihilationSupercharge D.amplitude (D.holonomy s) f S := by
            rfl
    _ =
        (Finset.sum (Finset.univ : Finset (Vertex P))
          (fun T =>
            Finset.sum (Finset.univ : Finset (PrimeMode P))
              (fun p => creationKernel D.amplitude (D.holonomy s) p S T * f T)))
        +
        (Finset.sum (Finset.univ : Finset (Vertex P))
          (fun T =>
            Finset.sum (Finset.univ : Finset (PrimeMode P))
              (fun p => annihilationKernel D.amplitude (D.holonomy s) p S T * f T))) := by
          rw [creationSupercharge_apply_eq_creationKernel_sum,
            dualAnnihilationSupercharge_apply_eq_annihilationKernel_sum]
    _ =
        Finset.sum (Finset.univ : Finset (Vertex P))
          (fun T =>
            Finset.sum (Finset.univ : Finset (PrimeMode P))
              (fun p =>
                (creationKernel D.amplitude (D.holonomy s) p S T +
                  annihilationKernel D.amplitude (D.holonomy s) p S T) * f T)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro T hT
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro p hp
          ring
    _ =
        Finset.sum (Finset.univ : Finset (Vertex P))
          (fun T =>
            (Finset.sum (Finset.univ : Finset (PrimeMode P))
              (fun p =>
                creationKernel D.amplitude (D.holonomy s) p S T +
                  annihilationKernel D.amplitude (D.holonomy s) p S T)) * f T) := by
          refine Finset.sum_congr rfl ?_
          intro T hT
          rw [Finset.sum_mul]
    _ =
        Finset.sum (Finset.univ : Finset (Vertex P))
          (fun T => D.kernel s S T * f T) := by
          refine Finset.sum_congr rfl ?_
          intro T hT
          rw [← D.kernel_eq_sum s S T]

/--
Kernel Hermitian symmetry implies the full finite pairing Hermitian law for `D.op s`.
-/
@[rep_depth thermo]
theorem op_pairing_hermitian_of_kernel_conj_symm
    (s : ℂ)
    (hK : ∀ S T : Vertex P, star (D.kernel s S T) = D.kernel s T S)
    (f g : CantorField P) :
    pairing (D.op s f) g = pairing f (D.op s g) := by
  unfold pairing
  simp [D.op_apply_eq_kernel_sum]
  calc
    ∑ S, (∑ T, star (D.kernel s S T) * star (f T)) * g S
        = ∑ S, ∑ T, (star (D.kernel s S T) * star (f T)) * g S := by
            simp [Finset.sum_mul]
    _ = ∑ S, ∑ T, star (f T) * (star (D.kernel s S T) * g S) := by
            simp [mul_assoc, mul_left_comm, mul_comm]
    _ = ∑ T, ∑ S, star (f T) * (star (D.kernel s S T) * g S) := by
            rw [Finset.sum_comm]
    _ = ∑ T, ∑ S, star (f T) * (D.kernel s T S * g S) := by
            refine Finset.sum_congr rfl ?_
            intro T hT
            refine Finset.sum_congr rfl ?_
            intro S hS
            rw [hK S T]
    _ = ∑ T, star (f T) * ∑ S, D.kernel s T S * g S := by
            refine Finset.sum_congr rfl ?_
            intro T hT
            rw [← Finset.mul_sum]
    _ = ∑ S, star (f S) * ∑ T, D.kernel s S T * g T := by
            simpa

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
Direct finite self-adjointness from scalar/holonomy conditions, without
external modewise-adjoint assumptions.

If amplitudes are self-adjoint scalars and holonomy is unitary at `s`, then
the finite Cantor--Dirac operator `op = Q + Q♯` is self-adjoint for the
finite pairing.
-/
@[rep_depth thermo]
theorem op_isSelfAdjoint_of_unitary_data
    (s : ℂ)
    (hAmp : ∀ p : PrimeMode P, star (D.amplitude p) = D.amplitude p)
    (hU : D.HolonomyUnitaryAt s) :
    IsAdjointPair (P := P) (D.op s) (D.op s) := by
  apply D.op_isSelfAdjoint_of_modewiseAdjoint (s := s)
  · intro p
    exact D.weighted_mode_isAdjointPair_of_unitary s hAmp hU p
  · intro p
    exact D.weighted_mode_isAdjointPairRev_of_unitary s hAmp hU p

/--
Legacy compatibility alias.

Prefer `op_isSelfAdjoint_of_unitary_data_of_zetaHolonomy`.
-/
@[rep_depth thermo]
theorem op_isSelfAdjoint_of_modewiseAdjoint_of_zetaHolonomy
    (hP : P.primes.Nonempty) (s : ℂ)
    (hhol : D.holonomy s = zetaHolonomy (P := P) s)
    (hs : s.re = 1 / 2)
    (hAmp : ∀ p : PrimeMode P, star (D.amplitude p) = D.amplitude p) :
    IsAdjointPair (P := P) (D.op s) (D.op s) := by
  have hU : D.HolonomyUnitaryAt s :=
    D.HolonomyUnitaryAt_of_re_eq_half_of_zetaHolonomy hP s hhol hs
  exact D.op_isSelfAdjoint_of_unitary_data s hAmp hU

/--
Legacy compatibility alias.

Prefer `op_isSelfAdjoint_of_unitary_data_of_HolonomyUnitaryAt_zetaHolonomy`.
-/
@[rep_depth thermo]
theorem op_isSelfAdjoint_of_modewiseAdjoint_of_HolonomyUnitaryAt_zetaHolonomy
    (hP : P.primes.Nonempty) (s : ℂ)
    (hhol : D.holonomy s = zetaHolonomy (P := P) s)
    (hU : D.HolonomyUnitaryAt s)
    (hAmp : ∀ p : PrimeMode P, star (D.amplitude p) = D.amplitude p) :
    IsAdjointPair (P := P) (D.op s) (D.op s) := by
  exact D.op_isSelfAdjoint_of_unitary_data s hAmp hU

/--
Zeta-specialized finite self-adjointness from unitary-data assumptions.

This eliminates explicit modewise adjoint hypotheses by deriving them from
`hAmp` and `HolonomyUnitaryAt`.
-/
@[rep_depth thermo]
theorem op_isSelfAdjoint_of_unitary_data_of_HolonomyUnitaryAt_zetaHolonomy
    (hP : P.primes.Nonempty) (s : ℂ)
    (hhol : D.holonomy s = zetaHolonomy (P := P) s)
    (hU : D.HolonomyUnitaryAt s)
    (hAmp : ∀ p : PrimeMode P, star (D.amplitude p) = D.amplitude p) :
    IsAdjointPair (P := P) (D.op s) (D.op s) := by
  exact D.op_isSelfAdjoint_of_unitary_data s hAmp hU

/--
Critical-line specialization of finite self-adjointness from unitary-data
assumptions.
-/
@[rep_depth thermo]
theorem op_isSelfAdjoint_of_unitary_data_of_zetaHolonomy
    (hP : P.primes.Nonempty) (s : ℂ)
    (hhol : D.holonomy s = zetaHolonomy (P := P) s)
    (hs : s.re = 1 / 2)
    (hAmp : ∀ p : PrimeMode P, star (D.amplitude p) = D.amplitude p) :
    IsAdjointPair (P := P) (D.op s) (D.op s) := by
  have hU : D.HolonomyUnitaryAt s :=
    D.HolonomyUnitaryAt_of_re_eq_half_of_zetaHolonomy hP s hhol hs
  exact D.op_isSelfAdjoint_of_unitary_data_of_HolonomyUnitaryAt_zetaHolonomy
    hP s hhol hU hAmp

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
Direct finite pairing Hermitian law from self-adjointness of `D.op s`.
-/
@[rep_depth thermo]
theorem op_pairing_hermitian_of_op_isSelfAdjoint
    (s : ℂ)
    (hself : IsAdjointPair (P := P) (D.op s) (D.op s))
    (f g : CantorField P) :
    pairing (D.op s f) g = pairing f (D.op s g) := by
  exact hself f g

/--
Direct kernel Hermitian symmetry from the finite pairing Hermitian law for `D.op s`.
-/
@[rep_depth thermo]
theorem kernel_conj_symm_of_op_pairing_hermitian
    (s : ℂ)
    (hpair :
      ∀ f g : CantorField P, pairing (D.op s f) g = pairing f (D.op s g))
    (S T : Vertex P) :
    star (D.kernel s S T) = D.kernel s T S := by
  have hself : IsAdjointPair (P := P) (D.op s) (D.op s) := by
    intro f g
    exact hpair f g
  exact D.kernel_conj_symm_of_op_isSelfAdjoint s hself S T

/--
Legacy compatibility alias.

Prefer `kernel_conj_symm_of_unitary_data_of_zetaHolonomy`.
-/
@[rep_depth thermo]
theorem kernel_conj_symm_of_modewiseAdjoint_of_zetaHolonomy
    (hP : P.primes.Nonempty) (s : ℂ)
    (hhol : D.holonomy s = zetaHolonomy (P := P) s)
    (hs : s.re = 1 / 2)
    (hAmp : ∀ p : PrimeMode P, star (D.amplitude p) = D.amplitude p)
    (S T : Vertex P) :
    star (D.kernel s S T) = D.kernel s T S := by
  have hself : IsAdjointPair (P := P) (D.op s) (D.op s) :=
    D.op_isSelfAdjoint_of_modewiseAdjoint_of_zetaHolonomy
      hP s hhol hs hAmp
  exact D.kernel_conj_symm_of_op_isSelfAdjoint s hself S T

/--
Legacy compatibility alias.

Prefer `kernel_conj_symm_of_unitary_data_of_HolonomyUnitaryAt_zetaHolonomy`.
-/
@[rep_depth thermo]
theorem kernel_conj_symm_of_modewiseAdjoint_of_HolonomyUnitaryAt_zetaHolonomy
    (hP : P.primes.Nonempty) (s : ℂ)
    (hhol : D.holonomy s = zetaHolonomy (P := P) s)
    (hU : D.HolonomyUnitaryAt s)
    (hAmp : ∀ p : PrimeMode P, star (D.amplitude p) = D.amplitude p)
    (S T : Vertex P) :
    star (D.kernel s S T) = D.kernel s T S := by
  have hself : IsAdjointPair (P := P) (D.op s) (D.op s) :=
    D.op_isSelfAdjoint_of_modewiseAdjoint_of_HolonomyUnitaryAt_zetaHolonomy
      hP s hhol hU hAmp
  exact D.kernel_conj_symm_of_op_isSelfAdjoint s hself S T

/--
Kernel Hermitian symmetry from unitary-data assumptions under zeta specialization.
-/
@[rep_depth thermo]
theorem kernel_conj_symm_of_unitary_data_of_HolonomyUnitaryAt_zetaHolonomy
    (hP : P.primes.Nonempty) (s : ℂ)
    (hhol : D.holonomy s = zetaHolonomy (P := P) s)
    (hU : D.HolonomyUnitaryAt s)
    (hAmp : ∀ p : PrimeMode P, star (D.amplitude p) = D.amplitude p)
    (S T : Vertex P) :
    star (D.kernel s S T) = D.kernel s T S := by
  have hself : IsAdjointPair (P := P) (D.op s) (D.op s) :=
    D.op_isSelfAdjoint_of_unitary_data_of_HolonomyUnitaryAt_zetaHolonomy
      hP s hhol hU hAmp
  exact D.kernel_conj_symm_of_op_isSelfAdjoint s hself S T

/--
Kernel Hermitian symmetry from unitary-data assumptions on the critical line
under zeta specialization.
-/
@[rep_depth thermo]
theorem kernel_conj_symm_of_unitary_data_of_zetaHolonomy
    (hP : P.primes.Nonempty) (s : ℂ)
    (hhol : D.holonomy s = zetaHolonomy (P := P) s)
    (hs : s.re = 1 / 2)
    (hAmp : ∀ p : PrimeMode P, star (D.amplitude p) = D.amplitude p)
    (S T : Vertex P) :
    star (D.kernel s S T) = D.kernel s T S := by
  have hU : D.HolonomyUnitaryAt s :=
    D.HolonomyUnitaryAt_of_re_eq_half_of_zetaHolonomy hP s hhol hs
  exact D.kernel_conj_symm_of_unitary_data_of_HolonomyUnitaryAt_zetaHolonomy
    hP s hhol hU hAmp S T

/--
Matrix-coefficient Hermitian symmetry on basis deltas:

`star (D.op s δ_T (S)) = D.op s δ_S (T)`.
-/
@[rep_depth thermo]
theorem op_basisDelta_conj_symm_of_kernel_conj_symm
    (s : ℂ)
    (hK : ∀ S T : Vertex P, star (D.kernel s S T) = D.kernel s T S)
    (S T : Vertex P) :
    star (D.op s (basisDelta T) S) = D.op s (basisDelta S) T := by
  calc
    star (D.op s (basisDelta T) S)
        = star (D.kernel s S T) := by
            rw [D.op_basisDelta_eq_kernel (s := s) (S := S) (T := T)]
    _ = D.kernel s T S := hK S T
    _ = D.op s (basisDelta S) T := by
          rw [D.op_basisDelta_eq_kernel (s := s) (S := T) (T := S)]

/--
Matrix-coefficient Hermitian symmetry on basis deltas induced by finite
self-adjointness of `D.op s`.
-/
@[rep_depth thermo]
theorem op_basisDelta_conj_symm_of_op_isSelfAdjoint
    (s : ℂ)
    (hself : IsAdjointPair (P := P) (D.op s) (D.op s))
    (S T : Vertex P) :
    star (D.op s (basisDelta T) S) = D.op s (basisDelta S) T := by
  have hK : ∀ S T : Vertex P, star (D.kernel s S T) = D.kernel s T S := by
    intro S T
    exact D.kernel_conj_symm_of_op_isSelfAdjoint s hself S T
  exact D.op_basisDelta_conj_symm_of_kernel_conj_symm s hK S T

/--
Conversely, matrix-coefficient Hermitian symmetry on basis deltas implies
kernel Hermitian symmetry.
-/
@[rep_depth thermo]
theorem kernel_conj_symm_of_op_basisDelta_conj_symm
    (s : ℂ)
    (hOp : ∀ S T : Vertex P,
      star (D.op s (basisDelta T) S) = D.op s (basisDelta S) T)
    (S T : Vertex P) :
    star (D.kernel s S T) = D.kernel s T S := by
  calc
    star (D.kernel s S T)
        = star (D.op s (basisDelta T) S) := by
            rw [D.op_basisDelta_eq_kernel (s := s) (S := S) (T := T)]
    _ = D.op s (basisDelta S) T := hOp S T
    _ = D.kernel s T S := by
          rw [D.op_basisDelta_eq_kernel (s := s) (S := T) (T := S)]

/--
Kernel Hermitian symmetry is equivalent to matrix-coefficient Hermitian symmetry
on basis deltas.
-/
@[rep_depth thermo]
theorem op_basisDelta_conj_symm_iff_kernel_conj_symm
    (s : ℂ) :
    (∀ S T : Vertex P, star (D.op s (basisDelta T) S) = D.op s (basisDelta S) T) ↔
      (∀ S T : Vertex P, star (D.kernel s S T) = D.kernel s T S) := by
  constructor
  · intro hOp S T
    exact D.kernel_conj_symm_of_op_basisDelta_conj_symm s hOp S T
  · intro hK S T
    exact D.op_basisDelta_conj_symm_of_kernel_conj_symm s hK S T

/--
Legacy compatibility alias.

Prefer `op_basisDelta_conj_symm_of_unitary_data_of_HolonomyUnitaryAt_zetaHolonomy`.
-/
@[rep_depth thermo]
theorem op_basisDelta_conj_symm_of_modewiseAdjoint_of_HolonomyUnitaryAt_zetaHolonomy
    (hP : P.primes.Nonempty) (s : ℂ)
    (hhol : D.holonomy s = zetaHolonomy (P := P) s)
    (hU : D.HolonomyUnitaryAt s)
    (hAmp : ∀ p : PrimeMode P, star (D.amplitude p) = D.amplitude p)
    (S T : Vertex P) :
    star (D.op s (basisDelta T) S) = D.op s (basisDelta S) T := by
  have hK : ∀ S T : Vertex P, star (D.kernel s S T) = D.kernel s T S := by
    intro S T
    exact D.kernel_conj_symm_of_modewiseAdjoint_of_HolonomyUnitaryAt_zetaHolonomy
      hP s hhol hU hAmp S T
  exact D.op_basisDelta_conj_symm_of_kernel_conj_symm s hK S T

/--
Basis-delta Hermitian symmetry from unitary-data assumptions under zeta specialization.
-/
@[rep_depth thermo]
theorem op_basisDelta_conj_symm_of_unitary_data_of_HolonomyUnitaryAt_zetaHolonomy
    (hP : P.primes.Nonempty) (s : ℂ)
    (hhol : D.holonomy s = zetaHolonomy (P := P) s)
    (hU : D.HolonomyUnitaryAt s)
    (hAmp : ∀ p : PrimeMode P, star (D.amplitude p) = D.amplitude p)
    (S T : Vertex P) :
    star (D.op s (basisDelta T) S) = D.op s (basisDelta S) T := by
  have hK : ∀ S T : Vertex P, star (D.kernel s S T) = D.kernel s T S := by
    intro S T
    exact D.kernel_conj_symm_of_unitary_data_of_HolonomyUnitaryAt_zetaHolonomy
      hP s hhol hU hAmp S T
  exact D.op_basisDelta_conj_symm_of_kernel_conj_symm s hK S T

/--
Basis-delta Hermitian symmetry from unitary-data assumptions on the critical
line under zeta specialization.
-/
@[rep_depth thermo]
theorem op_basisDelta_conj_symm_of_unitary_data_of_zetaHolonomy
    (hP : P.primes.Nonempty) (s : ℂ)
    (hhol : D.holonomy s = zetaHolonomy (P := P) s)
    (hs : s.re = 1 / 2)
    (hAmp : ∀ p : PrimeMode P, star (D.amplitude p) = D.amplitude p)
    (S T : Vertex P) :
    star (D.op s (basisDelta T) S) = D.op s (basisDelta S) T := by
  have hU : D.HolonomyUnitaryAt s :=
    D.HolonomyUnitaryAt_of_re_eq_half_of_zetaHolonomy hP s hhol hs
  exact D.op_basisDelta_conj_symm_of_unitary_data_of_HolonomyUnitaryAt_zetaHolonomy
    hP s hhol hU hAmp S T

/--
Matrix-coefficient Hermitian symmetry on basis deltas from the full finite
pairing Hermitian law.
-/
@[rep_depth thermo]
theorem op_basisDelta_conj_symm_of_op_pairing_hermitian
    (s : ℂ)
    (hpair :
      ∀ f g : CantorField P, pairing (D.op s f) g = pairing f (D.op s g))
    (S T : Vertex P) :
    star (D.op s (basisDelta T) S) = D.op s (basisDelta S) T := by
  have hK : ∀ S T : Vertex P, star (D.kernel s S T) = D.kernel s T S := by
    intro S T
    exact D.kernel_conj_symm_of_op_pairing_hermitian s hpair S T
  exact D.op_basisDelta_conj_symm_of_kernel_conj_symm s hK S T

/--
Legacy compatibility alias.

Prefer `op_basisDelta_conj_symm_of_unitary_data_of_zetaHolonomy`.
-/
@[rep_depth thermo]
theorem op_basisDelta_conj_symm_of_modewiseAdjoint_of_zetaHolonomy
    (hP : P.primes.Nonempty) (s : ℂ)
    (hhol : D.holonomy s = zetaHolonomy (P := P) s)
    (hs : s.re = 1 / 2)
    (hAmp : ∀ p : PrimeMode P, star (D.amplitude p) = D.amplitude p)
    (S T : Vertex P) :
    star (D.op s (basisDelta T) S) = D.op s (basisDelta S) T := by
  exact D.op_basisDelta_conj_symm_of_unitary_data_of_zetaHolonomy
    hP s hhol hs hAmp S T

/--
Legacy compatibility alias.

Prefer `op_pairing_hermitian_of_unitary_data_of_HolonomyUnitaryAt_zetaHolonomy`.
-/
@[rep_depth thermo]
theorem op_pairing_hermitian_of_modewiseAdjoint_of_HolonomyUnitaryAt_zetaHolonomy
    (hP : P.primes.Nonempty) (s : ℂ)
    (hhol : D.holonomy s = zetaHolonomy (P := P) s)
    (hU : D.HolonomyUnitaryAt s)
    (hAmp : ∀ p : PrimeMode P, star (D.amplitude p) = D.amplitude p)
    (f g : CantorField P) :
    pairing (D.op s f) g = pairing f (D.op s g) := by
  have hself : IsAdjointPair (P := P) (D.op s) (D.op s) :=
    D.op_isSelfAdjoint_of_modewiseAdjoint_of_HolonomyUnitaryAt_zetaHolonomy
      hP s hhol hU hAmp
  exact hself f g

/--
Full finite Hermitian pairing law from unitary-data assumptions under
zeta specialization.
-/
@[rep_depth thermo]
theorem op_pairing_hermitian_of_unitary_data_of_HolonomyUnitaryAt_zetaHolonomy
    (hP : P.primes.Nonempty) (s : ℂ)
    (hhol : D.holonomy s = zetaHolonomy (P := P) s)
    (hU : D.HolonomyUnitaryAt s)
    (hAmp : ∀ p : PrimeMode P, star (D.amplitude p) = D.amplitude p)
    (f g : CantorField P) :
    pairing (D.op s f) g = pairing f (D.op s g) := by
  have hself : IsAdjointPair (P := P) (D.op s) (D.op s) :=
    D.op_isSelfAdjoint_of_unitary_data_of_HolonomyUnitaryAt_zetaHolonomy
      hP s hhol hU hAmp
  exact hself f g

/--
Full finite Hermitian pairing law from unitary-data assumptions on the critical
line under zeta specialization.
-/
@[rep_depth thermo]
theorem op_pairing_hermitian_of_unitary_data_of_zetaHolonomy
    (hP : P.primes.Nonempty) (s : ℂ)
    (hhol : D.holonomy s = zetaHolonomy (P := P) s)
    (hs : s.re = 1 / 2)
    (hAmp : ∀ p : PrimeMode P, star (D.amplitude p) = D.amplitude p)
    (f g : CantorField P) :
    pairing (D.op s f) g = pairing f (D.op s g) := by
  have hU : D.HolonomyUnitaryAt s :=
    D.HolonomyUnitaryAt_of_re_eq_half_of_zetaHolonomy hP s hhol hs
  exact D.op_pairing_hermitian_of_unitary_data_of_HolonomyUnitaryAt_zetaHolonomy
    hP s hhol hU hAmp f g

/--
Legacy compatibility alias.

Prefer `op_pairing_hermitian_of_unitary_data_of_zetaHolonomy`.
-/
@[rep_depth thermo]
theorem op_pairing_hermitian_of_modewiseAdjoint_of_zetaHolonomy
    (hP : P.primes.Nonempty) (s : ℂ)
    (hhol : D.holonomy s = zetaHolonomy (P := P) s)
    (hs : s.re = 1 / 2)
    (hAmp : ∀ p : PrimeMode P, star (D.amplitude p) = D.amplitude p)
    (f g : CantorField P) :
    pairing (D.op s f) g = pairing f (D.op s g) := by
  exact D.op_pairing_hermitian_of_unitary_data_of_zetaHolonomy
    hP s hhol hs hAmp f g

end FiniteCantorZetaDirac

end InfoGeometry.Arithmetic.PrimeCantorZetaDiracOperator
