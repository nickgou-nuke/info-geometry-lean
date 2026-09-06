import Mathlib.Tactic
import InfoGeometry.Algebra.EulerLaurentDerivation
import InfoGeometry.Algebraic.EulerLaurentHestenesDivisor
import InfoGeometry.Clifford.HestenesWindingRotor
import InfoGeometry.Topology.AlgebraicPunctureDeRham
import InfoGeometry.Canonical.BilingualRealHestenesDictionary
import InfoGeometry.Arithmetic.IndexTheorem

/-!
# Riemann Pole-Zero Monodromy Bridge

Finite algebraic bridge from divisor charges to Hestenes rotor monodromy.

This owner connects:
* the signed integer order of a finite local divisor,
* the de Rham residue class `[du/u]`,
* the Hestenes winding rotor representation `ρ(n) = R^n`.

No infinities, no analytic continuation, no complex logarithm, no contour
integral.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.RiemannPoleZeroMonodromy

open InfoGeometry.Algebra.EulerLaurentDerivation
open InfoGeometry.Algebraic.EulerLaurentHestenesDivisor
open InfoGeometry.Clifford.HestenesWindingRotor
open InfoGeometry.Topology.AlgebraicPunctureDeRham
open InfoGeometry.Canonical.BilingualRealHestenesDictionary
open InfoGeometry.Arithmetic.IndexTheorem

variable {R : Type*} [Ring R]

/-! ## Finite divisor index -/

/-- The finite signed zero-minus-pole charge of a marked divisor. -/
def divisorIndex {ι : Type*} [Fintype ι] (order : ι → ℤ) : ℤ :=
  Finset.sum (Finset.univ : Finset ι) order

/-- The divisor index is additive under disjoint union. -/
theorem divisorIndex_add {ι : Type*} [Fintype ι]
    (order₁ order₂ : ι → ℤ) :
    divisorIndex (fun a => order₁ a + order₂ a) =
      divisorIndex order₁ + divisorIndex order₂ := by
  simp [divisorIndex, Finset.sum_add_distrib]

theorem divisorIndex_neg {ι : Type*} [Fintype ι]
    (order : ι → ℤ) :
    divisorIndex (fun a => -order a) = -divisorIndex order := by
  simp [divisorIndex, Finset.sum_neg_distrib]

theorem divisorIndex_sub {ι : Type*} [Fintype ι]
    (order₁ order₂ : ι → ℤ) :
    divisorIndex (fun a => order₁ a - order₂ a) =
      divisorIndex order₁ - divisorIndex order₂ := by
  simp [divisorIndex, Finset.sum_sub_distrib]

theorem winding_of_neg_divisorIndex
    {G : Type*} [Group G] {ι : Type*} [Fintype ι]
    (r : G) (order : ι → ℤ) :
    winding r (divisorIndex (fun a => -order a)) =
      (winding r (divisorIndex order))⁻¹ := by
  rw [divisorIndex_neg]
  exact winding_neg r (divisorIndex order)

theorem winding_of_sub_divisorIndex
    {G : Type*} [Group G] {ι : Type*} [Fintype ι]
    (r : G) (order₁ order₂ : ι → ℤ) :
    winding r (divisorIndex (fun a => order₁ a - order₂ a)) =
      winding r (divisorIndex order₁) *
        (winding r (divisorIndex order₂))⁻¹ := by
  rw [divisorIndex_sub]
  exact winding_sub r (divisorIndex order₁) (divisorIndex order₂)

/-- The divisor index of a reflection-invariant packet is reflection-invariant. -/
theorem divisorIndex_reflection_invariant {ι : Type*} [Fintype ι]
    (D : DivisorData ι) :
    (∑ a : ι, D.order a) = (∑ a : ι, D.order (D.reflect a)) := by
  simp [D.order_reflect]

/-- The de Rham class of the logarithmic differential of a local divisor
    packet is its order times `[du/u]`. -/
theorem deRham_class_equals_order (F : LocalDivisorData R) :
    ∃ (c : R), chargeForm F = Finsupp.single (-1) c ∧ c = F.order := by
  use F.order
  constructor
  · rfl
  · rfl

/-- The residue of the logarithmic differential equals the divisor order. -/
theorem residue_dlog_equals_divisor_order (F : LocalDivisorData R) :
    residue (chargeForm F) = F.order := by
  unfold chargeForm residue
  rw [Finsupp.single_apply]
  simp

/-! ## Bridge from unit-certified Laurent normal forms -/

/-
`LocalLaurentNormalForm` is the stronger local packet: besides the signed
order it records a Laurent carrier, its normal-form equation, and a unit
certificate.  The residue/index owner uses the smaller `LocalDivisorData`
packet.  This conversion forgets only the extra carrier witness; it does not
change the order or assert an analytic expansion.
-/
def localDivisorDataOfNormalForm
    {R : Type*} [CommRing R]
    (F : LocalLaurentNormalForm (R := R)) : LocalDivisorData R :=
  { order := F.order
    unit := F.unit }

@[simp] theorem localDivisorDataOfNormalForm_order
    {R : Type*} [CommRing R]
    (F : LocalLaurentNormalForm (R := R)) :
    (localDivisorDataOfNormalForm F).order = F.order :=
  rfl

theorem residue_normalForm_charge
    {R : Type*} [CommRing R]
    (F : LocalLaurentNormalForm (R := R)) :
    residue (chargeForm (localDivisorDataOfNormalForm F)) = F.order := by
  exact residue_dlog_equals_divisor_order (localDivisorDataOfNormalForm F)

theorem normalForm_divisorOrder_eq_residue
    {R : Type*} [CommRing R]
    (F : LocalLaurentNormalForm (R := R)) :
    divisorOrder F = F.order ∧
      residue (chargeForm (localDivisorDataOfNormalForm F)) = divisorOrder F := by
  exact ⟨rfl, by simpa using residue_normalForm_charge F⟩

/-! ## Finite residue/index aggregation -/

/-- The sum of local algebraic residues is the cast finite divisor index. -/
theorem residue_sum_chargeForms_eq_cast_divisorIndex
    [CharZero R] {ι : Type*} [Fintype ι]
    (data : ι → LocalDivisorData R) :
    (∑ a : ι, residue (chargeForm (data a))) =
      (divisorIndex (fun a => (data a).order) : R) := by
  simp only [residue_dlog_equals_divisor_order]
  exact_mod_cast (rfl :
    (∑ a : ι, (data a).order) =
      divisorIndex (fun a => (data a).order))

/-!
For integer divisor packets no scalar-cast interface is needed.  This is the
direct finite index statement used by the winding lane; it is distinct from
the later compatibility declaration whose two sides are definitionally the
same sum.
-/
theorem divisorIndex_eq_residue_sum_integer
    {ι : Type*} [Fintype ι]
    (data : ι → LocalDivisorData ℤ) :
    divisorIndex (fun a => (data a).order) =
      ∑ a : ι, residue (chargeForm (data a)) := by
  simp [divisorIndex, residue_dlog_equals_divisor_order]

/-- For integer local packets, the total residue charge transports directly
    to the existing Hestenes integer-power winding action. -/
theorem winding_of_residue_sum
    {G : Type*} [Group G] {ι : Type*} [Fintype ι]
    (r : G) (data : ι → LocalDivisorData ℤ) :
    winding r (divisorIndex (fun a => (data a).order)) =
      winding r (∑ a : ι, residue (chargeForm (data a))) := by
  congr 1
  simp [divisorIndex, residue_dlog_equals_divisor_order]

/-! ## Master bridge: divisor index as winding charge -/

/-- The finite divisor index is the total winding charge carried by the
    marked divisor.  This is the algebraic replacement for the contour
    integral `(1/2πi) ∮ d ln F`. -/
theorem divisor_index_equals_total_winding_charge
    {G : Type*} [CommGroup G]
    {ι : Type*} [Fintype ι]
    (r : G) (order : ι → ℤ) :
    divisorWinding r (Finset.univ : Finset ι) order =
      ∏ a : ι, winding r (order a) := by
  classical
  unfold divisorWinding Algebra.EulerLaurentDerivation.divisorIndex winding
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, Finset.prod_insert ha]
      rw [zpow_add r]
      rw [ih]

/-! ## A genuine finite divisor-to-kernel index realization -/

/-- Positive multiplicity carried by one signed divisor charge. -/
def positiveCharge (z : ℤ) : ℕ := Int.natAbs (max z 0)

/-- Pole multiplicity carried by one signed divisor charge. -/
def negativeCharge (z : ℤ) : ℕ := Int.natAbs (max (-z) 0)

theorem positiveCharge_sub_negativeCharge (z : ℤ) :
    (positiveCharge z : ℤ) - negativeCharge z = z := by
  by_cases hz : 0 ≤ z
  · have hneg : -z ≤ 0 := by omega
    simp [positiveCharge, negativeCharge, max_eq_left hz,
      max_eq_right hneg, Int.natAbs_of_nonneg hz]
  · have hz' : z < 0 := lt_of_not_ge hz
    have hpos : 0 ≤ -z := by omega
    simp [positiveCharge, negativeCharge, max_eq_right (le_of_lt hz'),
      max_eq_left hpos, abs_of_neg hz']

abbrev positiveDivisorCarrier {ι : Type*} [Fintype ι]
    (order : ι → ℤ) := Fin (∑ a : ι, positiveCharge (order a)) → ℚ

abbrev negativeDivisorCarrier {ι : Type*} [Fintype ι]
    (order : ι → ℤ) := Fin (∑ a : ι, negativeCharge (order a)) → ℚ

/-- The zero differential complex whose two graded carriers encode positive and
    negative divisor multiplicity. -/
def divisorKernelComplex {ι : Type*} [Fintype ι] (order : ι → ℤ) :
    FiniteTwoTermComplex
      (K := ℚ)
      (Vp := positiveDivisorCarrier order)
      (Vm := negativeDivisorCarrier order) :=
  zeroFiniteTwoTermComplex

theorem divisor_kernel_index_eq_divisor_index
    {ι : Type*} [Fintype ι] (order : ι → ℤ) :
    finiteKernelIndex (divisorKernelComplex order) = divisorIndex order := by
  unfold divisorKernelComplex
  rw [finiteKernelIndex_zero]
  simp only [positiveDivisorCarrier, negativeDivisorCarrier,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  calc
    ((∑ a : ι, positiveCharge (order a) : ℕ) : ℤ) -
        ((∑ a : ι, negativeCharge (order a) : ℕ) : ℤ) =
        ∑ a : ι, ((positiveCharge (order a) : ℤ) -
          negativeCharge (order a)) := by
      push_cast
      rw [Finset.sum_sub_distrib]
    _ = ∑ a : ι, order a := by
      apply Finset.sum_congr rfl
      intro a ha
      exact positiveCharge_sub_negativeCharge (order a)
    _ = divisorIndex order := by
      rfl

theorem divisor_kernel_index_eq_residue_sum
    {ι : Type*} [Fintype ι]
    (data : ι → LocalDivisorData ℤ) :
    finiteKernelIndex (divisorKernelComplex (fun a => (data a).order)) =
      ∑ a : ι, residue (chargeForm (data a)) := by
  rw [divisor_kernel_index_eq_divisor_index]
  exact divisorIndex_eq_residue_sum_integer data

/-- The finite kernel index and the divisor winding readout are the same
    integer charge after transport into a commutative rotor group. -/
theorem winding_of_divisor_kernel_index
    {G : Type*} [CommGroup G]
    {ι : Type*} [Fintype ι]
    (r : G) (order : ι → ℤ) :
    winding r (finiteKernelIndex (divisorKernelComplex order)) =
      ∏ a : ι, winding r (order a) := by
  rw [divisor_kernel_index_eq_divisor_index]
  exact divisor_index_equals_total_winding_charge r order

theorem winding_of_residue_kernel_index
    {G : Type*} [CommGroup G]
    {ι : Type*} [Fintype ι]
    (r : G) (data : ι → LocalDivisorData ℤ) :
    winding r (finiteKernelIndex
      (divisorKernelComplex (fun a => (data a).order))) =
      winding r (∑ a : ι, residue (chargeForm (data a))) := by
  rw [divisor_kernel_index_eq_residue_sum data]

/-! ## Composed finite charge capstone -/

/-- The complete finite charge square, composed from the native owners.

The first equality is the genuine finite kernel/divisor-index theorem, the
second is coefficient extraction for the algebraic logarithmic differential,
and the third transports that same integer charge to the chosen Hestenes
winding carrier.  This theorem deliberately does not identify any of these
finite readouts with an analytic determinant or a contour integral.
-/
theorem finite_charge_square
    {G : Type*} [CommGroup G]
    {ι : Type*} [Fintype ι]
    (r : G) (data : ι → LocalDivisorData ℤ) :
    finiteKernelIndex
        (divisorKernelComplex (fun a => (data a).order)) =
        divisorIndex (fun a => (data a).order) ∧
      divisorIndex (fun a => (data a).order) =
        ∑ a : ι, residue (chargeForm (data a)) ∧
      winding r
          (finiteKernelIndex
            (divisorKernelComplex (fun a => (data a).order))) =
        ∏ a : ι, winding r ((data a).order) := by
  refine ⟨divisor_kernel_index_eq_divisor_index _,
    divisorIndex_eq_residue_sum_integer data, ?_⟩
  exact winding_of_divisor_kernel_index r (fun a => (data a).order)

/-- The winding charge of a reflection-invariant divisor packet is
    reflection-invariant. -/
theorem winding_charge_reflection_invariant {ι : Type*} [Fintype ι]
    (D : DivisorData ι) :
    (∑ a : ι, D.order a) = (∑ a : ι, D.order (D.reflect a)) := by
  simp [D.order_reflect]

end InfoGeometry.Arithmetic.RiemannPoleZeroMonodromy

end noncomputable section
