/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Core.SupercolorMultiplication

/-!
# Common-source color closure and associative super-Jacobi

Reuse the existing supercolor, MP, Jordan, commutator and Majorana owners.
Common co-range absorption is characterized, not hidden in a structure named
`sl(k|1)`. The graded identities below are identities in an associative ring;
a graded carrier, representation map and classification are separate claims.
-/

namespace InfoGeometry.Core.SupercolorSourceClosure

open InfoGeometry.Core.SuperGrassmannianSusy
open InfoGeometry.Singular.MoorePenrose

section StarRing
variable {R : Type*} [Ring R] [StarRing R]
variable {ι : Type*} {d b : ι → R}

/-- A single absorption equation suffices for this matching-middle product. -/
theorem colorBoson_mul_of_absorption (i j m : ι)
    (h : d i * (b j * d j) = d i) :
    colorBoson d b i j * colorBoson d b j m = colorBoson d b i m := by
  rw [colorBoson_mul_middle, h]
  rfl

/-- Under MP self-adjointness, mutual source absorption is exactly equality
of all co-range projections. No star-duality of the primitive arrows is needed. -/
theorem common_absorption_iff_equal_corange (hS : IsSupercolorSystem d b) :
    (∀ i j, d i * (b j * d j) = d i) ↔
      (∀ i j, b i * d i = b j * d j) := by
  constructor
  · intro h i j
    have hleft : (b i * d i) * (b j * d j) = b i * d i := by
      calc
        (b i * d i) * (b j * d j) = b i * (d i * (b j * d j)) := by
          simp only [mul_assoc]
        _ = b i * d i := by rw [h i j]
    have hright : (b j * d j) * (b i * d i) = b j * d j := by
      calc
        (b j * d j) * (b i * d i) = b j * (d j * (b i * d i)) := by
          simp only [mul_assoc]
        _ = b j * d j := by rw [h j i]
    have hstar := congrArg star hleft
    rw [star_mul, (hS.mp i).ba_adj_eq, (hS.mp j).ba_adj_eq] at hstar
    exact hstar.symm.trans hright
  · intro h i j
    rw [← h i j, ← mul_assoc, (hS.mp i).aba_eq_a]

/-- Star symmetry of the sector charge follows from MP alone. -/
theorem sector_charge_star_of_mp {a m : R} (h : IsMoorePenroseInverse a m) :
    star (sectorCentralCharge a m) = sectorCentralCharge a m := by
  simp only [sectorCentralCharge, jordanProd, star_add, h.ab_adj_eq, h.ba_adj_eq]

/-- The active difference is also self-adjoint without assuming `m = star a`. -/
theorem chiral_difference_star_of_mp {a m : R} (h : IsMoorePenroseInverse a m) :
    star (a * m - m * a) = a * m - m * a := by
  rw [star_sub, h.ab_adj_eq, h.ba_adj_eq]

theorem total_charge_star_of_mp [Fintype ι]
    (h : ∀ i, IsMoorePenroseInverse (d i) (b i)) :
    star (totalCentralCharge d b) = totalCentralCharge d b := by
  unfold totalCentralCharge
  rw [star_sum]
  exact Finset.sum_congr rfl (fun i _ => sector_charge_star_of_mp (h i))

variable (hS : IsSupercolorSystem d b) {q : R} (hq : ∀ i, b i * d i = q)

/-- Source endpoint relations, retaining multiplication order. -/
theorem source_endpoint_actions (i : ι) :
    d i * q = d i ∧ q * d i = 0 ∧ q * b i = b i ∧ b i * q = 0 := by
  rw [← hq i]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← mul_assoc, (hS.mp i).aba_eq_a]
  · rw [mul_assoc, hS.d_mul_d i i, mul_zero]
  · exact (hS.mp i).bab_eq_b
  · rw [← mul_assoc, hS.b_mul_b i i, zero_mul]

theorem colorBoson_mul_forward [DecidableEq ι] (i j l : ι) :
    colorBoson d b i j * d l = if j = l then d i else 0 := by
  by_cases h : j = l
  · subst l
    simpa only [colorBoson, mul_assoc, hq j, if_true] using
      (source_endpoint_actions hS hq i).1
  · simp only [h, if_false, colorBoson, mul_assoc, hS.b_mul_d_ne h, mul_zero]

theorem forward_mul_colorBoson (i j l : ι) :
    d l * colorBoson d b i j = 0 := by
  simp only [colorBoson, ← mul_assoc, hS.d_mul_d l i, zero_mul]

theorem backward_mul_colorBoson [DecidableEq ι] (i j l : ι) :
    b l * colorBoson d b i j = if l = i then b j else 0 := by
  by_cases h : l = i
  · subst l
    simpa only [colorBoson, ← mul_assoc, hq i, if_true] using
      (source_endpoint_actions hS hq j).2.2.1
  · simp only [h, if_false, colorBoson, ← mul_assoc, hS.b_mul_d_ne h, zero_mul]

theorem colorBoson_mul_backward (i j l : ι) :
    colorBoson d b i j * b l = 0 := by
  simp only [colorBoson, mul_assoc, hS.b_mul_b j l, mul_zero]

/-- The two odd module actions of the common-source color algebra. -/
theorem colorBoson_odd_actions [DecidableEq ι] (i j l : ι) :
    lieBracket (colorBoson d b i j) (d l) = (if j = l then d i else 0) ∧
    lieBracket (colorBoson d b i j) (b l) = -(if l = i then b j else 0) := by
  constructor
  · simp only [lieBracket, colorBoson_mul_forward hS hq,
      forward_mul_colorBoson hS, sub_zero]
  · simp only [lieBracket, colorBoson_mul_backward hS,
      backward_mul_colorBoson hS hq, zero_sub]

/-- Odd--odd closure contains the reference-coordinate projection as well as
color matrix units; omitting that term loses the actual supermatrix relation. -/
theorem odd_pair_closure [DecidableEq ι] (i j : ι) :
    jordanProd (d i) (b j) =
      colorBoson d b i j + (if i = j then q else 0) := by
  by_cases h : i = j
  · subst j
    simp only [jordanProd, colorBoson, if_true, hq i]
  · simp only [jordanProd, colorBoson, h, if_false,
      hS.b_mul_d_ne h.symm, add_zero]

/-- A disjoint-support system cannot also have nonzero common-source arrows. -/
theorem orthogonal_absorption_forces_zero
    (hE : IsOrthogonalExtendedSusy d b) {i j : ι} (hij : i ≠ j)
    (habs : d i * (b j * d j) = d i) : d i = 0 ∧ b i = 0 := by
  have hd : d i = 0 := by
    calc
      d i = (d i * b j) * d j := by simpa only [mul_assoc] using habs.symm
      _ = 0 := by rw [hE.d_mul_b_ne hij, zero_mul]
  refine ⟨hd, ?_⟩
  have houter := (hE.mp i).bab_eq_b
  simpa only [hd, mul_zero, zero_mul] using houter.symm

end StarRing

section AssociativeJacobi
variable {R : Type*} [Ring R]

/-- Parity-labelled associative supercommutator. This definition alone does
not equip an arbitrary ring with a grading. -/
def gradedBracket (p q : Bool) (x y : R) : R :=
  if p && q then jordanProd x y else lieBracket x y

/-- All eight parity cases of the associative super-Jacobi derivation law. -/
theorem graded_jacobi (p q r : Bool) (x y z : R) :
    gradedBracket p (Bool.xor q r) x (gradedBracket q r y z) =
      gradedBracket (Bool.xor p q) r (gradedBracket p q x y) z +
        (if p && q then
          -gradedBracket q (Bool.xor p r) y (gradedBracket p r x z)
        else gradedBracket q (Bool.xor p r) y (gradedBracket p r x z)) := by
  cases p <;> cases q <;> cases r <;>
    simp [gradedBracket, jordanProd, lieBracket] <;> noncomm_ring

/-- The even--odd--odd specialization stated in the submitted note. -/
theorem superJacobi_even_odd_odd (z x y : R) :
    lieBracket z (jordanProd x y) =
      jordanProd (lieBracket z x) y + jordanProd x (lieBracket z y) := by
  unfold lieBracket jordanProd
  noncomm_ring

/-- The odd--odd--odd cyclic specialization stated in the submitted note. -/
theorem superJacobi_odd_odd_odd (x y z : R) :
    lieBracket x (jordanProd y z) + lieBracket y (jordanProd z x) +
      lieBracket z (jordanProd x y) = 0 := by
  unfold lieBracket jordanProd
  noncomm_ring

end AssociativeJacobi
end InfoGeometry.Core.SupercolorSourceClosure
