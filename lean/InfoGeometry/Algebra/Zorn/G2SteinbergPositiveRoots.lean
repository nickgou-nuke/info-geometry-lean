import InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
import InfoGeometry.Algebra.Zorn.G2TwoBasisRigidity
import InfoGeometry.Algebra.Zorn.G2UnipotentRootSubgroup
import InfoGeometry.Algebra.Zorn.G2TwoExplicitGenerators
import Mathlib.Tactic

/-!
# Initial Steinberg Root Automorphisms of G₂(2)

This module constructs three explicit unipotent root automorphisms in
`SplitOctF2Aut` and proves their native relations.  It does not yet construct
all six positive-root groups or the full unipotent radical:

$$[u_S, u_L] = u_S u_L u_S u_L = u_{\alpha_1 + \alpha_2}$$

All proofs in this initial packet are native Mathlib kernel-checked theorems
with 0 `sorry`s.
-/

namespace InfoGeometry.Algebra.Zorn.G2SteinbergRoots

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2Unipotent

/-- Simple short root unipotent automorphism $x_{\alpha_1}(1)$. -/
def uShort : SplitOctF2Aut := unipotentShortAut true

/-- Simple long root unipotent automorphism $x_{\alpha_2}(1)$. -/
def uLong : SplitOctF2Aut := unipotentLongAut true

/-- Unipotent action function for composite short root $\alpha_1 + \alpha_2$:
    shifts $x_0 \leftarrow x_0 + x_2$ and $y_2 \leftarrow y_2 + y_0$. -/
def uMidFun (X : SplitOctF2) : SplitOctF2 :=
  ⟨X.a, X.b, add2 X.x0 X.x2, X.x1, X.x2, X.y0, X.y1, add2 X.y2 X.y0⟩

def uMidEquiv : SplitOctF2 ≃ SplitOctF2 where
  toFun := uMidFun
  invFun := uMidFun
  left_inv X := by rcases X; ext <;> simp [uMidFun, add2]
  right_inv X := by rcases X; ext <;> simp [uMidFun, add2]

/-- Proof that `uMidEquiv` preserves the split-octonion unit, addition, and multiplication. -/
theorem isSplitOctF2Aut_uMid : IsSplitOctF2Aut uMidEquiv := by
  refine ⟨rfl, ?_, ?_⟩
  · intro X Y
    rcases X with ⟨a1, b1, x01, x11, x21, y01, y11, y21⟩
    rcases Y with ⟨a2, b2, x02, x12, x22, y02, y12, y22⟩
    ext
    · rfl
    · rfl
    · dsimp [uMidEquiv, uMidFun, add]
      exact xor_swap x01 x02 x21 x22
    · rfl
    · rfl
    · rfl
    · rfl
    · dsimp [uMidEquiv, uMidFun, add]
      exact xor_swap y21 y22 y01 y02
  · intro X Y
    rcases X with ⟨a1, b1, x01, x11, x21, y01, y11, y21⟩
    rcases Y with ⟨a2, b2, x02, x12, x22, y02, y12, y22⟩
    ext
    · dsimp [uMidEquiv, uMidFun, mul, add2, mul2, dot3]
      revert a1 a2 x01 x11 x21 y02 y12 y22 y01 y11 y21 x02 x12 x22
      decide
    · dsimp [uMidEquiv, uMidFun, mul, add2, mul2, dot3]
      revert b1 b2 y01 y11 y21 x02 x12 x22 x01 x11 x21 y02 y12 y22
      decide
    · dsimp [uMidEquiv, uMidFun, mul, add2, mul2, cross0, cross2]
      revert a1 a2 b1 b2 x01 x02 x21 x22 y11 y21 y12 y22 y01 y02
      decide
    · dsimp [uMidEquiv, uMidFun, mul, add2, mul2, cross1]
      revert a1 b2 x11 x12 y01 y21 y02 y22 y01 y02
      decide
    · rfl
    · rfl
    · dsimp [uMidEquiv, uMidFun, mul, add2, mul2, cross1]
      revert b1 a2 x21 x02 x01 x22 y12 y11
      decide
    · dsimp [uMidEquiv, uMidFun, mul, add2, mul2, cross2, cross0]
      revert b1 b2 a1 a2 y21 y22 y01 y02 x01 x11 x02 x12 x21 x22
      decide

/-- 🏆 THEOREM 1: The composite short root unipotent automorphism $x_{\alpha_1 + \alpha_2}(1)$. -/
def uMid : SplitOctF2Aut := ⟨uMidEquiv, isSplitOctF2Aut_uMid⟩

/-- All three positive root automorphisms are involutions of order 2. -/
theorem uShort_sq : uShort * uShort = 1 := unipotentShortAut_order true
theorem uLong_sq : uLong * uLong = 1 := unipotentLongAut_order true

theorem uMid_sq : uMid * uMid = 1 := by
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> decide

theorem uMid_ne_one : uMid ≠ (1 : SplitOctF2Aut) := by
  intro h
  have h0 := congrArg (fun f : SplitOctF2Aut => f.1 (basis8 4)) h
  revert h0
  decide

theorem uMid_ne_uShort : uMid ≠ uShort := by
  intro h
  have h0 := congrArg (fun f : SplitOctF2Aut => f.1 (basis8 4)) h
  revert h0
  decide

theorem uMid_ne_uLong : uMid ≠ uLong := by
  intro h
  have h0 := congrArg (fun f : SplitOctF2Aut => f.1 (basis8 4)) h
  revert h0
  decide

/-- 🏆 THEOREM 2: Exact G₂ Steinberg Commutator Relation over 𝔽₂:
    [u_S, u_L] = u_S * u_L * u_S * u_L = u_{α₁ + α₂} -/
theorem steinberg_commutator_short_long :
    uShort * uLong * uShort * uLong = uMid := by
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> decide

/-- 🏆 THEOREM 3: Commutation between uMid and uShort:
    [u_{α₁ + α₂}, u_S] = 1 -/
theorem uMid_commutes_uShort :
    uMid * uShort = uShort * uMid := by
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> decide

/-- 🏆 THEOREM 4: Commutation between uMid and uLong:
    [u_{α₁ + α₂}, u_L] = 1 -/
theorem uMid_commutes_uLong :
    uMid * uLong = uLong * uMid := by
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> decide

theorem uMid_mem_candidateRootSubgroup :
    uMid ∈ candidateRootSubgroup := by
  rw [← steinberg_commutator_short_long]
  have hs : uShort ∈ candidateRootSubgroup := by
    change unipotentShortAut true ∈ candidateRootSubgroup
    exact candidateRootFamily_mem 0
  have hl : uLong ∈ candidateRootSubgroup := by
    change unipotentLongAut true ∈ candidateRootSubgroup
    exact candidateRootFamily_mem 3
  exact candidateRootSubgroup.mul_mem
    (candidateRootSubgroup.mul_mem
      (candidateRootSubgroup.mul_mem hs hl) hs) hl

theorem simpleRootCommutator_eq_uMid :
    simpleRootCommutator = uMid := by
  exact steinberg_commutator_short_long

theorem uMid_mem_simpleRootSubgroup :
    uMid ∈ simpleRootSubgroup := by
  rw [← simpleRootCommutator_eq_uMid]
  exact simpleRootCommutator_mem

noncomputable def positiveRootPacket : Fin 6 → SplitOctF2Aut
  | 0 => uShort
  | 1 => uLong
  | 2 => uMid
  | 3 => conjugateAut cycle012Aut uLong
  | 4 => conjugateAut cycle012Aut uMid
  | 5 => conjugateAut (cycle012Aut * cycle012Aut) uMid

theorem positiveRootPacket_sq (i : Fin 6) :
    positiveRootPacket i * positiveRootPacket i = 1 := by
  fin_cases i
  · exact uShort_sq
  · exact uLong_sq
  · exact uMid_sq
  · exact conjugateAut_sq cycle012Aut uLong uLong_sq
  · exact conjugateAut_sq cycle012Aut uMid uMid_sq
  · exact conjugateAut_sq (cycle012Aut * cycle012Aut) uMid uMid_sq

theorem positiveRootPacket_ne_one (i : Fin 6) :
    positiveRootPacket i ≠ (1 : SplitOctF2Aut) := by
  fin_cases i
  · exact unipotentShortAut_true_ne_one
  · exact unipotentLongAut_true_ne_one
  · exact uMid_ne_one
  · exact conjugateAut_ne_one cycle012Aut uLong
      unipotentLongAut_true_ne_one
  · exact conjugateAut_ne_one cycle012Aut uMid uMid_ne_one
  · exact conjugateAut_ne_one (cycle012Aut * cycle012Aut) uMid uMid_ne_one



theorem positiveRootPacket_injective :
    Function.Injective positiveRootPacket := by
  intro i j h
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals
    exfalso
    have h0 := congrArg (fun f : SplitOctF2Aut => f.1 (basis8 0)) h
    have h1 := congrArg (fun f : SplitOctF2Aut => f.1 (basis8 1)) h
    have h2 := congrArg (fun f : SplitOctF2Aut => f.1 (basis8 2)) h
    have h3 := congrArg (fun f : SplitOctF2Aut => f.1 (basis8 3)) h
    have h4 := congrArg (fun f : SplitOctF2Aut => f.1 (basis8 4)) h
    have h5 := congrArg (fun f : SplitOctF2Aut => f.1 (basis8 5)) h
    have h6 := congrArg (fun f : SplitOctF2Aut => f.1 (basis8 6)) h
    have h7 := congrArg (fun f : SplitOctF2Aut => f.1 (basis8 7)) h
    revert h0 h1 h2 h3 h4 h5 h6 h7
    decide

noncomputable def positiveRootSubgroup : Subgroup SplitOctF2Aut :=
  Subgroup.closure (Set.range positiveRootPacket)

theorem positiveRootPacket_mem_subgroup (i : Fin 6) :
    positiveRootPacket i ∈ positiveRootSubgroup := by
  exact Subgroup.subset_closure ⟨i, rfl⟩

theorem positiveRootSubgroup_mul_mem {g h : SplitOctF2Aut}
    (hg : g ∈ positiveRootSubgroup) (hh : h ∈ positiveRootSubgroup) :
    g * h ∈ positiveRootSubgroup := by
  exact positiveRootSubgroup.mul_mem hg hh

theorem positiveRootSubgroup_inv_mem {g : SplitOctF2Aut}
    (hg : g ∈ positiveRootSubgroup) : g⁻¹ ∈ positiveRootSubgroup := by
  exact positiveRootSubgroup.inv_mem hg

theorem positiveRootSubgroup_contains_packet_range :
    Set.range positiveRootPacket ⊆ positiveRootSubgroup := by
  intro g hg
  exact Subgroup.subset_closure hg

noncomputable instance positiveRootSubgroupFintype :
    Fintype positiveRootSubgroup := Fintype.ofFinite _

noncomputable def positiveRootPacketEquivRange :
    Fin 6 ≃ Set.range positiveRootPacket :=
  Equiv.ofBijective
    (fun i => ⟨positiveRootPacket i, ⟨i, rfl⟩⟩)
    ⟨by
      intro i j h
      exact positiveRootPacket_injective (Subtype.ext_iff.mp h),
     by
      intro x
      rcases x with ⟨x, i, rfl⟩
      exact ⟨i, rfl⟩⟩

noncomputable instance positiveRootRangeFintype :
    Fintype (Set.range positiveRootPacket) := Fintype.ofFinite _

theorem positiveRootPacket_range_card :
    Fintype.card (Set.range positiveRootPacket) = 6 := by
  rw [← Fintype.card_congr positiveRootPacketEquivRange]
  simp

noncomputable def positiveRootRangeToSubgroup
    (x : Set.range positiveRootPacket) : positiveRootSubgroup :=
  ⟨x.1, positiveRootSubgroup_contains_packet_range x.2⟩

theorem positiveRootRangeToSubgroup_injective :
    Function.Injective positiveRootRangeToSubgroup := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : positiveRootSubgroup => (z : SplitOctF2Aut)) h

theorem positiveRootSubgroup_card_lower_bound_six :
    6 ≤ Fintype.card positiveRootSubgroup := by
  have hcard : Fintype.card (Set.range positiveRootPacket) ≤
      Fintype.card positiveRootSubgroup :=
    Fintype.card_le_of_injective positiveRootRangeToSubgroup
      positiveRootRangeToSubgroup_injective
  simpa [positiveRootPacket_range_card] using hcard

noncomputable def positiveRootAction (i : Fin 6) (t : Bool) : SplitOctF2Aut :=
  if t then positiveRootPacket i else 1

theorem positiveRootAction_false (i : Fin 6) :
    positiveRootAction i false = (1 : SplitOctF2Aut) := by
  rfl

theorem positiveRootAction_true (i : Fin 6) :
    positiveRootAction i true = positiveRootPacket i := by
  simp [positiveRootAction]

theorem positiveRootAction_add (i : Fin 6) (s t : Bool) :
    positiveRootAction i (s ^^ t) =
      positiveRootAction i s * positiveRootAction i t := by
  cases s <;> cases t
  · rfl
  · simp [positiveRootAction]
  · simp [positiveRootAction]
  · simpa [positiveRootAction] using (positiveRootPacket_sq i).symm

theorem positiveRootAction_comm (i : Fin 6) (s t : Bool) :
    positiveRootAction i s * positiveRootAction i t =
      positiveRootAction i t * positiveRootAction i s := by
  rw [← positiveRootAction_add, ← positiveRootAction_add, Bool.xor_comm]

theorem positiveRootAction_ne_one (i : Fin 6) :
    positiveRootAction i true ≠ (1 : SplitOctF2Aut) := by
  simpa [positiveRootAction] using positiveRootPacket_ne_one i

theorem positiveRootPacket_comm_0_2 :
    positiveRootPacket 0 * positiveRootPacket 2 =
      positiveRootPacket 2 * positiveRootPacket 0 := by
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> decide

theorem positiveRootPacket_comm_0_5 :
    positiveRootPacket 0 * positiveRootPacket 5 =
      positiveRootPacket 5 * positiveRootPacket 0 := by
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> decide

theorem positiveRootPacket_comm_1_4 :
    positiveRootPacket 1 * positiveRootPacket 4 =
      positiveRootPacket 4 * positiveRootPacket 1 := by
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> decide

theorem positiveRootPacket_comm_3_4 :
    positiveRootPacket 3 * positiveRootPacket 4 =
      positiveRootPacket 4 * positiveRootPacket 3 := by
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> decide

theorem positiveRootPacket_comm_3_5 :
    positiveRootPacket 3 * positiveRootPacket 5 =
      positiveRootPacket 5 * positiveRootPacket 3 := by
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> decide

theorem positiveRootPacket_commutator_0_1 :
    automorphismCommutator (positiveRootPacket 0) (positiveRootPacket 1) =
      positiveRootPacket 2 := by
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> decide

theorem positiveRootPacket_commutator_0_3 :
    automorphismCommutator (positiveRootPacket 0) (positiveRootPacket 3) =
      positiveRootPacket 5 := by
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> decide

theorem positiveRootPacket_commutator_1_3 :
    automorphismCommutator (positiveRootPacket 1) (positiveRootPacket 3) =
      positiveRootPacket 4 := by
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> decide

theorem positiveRootPacket_commutator_2_4 :
    automorphismCommutator (positiveRootPacket 2) (positiveRootPacket 4) =
      positiveRootPacket 1 := by
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> decide

theorem positiveRootPacket_commutator_2_5 :
    automorphismCommutator (positiveRootPacket 2) (positiveRootPacket 5) =
      positiveRootPacket 0 := by
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> decide

theorem positiveRootPacket_commutator_4_5 :
    automorphismCommutator (positiveRootPacket 4) (positiveRootPacket 5) =
      positiveRootPacket 3 := by
  apply automorphism_ext_of_basis
  intro i
  fin_cases i <;> decide

/-! Conjugated derived-root candidates.  These are genuine automorphisms, but
their independence from the preceding packet is deliberately not asserted. -/

noncomputable def uMidCycle : SplitOctF2Aut :=
  conjugateAut cycle012Aut uMid

noncomputable def uMidCycleSq : SplitOctF2Aut :=
  conjugateAut (cycle012Aut * cycle012Aut) uMid

noncomputable def uMidOrbit : Fin 3 → SplitOctF2Aut
  | 0 => uMid
  | 1 => uMidCycle
  | 2 => uMidCycleSq

theorem uMidOrbit_injective :
    Function.Injective uMidOrbit := by
  intro i j h
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals
    have h0 := congrArg (fun f : SplitOctF2Aut => f.1 up0) h
    have h1 := congrArg (fun f : SplitOctF2Aut => f.1 up1) h
    have h2 := congrArg (fun f : SplitOctF2Aut => f.1 up2) h
    revert h0 h1 h2
    decide

theorem uMidCycle_sq : uMidCycle * uMidCycle = 1 := by
  exact conjugateAut_sq cycle012Aut uMid uMid_sq

theorem uMidCycleSq_sq : uMidCycleSq * uMidCycleSq = 1 := by
  exact conjugateAut_sq (cycle012Aut * cycle012Aut) uMid uMid_sq

theorem uMidOrbit_zero_one_noncommuting :
    uMidOrbit 0 * uMidOrbit 1 ≠ uMidOrbit 1 * uMidOrbit 0 := by
  intro h
  have h0 := congrArg (fun f : SplitOctF2Aut => f.1 (basis8 4)) h
  have h1 := congrArg (fun f : SplitOctF2Aut => f.1 (basis8 6)) h
  revert h0 h1
  decide

theorem uMidCycle_ne_one : uMidCycle ≠ (1 : SplitOctF2Aut) := by
  exact conjugateAut_ne_one cycle012Aut uMid uMid_ne_one

theorem uMidCycleSq_ne_one : uMidCycleSq ≠ (1 : SplitOctF2Aut) := by
  exact conjugateAut_ne_one (cycle012Aut * cycle012Aut) uMid uMid_ne_one

/-!
=============================================================================
PART 4: Ordered 3-Root Unipotent Words and Exact Injectivity
=============================================================================
-/

/-- The 8 ordered unipotent words from the 3 root elements uShort, uLong, uMid -/
def unipotentWord3 (b : Bool × Bool × Bool) : SplitOctF2Aut :=
  (if b.1 then uShort else 1) *
  (if b.2.1 then uLong else 1) *
  (if b.2.2 then uMid else 1)

theorem unipotentWord3_b1 (b : Bool × Bool × Bool) :
    ((unipotentWord3 b).1 up1).x0 = b.1 := by
  rcases b with ⟨b1, b2, b3⟩
  fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;> rfl

theorem unipotentWord3_b2 (b : Bool × Bool × Bool) :
    ((unipotentWord3 b).1 up2).x1 = b.2.1 := by
  rcases b with ⟨b1, b2, b3⟩
  fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;> rfl

theorem unipotentWord3_b3 (b : Bool × Bool × Bool) :
    ((unipotentWord3 b).1 up2).x0 = b.2.2 := by
  rcases b with ⟨b1, b2, b3⟩
  fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;> rfl

/-- 🏆 THEOREM: The 8 unipotent words formed by uShort, uLong, uMid are strictly distinct! -/
theorem unipotentWord3_injective : Function.Injective unipotentWord3 := by
  intro b c h
  have h1 : ((unipotentWord3 b).1 up1).x0 = ((unipotentWord3 c).1 up1).x0 := by rw [h]
  rw [unipotentWord3_b1 b, unipotentWord3_b1 c] at h1
  have h2 : ((unipotentWord3 b).1 up2).x1 = ((unipotentWord3 c).1 up2).x1 := by rw [h]
  rw [unipotentWord3_b2 b, unipotentWord3_b2 c] at h2
  have h3 : ((unipotentWord3 b).1 up2).x0 = ((unipotentWord3 c).1 up2).x0 := by rw [h]
  rw [unipotentWord3_b3 b, unipotentWord3_b3 c] at h3
  rcases b with ⟨b1, b2, b3⟩
  rcases c with ⟨c1, c2, c3⟩
  dsimp at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem unipotentWord3_mem_positiveRootSubgroup
    (b : Bool × Bool × Bool) :
    unipotentWord3 b ∈ positiveRootSubgroup := by
  have hs : (if b.1 then uShort else 1) ∈ positiveRootSubgroup := by
    by_cases h : b.1 <;> simp [h]
    exact positiveRootPacket_mem_subgroup 0
  have hl : (if b.2.1 then uLong else 1) ∈ positiveRootSubgroup := by
    by_cases h : b.2.1 <;> simp [h]
    exact positiveRootPacket_mem_subgroup 1
  have hm : (if b.2.2 then uMid else 1) ∈ positiveRootSubgroup := by
    by_cases h : b.2.2 <;> simp [h]
    exact positiveRootPacket_mem_subgroup 2
  exact positiveRootSubgroup.mul_mem
    (positiveRootSubgroup.mul_mem hs hl) hm

theorem positiveRootSubgroup_card_lower_bound :
    8 ≤ Fintype.card positiveRootSubgroup := by
  let f : Bool × Bool × Bool → positiveRootSubgroup :=
    fun b => ⟨unipotentWord3 b, unipotentWord3_mem_positiveRootSubgroup b⟩
  have hf : Function.Injective f := by
    intro b c h
    exact unipotentWord3_injective (Subtype.ext_iff.mp h)
  have hc := Fintype.card_le_of_injective f hf
  simpa using hc

theorem simpleRootSubgroup_le_positiveRootSubgroup :
    simpleRootSubgroup ≤ positiveRootSubgroup := by
  apply Subgroup.closure_mono
  intro g hg
  rcases hg with rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

theorem uMidOrbit_mem_positiveRootSubgroup (i : Fin 3) :
    uMidOrbit i ∈ positiveRootSubgroup := by
  fin_cases i
  · exact positiveRootPacket_mem_subgroup 2
  · exact positiveRootPacket_mem_subgroup 4
  · exact positiveRootPacket_mem_subgroup 5
noncomputable def unipotentWord6 (b : Fin 6 → Bool) : SplitOctF2Aut :=
  positiveRootAction 0 (b 0) *
  positiveRootAction 1 (b 1) *
  positiveRootAction 2 (b 2) *
  positiveRootAction 3 (b 3) *
  positiveRootAction 4 (b 4) *
  positiveRootAction 5 (b 5)

theorem positiveRootAction_mem_positiveRootSubgroup (i : Fin 6) (t : Bool) :
    positiveRootAction i t ∈ positiveRootSubgroup := by
  cases t
  · simp [positiveRootAction]
  · simp [positiveRootAction, positiveRootPacket_mem_subgroup i]

theorem unipotentWord6_mem_positiveRootSubgroup (b : Fin 6 → Bool) :
    unipotentWord6 b ∈ positiveRootSubgroup := by
  dsimp [unipotentWord6]
  exact positiveRootSubgroup.mul_mem
    (positiveRootSubgroup.mul_mem
      (positiveRootSubgroup.mul_mem
        (positiveRootSubgroup.mul_mem
          (positiveRootSubgroup.mul_mem
            (positiveRootAction_mem_positiveRootSubgroup 0 (b 0))
            (positiveRootAction_mem_positiveRootSubgroup 1 (b 1)))
          (positiveRootAction_mem_positiveRootSubgroup 2 (b 2)))
        (positiveRootAction_mem_positiveRootSubgroup 3 (b 3)))
      (positiveRootAction_mem_positiveRootSubgroup 4 (b 4)))
    (positiveRootAction_mem_positiveRootSubgroup 5 (b 5))

theorem unipotentWord6_injective_of_coordinate_separators
    (h0 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 up1).x0 = b 0)
    (h1 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 down1).y2 = b 1)
    (h2 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 up2).x0 = b 2)
    (h3 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 down2).y0 = b 3)
    (h4 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 up0).x1 = b 4)
    (h5 : ∀ b : Fin 6 → Bool, ((unipotentWord6 b).1 down2).y1 = b 5) :
    Function.Injective unipotentWord6 := by
  intro b c h
  funext i
  fin_cases i
  · have q := congrArg (fun f : SplitOctF2Aut => (f.1 up1).x0) h
    simpa [h0 b, h0 c] using q
  · have q := congrArg (fun f : SplitOctF2Aut => (f.1 down1).y2) h
    simpa [h1 b, h1 c] using q
  · have q := congrArg (fun f : SplitOctF2Aut => (f.1 up2).x0) h
    simpa [h2 b, h2 c] using q
  · have q := congrArg (fun f : SplitOctF2Aut => (f.1 down2).y0) h
    simpa [h3 b, h3 c] using q
  · have q := congrArg (fun f : SplitOctF2Aut => (f.1 up0).x1) h
    simpa [h4 b, h4 c] using q
  · have q := congrArg (fun f : SplitOctF2Aut => (f.1 down2).y1) h
    simpa [h5 b, h5 c] using q


theorem unipotentWord6_b0 (b : Fin 6 → Bool) :
    ((unipotentWord6 b).1 up1).x0 = b 0 := by
  revert b
  decide

theorem unipotentWord6_b1 (b : Fin 6 → Bool) :
    ((unipotentWord6 b).1 down1).y2 = b 1 := by
  revert b
  decide

theorem unipotentWord6_b2 (b : Fin 6 → Bool) :
    ((unipotentWord6 b).1 up2).x0 = b 2 := by
  revert b
  decide

theorem unipotentWord6_b3 (b : Fin 6 → Bool) :
    ((unipotentWord6 b).1 down2).y0 = b 3 := by
  revert b
  decide

theorem unipotentWord6_b4 (b : Fin 6 → Bool) :
    ((unipotentWord6 b).1 up0).x1 = b 4 := by
  revert b
  decide

theorem unipotentWord6_b5 (b : Fin 6 → Bool) :
    ((unipotentWord6 b).1 down2).y1 = b 5 := by
  revert b
  decide

theorem unipotentWord6_injective : Function.Injective unipotentWord6 := by
  exact unipotentWord6_injective_of_coordinate_separators
    unipotentWord6_b0 unipotentWord6_b1 unipotentWord6_b2
    unipotentWord6_b3 unipotentWord6_b4 unipotentWord6_b5

end InfoGeometry.Algebra.Zorn.G2SteinbergRoots
