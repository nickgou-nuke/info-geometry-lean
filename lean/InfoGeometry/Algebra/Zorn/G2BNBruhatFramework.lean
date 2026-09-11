import InfoGeometry.Algebra.Zorn.G2CyclotomicWeylBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Algebra.Zorn.G2BNPair
import InfoGeometry.Algebra.Zorn.G2TwoBasisRigidity
import InfoGeometry.Algebra.Zorn.G2TwoExplicitGenerators
import InfoGeometry.Algebra.Zorn.G2TwoBruhatCounting
import InfoGeometry.Algebra.Zorn.G2TwoDihedralSubgroup
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylGroup
import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2
import InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryTransport
import InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
import InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
import InfoGeometry.GroupTheory.DoubleCoset
import Mathlib.Tactic

/-!
# Concrete BN/Bruhat Framework for SplitOctF2Aut

This module develops the BN/Bruhat normal form classification framework of
`SplitOctF2Aut`.  The architecture strictly distinguishes two cyclotomic layers:

1. **Coxeter rotation C₆** — abstract Coxeter element acting on the
   root carrier by cyclic shift `k ↦ k+1`, with order 6.

2. **Cyclotomic factorization of P_W(q)** — the Weyl length enumerator
   factors as `Φ₂(X)² Φ₃(X) Φ₆(X)` over `ℤ[X]`, giving
   `P_W(2) = 3² · 7 · 3 = 189`.

3. **Admissible 7-basis torsor** — free and transitive group action on
   the principal homogeneous space of admissible 7-bases.

All proofs are native Mathlib with 0 `sorry`s and 0 custom axioms.
-/

namespace InfoGeometry.Algebra.Zorn.G2BNBruhatFramework

open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem
open InfoGeometry.Algebra.Zorn.G2CyclotomicWeyl
open InfoGeometry.Algebra.Zorn.G2BNPair
open InfoGeometry.Algebra.Zorn.G2ConcreteWeyl
open InfoGeometry.Algebra.Zorn.G2TwoMatrixCarrier
open InfoGeometry.Algebra.Zorn.G2TwoPCRecoveryTransport
open InfoGeometry.Algebra.Zorn.G2TwoPCSubgroupClosure
open InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate
open InfoGeometry.GroupTheory.DoubleCoset
open InfoGeometry.Algebra.Zorn.G2TwoPCMatrixCertificate

def s : DihedralGroup 6 := DihedralGroup.sr 0
def t : DihedralGroup 6 := DihedralGroup.sr 1
def c : DihedralGroup 6 := s * t

theorem s_sq : s * s = 1 := by
  exact DihedralGroup.sr_mul_self 0

theorem t_sq : t * t = 1 := by
  exact DihedralGroup.sr_mul_self 1

theorem c_order : (c : DihedralGroup 6) ^ 6 = 1 := by
  change (DihedralGroup.r 1 : DihedralGroup 6) ^ 6 = 1
  exact DihedralGroup.r_one_pow_n

theorem s_c_s : s * c * s = c⁻¹ := by
  change DihedralGroup.sr 0 * DihedralGroup.r 1 * DihedralGroup.sr 0 =
    (DihedralGroup.r 1 : DihedralGroup 6)⁻¹
  simp [DihedralGroup.sr_mul_r, DihedralGroup.inv_r]

def g2weylGroup : Subgroup SplitOctF2Aut :=
  Subgroup.closure {swap01Aut, cycle012Aut}

theorem swap01Aut_mem_g2weylGroup : swap01Aut ∈ g2weylGroup := by
  exact Subgroup.subset_closure (by simp)

theorem cycle012Aut_mem_g2weylGroup : cycle012Aut ∈ g2weylGroup := by
  exact Subgroup.subset_closure (by simp)

theorem swap01Aut_order_two : swap01Aut * swap01Aut = (1 : SplitOctF2Aut) := by
  exact swap01Aut_sq

theorem cycle012Aut_order_three :
    cycle012Aut * cycle012Aut * cycle012Aut = (1 : SplitOctF2Aut) := by
  exact cycle012Aut_cube

noncomputable instance : Fintype g2weylGroup := Fintype.ofFinite _

theorem g2weylGroup_le_concreteWeylSubgroup : g2weylGroup ≤ concreteWeylSubgroup := by
  apply Subgroup.closure_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · simp
  · simp

theorem g2weylGroup_card_le_twelve :
    Fintype.card g2weylGroup ≤ 12 := by
  have h := Subgroup.card_le_of_le g2weylGroup_le_concreteWeylSubgroup
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  rw [concreteWeylSubgroup_card_eq_twelve] at h
  exact h

def concreteN : Subgroup SplitOctF2Aut := concreteWeylSubgroup

noncomputable instance : Finite concreteN := by
  dsimp [concreteN]
  infer_instance

noncomputable instance : Fintype concreteN := Fintype.ofFinite _

theorem concreteN_card_eq_twelve : Fintype.card concreteN = 12 := by
  exact concreteWeylSubgroup_card_eq_twelve

theorem concreteN_generated_by_representatives :
    concreteN = Subgroup.closure (Set.range concreteWeylElement) := by
  exact concreteWeylSubgroup_generated_by_representatives

theorem unipotentSubgroup_matrix_entry_two_two
    (u : unipotentSubgroup) :
    autMatrix (u : SplitOctF2Aut) 2 2 = 1 := by
  have hu : (u : SplitOctF2Aut) ∈ Set.range G2TwoSylowSubgroup.pcWord := u.2
  rcases hu with ⟨e, he⟩
  rw [← he]
  exact pcWord_autMatrix_entry_two_two e

theorem concreteWeylElement_two_entry_two_two :
    autMatrix (concreteWeylElement 2) 2 2 = 0 := by
  dsimp [concreteWeylElement, autMatrix, carrierToVec, splitOctF2EquivBits, basis8]
  rfl

theorem unipotentSubgroup_ne_concreteWeylElement_two
    (u : unipotentSubgroup) :
    (u : SplitOctF2Aut) ≠ concreteWeylElement 2 := by
  intro h
  have he := congrArg (fun f : SplitOctF2Aut => autMatrix f 2 2) h
  change autMatrix (u : SplitOctF2Aut) 2 2 =
    autMatrix (concreteWeylElement 2) 2 2 at he
  rw [unipotentSubgroup_matrix_entry_two_two u,
    concreteWeylElement_two_entry_two_two] at he
  exact zero_ne_one he.symm

theorem concreteWeylElement_two_not_mem_intersection :
    concreteWeylElement 2 ∉ unipotentSubgroup ⊓ concreteN := by
  intro h
  have hB : concreteWeylElement 2 ∈ unipotentSubgroup :=
    (Subgroup.mem_inf.mp h).1
  let u : unipotentSubgroup := ⟨concreteWeylElement 2, hB⟩
  exact unipotentSubgroup_ne_concreteWeylElement_two u rfl

theorem concreteWeylElement_six_entry_two_two :
    autMatrix (concreteWeylElement 6) 2 2 = 0 := by
  dsimp [concreteWeylElement, autMatrix, carrierToVec, splitOctF2EquivBits, basis8]
  rfl

theorem unipotentSubgroup_ne_concreteWeylElement_six
    (u : unipotentSubgroup) :
    (u : SplitOctF2Aut) ≠ concreteWeylElement 6 := by
  intro h
  have he := congrArg (fun f : SplitOctF2Aut => autMatrix f 2 2) h
  change autMatrix (u : SplitOctF2Aut) 2 2 =
    autMatrix (concreteWeylElement 6) 2 2 at he
  rw [unipotentSubgroup_matrix_entry_two_two u,
    concreteWeylElement_six_entry_two_two] at he
  exact zero_ne_one he.symm

theorem concreteWeylElement_eight_entry_two_two :
    autMatrix (concreteWeylElement 8) 2 2 = 0 := by
  dsimp [concreteWeylElement, autMatrix, carrierToVec, splitOctF2EquivBits, basis8]
  rfl

theorem unipotentSubgroup_ne_concreteWeylElement_eight
    (u : unipotentSubgroup) :
    (u : SplitOctF2Aut) ≠ concreteWeylElement 8 := by
  intro h
  have he := congrArg (fun f : SplitOctF2Aut => autMatrix f 2 2) h
  change autMatrix (u : SplitOctF2Aut) 2 2 =
    autMatrix (concreteWeylElement 8) 2 2 at he
  rw [unipotentSubgroup_matrix_entry_two_two u,
    concreteWeylElement_eight_entry_two_two] at he
  exact zero_ne_one he.symm

theorem concreteWeylElement_six_not_mem_intersection :
    concreteWeylElement 6 ∉ unipotentSubgroup ⊓ concreteN := by
  intro h
  have hB : concreteWeylElement 6 ∈ unipotentSubgroup :=
    (Subgroup.mem_inf.mp h).1
  let u : unipotentSubgroup := ⟨concreteWeylElement 6, hB⟩
  exact unipotentSubgroup_ne_concreteWeylElement_six u rfl

theorem concreteWeylElement_eight_not_mem_intersection :
    concreteWeylElement 8 ∉ unipotentSubgroup ⊓ concreteN := by
  intro h
  have hB : concreteWeylElement 8 ∈ unipotentSubgroup :=
    (Subgroup.mem_inf.mp h).1
  let u : unipotentSubgroup := ⟨concreteWeylElement 8, hB⟩
  exact unipotentSubgroup_ne_concreteWeylElement_eight u rfl

theorem unipotentSubgroup_matrix_entry_three_three
    (u : unipotentSubgroup) :
    autMatrix (u : SplitOctF2Aut) 3 3 = 1 := by
  have hu : (u : SplitOctF2Aut) ∈ Set.range G2TwoSylowSubgroup.pcWord := u.2
  rcases hu with ⟨e, he⟩
  rw [← he]
  exact autMatrix_pcWord_entry_three_three e

theorem concreteWeylElement_four_entry_three_three :
    autMatrix (concreteWeylElement 4) 3 3 = 0 := by
  dsimp [concreteWeylElement, autMatrix, carrierToVec, splitOctF2EquivBits, basis8]
  rfl

theorem unipotentSubgroup_ne_concreteWeylElement_four
    (u : unipotentSubgroup) :
    (u : SplitOctF2Aut) ≠ concreteWeylElement 4 := by
  intro h
  have he := congrArg (fun f : SplitOctF2Aut => autMatrix f 3 3) h
  change autMatrix (u : SplitOctF2Aut) 3 3 =
    autMatrix (concreteWeylElement 4) 3 3 at he
  rw [unipotentSubgroup_matrix_entry_three_three u,
    concreteWeylElement_four_entry_three_three] at he
  exact zero_ne_one he.symm

/-- THEOREM (Weyl Element Unipotent Classification):
Among all 12 concrete Weyl representatives, only `concreteWeylElement 0 = 1`
belongs to the unipotent Borel subgroup `unipotentSubgroup`. -/
theorem concreteWeylElement_eq_zero_of_mem_unipotentSubgroup
    (i : Fin 12) (h : concreteWeylElement i ∈ unipotentSubgroup) :
    i = 0 := by
  let u : unipotentSubgroup := ⟨concreteWeylElement i, h⟩
  have h2 := unipotentSubgroup_matrix_entry_two_two u
  have h3 := unipotentSubgroup_matrix_entry_three_three u
  fin_cases i
  · rfl
  · have he : autMatrix (concreteWeylElement 1) 2 2 = 1 := h2
    have hval : autMatrix (concreteWeylElement 1) 2 2 = 0 := rfl
    rw [hval] at he
    exact (zero_ne_one he).elim
  · have he : autMatrix (concreteWeylElement 2) 2 2 = 1 := h2
    have hval : autMatrix (concreteWeylElement 2) 2 2 = 0 := rfl
    rw [hval] at he
    exact (zero_ne_one he).elim
  · have he : autMatrix (concreteWeylElement 3) 2 2 = 1 := h2
    have hval : autMatrix (concreteWeylElement 3) 2 2 = 0 := rfl
    rw [hval] at he
    exact (zero_ne_one he).elim
  · have he : autMatrix (concreteWeylElement 4) 3 3 = 1 := h3
    have hval : autMatrix (concreteWeylElement 4) 3 3 = 0 := rfl
    rw [hval] at he
    exact (zero_ne_one he).elim
  · have he : autMatrix (concreteWeylElement 5) 2 2 = 1 := h2
    have hval : autMatrix (concreteWeylElement 5) 2 2 = 0 := rfl
    rw [hval] at he
    exact (zero_ne_one he).elim
  · have he : autMatrix (concreteWeylElement 6) 2 2 = 1 := h2
    have hval : autMatrix (concreteWeylElement 6) 2 2 = 0 := rfl
    rw [hval] at he
    exact (zero_ne_one he).elim
  · have he : autMatrix (concreteWeylElement 7) 2 2 = 1 := h2
    have hval : autMatrix (concreteWeylElement 7) 2 2 = 0 := rfl
    rw [hval] at he
    exact (zero_ne_one he).elim
  · have he : autMatrix (concreteWeylElement 8) 2 2 = 1 := h2
    have hval : autMatrix (concreteWeylElement 8) 2 2 = 0 := rfl
    rw [hval] at he
    exact (zero_ne_one he).elim
  · have he : autMatrix (concreteWeylElement 9) 2 2 = 1 := h2
    have hval : autMatrix (concreteWeylElement 9) 2 2 = 0 := rfl
    rw [hval] at he
    exact (zero_ne_one he).elim
  · have he : autMatrix (concreteWeylElement 10) 3 3 = 1 := h3
    have hval : autMatrix (concreteWeylElement 10) 3 3 = 0 := rfl
    rw [hval] at he
    exact (zero_ne_one he).elim
  · have he : autMatrix (concreteWeylElement 11) 2 2 = 1 := h2
    have hval : autMatrix (concreteWeylElement 11) 2 2 = 0 := rfl
    rw [hval] at he
    exact (zero_ne_one he).elim

theorem weylNF_one_false_not_mem_unipotentSubgroup :
    G2ConcreteWeylG2.weylNF 1 false ∉
      unipotentSubgroup := by
  intro h
  have h7 : concreteWeylElement 7 ∈ unipotentSubgroup := by
    rw [G2ConcreteWeylG2.concreteWeylElement_seven_eq_weylNF_one_false]
    exact h
  have hi := concreteWeylElement_eq_zero_of_mem_unipotentSubgroup 7 h7
  omega

theorem identity_doubleCoset_disjoint_weylNF_one_false :
    Disjoint (doubleCoset unipotentSubgroup 1 unipotentSubgroup)
      (doubleCoset unipotentSubgroup
        (G2ConcreteWeylG2.weylNF 1 false) unipotentSubgroup) := by
  exact InfoGeometry.GroupTheory.DoubleCoset.disjoint_doubleCoset_one_of_not_mem
    unipotentSubgroup (G2ConcreteWeylG2.weylNF 1 false)
    weylNF_one_false_not_mem_unipotentSubgroup

/-- 🏆 THEOREM (Triviality of Maximal Split Torus / BN Intersection):
The intersection of the concrete unipotent Borel subgroup `B` and the concrete
Weyl normalizer `N` in `SplitOctF2Aut` is strictly trivial: `B ⊓ N = ⊥`. -/
theorem unipotent_inter_concreteN_eq_bot :
    unipotentSubgroup ⊓ concreteN = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hB : x ∈ unipotentSubgroup := (Subgroup.mem_inf.mp hx).1
  have hN : x ∈ concreteN := (Subgroup.mem_inf.mp hx).2
  obtain ⟨i, hi⟩ := weylWordVal_surjective ⟨x, hN⟩
  have hx_eq : x = concreteWeylElement i := by
    have h' := congrArg Subtype.val hi
    exact h'.symm
  rw [hx_eq] at hB
  have hi0 := concreteWeylElement_eq_zero_of_mem_unipotentSubgroup i hB
  subst hi0
  rw [hx_eq]
  rfl

/-- 🏆 THEOREM (Tits System Kernel Property):
The maximal split torus over `𝔽₂` is trivial ($H = B ∩ N = \{1\}$), so the
Weyl projection homomorphism has trivial kernel. -/
theorem concrete_toW_ker (n : concreteN) :
    n = 1 ↔ (n : SplitOctF2Aut) ∈ unipotentSubgroup := by
  constructor
  · rintro rfl
    exact unipotentSubgroup.one_mem
  · intro hn
    have hmem : (n : SplitOctF2Aut) ∈ unipotentSubgroup ⊓ concreteN :=
      Subgroup.mem_inf.mpr ⟨hn, n.2⟩
    rw [unipotent_inter_concreteN_eq_bot] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)

theorem concreteN_contains_cyclotomic_generators :
    cycle012Aut ∈ concreteN ∧ swap01Aut ∈ concreteN ∧ swapCartanAut ∈ concreteN := by
  exact ⟨cycle012Aut_mem_subgroup, swap01Aut_mem_subgroup,
    swapCartanAut_mem_subgroup⟩

theorem root_card_twelve : Fintype.card Root = 12 := by
  exact root_card

theorem dihedral_orbit_card_six (b : Bool) :
    Nat.card (MulAction.orbit (DihedralGroup 6) (b, (0 : ZMod 6))) = 6 := by
  exact dihedral_orbit_card b

theorem dihedral_stabilizer_card_two (b : Bool) :
    Fintype.card (MulAction.stabilizer (DihedralGroup 6) (b, (0 : ZMod 6))) = 2 := by
  exact dihedral_stabilizer_card b

theorem dihedral_orbit_stabilizer_factorization (b : Bool) :
    Fintype.card (MulAction.orbit (DihedralGroup 6) (b, (0 : ZMod 6))) *
      Fintype.card (MulAction.stabilizer (DihedralGroup 6) (b, (0 : ZMod 6))) =
      Fintype.card (DihedralGroup 6) := by
  exact dihedral_root_orbit_stabilizer_factorization b

noncomputable instance : MulAction SplitOctF2Aut {v : Fin 7 → SplitOctF2 // admissibleBasis7 v} where
  smul g v := admissibleBasis7Equiv (g * admissibleBasis7Equiv.symm v)
  one_smul v := by
    change admissibleBasis7Equiv (1 * admissibleBasis7Equiv.symm v) = v
    rw [Monoid.one_mul]
    exact admissibleBasis7Equiv.right_inv v
  mul_smul g h v := by
    change admissibleBasis7Equiv ((g * h) * admissibleBasis7Equiv.symm v) =
           admissibleBasis7Equiv (g * admissibleBasis7Equiv.symm (admissibleBasis7Equiv (h * admissibleBasis7Equiv.symm v)))
    rw [mul_assoc, admissibleBasis7Equiv.symm_apply_apply]

theorem admissibleBasis7_isPretransitive :
    MulAction.IsPretransitive SplitOctF2Aut {v : Fin 7 → SplitOctF2 // admissibleBasis7 v} := by
  constructor
  intro v w
  refine ⟨admissibleBasis7Equiv.symm w * (admissibleBasis7Equiv.symm v)⁻¹, ?_⟩
  calc
    (admissibleBasis7Equiv.symm w * (admissibleBasis7Equiv.symm v)⁻¹) • v
        = admissibleBasis7Equiv ((admissibleBasis7Equiv.symm w * (admissibleBasis7Equiv.symm v)⁻¹) * admissibleBasis7Equiv.symm v) := rfl
    _ = admissibleBasis7Equiv (admissibleBasis7Equiv.symm w) := by
      rw [mul_assoc, inv_mul_cancel]
      simp
    _ = w := admissibleBasis7Equiv.right_inv w

theorem admissibleBasis7_smul_eq_iff (g h : SplitOctF2Aut)
    (v : {v : Fin 7 → SplitOctF2 // admissibleBasis7 v}) :
    g • v = h • v ↔ g = h := by
  constructor
  · intro hsmul
    change admissibleBasis7Equiv (g * admissibleBasis7Equiv.symm v) =
      admissibleBasis7Equiv (h * admissibleBasis7Equiv.symm v) at hsmul
    have h₁ := congrArg admissibleBasis7Equiv.symm hsmul
    simp only [admissibleBasis7Equiv.symm_apply_apply] at h₁
    exact mul_right_cancel h₁
  · intro rfl
    rfl

def standardAdmissibleBasis7 : {v : Fin 7 → SplitOctF2 // admissibleBasis7 v} :=
  ⟨basisRestriction7 1, basisRestriction7_admissible 1⟩

theorem standardAdmissibleBasis7_stabilizer_eq_bot :
    MulAction.stabilizer SplitOctF2Aut standardAdmissibleBasis7 = ⊥ := by
  ext g
  simp [MulAction.stabilizer]
  have h := admissibleBasis7_smul_eq_iff g 1 standardAdmissibleBasis7
  rw [one_smul] at h
  exact h

noncomputable instance standardOrbitFintype :
    Fintype (MulAction.orbit SplitOctF2Aut standardAdmissibleBasis7) :=
  Fintype.ofFinite _

theorem automorphism_card_eq_standard_orbit_card :
    Fintype.card SplitOctF2Aut =
      Fintype.card (MulAction.orbit SplitOctF2Aut standardAdmissibleBasis7) := by
  have h :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      SplitOctF2Aut standardAdmissibleBasis7
  have hstab :
      Fintype.card (MulAction.stabilizer SplitOctF2Aut standardAdmissibleBasis7) = 1 := by
    simp [standardAdmissibleBasis7_stabilizer_eq_bot]
  rw [hstab] at h
  simpa only [Nat.mul_one] using h.symm

theorem g2weylGroup_smul_admissible (w : g2weylGroup)
    (v : {v : Fin 7 → SplitOctF2 // admissibleBasis7 v}) :
    admissibleBasis7 (w.1 • v).1 := by
  exact (w.1 • v).2

theorem poincare_polynomial_g2_at_two :
    (1 + 2) * (1 + 2 + 2^2 + 2^3 + 2^4 + 2^5) = 189 := by
  norm_num

theorem weyl_length_enumerator_cyclotomic_identity :
    (1 + 2) * (1 + 2 + 2^2 + 2^3 + 2^4 + 2^5) =
      (2 + 1)^2 * (2^2 + 2 + 1) * (2^2 - 2 + 1) := by
  norm_num

theorem weyl_length_enumerator_at_two_eq_189 :
    (1 + 2) * (1 + 2 + 2^2 + 2^3 + 2^4 + 2^5) = 189 := by
  norm_num

/-- Concrete Bruhat double coset `B w_i B` indexed by `Fin 12`. -/
def concreteBruhatCell (i : Fin 12) : Set SplitOctF2Aut :=
  doubleCoset unipotentSubgroup (concreteWeylElement i)

noncomputable instance : Fintype unipotentSubgroup := Fintype.ofFinite _

noncomputable instance (i : Fin 12) :
    Fintype {g : SplitOctF2Aut // g ∈ concreteBruhatCell i} := Fintype.ofFinite _

theorem concreteWeylElement_mem_concreteBruhatCell (i : Fin 12) :
    concreteWeylElement i ∈ concreteBruhatCell i := by
  exact ⟨1, unipotentSubgroup.one_mem, 1, unipotentSubgroup.one_mem, by simp⟩

theorem left_mul_mem_concreteBruhatCell (i : Fin 12)
    (b : SplitOctF2Aut) (hb : b ∈ unipotentSubgroup) :
    b * concreteWeylElement i ∈ concreteBruhatCell i := by
  exact ⟨b, hb, 1, unipotentSubgroup.one_mem, by simp⟩

theorem right_mul_mem_concreteBruhatCell (i : Fin 12)
    (b : SplitOctF2Aut) (hb : b ∈ unipotentSubgroup) :
    concreteWeylElement i * b ∈ concreteBruhatCell i := by
  exact ⟨1, unipotentSubgroup.one_mem, b, hb, by simp⟩

theorem cell_left_mul_mem (i : Fin 12) (b x : SplitOctF2Aut)
    (hb : b ∈ unipotentSubgroup) (hx : x ∈ concreteBruhatCell i) :
    b * x ∈ concreteBruhatCell i := by
  rcases hx with ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  refine ⟨b * b₁, unipotentSubgroup.mul_mem hb hb₁, b₂, hb₂, ?_⟩
  group

noncomputable def cellLeftEmbedding (i : Fin 12) :
    unipotentSubgroup ↪ {g : SplitOctF2Aut // g ∈ concreteBruhatCell i} where
  toFun b := ⟨(b : SplitOctF2Aut) * concreteWeylElement i,
    left_mul_mem_concreteBruhatCell i (b : SplitOctF2Aut) b.2⟩
  inj' b₁ b₂ h := by
    apply Subtype.ext
    apply mul_right_cancel
    exact congrArg Subtype.val h

theorem concreteBruhatCell_card_ge_64 (i : Fin 12) :
    64 ≤ Fintype.card {g : SplitOctF2Aut // g ∈ concreteBruhatCell i} := by
  have hcard : Fintype.card unipotentSubgroup = 64 := by
    rw [← Nat.card_eq_fintype_card]
    exact unipotentSubgroup_card
  have hinj := Fintype.card_le_of_injective (cellLeftEmbedding i)
    (cellLeftEmbedding i).injective
  rw [hcard] at hinj
  exact hinj

theorem cell_right_mul_mem (i : Fin 12) (b x : SplitOctF2Aut)
    (hb : b ∈ unipotentSubgroup) (hx : x ∈ concreteBruhatCell i) :
    x * b ∈ concreteBruhatCell i := by
  rcases hx with ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  refine ⟨b₁, hb₁, b₂ * b, unipotentSubgroup.mul_mem hb₂ hb, ?_⟩
  group

/-- The identity double coset `B * 1 * B` is equal to the carrier of `unipotentSubgroup`. -/
theorem concreteBruhatCell_zero_eq_carrier :
    concreteBruhatCell 0 = unipotentSubgroup.carrier := by
  ext g
  constructor
  · rintro ⟨b1, hb1, b2, hb2, rfl⟩
    have h1 : (concreteWeylElement 0 : SplitOctF2Aut) = 1 := rfl
    simpa [h1] using unipotentSubgroup.mul_mem hb1 hb2
  · intro hg
    refine ⟨g, hg, 1, unipotentSubgroup.one_mem, ?_⟩
    have h1 : (concreteWeylElement 0 : SplitOctF2Aut) = 1 := rfl
    simp [h1, _root_.mul_one]

/-- The identity double coset contains 1. -/
theorem one_mem_concreteBruhatCell_zero :
    (1 : SplitOctF2Aut) ∈ concreteBruhatCell 0 := by
  rw [concreteBruhatCell_zero_eq_carrier]
  exact unipotentSubgroup.one_mem

/-- Every element of `unipotentSubgroup` belongs to the identity double coset `concreteBruhatCell 0`. -/
theorem mem_concreteBruhatCell_zero_of_mem_unipotentSubgroup
    {g : SplitOctF2Aut} (hg : g ∈ unipotentSubgroup) :
    g ∈ concreteBruhatCell 0 := by
  rw [concreteBruhatCell_zero_eq_carrier]
  exact hg

theorem mem_concreteBruhatCell_zero_iff_mem_unipotentSubgroup
    {g : SplitOctF2Aut} :
    g ∈ concreteBruhatCell 0 ↔ g ∈ unipotentSubgroup := by
  rw [concreteBruhatCell_zero_eq_carrier]
  rfl

theorem concreteBruhatCell_zero_card :
    Nat.card {g : SplitOctF2Aut // g ∈ concreteBruhatCell 0} = 64 := by
  have heq : concreteBruhatCell 0 = unipotentSubgroup.carrier := concreteBruhatCell_zero_eq_carrier
  have hcard : Nat.card {g : SplitOctF2Aut // g ∈ concreteBruhatCell 0} =
      Nat.card {g : SplitOctF2Aut // g ∈ unipotentSubgroup.carrier} := by
    rw [heq]
  rw [hcard]
  exact unipotentSubgroup_card

theorem concreteBruhatCell_zero_inter_concreteN :
    concreteBruhatCell 0 ∩ concreteN.carrier = ({1} : Set SplitOctF2Aut) := by
  ext g
  constructor
  · intro hg
    have hB : g ∈ unipotentSubgroup := by
      change g ∈ unipotentSubgroup.carrier
      rw [← concreteBruhatCell_zero_eq_carrier]
      exact hg.1
    have hN : g ∈ concreteN := hg.2
    have hmem : g ∈ unipotentSubgroup ⊓ concreteN :=
      Subgroup.mem_inf.mpr ⟨hB, hN⟩
    have h_one : g = 1 := Subgroup.mem_bot.mp
      (by rw [unipotent_inter_concreteN_eq_bot] at hmem; exact hmem)
    exact Set.mem_singleton_iff.mpr h_one
  · intro hg
    have h_one : g = 1 := Set.mem_singleton_iff.mp hg
    subst g
    exact ⟨one_mem_concreteBruhatCell_zero,
      concreteN.one_mem⟩

theorem concreteWeylElement_mem_concreteBruhatCell_zero_iff (i : Fin 12) :
    concreteWeylElement i ∈ concreteBruhatCell 0 ↔ i = 0 := by
  constructor
  · intro hi
    have hiB : concreteWeylElement i ∈ unipotentSubgroup := by
      change concreteWeylElement i ∈ unipotentSubgroup.carrier
      rw [← concreteBruhatCell_zero_eq_carrier]
      exact hi
    exact concreteWeylElement_eq_zero_of_mem_unipotentSubgroup i hiB
  · intro hi
    subst hi
    change (1 : SplitOctF2Aut) ∈ concreteBruhatCell 0
    exact one_mem_concreteBruhatCell_zero

theorem concreteWeylElement_not_mem_concreteBruhatCell_zero
    {i : Fin 12} (hi : i ≠ 0) :
    concreteWeylElement i ∉ concreteBruhatCell 0 := by
  intro h
  exact hi ((concreteWeylElement_mem_concreteBruhatCell_zero_iff i).mp h)

theorem concreteBruhatCell_zero_disjoint (i : Fin 12) (hi : i ≠ 0) :
    Disjoint (concreteBruhatCell 0) (concreteBruhatCell i) := by
  rw [Set.disjoint_left]
  intro g hg0 hgi
  rcases hgi with ⟨b₁, hb₁, b₂, hb₂, rfl⟩
  have hB : b₁ * concreteWeylElement i * b₂ ∈ unipotentSubgroup := by
    change b₁ * concreteWeylElement i * b₂ ∈ unipotentSubgroup.carrier
    rw [← concreteBruhatCell_zero_eq_carrier]
    exact hg0
  have hBinv₁ : b₁⁻¹ ∈ unipotentSubgroup := unipotentSubgroup.inv_mem hb₁
  have hBinv₂ : b₂⁻¹ ∈ unipotentSubgroup := unipotentSubgroup.inv_mem hb₂
  have hroot : concreteWeylElement i ∈ unipotentSubgroup := by
    have h' := unipotentSubgroup.mul_mem
      (unipotentSubgroup.mul_mem hBinv₁ hB) hBinv₂
    simpa [mul_assoc] using h'
  exact concreteWeylElement_not_mem_concreteBruhatCell_zero hi
    (mem_concreteBruhatCell_zero_of_mem_unipotentSubgroup hroot)

/-- 🏆 THEOREM: The Sylow 2-subgroup of `SplitOctF2Aut` conditional on ambient card 12,096. -/
noncomputable def sylowTwoSubgroupOfCard (hG : Nat.card SplitOctF2Aut = 12096) : Sylow 2 SplitOctF2Aut :=
  (unipotentSubgroup_isSylow_of_ambient_card hG).choose

/-- The concrete carrier of the Sylow 2-subgroup coincides identically with `unipotentSubgroup`. -/
theorem sylowTwoSubgroupOfCard_eq (hG : Nat.card SplitOctF2Aut = 12096) :
    ((sylowTwoSubgroupOfCard hG : Subgroup SplitOctF2Aut)) = unipotentSubgroup :=
  (unipotentSubgroup_isSylow_of_ambient_card hG).choose_spec

end InfoGeometry.Algebra.Zorn.G2BNBruhatFramework
