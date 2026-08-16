import Mathlib.Tactic
import InfoGeometry.Clifford.Clifford55

open CliffordAlgebra

/-!
# Artin-word parity into finite central signs

Finite algebraic facts for:

* braid/Artin monodromy;
* winding around n-fold roots;
* the `{I,-I}` sign subgroup in the Pin(5,5)/O(5,5) layer.

The finite sign group is `{I,-I}`.  An Artin word contributes its winding
parity: odd winding lands on `-I`, and even winding lands on `I`.  The file also
records the corresponding `Pin(5,5)` membership fact for the scalar `-1`.
-/

namespace InfoGeometry.Topology.ArtinCentralizerMonodromy

/-- The finite central sign group `{I,-I}`. -/
inductive CentralSign where
  | I
  | negI
  deriving DecidableEq, Repr

open CentralSign

/-- Multiplication in `{I,-I}`. -/
def cmul : CentralSign → CentralSign → CentralSign
  | I, b => b
  | negI, I => negI
  | negI, negI => I

instance : Mul CentralSign where
  mul := cmul

instance : One CentralSign where
  one := I

instance : Inv CentralSign where
  inv := fun
    | I => I
    | negI => negI

instance : Monoid CentralSign where
  mul := (· * ·)
  one := I
  mul_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> decide
  one_mul := by
    intro a
    cases a <;> decide
  mul_one := by
    intro a
    cases a <;> decide

instance : Group CentralSign where
  mul := (· * ·)
  one := I
  inv := Inv.inv
  mul_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> decide
  one_mul := by
    intro a
    cases a <;> decide
  mul_one := by
    intro a
    cases a <;> decide
  inv_mul_cancel := by
    intro a
    cases a <;> decide

instance : CommGroup CentralSign where
  mul_comm := by
    intro a b
    cases a <;> cases b <;> decide

/-- The nontrivial central element squares to the identity. -/
theorem negI_sq : negI * negI = I := rfl

/-- `I` is a left unit. -/
@[simp] theorem I_mul (a : CentralSign) : I * a = a := by
  cases a <;> rfl

/-- `I` is a right unit. -/
@[simp] theorem mul_I (a : CentralSign) : a * I = a := by
  cases a <;> rfl

/-- The centralizer multiplication is commutative. -/
theorem cmul_comm (a b : CentralSign) : a * b = b * a := by
  cases a <;> cases b <;> rfl

/-- Winding parity as centralizer monodromy: even windings give `I`, odd give `-I`. -/
def centralFromWinding (w : ℕ) : CentralSign :=
  if Even w then I else negI

/-- Even winding is central-trivial. -/
theorem centralFromWinding_even {w : ℕ} (h : Even w) : centralFromWinding w = I := by
  simp [centralFromWinding, h]

/-- Odd winding is the nontrivial central element. -/
theorem centralFromWinding_odd {w : ℕ} (h : Odd w) : centralFromWinding w = negI := by
  simp [centralFromWinding, Nat.not_even_iff_odd.mpr h]

/-- A finite positive Artin word, represented by generator indices. -/
abbrev ArtinWord := List ℕ

/-- The scalar centralizer monodromy of an Artin word is its length parity. -/
def artinCentralMonodromy (w : ArtinWord) : CentralSign :=
  centralFromWinding w.length

/-- Central parity is additive under concatenation of words. -/
theorem centralFromWinding_add (m n : ℕ) :
    centralFromWinding (m + n) =
      centralFromWinding m * centralFromWinding n := by
  by_cases hm : Even m
  · by_cases hn : Even n
    · simp [centralFromWinding, hm, hn, Nat.even_add]
    · simp [centralFromWinding, hm, hn, Nat.even_add, I_mul]
  · by_cases hn : Even n
    · simp [centralFromWinding, hm, hn, Nat.even_add]
    · simp [centralFromWinding, hm, hn, Nat.even_add, negI_sq]

/-- central parity is multiplicative over word concatenation. -/
theorem artinCentralMonodromy_append (w₁ w₂ : ArtinWord) :
    artinCentralMonodromy (w₁ ++ w₂) =
      artinCentralMonodromy w₁ * artinCentralMonodromy w₂ := by
  simp [artinCentralMonodromy, centralFromWinding_add, List.length_append]

/-- Adjacent Artin braid relation preserves central monodromy. -/
theorem adjacent_artin_monodromy (i : ℕ) :
    artinCentralMonodromy [i, i + 1, i] =
      artinCentralMonodromy [i + 1, i, i + 1] := by
  rfl

/-- Trivial two-letter commutation on separated indices preserves central monodromy. -/
theorem separated_artin_monodromy (i j : ℕ) (_hij : i + 2 ≤ j ∨ j + 2 ≤ i) :
    artinCentralMonodromy [i, j] = artinCentralMonodromy [j, i] := by
  rfl

/-- Length-parity readback of a two-letter separated exchange. -/
theorem separated_artin_monodromy_raw (i j : ℕ) :
    artinCentralMonodromy [i, j] = artinCentralMonodromy [j, i] := by
  rfl

/-- The adjacent braid word has odd winding and therefore maps to `-I`. -/
theorem adjacent_artin_hits_negI (i : ℕ) :
    artinCentralMonodromy [i, i + 1, i] = negI := by
  norm_num [artinCentralMonodromy, centralFromWinding]

/-- A separated two-generator exchange has even winding and therefore maps to `I`. -/
theorem separated_artin_hits_I (i j : ℕ) :
    artinCentralMonodromy [i, j] = I := by
  norm_num [artinCentralMonodromy, centralFromWinding]

/-- An `n`-fold winding datum for a target finite central sign. -/
structure NFoldCentralRoot (n : ℕ) (target : CentralSign) where
  winding : ℕ
  hits_target : centralFromWinding (n * winding) = target

theorem odd_unit_winding_negI {n : ℕ} (h : Odd n) :
    centralFromWinding (n * 1) = negI := by
  simpa using centralFromWinding_odd (w := n) h

theorem even_unit_winding_I {n : ℕ} (h : Even n) :
    centralFromWinding (n * 1) = I := by
  simpa using centralFromWinding_even (w := n) h

/-- For odd `n`, unit winding maps to the nontrivial central sign. -/
def oddUnitRootOfNegI {n : ℕ} (h : Odd n) : NFoldCentralRoot n negI where
  winding := 1
  hits_target := odd_unit_winding_negI h

/-- For even `n`, unit winding maps to the trivial central sign. -/
def evenUnitRootOfI {n : ℕ} (h : Even n) : NFoldCentralRoot n I where
  winding := 1
  hits_target := even_unit_winding_I h

/-- The positive full twist on `n` strands has `n(n-1)` generator crossings. -/
def fullTwistWinding (n : ℕ) : ℕ := n * (n - 1)

/-- Consecutive-product parity: `n(n-1)` is always even. -/
theorem fullTwistWinding_even (n : ℕ) : Even (fullTwistWinding n) := by
  unfold fullTwistWinding
  obtain hn | hn := Nat.even_or_odd n
  · exact Even.mul_right hn (n - 1)
  · have hpred : Even (n - 1) := by
      rcases hn with ⟨k, hk⟩
      use k
      omega
    exact Even.mul_left hpred n

/-- Therefore the full twist has trivial `{I,-I}` centralizer monodromy. -/
theorem fullTwist_central_trivial (n : ℕ) :
    centralFromWinding (fullTwistWinding n) = I := by
  exact centralFromWinding_even (fullTwistWinding_even n)

/-- The half-twist crossing count `n(n-1)/2` mapped to the finite sign group. -/
def halfTwistCentral (n : ℕ) : CentralSign :=
  centralFromWinding (n * (n - 1) / 2)

/-- Concrete check: the three-strand half twist has nontrivial centralizer phase. -/
theorem halfTwist_three_negI : halfTwistCentral 3 = negI := by
  norm_num [halfTwistCentral, centralFromWinding]

/-- Concrete check: the four-strand half twist maps to the trivial sign. -/
theorem halfTwist_four_I : halfTwistCentral 4 = I := by
  norm_num [halfTwistCentral, centralFromWinding]

/-- The scalar `-1` is in the canonical mathlib `Pin(5,5)` submonoid: it is the
square of a negative-signature Clifford unit, and it is unitary. -/
theorem neg_one_mem_pin55 : (-1 : InfoGeometry.Clifford.Clifford55.Cl55) ∈ InfoGeometry.Clifford.Clifford55.Pin55 := by
  classical
  rw [pinGroup.mem_iff]
  constructor
  · have hQunit : IsUnit (InfoGeometry.Clifford.Clifford55.Q55 (InfoGeometry.Clifford.Clifford55.f_neg 0)) := by
      rw [InfoGeometry.Clifford.Clifford55.Q55_f_neg]
      exact ⟨-1, rfl⟩
    let u : InfoGeometry.Clifford.Clifford55.Cl55ˣ :=
      (CliffordAlgebra.isUnit_ι_of_isUnit InfoGeometry.Clifford.Clifford55.Q55 hQunit).unit
    have huval : (u : InfoGeometry.Clifford.Clifford55.Cl55) = InfoGeometry.Clifford.Clifford55.ι55 (InfoGeometry.Clifford.Clifford55.f_neg 0) :=
      (CliffordAlgebra.isUnit_ι_of_isUnit InfoGeometry.Clifford.Clifford55.Q55 hQunit).unit_spec
    have hgen :
        u ∈ ((↑) ⁻¹' Set.range InfoGeometry.Clifford.Clifford55.ι55 : Set InfoGeometry.Clifford.Clifford55.Cl55ˣ) := by
      refine ⟨InfoGeometry.Clifford.Clifford55.f_neg 0, ?_⟩
      simpa using huval
    have hulip : u ∈ InfoGeometry.Clifford.Clifford55.LipschitzGroup55 :=
      Subgroup.subset_closure hgen
    have hu2lip : u * u ∈ InfoGeometry.Clifford.Clifford55.LipschitzGroup55 :=
      mul_mem hulip hulip
    refine ⟨u * u, hu2lip, ?_⟩
    change (u : InfoGeometry.Clifford.Clifford55.Cl55) * (u : InfoGeometry.Clifford.Clifford55.Cl55) = (-1 : InfoGeometry.Clifford.Clifford55.Cl55)
    rw [huval, InfoGeometry.Clifford.Clifford55.f_neg_mul_self]
  · rw [Unitary.mem_iff]
    simp

/-- The scalar `-1` is in the canonical `Spin(5,5)` subgroup (hence in the even part). -/
theorem neg_one_mem_spin55 : (-1 : InfoGeometry.Clifford.Clifford55.Cl55) ∈ InfoGeometry.Clifford.Clifford55.Spin55 := by
  rw [spinGroup.mem_iff]
  constructor
  · exact neg_one_mem_pin55
  · change (-1 : InfoGeometry.Clifford.Clifford55.Cl55) ∈
      (CliffordAlgebra.even InfoGeometry.Clifford.Clifford55.Q55).toSubring.toSubmonoid
    exact (CliffordAlgebra.even InfoGeometry.Clifford.Clifford55.Q55).neg_mem <|
      by
        simp

/-- The nontrivial `{I,-I}` element as an actual `Pin(5,5)` element. -/
def negOnePin55 : InfoGeometry.Clifford.Clifford55.Pin55 :=
  ⟨(-1 : InfoGeometry.Clifford.Clifford55.Cl55), neg_one_mem_pin55⟩

/-- The central sign `-I` as an actual `Spin(5,5)` element; this is the central scalar lift, not
an orthogonal reflection. -/
def negOneSpin55 : InfoGeometry.Clifford.Clifford55.Spin55 :=
  ⟨(-1 : InfoGeometry.Clifford.Clifford55.Cl55), neg_one_mem_spin55⟩

/-- The centralizer elements map into the Pin(5,5) group over the identity. -/
def centralizerElement (c : CentralSign) : InfoGeometry.Clifford.Clifford55.Pin55 :=
  match c with
  | I => 1
  | negI => negOnePin55

/-- The centralizer elements map into the Spin(5,5) group over the identity. -/
def centralizerElementSpin (c : CentralSign) : InfoGeometry.Clifford.Clifford55.Spin55 :=
  match c with
  | I => 1
  | negI => negOneSpin55

/-- Central sign as a Pin(5,5) monoid morphism. -/
def centralizerElementHom : CentralSign →* InfoGeometry.Clifford.Clifford55.Pin55 where
  toFun := centralizerElement
  map_one' := rfl
  map_mul' := by
    intro a b
    cases a <;> cases b <;> ext <;>
      simp [centralizerElement, negOnePin55, negI_sq]

/-- Central sign as a Spin(5,5) monoid morphism. -/
def centralizerElementSpinHom : CentralSign →* InfoGeometry.Clifford.Clifford55.Spin55 where
  toFun := centralizerElementSpin
  map_one' := rfl
  map_mul' := by
    intro a b
    cases a <;> cases b <;> ext <;>
      simp [centralizerElementSpin, negOneSpin55, negI_sq]

@[simp] theorem centralizerElement_apply (c : CentralSign) :
    centralizerElementHom c = centralizerElement c := rfl

@[simp] theorem centralizerElementSpin_apply (c : CentralSign) :
    centralizerElementSpinHom c = centralizerElementSpin c := rfl

end InfoGeometry.Topology.ArtinCentralizerMonodromy
