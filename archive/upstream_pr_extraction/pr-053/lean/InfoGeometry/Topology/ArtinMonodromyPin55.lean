import Mathlib.Tactic
import InfoGeometry.Topology.BraidNegativeIdentityMonodromy
import InfoGeometry.Canonical.Pin55NativeCover

open Matrix Complex

/-!
# Artin parity and native `Pin(5,5)` central signs

This file keeps two finite channels distinct.

* `artinParitySign` is the length-parity character of positive Artin words.
* `BraidNegativeIdentityMonodromy` is the spinor half-twist channel whose
  generator squares to `-I`.

The first channel is a genuine `C₂`-valued monoid homomorphism.  Its native
Clifford readout uses the existing `Pin55` owner and its actual `-1` kernel
element.  No `O(5,5)` or `Pin(5,5)` double-cover claim is made for the matrix
spinor shadow.
-/

noncomputable section

namespace InfoGeometry.Topology.ArtinMonodromyPin55

abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ
abbrev ArtinWord := List ℕ

instance : Monoid ArtinWord where
  mul := List.append
  one := []
  mul_assoc := List.append_assoc
  one_mul := List.nil_append
  mul_one := List.append_nil

inductive CentralizerAtom where
  | plusI
  | minusI
  deriving DecidableEq, Repr

abbrev CentralSign := CentralizerAtom
abbrev CentralSignAtom := CentralizerAtom

def cmul : CentralizerAtom → CentralizerAtom → CentralizerAtom
  | .plusI, b => b
  | .minusI, .plusI => .minusI
  | .minusI, .minusI => .plusI

instance : One CentralizerAtom := ⟨.plusI⟩
instance : Mul CentralizerAtom := ⟨cmul⟩
instance : Inv CentralizerAtom := ⟨id⟩

instance : CommGroup CentralizerAtom where
  mul_assoc := by
    intro a b c
    cases a <;> cases b <;> cases c <;> rfl
  one_mul := by
    intro a
    cases a <;> rfl
  mul_one := by
    intro a
    cases a <;> rfl
  inv_mul_cancel := by
    intro a
    cases a <;> rfl
  mul_comm := by
    intro a b
    cases a <;> cases b <;> rfl

@[simp] theorem plusI_mul (a : CentralizerAtom) : .plusI * a = a := by
  cases a <;> rfl

@[simp] theorem mul_plusI (a : CentralizerAtom) : a * .plusI = a := by
  cases a <;> rfl

@[simp] theorem minusI_sq : (CentralizerAtom.minusI : CentralizerAtom) ^ 2 = .plusI := by
  rfl

def centralizerValue : CentralizerAtom → M2C
  | .plusI => 1
  | .minusI => -1

abbrev centralSignValue := centralizerValue

@[simp] theorem centralizerValue_plusI : centralizerValue .plusI = (1 : M2C) := rfl
@[simp] theorem centralizerValue_minusI : centralizerValue .minusI = -(1 : M2C) := rfl

theorem centralizerValue_mul (a b : CentralizerAtom) :
    centralizerValue (a * b) = centralizerValue a * centralizerValue b := by
  change centralizerValue (cmul a b) = centralizerValue a * centralizerValue b
  cases a <;> cases b <;>
    simp [centralizerValue, cmul]

def centralizerValueHom : CentralizerAtom →* M2C where
  toFun := centralizerValue
  map_one' := rfl
  map_mul' := centralizerValue_mul

theorem centralizer_atom_sq (z : CentralizerAtom) :
    centralizerValue z * centralizerValue z = (1 : M2C) := by
  cases z <;> simp [centralizerValue]

theorem centralSign_atom_sq (z : CentralSignAtom) :
    centralSignValue z * centralSignValue z = (1 : M2C) :=
  centralizer_atom_sq z

def IsNfoldRootOfCentralSign (n : ℕ) (A : M2C) : Prop :=
  A ^ n = (1 : M2C) ∨ A ^ n = -(1 : M2C)

abbrev IsNfoldRootOfCentralizer := IsNfoldRootOfCentralSign

theorem isNfoldRootOfCentralizer_iff_exists_atom (n : ℕ) (A : M2C) :
    IsNfoldRootOfCentralizer n A ↔
      ∃ c : CentralizerAtom, A ^ n = centralizerValue c := by
  constructor
  · rintro (h | h)
    · exact ⟨.plusI, h⟩
    · exact ⟨.minusI, h⟩
  · rintro ⟨c, h⟩
    cases c
    · exact Or.inl h
    · exact Or.inr h

theorem positive_centralizer_root_closes (A : M2C) (n : ℕ)
    (h : A ^ n = (1 : M2C)) :
    A ^ (2 * n) = (1 : M2C) := by
  rw [show 2 * n = n + n by rw [two_mul], pow_add, h]
  simp

theorem spinorHalfTwist_twofold_root :
    IsNfoldRootOfCentralSign 2 BraidNegativeIdentityMonodromy.spinorHalfTwist := by
  right
  simpa [IsNfoldRootOfCentralSign, pow_two] using
    BraidNegativeIdentityMonodromy.spinorHalfTwist_sq

theorem negative_centralizer_root_closes (A : M2C) (n : ℕ)
    (h : A ^ n = -(1 : M2C)) :
    A ^ (2 * n) = (1 : M2C) :=
  BraidNegativeIdentityMonodromy.negative_root_doubles_to_identity A n h

theorem artin_spinor_monodromy (i : ℕ) :
    BraidNegativeIdentityMonodromy.ρσ i *
        BraidNegativeIdentityMonodromy.ρσ (i + 1) *
        BraidNegativeIdentityMonodromy.ρσ i =
      BraidNegativeIdentityMonodromy.ρσ (i + 1) *
        BraidNegativeIdentityMonodromy.ρσ i *
        BraidNegativeIdentityMonodromy.ρσ (i + 1) :=
  BraidNegativeIdentityMonodromy.spinor_adjacent_artin i

def centralFromWinding : ℕ → CentralizerAtom
  | 0 => .plusI
  | n + 1 => .minusI * centralFromWinding n

@[simp] theorem centralFromWinding_zero : centralFromWinding 0 = .plusI := rfl
@[simp] theorem centralFromWinding_succ (n : ℕ) :
    centralFromWinding (n + 1) = .minusI * centralFromWinding n := rfl

theorem centralFromWinding_add (m n : ℕ) :
    centralFromWinding (m + n) =
      centralFromWinding m * centralFromWinding n := by
  induction m with
  | zero => simp [centralFromWinding]
  | succ m ih =>
      simp [Nat.succ_add, centralFromWinding, ih, mul_assoc]

def artinParitySign (w : ArtinWord) : CentralizerAtom :=
  centralFromWinding w.length

abbrev artinCentralMonodromy := artinParitySign

@[simp] theorem artinParitySign_append (u v : ArtinWord) :
    artinParitySign (u ++ v) = artinParitySign u * artinParitySign v := by
  simp only [artinParitySign, List.length_append]
  exact centralFromWinding_add u.length v.length

def artinParitySignHom : ArtinWord →* CentralizerAtom where
  toFun := artinParitySign
  map_one' := by
    change centralFromWinding 0 = .plusI
    rfl
  map_mul' := artinParitySign_append

abbrev artinParitySignMonoidHom := artinParitySignHom

structure NFoldCentralWinding (n : ℕ) (target : CentralizerAtom) where
  winding : ℕ
  hits_target : centralFromWinding (n * winding) = target

abbrev NFoldCentralRoot := NFoldCentralWinding
abbrev NFoldWindingDatum := NFoldCentralWinding

def centralizerPinValue (c : CentralizerAtom) :
    InfoGeometry.Clifford.Clifford55.Pin55 :=
  match c with
  | .plusI => 1
  | .minusI => InfoGeometry.Clifford.Clifford55.negOnePin

theorem centralizerPinValue_mul (a b : CentralizerAtom) :
    centralizerPinValue (a * b) =
      centralizerPinValue a * centralizerPinValue b := by
  change centralizerPinValue (cmul a b) =
    centralizerPinValue a * centralizerPinValue b
  cases a <;> cases b <;>
    simp [centralizerPinValue, cmul,
      InfoGeometry.Clifford.Clifford55.negOnePin_sq]

def centralizerPinHom : CentralizerAtom →*
    InfoGeometry.Clifford.Clifford55.Pin55 where
  toFun := centralizerPinValue
  map_one' := rfl
  map_mul' := centralizerPinValue_mul

theorem centralizerPinValue_native_action (c : CentralizerAtom) :
    InfoGeometry.Clifford.Clifford55.pin55NativeOrthogonalAction
        (centralizerPinValue c) = 1 := by
  cases c
  · simp [centralizerPinValue]
  · exact InfoGeometry.Clifford.Clifford55.negOnePin_mem_pin55NativeOrthogonalAction_kernel

theorem centralizerPinValue_sq (c : CentralizerAtom) :
    centralizerPinValue c * centralizerPinValue c = 1 := by
  cases c
  · simp [centralizerPinValue]
  · apply Subtype.ext
    simp [centralizerPinValue,
      InfoGeometry.Clifford.Clifford55.negOnePin_coe]

theorem centralizerPinValue_commutes (c : CentralizerAtom)
    (g : InfoGeometry.Clifford.Clifford55.Pin55) :
    centralizerPinValue c * g = g * centralizerPinValue c := by
  cases c
  · simp [centralizerPinValue]
  · exact InfoGeometry.Clifford.Clifford55.negOnePin_commute g

theorem centralizerPinValue_sandwich_trivial (c : CentralizerAtom)
    (x : InfoGeometry.Clifford.Clifford55.Cl55) :
    (centralizerPinValue c : InfoGeometry.Clifford.Clifford55.Cl55) * x *
        (centralizerPinValue c : InfoGeometry.Clifford.Clifford55.Cl55) = x := by
  cases c
  · simp [centralizerPinValue]
  · simp [centralizerPinValue,
      InfoGeometry.Clifford.Clifford55.negOnePin_coe]

theorem centralizer_is_plus_minus_I (z : CentralizerAtom) :
    centralizerValue z = 1 ∨ centralizerValue z = -1 := by
  cases z <;> simp [centralizerValue]

theorem artin_monodromy_winds_centralizer :
    BraidNegativeIdentityMonodromy.ρσ 0 *
        BraidNegativeIdentityMonodromy.ρσ 0 = -(1 : M2C) :=
  BraidNegativeIdentityMonodromy.B2_full_twist_negative

theorem n_fold_roots_close_in_centralizer (A : M2C) (n : ℕ)
    (h : A ^ n = -1) : A ^ (2 * n) = 1 :=
  negative_centralizer_root_closes A n h

theorem nfold_centralizer_root_closes (A : M2C) (n : ℕ)
    (h : IsNfoldRootOfCentralizer n A) :
    A ^ (2 * n) = (1 : M2C) := by
  rcases h with h | h
  · exact positive_centralizer_root_closes A n h
  · exact negative_centralizer_root_closes A n h

end InfoGeometry.Topology.ArtinMonodromyPin55
