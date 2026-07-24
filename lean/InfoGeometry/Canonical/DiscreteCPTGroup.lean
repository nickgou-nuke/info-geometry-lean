import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic

/-!
# Finite C/P/T bookkeeping group

This file formalizes only the finite algebraic bookkeeping behind three
commuting involutive labels:

* charge conjugation `C`;
* parity `P`;
* time reversal `T`.

The carrier is `Fin 3 → Bool`, with composition given by bitwise XOR.  This is
the concrete finite `Z₂ × Z₂ × Z₂` shadow.  It does not prove the analytic CPT
theorem, antiunitarity of time reversal, or any interaction-specific
conservation/violation statement.
-/

namespace InfoGeometry.Canonical.DiscreteCPTGroup

/-! ## Mathlib-native `Z₂³` carrier -/

/--
The canonical abstract finite C/P/T bookkeeping group, written additively as
the three-dimensional vector space over `ZMod 2`.

This is the group-theoretic shadow only.  It does not encode antiunitarity of
time reversal, the fermionic `T² = -1` representation case, or the analytic CPT
theorem of relativistic QFT.
-/
abbrev CPTZ2 : Type :=
  Fin 3 → ZMod 2

/-- Elementary `Z₂³` generator at one coordinate. -/
def z2Generator (i : Fin 3) : CPTZ2 :=
  fun j => if j = i then 1 else 0

/-- Charge-conjugation coordinate in the abstract `Z₂³` bookkeeping group. -/
def z2C : CPTZ2 :=
  z2Generator 0

/-- Parity coordinate in the abstract `Z₂³` bookkeeping group. -/
def z2P : CPTZ2 :=
  z2Generator 1

/-- Time-reversal coordinate in the abstract `Z₂³` bookkeeping group. -/
def z2T : CPTZ2 :=
  z2Generator 2

/-- Every elementary coordinate has order two. -/
@[simp]
theorem z2Generator_add_self (i : Fin 3) :
    z2Generator i + z2Generator i = 0 := by
  funext j
  by_cases h : j = i
  · simp [z2Generator, h, CharTwo.add_self_eq_zero]
  · simp [z2Generator, h]

@[simp]
theorem z2C_add_self :
    z2C + z2C = 0 := by
  simp [z2C]

@[simp]
theorem z2P_add_self :
    z2P + z2P = 0 := by
  simp [z2P]

@[simp]
theorem z2T_add_self :
    z2T + z2T = 0 := by
  simp [z2T]

theorem z2C_add_z2P_comm :
    z2C + z2P = z2P + z2C := by
  ext i
  simp [add_comm]

theorem z2C_add_z2T_comm :
    z2C + z2T = z2T + z2C := by
  ext i
  simp [add_comm]

theorem z2P_add_z2T_comm :
    z2P + z2T = z2T + z2P := by
  ext i
  simp [add_comm]

/-- The native abstract C/P/T bookkeeping carrier has eight elements. -/
theorem card_CPTZ2 :
    Fintype.card CPTZ2 = 8 := by
  simp [CPTZ2, ZMod.card]

/--
Every abstract C/P/T bookkeeping element decomposes uniquely by its three
`ZMod 2` coordinates.
-/
theorem z2_decompose (g : CPTZ2) :
    g = g 0 • z2C + g 1 • z2P + g 2 • z2T := by
  funext i
  fin_cases i <;> simp [z2C, z2P, z2T, z2Generator]

/-! ## Labels and elements -/

/-- The three elementary discrete-symmetry labels. -/
inductive CPTLabel where
  | C
  | P
  | T
  deriving DecidableEq, Repr

/-- Convert a label to its bit coordinate. -/
def CPTLabel.toFin3 : CPTLabel → Fin 3
  | .C => 0
  | .P => 1
  | .T => 2

/-- A finite C/P/T group element is a three-bit address. -/
abbrev CPTElement : Type :=
  Fin 3 → Bool

/-- Identity element: no C/P/T flip is active. -/
def E : CPTElement :=
  fun _ => false

/-- Bitwise XOR composition. -/
def cptMul (g h : CPTElement) : CPTElement :=
  fun i => Bool.xor (g i) (h i)

/-- Elementary generator at one coordinate. -/
def generator (label : CPTLabel) : CPTElement :=
  fun i => i = label.toFin3

/-- Charge conjugation bit. -/
def C : CPTElement :=
  generator .C

/-- Parity bit. -/
def P : CPTElement :=
  generator .P

/-- Time-reversal bit. -/
def T : CPTElement :=
  generator .T

/-- Combined `CP`. -/
def CP : CPTElement :=
  cptMul C P

/-- Combined `CT`. -/
def CT : CPTElement :=
  cptMul C T

/-- Combined `PT`. -/
def PT : CPTElement :=
  cptMul P T

/-- Combined `CPT`. -/
def CPT : CPTElement :=
  cptMul (cptMul C P) T

/-! ## Finite group laws -/

@[simp]
theorem cptMul_apply (g h : CPTElement) (i : Fin 3) :
    cptMul g h i = Bool.xor (g i) (h i) :=
  rfl

@[simp]
theorem cptMul_E_left (g : CPTElement) :
    cptMul E g = g := by
  funext i
  simp [cptMul, E]

@[simp]
theorem cptMul_E_right (g : CPTElement) :
    cptMul g E = g := by
  funext i
  cases hgi : g i <;> simp [cptMul, E, hgi]

theorem cptMul_assoc (g h k : CPTElement) :
    cptMul (cptMul g h) k = cptMul g (cptMul h k) := by
  funext i
  cases g i <;> cases h i <;> cases k i <;> simp [cptMul]

theorem cptMul_comm (g h : CPTElement) :
    cptMul g h = cptMul h g := by
  funext i
  cases hg : g i <;> cases hh : h i <;> simp [cptMul, hg, hh]

/-- Every element is its own inverse. -/
@[simp]
theorem cptMul_self (g : CPTElement) :
    cptMul g g = E := by
  funext i
  cases g i <;> simp [cptMul, E]

/-- The finite C/P/T bookkeeping forms an elementary abelian two-group. -/
theorem elementary_abelian_two_group_laws (g h k : CPTElement) :
    cptMul E g = g
      ∧ cptMul g E = g
      ∧ cptMul (cptMul g h) k = cptMul g (cptMul h k)
      ∧ cptMul g h = cptMul h g
      ∧ cptMul g g = E := by
  exact ⟨cptMul_E_left g, cptMul_E_right g, cptMul_assoc g h k,
    cptMul_comm g h, cptMul_self g⟩

/-! ## C, P, T readbacks -/

@[simp]
theorem C_sq :
    cptMul C C = E :=
  cptMul_self C

@[simp]
theorem P_sq :
    cptMul P P = E :=
  cptMul_self P

@[simp]
theorem T_sq :
    cptMul T T = E :=
  cptMul_self T

theorem C_comm_P :
    cptMul C P = cptMul P C :=
  cptMul_comm C P

theorem C_comm_T :
    cptMul C T = cptMul T C :=
  cptMul_comm C T

theorem P_comm_T :
    cptMul P T = cptMul T P :=
  cptMul_comm P T

@[simp]
theorem CPT_sq :
    cptMul CPT CPT = E :=
  cptMul_self CPT

/--
The eight named C/P/T combinations exhaust the three-bit finite carrier.
-/
theorem cases_eq_named
    (g : CPTElement) :
    g = E ∨ g = C ∨ g = P ∨ g = T ∨ g = CP ∨ g = CT ∨ g = PT ∨ g = CPT := by
  cases h0 : g 0 <;> cases h1 : g 1 <;> cases h2 : g 2
  · left
    funext i
    fin_cases i <;> simp [E, h0, h1, h2]
  · right; right; right; left
    funext i
    fin_cases i <;> simp [T, generator, CPTLabel.toFin3, h0, h1, h2]
  · right; right; left
    funext i
    fin_cases i <;> simp [P, generator, CPTLabel.toFin3, h0, h1, h2]
  · right; right; right; right; right; right; left
    funext i
    fin_cases i <;> simp [PT, P, T, generator, CPTLabel.toFin3, cptMul, h0, h1, h2]
  · right; left
    funext i
    fin_cases i <;> simp [C, generator, CPTLabel.toFin3, h0, h1, h2]
  · right; right; right; right; right; left
    funext i
    fin_cases i <;> simp [CT, C, T, generator, CPTLabel.toFin3, cptMul, h0, h1, h2]
  · right; right; right; right; left
    funext i
    fin_cases i <;> simp [CP, C, P, generator, CPTLabel.toFin3, cptMul, h0, h1, h2]
  · right; right; right; right; right; right; right
    funext i
    fin_cases i <;> simp [CPT, C, P, T, generator, CPTLabel.toFin3, cptMul, h0, h1, h2]

end InfoGeometry.Canonical.DiscreteCPTGroup
