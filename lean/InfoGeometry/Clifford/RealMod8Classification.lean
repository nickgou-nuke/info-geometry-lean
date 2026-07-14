import Mathlib.Data.List.Basic
import InfoGeometry.Clifford.BottPeriodicity
import InfoGeometry.Meta.Architecture

/-!
# InfoGeometry.Clifford.RealMod8Classification

Theorem-safe real mod-8 Clifford classification facade.

This file records the full residue-level classification data used by
Varlamov's `Discrete Symmetries and Clifford Algebras`:

* the real division-ring type by `p - q mod 8`,
* central-simple versus semisimple status,
* the eight Varlamov / Dabrowski signatures `(a,b,c)`,
* the associated discrete double-cover group type,
* broad signature availability by residue.

It does not assert matrix-algebra isomorphisms for `Cl(p,q)`.
Those are deeper algebraic theorems not currently owned by the repo.
-/

namespace RealMod8Classification

/-- Residue class of `p - q mod 8`. -/
inductive ClMod8 where
  | r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7
  deriving DecidableEq, Repr

/-- Division-ring type appearing in the real Clifford mod-8 table. -/
inductive RealDivisionRingKind where
  | R
  | C
  | H
  | RsumR
  | HsumH
  deriving DecidableEq, Repr

/-- Simple/semisimple structural class at the mod-8 level. -/
inductive RealCliffordStructuralKind where
  | centralSimple
  | semisimple
  | complexCentered
  deriving DecidableEq, Repr

/-- Division-ring readout for the real Clifford residue `p - q mod 8`. -/
def divisionRingKind : ClMod8 → RealDivisionRingKind
  | .r0 => .R
  | .r1 => .RsumR
  | .r2 => .R
  | .r3 => .C
  | .r4 => .H
  | .r5 => .HsumH
  | .r6 => .H
  | .r7 => .C

/-- Structural kind by residue. -/
def structuralKind : ClMod8 → RealCliffordStructuralKind
  | .r0 => .centralSimple
  | .r1 => .semisimple
  | .r2 => .centralSimple
  | .r3 => .complexCentered
  | .r4 => .centralSimple
  | .r5 => .semisimple
  | .r6 => .centralSimple
  | .r7 => .complexCentered

@[simp] theorem divisionRingKind_r0 : divisionRingKind .r0 = .R := rfl
@[simp] theorem divisionRingKind_r1 : divisionRingKind .r1 = .RsumR := rfl
@[simp] theorem divisionRingKind_r2 : divisionRingKind .r2 = .R := rfl
@[simp] theorem divisionRingKind_r3 : divisionRingKind .r3 = .C := rfl
@[simp] theorem divisionRingKind_r4 : divisionRingKind .r4 = .H := rfl
@[simp] theorem divisionRingKind_r5 : divisionRingKind .r5 = .HsumH := rfl
@[simp] theorem divisionRingKind_r6 : divisionRingKind .r6 = .H := rfl
@[simp] theorem divisionRingKind_r7 : divisionRingKind .r7 = .C := rfl

@[simp] theorem structuralKind_r0 : structuralKind .r0 = .centralSimple := rfl
@[simp] theorem structuralKind_r1 : structuralKind .r1 = .semisimple := rfl
@[simp] theorem structuralKind_r2 : structuralKind .r2 = .centralSimple := rfl
@[simp] theorem structuralKind_r3 : structuralKind .r3 = .complexCentered := rfl
@[simp] theorem structuralKind_r4 : structuralKind .r4 = .centralSimple := rfl
@[simp] theorem structuralKind_r5 : structuralKind .r5 = .semisimple := rfl
@[simp] theorem structuralKind_r6 : structuralKind .r6 = .centralSimple := rfl
@[simp] theorem structuralKind_r7 : structuralKind .r7 = .complexCentered := rfl

/-- Residue successor on the Bott 8-cycle. -/
def bottShift : ClMod8 → ClMod8
  | .r0 => .r1
  | .r1 => .r2
  | .r2 => .r3
  | .r3 => .r4
  | .r4 => .r5
  | .r5 => .r6
  | .r6 => .r7
  | .r7 => .r0

@[simp] theorem bottShift_r0 : bottShift .r0 = .r1 := rfl
@[simp] theorem bottShift_r1 : bottShift .r1 = .r2 := rfl
@[simp] theorem bottShift_r2 : bottShift .r2 = .r3 := rfl
@[simp] theorem bottShift_r3 : bottShift .r3 = .r4 := rfl
@[simp] theorem bottShift_r4 : bottShift .r4 = .r5 := rfl
@[simp] theorem bottShift_r5 : bottShift .r5 = .r6 := rfl
@[simp] theorem bottShift_r6 : bottShift .r6 = .r7 := rfl
@[simp] theorem bottShift_r7 : bottShift .r7 = .r0 := rfl

/-- The Bott residue successor has period eight. -/
theorem bottShift_iterate_eight (r : ClMod8) : bottShift^[8] r = r := by
  cases r <;> rfl

/-- Sign of a Varlamov / Dabrowski square. -/
inductive VSign where
  | plus
  | minus
  deriving DecidableEq, Repr

/--
Varlamov signature `(a,b,c) = (W²,E²,C²)`.

Here `W` is grade involution, `E` is reversion, and `C = E W`
is Clifford conjugation.
-/
structure VarlamovSignature where
  W2 : VSign
  E2 : VSign
  C2 : VSign
  deriving DecidableEq, Repr

namespace VarlamovSignature

def ppp : VarlamovSignature := ⟨.plus, .plus, .plus⟩
def pmm : VarlamovSignature := ⟨.plus, .minus, .minus⟩
def mpm : VarlamovSignature := ⟨.minus, .plus, .minus⟩
def mmp : VarlamovSignature := ⟨.minus, .minus, .plus⟩
def mmm : VarlamovSignature := ⟨.minus, .minus, .minus⟩
def mpp : VarlamovSignature := ⟨.minus, .plus, .plus⟩
def pmp : VarlamovSignature := ⟨.plus, .minus, .plus⟩
def ppm : VarlamovSignature := ⟨.plus, .plus, .minus⟩

def all : List VarlamovSignature :=
  [ppp, pmm, mpm, mmp, mmm, mpp, pmp, ppm]

end VarlamovSignature

/-- Discrete group type appearing in the Dabrowski cover table. -/
inductive DiscreteCoverGroupKind where
  | Z2xZ2xZ2
  | Z2xZ4
  | Q4
  | D4
  deriving DecidableEq, Repr

/--
Whether the Varlamov/Dabrowski discrete cover is Cliffordian
in Varlamov's sense: `PT = -TP`.
-/
inductive CliffordianKind where
  | nonCliffordian
  | cliffordian
  deriving DecidableEq, Repr

/-- Discrete cover group determined by the signature `(a,b,c)`. -/
def coverGroupKind : VarlamovSignature → DiscreteCoverGroupKind
  | ⟨.plus, .plus, .plus⟩ => .Z2xZ2xZ2
  | ⟨.plus, .minus, .minus⟩ => .Z2xZ4
  | ⟨.minus, .plus, .minus⟩ => .Z2xZ4
  | ⟨.minus, .minus, .plus⟩ => .Z2xZ4
  | ⟨.minus, .minus, .minus⟩ => .Q4
  | ⟨.minus, .plus, .plus⟩ => .D4
  | ⟨.plus, .minus, .plus⟩ => .D4
  | ⟨.plus, .plus, .minus⟩ => .D4

/-- Cliffordian/non-Cliffordian status determined by `(a,b,c)`. -/
def cliffordianKind : VarlamovSignature → CliffordianKind
  | ⟨.plus, .plus, .plus⟩ => .nonCliffordian
  | ⟨.plus, .minus, .minus⟩ => .nonCliffordian
  | ⟨.minus, .plus, .minus⟩ => .nonCliffordian
  | ⟨.minus, .minus, .plus⟩ => .nonCliffordian
  | ⟨.minus, .minus, .minus⟩ => .cliffordian
  | ⟨.minus, .plus, .plus⟩ => .cliffordian
  | ⟨.plus, .minus, .plus⟩ => .cliffordian
  | ⟨.plus, .plus, .minus⟩ => .cliffordian

@[simp] theorem coverGroupKind_ppp :
    coverGroupKind VarlamovSignature.ppp = .Z2xZ2xZ2 := rfl
@[simp] theorem coverGroupKind_pmm :
    coverGroupKind VarlamovSignature.pmm = .Z2xZ4 := rfl
@[simp] theorem coverGroupKind_mpm :
    coverGroupKind VarlamovSignature.mpm = .Z2xZ4 := rfl
@[simp] theorem coverGroupKind_mmp :
    coverGroupKind VarlamovSignature.mmp = .Z2xZ4 := rfl
@[simp] theorem coverGroupKind_mmm :
    coverGroupKind VarlamovSignature.mmm = .Q4 := rfl
@[simp] theorem coverGroupKind_mpp :
    coverGroupKind VarlamovSignature.mpp = .D4 := rfl
@[simp] theorem coverGroupKind_pmp :
    coverGroupKind VarlamovSignature.pmp = .D4 := rfl
@[simp] theorem coverGroupKind_ppm :
    coverGroupKind VarlamovSignature.ppm = .D4 := rfl

/--
Broad Varlamov signatures admitted by a residue class.

For quaternionic residues `r4` and `r6`, finer branch conditions depend on
the symmetric/skew-symmetric spinbasis counts. This table records the
residue-level admissible signature family.

For semisimple residues `r1` and `r5`, the general case admits all eight.
-/
def broadAllowedSignatures : ClMod8 → List VarlamovSignature
  | .r0 =>
      [VarlamovSignature.ppp,
       VarlamovSignature.pmm,
       VarlamovSignature.pmp,
       VarlamovSignature.ppm]
  | .r1 =>
      VarlamovSignature.all
  | .r2 =>
      [VarlamovSignature.mpm,
       VarlamovSignature.mmp,
       VarlamovSignature.mmm,
       VarlamovSignature.mpp]
  | .r3 =>
      [VarlamovSignature.ppp,
       VarlamovSignature.mmm]
  | .r4 =>
      [VarlamovSignature.ppp,
       VarlamovSignature.pmm,
       VarlamovSignature.pmp,
       VarlamovSignature.ppm]
  | .r5 =>
      VarlamovSignature.all
  | .r6 =>
      [VarlamovSignature.mpm,
       VarlamovSignature.mmp,
       VarlamovSignature.mmm,
       VarlamovSignature.mpp]
  | .r7 =>
      [VarlamovSignature.ppp,
       VarlamovSignature.mmm]

@[simp] theorem broadAllowedSignatures_r1 :
    broadAllowedSignatures .r1 = VarlamovSignature.all := rfl

@[simp] theorem broadAllowedSignatures_r5 :
    broadAllowedSignatures .r5 = VarlamovSignature.all := rfl

/--
For residues `1` and `5`, the general semisimple case admits all eight
Varlamov/Dabrowski signatures.
-/
theorem semisimpleResidues_admit_all_signatures :
    broadAllowedSignatures .r1 = VarlamovSignature.all
      ∧
    broadAllowedSignatures .r5 = VarlamovSignature.all := by
  exact ⟨rfl, rfl⟩

/-- Residues with real division ring `R`. -/
def hasRealDivisionRing (r : ClMod8) : Prop :=
  r = .r0 ∨ r = .r2

/-- Residues with complex division ring `C`. -/
def hasComplexDivisionRing (r : ClMod8) : Prop :=
  r = .r3 ∨ r = .r7

/-- Residues with quaternionic division ring `H`. -/
def hasQuaternionicDivisionRing (r : ClMod8) : Prop :=
  r = .r4 ∨ r = .r6

/-- Residues with semisimple double division ring. -/
def hasDoubleDivisionRing (r : ClMod8) : Prop :=
  r = .r1 ∨ r = .r5

theorem hasRealDivisionRing_iff (r : ClMod8) :
    hasRealDivisionRing r ↔ r = .r0 ∨ r = .r2 := by
  rfl

theorem hasComplexDivisionRing_iff (r : ClMod8) :
    hasComplexDivisionRing r ↔ r = .r3 ∨ r = .r7 := by
  rfl

theorem hasQuaternionicDivisionRing_iff (r : ClMod8) :
    hasQuaternionicDivisionRing r ↔ r = .r4 ∨ r = .r6 := by
  rfl

theorem hasDoubleDivisionRing_iff (r : ClMod8) :
    hasDoubleDivisionRing r ↔ r = .r1 ∨ r = .r5 := by
  rfl

end RealMod8Classification
