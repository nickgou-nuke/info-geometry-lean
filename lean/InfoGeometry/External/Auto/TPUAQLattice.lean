import Mathlib.Data.Fin.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace AutonomousHypothesisEngine

inductive PropositionNode where
  | atom : Fin 4 → PropositionNode
  | arrow : Fin 4 → Fin 4 → PropositionNode
  | vacuum : PropositionNode
deriving DecidableEq, Repr

inductive NodeTag where
  | atom
  | arrow
  | vacuum
deriving DecidableEq, Repr

structure NormalForm where
  tag : NodeTag
  code : Fin 16
deriving DecidableEq, Repr

def codeOfNat (n : Nat) : Fin 16 :=
  ⟨n % 16, Nat.mod_lt n (by decide)⟩

def zeroCode : Fin 16 := codeOfNat 0

def atomCode (i : Fin 4) : Fin 16 :=
  codeOfNat i.val

def arrowCode (i j : Fin 4) : Fin 16 :=
  codeOfNat (4 * i.val + j.val)

def normalize : PropositionNode → NormalForm
  | .atom i => ⟨.atom, atomCode i⟩
  | .arrow i j => ⟨.arrow, arrowCode i j⟩
  | .vacuum => ⟨.vacuum, zeroCode⟩

def vacuumNode : PropositionNode := .vacuum

def tagNumber : NodeTag → Fin 3
  | .atom => ⟨0, by decide⟩
  | .arrow => ⟨1, by decide⟩
  | .vacuum => ⟨2, by decide⟩

theorem vacuum_normalized :
    tagNumber (normalize vacuumNode).tag = ⟨2, by decide⟩ ∧
      (normalize vacuumNode).code = zeroCode := by
  simp [vacuumNode, normalize, tagNumber, zeroCode, codeOfNat]

end AutonomousHypothesisEngine
