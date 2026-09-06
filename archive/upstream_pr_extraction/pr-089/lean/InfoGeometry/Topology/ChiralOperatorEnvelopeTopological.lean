import Mathlib
import InfoGeometry.Algebra.ChiralOperatorEnvelope

/-!
# Topological representations of the chiral operator envelope

The abstract free envelope is represented on a normed real space by eight
continuous linear operators.  Word products are evaluated by composition, so
the operator layer remains associative and all finite word evaluations are
continuous linear maps.
-/

namespace InfoGeometry.Topology

open InfoGeometry.Algebra
open InfoGeometry.OperatorAlgebra

structure ChiralContinuousRepresentation (H : Type*)
    [NormedAddCommGroup H] [NormedSpace ℝ H] where
  pPlus : H →L[ℝ] H
  pMinus : H →L[ℝ] H
  sPlus : Fin 3 → H →L[ℝ] H
  sMinus : Fin 3 → H →L[ℝ] H

abbrev ChiralContinuousOperator (H : Type*)
    [NormedAddCommGroup H] [NormedSpace ℝ H] := H →L[ℝ] H

def ChiralContinuousRepresentation.generator
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ρ : ChiralContinuousRepresentation H)
    (g : ChiralGenerator) : ChiralContinuousOperator H :=
  match g with
  | .pPlus => ρ.pPlus
  | .pMinus => ρ.pMinus
  | .sPlus i => ρ.sPlus i
  | .sMinus i => ρ.sMinus i

def ChiralContinuousRepresentation.evalWord
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ρ : ChiralContinuousRepresentation H) :
    List ChiralGenerator → ChiralContinuousOperator H
  | [] => ContinuousLinearMap.id ℝ H
  | g :: w =>
      (ρ.generator g).comp (ρ.evalWord w)

@[simp] theorem ChiralContinuousRepresentation.evalWord_nil
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ρ : ChiralContinuousRepresentation H) :
    ρ.evalWord [] = ContinuousLinearMap.id ℝ H :=
  rfl

@[simp] theorem ChiralContinuousRepresentation.evalWord_cons
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ρ : ChiralContinuousRepresentation H)
    (g : ChiralGenerator) (w : List ChiralGenerator) :
    ρ.evalWord (g :: w) = (ρ.generator g).comp (ρ.evalWord w) :=
  rfl

theorem ChiralContinuousRepresentation.evalWord_append
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ρ : ChiralContinuousRepresentation H)
    (u v : List ChiralGenerator) :
    ρ.evalWord (u ++ v) = (ρ.evalWord u).comp (ρ.evalWord v) := by
  induction u with
  | nil => simp [ChiralContinuousRepresentation.evalWord]
  | cons g u ih =>
      simp [ChiralContinuousRepresentation.evalWord, ih,
        ContinuousLinearMap.comp_assoc]

def ChiralContinuousRepresentation.sageSymbol
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ρ : ChiralContinuousRepresentation H) :
    Fin 8 → ChiralContinuousOperator H
  | 0 => ρ.pPlus + ρ.pMinus
  | 1 => ρ.sMinus 0 - ρ.sPlus 0
  | 2 => ρ.sMinus 1 - ρ.sPlus 1
  | 3 => ρ.sMinus 2 - ρ.sPlus 2
  | 4 => ρ.pPlus - ρ.pMinus
  | 5 => ρ.sPlus 0 + ρ.sMinus 0
  | 6 => ρ.sPlus 1 + ρ.sMinus 1
  | 7 => ρ.sPlus 2 + ρ.sMinus 2

@[simp] theorem ChiralContinuousRepresentation.sageSymbol_zero
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ρ : ChiralContinuousRepresentation H) :
    ρ.sageSymbol 0 = ρ.pPlus + ρ.pMinus :=
  rfl

@[simp] theorem ChiralContinuousRepresentation.sageSymbol_four
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ρ : ChiralContinuousRepresentation H) :
    ρ.sageSymbol 4 = ρ.pPlus - ρ.pMinus :=
  rfl

end InfoGeometry.Topology
