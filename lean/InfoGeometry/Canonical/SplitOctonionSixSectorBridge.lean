import InfoGeometry.Canonical.SplitOctonionChiralZornMultiplication
import InfoGeometry.Canonical.ThreeColorNativeBracketTable

namespace InfoGeometry.Canonical

open SplitOctonionColour

noncomputable section

def sixSectorBasis
    (s : Fin 2) (c : SplitOctonionColour) : ChiralZornCarrier :=
  if s = 0 then modularSigmaPlus c else modularSigmaMinus c

@[simp] theorem sixSectorBasis_pos (c : SplitOctonionColour) :
    sixSectorBasis 0 c = modularSigmaPlus c := by
  simp [sixSectorBasis]

@[simp] theorem sixSectorBasis_neg (c : SplitOctonionColour) :
    sixSectorBasis 1 c = modularSigmaMinus c := by
  simp [sixSectorBasis]

theorem colourIndex_injective :
    Function.Injective (fun i : Fin 3 =>
      match i with
      | 0 => SplitOctonionColour.red
      | 1 => SplitOctonionColour.green
      | 2 => SplitOctonionColour.blue) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

theorem colourIndex_surjective :
    Function.Surjective (fun i : Fin 3 =>
      match i with
      | 0 => SplitOctonionColour.red
      | 1 => SplitOctonionColour.green
      | 2 => SplitOctonionColour.blue) := by
  intro c
  cases c
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

theorem sixSector_card :
    Fintype.card (Fin 2 × SplitOctonionColour) = 6 := by
  native_decide

theorem sixSectorBasis_injective :
    Function.Injective (fun p : Fin 2 × SplitOctonionColour =>
      sixSectorBasis p.1 p.2) := by
  intro p q
  rcases p with ⟨s, c⟩
  rcases q with ⟨t, d⟩
  fin_cases s <;> fin_cases t <;> cases c <;> cases d <;> native_decide

def colourFin3Equiv : Fin 3 ≃ SplitOctonionColour :=
  Equiv.ofBijective
    (fun i : Fin 3 =>
      match i with
      | 0 => SplitOctonionColour.red
      | 1 => SplitOctonionColour.green
      | 2 => SplitOctonionColour.blue)
    ⟨colourIndex_injective, colourIndex_surjective⟩

def sixSectorBasisFin3
    (s : Fin 2) (c : Fin 3) : ChiralZornCarrier :=
  sixSectorBasis s (colourFin3Equiv c)

theorem sixSectorBasisFin3_injective :
    Function.Injective (fun p : Fin 2 × Fin 3 =>
      sixSectorBasisFin3 p.1 p.2) := by
  intro p q h
  rcases p with ⟨ps, pc⟩
  rcases q with ⟨qs, qc⟩
  have h' :
      sixSectorBasis ps (colourFin3Equiv pc) =
        sixSectorBasis qs (colourFin3Equiv qc) := by
    simpa [sixSectorBasisFin3] using h
  have hpq : (ps, colourFin3Equiv pc) =
      (qs, colourFin3Equiv qc) :=
    sixSectorBasis_injective h'
  have hs : ps = qs :=
    congrArg (fun z : Fin 2 × SplitOctonionColour => z.1) hpq
  have hc : pc = qc :=
    colourFin3Equiv.injective
      (congrArg (fun z : Fin 2 × SplitOctonionColour => z.2) hpq)
  cases hs
  cases hc
  rfl

theorem sixSectorBasis_eq_iff
    {p q : Fin 2 × SplitOctonionColour} :
    sixSectorBasis p.1 p.2 = sixSectorBasis q.1 q.2 ↔ p = q := by
  constructor
  · intro h
    exact sixSectorBasis_injective h
  · intro h
    exact congrArg (fun r => sixSectorBasis r.1 r.2) h

theorem sixSectorBasis_square_zero
    (s : Fin 2) (c : SplitOctonionColour) :
    chiralZornMul (sixSectorBasis s c) (sixSectorBasis s c) = 0 := by
  fin_cases s <;>
    simp [sixSectorBasis, chiralZornMul]

theorem sixSectorBasis_pos_mul_neg
    (c : SplitOctonionColour) :
    chiralZornMul (sixSectorBasis 0 c) (sixSectorBasis 1 c) = modularNPlus := by
  simp [chiralZornMul]

theorem sixSectorBasis_neg_mul_pos
    (c : SplitOctonionColour) :
    chiralZornMul (sixSectorBasis 1 c) (sixSectorBasis 0 c) = modularNMinus := by
  simp [chiralZornMul]

theorem sixSector_pos_mul_neg_of_ne
    {c d : SplitOctonionColour} (h : c ≠ d) :
    chiralZornMul (sixSectorBasis 0 c) (sixSectorBasis 1 d) = 0 := by
  cases c <;> cases d <;> simp_all [sixSectorBasis, chiralZornMul] <;> native_decide

theorem sixSector_neg_mul_pos_of_ne
    {c d : SplitOctonionColour} (h : c ≠ d) :
    chiralZornMul (sixSectorBasis 1 c) (sixSectorBasis 0 d) = 0 := by
  cases c <;> cases d <;> simp_all [sixSectorBasis, chiralZornMul] <;> native_decide

theorem sixSector_pos_mul_neg (c d : SplitOctonionColour) :
    chiralZornMul (sixSectorBasis 0 c) (sixSectorBasis 1 d) =
      if c = d then modularNPlus else 0 := by
  by_cases h : c = d
  · subst d
    simp [sixSectorBasis, chiralZornMul]
  · simpa [h] using sixSector_pos_mul_neg_of_ne h

theorem sixSector_neg_mul_pos (c d : SplitOctonionColour) :
    chiralZornMul (sixSectorBasis 1 c) (sixSectorBasis 0 d) =
      if c = d then modularNMinus else 0 := by
  by_cases h : c = d
  · subst d
    simp [sixSectorBasis, chiralZornMul]
  · simpa [h] using sixSector_neg_mul_pos_of_ne h

theorem sixSector_pos_mul_pos_skew
    {c d : SplitOctonionColour} (h : c ≠ d) :
    chiralZornMul (sixSectorBasis 0 c) (sixSectorBasis 0 d) =
      -chiralZornMul (sixSectorBasis 0 d) (sixSectorBasis 0 c) := by
  cases c <;> cases d <;> simp_all [sixSectorBasis, chiralZornMul] <;> native_decide

theorem sixSector_neg_mul_neg_skew
    {c d : SplitOctonionColour} (h : c ≠ d) :
    chiralZornMul (sixSectorBasis 1 c) (sixSectorBasis 1 d) =
      -chiralZornMul (sixSectorBasis 1 d) (sixSectorBasis 1 c) := by
  cases c <;> cases d <;> simp_all [sixSectorBasis, chiralZornMul] <;> native_decide

theorem sixSector_pos_red_mul_green :
    chiralZornMul (sixSectorBasis 0 .red) (sixSectorBasis 0 .green) =
      sixSectorBasis 1 .blue := by
  native_decide

theorem sixSector_pos_red_mul_blue :
    chiralZornMul (sixSectorBasis 0 .red) (sixSectorBasis 0 .blue) =
      -sixSectorBasis 1 .green := by
  native_decide

theorem sixSector_pos_green_mul_blue :
    chiralZornMul (sixSectorBasis 0 .green) (sixSectorBasis 0 .blue) =
      sixSectorBasis 1 .red := by
  native_decide

theorem sixSector_neg_red_mul_green :
    chiralZornMul (sixSectorBasis 1 .red) (sixSectorBasis 1 .green) =
      -sixSectorBasis 0 .blue := by
  native_decide

theorem sixSector_neg_red_mul_blue :
    chiralZornMul (sixSectorBasis 1 .red) (sixSectorBasis 1 .blue) =
      sixSectorBasis 0 .green := by
  native_decide

theorem sixSector_neg_green_mul_blue :
    chiralZornMul (sixSectorBasis 1 .green) (sixSectorBasis 1 .blue) =
      -sixSectorBasis 0 .red := by
  native_decide

theorem sixSector_corners_resolve
    (c : SplitOctonionColour) :
    chiralZornMul modularNPlus (sixSectorBasis 0 c) = sixSectorBasis 0 c ∧
      chiralZornMul (sixSectorBasis 0 c) modularNMinus = sixSectorBasis 0 c ∧
      chiralZornMul modularNMinus (sixSectorBasis 1 c) = sixSectorBasis 1 c ∧
      chiralZornMul (sixSectorBasis 1 c) modularNPlus = sixSectorBasis 1 c := by
  simp [sixSectorBasis, chiralZornMul]

theorem splitOctonion_two_poles_plus_six_channels :
    modularNPlus + modularNMinus = chiralZornOne :=
  chiralZorn_basis_resolution

end
end InfoGeometry.Canonical
