import InfoGeometry.Projective.ProjectiveNullBoundaryBraidFrameEquivariance

/-!
# Color-indexed logarithmic residues under the finite braid permutation

This owner transports labels only.  A residue family or a formal Hadjiivanov
family is read through the color of each marked point, and the existing
`B₃ → S₃` action merely reindexes that readout.  No operator multiplication,
conjugation, or common representation carrier is used here.
-/

namespace InfoGeometry.Projective.HadjiivanovBraidResidueReadout

open InfoGeometry.Projective.ProjectiveNullBoundaryBraidFrameBridge
open InfoGeometry.Projective.ProjectiveNullBoundaryBraidEquivariance

variable {X W : Type*}

def permuteLabelReadout (p : BraidPermutation) (r : Fin 3 → X) : Fin 3 → X :=
  fun i => r (p.symm i)

def residueReadout {S : BoundarySurface}
    (N : Fin 3 → X) (C : MarkedConfiguration S 3) : Fin 3 → X :=
  fun i => N (colorReadout C i)

theorem residueReadout_permutation_equivariant {S : BoundarySurface}
    (N : Fin 3 → X) (p : BraidPermutation) (C : MarkedConfiguration S 3) :
    residueReadout N (permuteMarkedConfiguration p C) =
      permuteLabelReadout p (residueReadout N C) := by
  rfl

theorem residueReadout_braid_equivariant {S : BoundarySurface}
    (N : Fin 3 → X) (g : BoundaryBraidGroup) (C : MarkedConfiguration S 3) :
    residueReadout N (markedConfigAction g C) =
      permuteLabelReadout (braidPermutation g) (residueReadout N C) := by
  rfl

def hadjiivanovLabelReadout {S : BoundarySurface}
    (M : Fin 3 → W → X) (w : W) (C : MarkedConfiguration S 3) : Fin 3 → X :=
  residueReadout (fun a => M a w) C

theorem hadjiivanovLabelReadout_permutation_equivariant {S : BoundarySurface}
    (M : Fin 3 → W → X) (w : W) (p : BraidPermutation)
    (C : MarkedConfiguration S 3) :
    hadjiivanovLabelReadout M w (permuteMarkedConfiguration p C) =
      permuteLabelReadout p (hadjiivanovLabelReadout M w C) := by
  exact residueReadout_permutation_equivariant (fun a => M a w) p C

theorem hadjiivanovLabelReadout_braid_equivariant {S : BoundarySurface}
    (M : Fin 3 → W → X) (w : W) (g : BoundaryBraidGroup)
    (C : MarkedConfiguration S 3) :
    hadjiivanovLabelReadout M w (markedConfigAction g C) =
      permuteLabelReadout (braidPermutation g) (hadjiivanovLabelReadout M w C) := by
  exact residueReadout_braid_equivariant (fun a => M a w) g C

end InfoGeometry.Projective.HadjiivanovBraidResidueReadout
