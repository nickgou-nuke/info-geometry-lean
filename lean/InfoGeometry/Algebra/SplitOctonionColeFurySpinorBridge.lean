import Mathlib

noncomputable section

namespace InfoGeometry.Algebra.ColeFurySpinorBridge

abbrev ColeFurySpinor (C : Type*) [CommRing C] := Fin 32 -> C

namespace ColeFurySpinor

variable {C : Type*} [CommRing C]

def zero : ColeFurySpinor C := fun _ => 0

def add (psi phi : ColeFurySpinor C) : ColeFurySpinor C := fun i => psi i + phi i

def smul (c : C) (psi : ColeFurySpinor C) : ColeFurySpinor C := fun i => c * psi i

end ColeFurySpinor

end InfoGeometry.Algebra.ColeFurySpinorBridge
