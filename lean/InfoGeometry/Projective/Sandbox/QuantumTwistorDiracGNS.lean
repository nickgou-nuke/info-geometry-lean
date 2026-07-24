import Mathlib

noncomputable section

namespace InfoGeometry.Projective.Sandbox.QuantumTwistorDiracGNS

/-- Binary cylinder words, kept local to this sandbox statement surface. -/
abbrev BinaryWord : Type := List Bool

/-- Complex finite cylinder vectors on binary words. -/
abbrev CylinderVector : Type := BinaryWord →₀ ℂ

/-- A simple positive cylinder weight used by the algebraic pre-inner formula. -/
def gnsCylinderWeight (w : BinaryWord) : ℝ := (2 : ℝ) ^ (-(w.length : ℤ))

/-- Complexified cylinder pre-inner expression on finite vectors.  This is only
an algebraic formula; no Hilbert-space instance is installed. -/
def gnsPreInnerComplex (x y : CylinderVector) : ℂ :=
  x.sum (fun w c => star c * y w * (gnsCylinderWeight w : ℂ))

/-- The diagonal length operator on finite cylinder vectors. -/
def gnsDiracOp (x : CylinderVector) : CylinderVector :=
  x.sum (fun w c => Finsupp.single w (c * (w.length : ℂ)))

/-- Statement shape for the missing analytic GNS/spectral-triple package. -/
def gnsSpectralTripleStatement : Prop :=
  ∃ (norm : CylinderVector → ℝ) (_rep : Type),
    ∀ x : CylinderVector, 0 ≤ norm x

end InfoGeometry.Projective.Sandbox.QuantumTwistorDiracGNS
