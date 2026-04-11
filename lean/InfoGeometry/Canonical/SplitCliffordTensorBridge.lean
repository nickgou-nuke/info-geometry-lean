import InfoGeometry.Canonical.BottPeriodicity
import InfoGeometry.Canonical.ClNNBottBridge
import InfoGeometry.Canonical.KreinDoubledAtom
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Quantum.RealSplitClifford
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace TensorProduct

/-!
# InfoGeometry.Canonical.SplitCliffordTensorBridge

Canonical bridge from the concrete doubled split `Cl(1,1)` atom to the
recursive split `Cl(n,n)` tower already present in `ClNN` and
`BottPeriodicity`.

This file does not introduce a second tensor calculus. It packages the existing
one-step Bott factorization as the repo-native recursive statement:

- the doubled-space atom `⟨1, ε, J, Jε⟩` is the concrete split `Cl(1,1)` head
  factor;
- adjoining that head factor recursively yields the split `Cl(n,n)` tower;
- the `n = 4` specialization is the split `Cl(4,4)` stage used by downstream
  D4 / `Spin(4,4)` files.
-/

namespace InfoGeometry.Canonical.SplitCliffordTensorBridge

open InfoGeometry.Canonical.BottPeriodicity
open InfoGeometry.Canonical.ClNNBottBridge
open InfoGeometry.Clifford.ClNN
open InfoGeometry.CliffordTower

/-- Canonical split `Cl(1,1)` algebra in the split tower. -/
abbrev SplitCl11Alg := CliffordAlgebra InfoGeometry.CliffordTower.Q11

/-- Canonical carrier for the recursive split `Cl(n,n)` tower. -/
@[rep_depth krein] abbrev SplitClNNCarrier (n : ℕ) := Carrier n

/-- Canonical quadratic form for the recursive split `Cl(n,n)` tower. -/
@[rep_depth krein] noncomputable abbrev SplitClNNQuad (n : ℕ) :
    QuadraticForm ℝ (SplitClNNCarrier n) := Quad n

/-- Canonical algebra for the recursive split `Cl(n,n)` tower. -/
@[rep_depth krein] abbrev SplitClNNAlg (n : ℕ) := Alg n

/-- One-step graded tensor target in the split tower. -/
@[rep_depth krein] abbrev SplitClNNTensorStep (n : ℕ) := BottTensor n

section HeadAtom

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Canonical doubled-space realization of the split `Cl(1,1)` head atom. -/
@[rep_depth krein]
noncomputable abbrev doubledHeadAtom :
    InfoGeometry.Canonical.KreinDoubledAtom :=
  InfoGeometry.Canonical.cl11DoubledAtom E

/--
The doubled split `Cl(1,1)` head atom already carries the repo-native
supergraded `⟨1, ε, J, Jε⟩` package before any tensor expansion.
-/
@[rep_depth krein] theorem doubledHeadAtom_supergradedLiePackage :
    InfoGeometry.Krein.isEven (E := E)
        (InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ (E := E)) ∧
      InfoGeometry.Krein.isOdd (E := E)
        (InfoGeometry.Canonical.TomitaTakesaki.modularSignEpsilon (E := E)) ∧
      InfoGeometry.Krein.isOdd (E := E)
        (InfoGeometry.Canonical.TomitaTakesaki.modularComplexI (E := E)) ∧
      (InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ (E := E)).comp
          (InfoGeometry.Canonical.TomitaTakesaki.modularSignEpsilon (E := E))
        + (InfoGeometry.Canonical.TomitaTakesaki.modularSignEpsilon (E := E)).comp
            (InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ (E := E)) = 0 := by
  simpa using
    (InfoGeometry.Canonical.TomitaTakesaki.modularCPT_supergraded_lie_package (E := E))

/--
Owner-name form of the doubled split `Cl(1,1)` supergraded package on the root
`(modular_j, spectral_epsilon, complex_i)` packet.
-/
@[rep_depth krein] theorem doubledHeadAtom_supergradedLiePackage_root :
    InfoGeometry.Krein.isEven (E := E)
        (InfoGeometry.Krein.modular_j (E := E)) ∧
      InfoGeometry.Krein.isOdd (E := E)
        (InfoGeometry.Krein.spectral_epsilon (E := E)) ∧
      InfoGeometry.Krein.isOdd (E := E)
        (InfoGeometry.Krein.complex_i (E := E)) ∧
      (InfoGeometry.Krein.modular_j (E := E)).comp
          (InfoGeometry.Krein.spectral_epsilon (E := E))
        + (InfoGeometry.Krein.spectral_epsilon (E := E)).comp
            (InfoGeometry.Krein.modular_j (E := E)) = 0 := by
  simpa [InfoGeometry.Canonical.TomitaTakesaki.modularConjugationJ_eq_modular_j,
    InfoGeometry.Canonical.TomitaTakesaki.modularSignEpsilon_eq_spectral_epsilon,
    InfoGeometry.Canonical.TomitaTakesaki.modularComplexI_eq_complex_i] using
    (doubledHeadAtom_supergradedLiePackage (E := E))

/--
The canonical doubled-space `J`-generator is exactly the left generator consumed
by the first Bott step.
-/
@[rep_depth krein] theorem doubledHeadAtom_feeds_first_tensorStep_J :
    (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)).J
      = InfoGeometry.Krein.cl11Rep (E := E)
          (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 (1, 0)) ∧
    bottStepEquiv 0
        (CliffordAlgebra.ι (SplitClNNQuad 1) (headPair 0 (1, 0)))
      = (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 (1, 0))
          ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit 0)) := by
  constructor
  · simpa using
      (InfoGeometry.Quantum.doubledSpaceCl11Action_J_eq_cl11Rep_leftGenerator (E := E))
  · simpa [SplitClNNQuad] using
      (bottStep_headPair 0 (1, 0))

/--
The canonical doubled-space `K = Jε` generator is exactly the right generator
consumed by the first Bott step.
-/
@[rep_depth krein] theorem doubledHeadAtom_feeds_first_tensorStep_K :
    (InfoGeometry.Quantum.doubledSpaceCl11Action (E := E)).K
      = InfoGeometry.Krein.cl11Rep (E := E)
          (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 (0, 1)) ∧
    bottStepEquiv 0
        (CliffordAlgebra.ι (SplitClNNQuad 1) (headPair 0 (0, 1)))
      = (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 (0, 1))
          ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit 0)) := by
  constructor
  · simpa using
      (InfoGeometry.Quantum.doubledSpaceCl11Action_K_eq_cl11Rep_rightGenerator (E := E))
  · simpa [SplitClNNQuad] using
      (bottStep_headPair 0 (0, 1))

end HeadAtom

section RecursiveStep

/--
Repo-native recursive split step:
the next split algebra `Cl(n+1,n+1)` factors as one split `Cl(1,1)` head
channel tensored with the previous split `Cl(n,n)` stage.
-/
@[rep_depth krein]
noncomputable abbrev splitCliffordTensorStepEquiv (n : ℕ) :
    SplitClNNAlg (n + 1) ≃ₐ[ℝ] SplitClNNTensorStep n :=
  bottStepEquiv n

@[rep_depth krein] theorem splitCliffordTensorStep_headFactor
    (n : ℕ) (x : ℝ × ℝ) :
    splitCliffordTensorStepEquiv n
        (CliffordAlgebra.ι (SplitClNNQuad (n + 1)) (headPair n x))
      = (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 x)
          ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit n)) := by
  simpa [splitCliffordTensorStepEquiv, SplitClNNQuad] using
    bottStep_headPair n x

@[rep_depth krein] theorem splitCliffordTensorStep_tailFactor
    (n : ℕ) (xs : SplitClNNCarrier n) :
    splitCliffordTensorStepEquiv n
        (CliffordAlgebra.ι (SplitClNNQuad (n + 1)) (tailLift n xs))
      = (1 : CliffordAlgebra InfoGeometry.CliffordTower.Q11)
          ᵍ⊗ₜ (CliffordAlgebra.ι (Qsplit n) xs) := by
  simpa [splitCliffordTensorStepEquiv, SplitClNNQuad] using
    bottStep_tailLift n xs

@[rep_depth krein] theorem splitCliffordTensorStep_headNullMinus
    (n : ℕ) :
    splitCliffordTensorStepEquiv n (gammaHeadNullMinus n)
      = (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 ((1 / 2 : ℝ), (1 / 2 : ℝ)))
          ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit n)) := by
  simpa [splitCliffordTensorStepEquiv] using bottStep_headNullMinus n

@[rep_depth krein] theorem splitCliffordTensorStep_headNullPlus
    (n : ℕ) :
    splitCliffordTensorStepEquiv n (gammaHeadNullPlus n)
      = (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 ((1 / 2 : ℝ), (-(1 / 2 : ℝ))))
          ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit n)) := by
  simpa [splitCliffordTensorStepEquiv] using bottStep_headNullPlus n

end RecursiveStep

section Split44

/-- Canonical split `Cl(4,4)` carrier in the recursive split tower. -/
@[rep_depth krein] abbrev SplitCl44Carrier := SplitClNNCarrier 4

/-- Canonical split quadratic form for the recursive `Cl(4,4)` stage. -/
@[rep_depth krein] noncomputable abbrev SplitCl44Quad :
    QuadraticForm ℝ SplitCl44Carrier := SplitClNNQuad 4

/-- Canonical split `Cl(4,4)` algebra in the recursive split tower. -/
@[rep_depth krein] abbrev SplitCl44Alg := SplitClNNAlg 4

/--
The split `Cl(4,4)` stage is the fourth recursive head-factor step:
one split `Cl(1,1)` channel tensored with the split `Cl(3,3)` remainder.
-/
@[rep_depth krein]
noncomputable abbrev splitCl44_headFactorEquiv :
    SplitCl44Alg ≃ₐ[ℝ] SplitClNNTensorStep 3 :=
  splitCliffordTensorStepEquiv 3

@[rep_depth krein] theorem splitCl44_headFactor
    (x : ℝ × ℝ) :
    splitCl44_headFactorEquiv
        (CliffordAlgebra.ι SplitCl44Quad (headPair 3 x))
      = (CliffordAlgebra.ι InfoGeometry.CliffordTower.Q11 x)
          ᵍ⊗ₜ (1 : CliffordAlgebra (Qsplit 3)) := by
  simpa [splitCl44_headFactorEquiv, SplitCl44Quad] using
    splitCliffordTensorStep_headFactor 3 x

@[rep_depth krein] theorem splitCl44_tailFactor
    (xs : SplitClNNCarrier 3) :
    splitCl44_headFactorEquiv
        (CliffordAlgebra.ι SplitCl44Quad (tailLift 3 xs))
      = (1 : CliffordAlgebra InfoGeometry.CliffordTower.Q11)
          ᵍ⊗ₜ (CliffordAlgebra.ι (Qsplit 3) xs) := by
  simpa [splitCl44_headFactorEquiv, SplitCl44Quad] using
    splitCliffordTensorStep_tailFactor 3 xs

end Split44

end InfoGeometry.Canonical.SplitCliffordTensorBridge
