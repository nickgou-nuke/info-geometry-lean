import InfoGeometry.Quantum.RealMajoranaCategory
import InfoGeometry.Canonical.TomitaTakesaki
import InfoGeometry.Krein.ExponentialIsometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement

set_option linter.unusedSectionVars false

namespace InfoGeometry.Quantum.ModularAnomaly

open InfoGeometry.Krein

open InfoGeometry.Quantum.RealMajoranaCategory

/--
Topological refinement of the real-Majorana modular shadow.
Requires a normed carrier to support differential calculus on endomorphisms.
-/
structure TopologicalMajoranaShadow
    (X : RealMajoranaCore)
    [NormedAddCommGroup X] [NormedSpace ℝ X] where
  sigma : ℝ → X ≃L[ℝ] X
  sigma_zero : sigma 0 = ContinuousLinearEquiv.refl ℝ X
  sigma_add : ∀ t s, sigma (t + s) = (sigma t).trans (sigma s)
  J_conj_sigma :
    ∀ t x, X.J ((sigma t) x) = (sigma (-t)) (X.J x)

namespace TopologicalMajoranaShadow

variable {X : RealMajoranaCore}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

variable (M : TopologicalMajoranaShadow X)

/-- Continuous Connes cocycle shadow `u_t(U) = U⁻¹ σ_t U σ_{-t}`. -/
noncomputable def modularCocycle (U : X ≃L[ℝ] X) (t : ℝ) : X →L[ℝ] X :=
  (U.symm : X →L[ℝ] X).comp
    (((M.sigma t : X →L[ℝ] X).comp
      ((U : X →L[ℝ] X).comp (M.sigma (-t) : X →L[ℝ] X))))

/-- A symmetry is anomaly-free when the cocycle is identically the identity. -/
def IsAnomalyFree (U : X ≃L[ℝ] X) : Prop :=
  ∀ t : ℝ, modularCocycle M U t = ContinuousLinearMap.id ℝ X

/-- Infinitesimal anomaly generator at `t = 0`. -/
noncomputable def modularAnomalyGenerator (U : X ≃L[ℝ] X) : X →L[ℝ] X :=
  deriv (fun t => modularCocycle M U t) 0

lemma sigma_zero_clm : (M.sigma 0 : X →L[ℝ] X) = ContinuousLinearMap.id ℝ X := by
  simpa using congrArg (fun e : X ≃L[ℝ] X => (e : X →L[ℝ] X)) M.sigma_zero

lemma modularCocycle_zero (U : X ≃L[ℝ] X) :
    modularCocycle M U 0 = ContinuousLinearMap.id ℝ X := by
  ext x
  simp [modularCocycle, sigma_zero_clm (M := M)]

theorem hasDerivAt_modularCocycle_inner
    (U : X ≃L[ℝ] X)
    (σGen : X →L[ℝ] X)
  (hSigma : HasDerivAt (fun t => (M.sigma t : X →L[ℝ] X)) σGen 0)
  (hSigmaNeg : HasDerivAt (fun t => (M.sigma (-t) : X →L[ℝ] X)) (-σGen) 0) :
    HasDerivAt
      (fun t => (M.sigma t : X →L[ℝ] X).comp
        ((U : X →L[ℝ] X).comp (M.sigma (-t) : X →L[ℝ] X)))
      (σGen.comp (U : X →L[ℝ] X) - (U : X →L[ℝ] X).comp σGen)
      0 := by
  have hRight :
      HasDerivAt
        (fun t => (U : X →L[ℝ] X).comp (M.sigma (-t) : X →L[ℝ] X))
        ((U : X →L[ℝ] X).comp (-σGen))
        0 := by
    simpa using (hasDerivAt_const (0 : ℝ) (U : X →L[ℝ] X)).clm_comp hSigmaNeg
  have hComp := hSigma.clm_comp hRight
  simpa [sigma_zero_clm (M := M), sub_eq_add_neg, ContinuousLinearMap.comp_assoc] using hComp

section BridgeTheorem

variable (U : X ≃L[ℝ] X)
variable (σGen : X →L[ℝ] X)

/--
Bridge theorem: the modular anomaly generator equals the commutator shadow.
-/
theorem modularAnomalyGenerator_eq_commutator_shadow :
    (hSigma : HasDerivAt (fun t => (M.sigma t : X →L[ℝ] X)) σGen 0) →
    (hSigmaNeg : HasDerivAt (fun t => (M.sigma (-t) : X →L[ℝ] X)) (-σGen) 0) →
    M.modularAnomalyGenerator U =
      (U.symm : X →L[ℝ] X).comp
        (σGen.comp (U : X →L[ℝ] X) - (U : X →L[ℝ] X).comp σGen) := by
  intro hSigma hSigmaNeg
  unfold modularAnomalyGenerator
  have hInner :
      HasDerivAt
        (fun t => (M.sigma t : X →L[ℝ] X).comp
          ((U : X →L[ℝ] X).comp (M.sigma (-t) : X →L[ℝ] X)))
        (σGen.comp (U : X →L[ℝ] X) - (U : X →L[ℝ] X).comp σGen)
        0 :=
    hasDerivAt_modularCocycle_inner (M := M) U σGen hSigma hSigmaNeg
  have hFull :
      HasDerivAt
        (fun t => modularCocycle M U t)
        ((U.symm : X →L[ℝ] X).comp
          (σGen.comp (U : X →L[ℝ] X) - (U : X →L[ℝ] X).comp σGen))
        0 := by
    simpa [modularCocycle] using
      (hasDerivAt_const (0 : ℝ) (U.symm : X →L[ℝ] X)).clm_comp hInner
  simpa using hFull.deriv

end BridgeTheorem

section RosettaBridge

variable (U : X ≃L[ℝ] X)
variable (σGen : X →L[ℝ] X)

/--
Unified anomaly bridge: modular cocycle generator equals the commutator-shadow form.
This is the reusable transport-facing theorem surface for anomaly identifications.
-/
theorem unified_anomaly_bridge
    (hFlow : HasDerivAt (fun t => (M.sigma t : X →L[ℝ] X)) σGen 0)
    (hFlowNeg : HasDerivAt (fun t => (M.sigma (-t) : X →L[ℝ] X)) (-σGen) 0) :
    M.modularAnomalyGenerator U =
      (U.symm : X →L[ℝ] X).comp
        (σGen.comp (U : X →L[ℝ] X) - (U : X →L[ℝ] X).comp σGen) := by
  unfold TopologicalMajoranaShadow.modularAnomalyGenerator
  have hInner :
      HasDerivAt
        (fun t => (M.sigma t : X →L[ℝ] X).comp
          ((U : X →L[ℝ] X).comp (M.sigma (-t) : X →L[ℝ] X)))
        (σGen.comp (U : X →L[ℝ] X) - (U : X →L[ℝ] X).comp σGen)
        0 :=
    hasDerivAt_modularCocycle_inner (M := M) U σGen hFlow hFlowNeg
  have hFull :
      HasDerivAt
        (fun t => TopologicalMajoranaShadow.modularCocycle M U t)
        ((U.symm : X →L[ℝ] X).comp
          (σGen.comp (U : X →L[ℝ] X) - (U : X →L[ℝ] X).comp σGen))
        0 := by
    simpa [TopologicalMajoranaShadow.modularCocycle] using
      (hasDerivAt_const (0 : ℝ) (U.symm : X →L[ℝ] X)).clm_comp hInner
  simpa using hFull.deriv

/--
Projector-mismatch specialization of the unified bridge.
When the flow generator is a transported commutator source `(P_mp ∘ P_d - P_d ∘ P_mp)`,
the modular anomaly generator is exactly its conjugated commutator shadow.
-/
theorem einstein_anomaly_is_modular_generator
    (P_mp P_d : X →L[ℝ] X)
    (hFlow : HasDerivAt (fun t => (M.sigma t : X →L[ℝ] X)) σGen 0)
    (hFlowNeg : HasDerivAt (fun t => (M.sigma (-t) : X →L[ℝ] X)) (-σGen) 0)
    (hGen : σGen = (P_mp.comp P_d - P_d.comp P_mp)) :
    M.modularAnomalyGenerator U =
      (U.symm : X →L[ℝ] X).comp
        ((P_mp.comp P_d - P_d.comp P_mp).comp (U : X →L[ℝ] X)
          - (U : X →L[ℝ] X).comp (P_mp.comp P_d - P_d.comp P_mp)) := by
  subst hGen
  exact unified_anomaly_bridge
    (M := M) (U := U) (σGen := (P_mp.comp P_d - P_d.comp P_mp)) hFlow hFlowNeg

end RosettaBridge

end TopologicalMajoranaShadow

namespace Cl11Shadow

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open InfoGeometry.Canonical.TomitaTakesaki

local notation "Xc" => (cl11DoubledCore E)

noncomputable local instance : NormedAddCommGroup Xc := by
  change NormedAddCommGroup (InfoGeometry.Krein.DoubledSpace E)
  infer_instance

noncomputable local instance : NormedSpace ℝ Xc := by
  change NormedSpace ℝ (InfoGeometry.Krein.DoubledSpace E)
  infer_instance

noncomputable local instance : InnerProductSpace ℝ Xc := by
  change InnerProductSpace ℝ (InfoGeometry.Krein.DoubledSpace E)
  infer_instance

noncomputable local instance : CompleteSpace Xc := by
  change CompleteSpace (InfoGeometry.Krein.DoubledSpace E)
  infer_instance

noncomputable local instance : KreinSpace Xc := by
  change KreinSpace (InfoGeometry.Krein.DoubledSpace E)
  infer_instance

noncomputable local instance : NormedRing (Xc →L[ℝ] Xc) := inferInstance
noncomputable local instance : NormedAlgebra ℝ (Xc →L[ℝ] Xc) := inferInstance
noncomputable local instance : CompleteSpace (Xc →L[ℝ] Xc) := by
  infer_instance

local instance : IsTopologicalRing (Xc →L[ℝ] Xc) := inferInstance

noncomputable local instance :
    NormedRing
      (InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E) := inferInstance
noncomputable local instance :
    NormedAlgebra ℝ
      (InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E) := inferInstance
noncomputable local instance :
    CompleteSpace
      (InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E) := by
  infer_instance

local instance :
    IsTopologicalRing
      (InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E) := inferInstance

noncomputable abbrev IdCLM : Xc →L[ℝ] Xc :=
  ContinuousLinearMap.id ℝ Xc

/--
Single-parameter exponential carrier automorphism generated by `σGen`.
-/
noncomputable def expFlow (σGen : Xc →L[ℝ] Xc) (t : ℝ) : Xc ≃L[ℝ] Xc :=
  InfoGeometry.Krein.expAutomorphism (A := σGen) t

@[simp] theorem expFlow_toContinuousLinearMap
    (σGen : Xc →L[ℝ] Xc) (t : ℝ) :
    ((expFlow σGen t : Xc ≃L[ℝ] Xc) : Xc →L[ℝ] Xc) = NormedSpace.exp (t • σGen) :=
  InfoGeometry.Krein.expAutomorphism_toContinuousLinearMap (A := σGen) t

@[simp] theorem expFlow_zero
    (σGen : Xc →L[ℝ] Xc) :
    expFlow σGen 0 = ContinuousLinearEquiv.refl ℝ Xc := by
  ext x
  change (NormedSpace.exp (0 • σGen)) x = x
  simp

/--
Additive-time law for the exponential carrier flow generated by `σGen`.
-/
theorem expFlow_add
    (σGen : Xc →L[ℝ] Xc) (t s : ℝ) :
    expFlow σGen (t + s) = (expFlow σGen t).trans (expFlow σGen s) := by
  ext x
  have hComm : Commute (s • σGen) (t • σGen) :=
    ((Commute.refl σGen).smul_left s).smul_right t
  have hExp :
      NormedSpace.exp ((t + s) • σGen) =
        NormedSpace.exp (s • σGen) * NormedSpace.exp (t • σGen) := by
    calc
      NormedSpace.exp ((t + s) • σGen)
          = NormedSpace.exp ((s + t) • σGen) := by simp [add_comm]
      _ = NormedSpace.exp (s • σGen + t • σGen) := by simp [add_smul]
      _ = NormedSpace.exp (s • σGen) * NormedSpace.exp (t • σGen) := by
            rw [NormedSpace.exp_add_of_commute hComm]
  change (NormedSpace.exp ((t + s) • σGen)) x =
    ((NormedSpace.exp (s • σGen)).comp (NormedSpace.exp (t • σGen))) x
  rw [hExp]
  rfl

/--
Exponential topological Majorana shadow generated by `σGen`.

The only extra datum needed beyond exponentiation is the `J`-compatibility
law expressing the modular symmetry relation at the carrier level.
-/
noncomputable def topologicalShadowOfExp
    (σGen : Xc →L[ℝ] Xc)
    (hJConj :
      ∀ t x,
        (cl11DoubledCore E).J ((expFlow σGen t) x) =
          (expFlow σGen (-t)) ((cl11DoubledCore E).J x)) :
    TopologicalMajoranaShadow Xc where
  sigma := expFlow σGen
  sigma_zero := expFlow_zero σGen
  sigma_add := expFlow_add σGen
  J_conj_sigma := hJConj

/--
Exponential single-parameter modular flow:
for the shadow generated by `σGen`, the modular anomaly generator is the
expected commutator shadow.
-/
theorem modularAnomalyGenerator_eq_exp_commutator_shadow
    (σGen : Xc →L[ℝ] Xc)
    (hJConj :
      ∀ t x,
        (cl11DoubledCore E).J ((expFlow σGen t) x) =
          (expFlow σGen (-t)) ((cl11DoubledCore E).J x))
    (U : Xc ≃L[ℝ] Xc) :
    (topologicalShadowOfExp σGen hJConj).modularAnomalyGenerator U =
      (U.symm : Xc →L[ℝ] Xc).comp
        (σGen.comp (U : Xc →L[ℝ] Xc) - (U : Xc →L[ℝ] Xc).comp σGen) := by
  unfold TopologicalMajoranaShadow.modularAnomalyGenerator
  have hSigma :
      HasDerivAt
        (fun t => ((topologicalShadowOfExp σGen hJConj).sigma t : Xc →L[ℝ] Xc))
        σGen
        0 := by
    simpa [topologicalShadowOfExp, expFlow] using
      (hasDerivAt_exp_smul_const (x := σGen) (t := (0 : ℝ)))
  have hSigmaNeg :
      HasDerivAt
        (fun t => ((topologicalShadowOfExp σGen hJConj).sigma (-t) : Xc →L[ℝ] Xc))
        (-σGen)
        0 := by
    have hBase :
        HasDerivAt (fun t : ℝ => NormedSpace.exp (t • σGen)) σGen 0 := by
      simpa using (hasDerivAt_exp_smul_const (x := σGen) (t := (0 : ℝ)))
    have hBase' :
        HasDerivAt (fun t : ℝ => NormedSpace.exp (t • σGen)) σGen ((0 : ℝ) - 0) := by
      simpa using hBase
    have hShift :
        HasDerivAt
          (fun t : ℝ => (fun u : ℝ => NormedSpace.exp (u • σGen)) ((0 : ℝ) - t))
          (-σGen)
          0 :=
      HasDerivAt.comp_const_sub
        (f := fun u : ℝ => NormedSpace.exp (u • σGen))
        (a := (0 : ℝ))
        (x := (0 : ℝ))
        hBase'
    simpa [topologicalShadowOfExp, expFlow, zero_sub, neg_smul] using hShift
  have hInner :
      HasDerivAt
        (fun t =>
          ((topologicalShadowOfExp σGen hJConj).sigma t : Xc →L[ℝ] Xc).comp
            ((U : Xc →L[ℝ] Xc).comp
              ((topologicalShadowOfExp σGen hJConj).sigma (-t) : Xc →L[ℝ] Xc)))
        (σGen.comp (U : Xc →L[ℝ] Xc) - (U : Xc →L[ℝ] Xc).comp σGen)
        0 :=
    TopologicalMajoranaShadow.hasDerivAt_modularCocycle_inner
      (M := topologicalShadowOfExp σGen hJConj)
      (U := U)
      (σGen := σGen)
      hSigma
      hSigmaNeg
  have hFull :
      HasDerivAt
        (fun t => TopologicalMajoranaShadow.modularCocycle (topologicalShadowOfExp σGen hJConj) U t)
        ((U.symm : Xc →L[ℝ] Xc).comp
          (σGen.comp (U : Xc →L[ℝ] Xc) - (U : Xc →L[ℝ] Xc).comp σGen))
        0 := by
    simpa [TopologicalMajoranaShadow.modularCocycle] using
      (hasDerivAt_const (0 : ℝ) (U.symm : Xc →L[ℝ] Xc)).clm_comp hInner
  simpa using hFull.deriv

/--
Canonical `Cl(1,1)` exponential generator: the modular sign involution `ε`.
-/
noncomputable abbrev canonicalCl11Generator : Xc →L[ℝ] Xc :=
  modularSignEpsilon (E := E)

/--
For the distinguished `Cl(1,1)` generator `ε`, the exponential flow satisfies
the required Majorana modular symmetry law.
-/
theorem canonicalCl11Generator_J_conj_expFlow
    (t : ℝ) (x : Xc) :
    (cl11DoubledCore E).J ((expFlow (canonicalCl11Generator (E := E)) t) x) =
      (expFlow (canonicalCl11Generator (E := E)) (-t)) ((cl11DoubledCore E).J x) := by
  have hExp :
      (modularConjugationJ (E := E)) *
          NormedSpace.exp (t • (modularSignEpsilon (E := E))) *
          (modularConjugationJ (E := E)) =
        NormedSpace.exp ((-t) • (modularSignEpsilon (E := E))) :=
    modularConjugationJ_exp_modularSignEpsilon (E := E) t
  have hJJ :
      (InfoGeometry.Krein.modular_j (E := E))
        ((InfoGeometry.Krein.modular_j (E := E)) x) = x := by
    change (((InfoGeometry.Krein.modular_j (E := E)).comp
      (InfoGeometry.Krein.modular_j (E := E))) x) = x
    convert
      congrArg
        (fun f : InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E => f x)
        (InfoGeometry.Krein.modular_j_involution E) using 1
  have hApply := congrArg
    (fun A : InfoGeometry.Krein.DoubledSpace E →L[ℝ] InfoGeometry.Krein.DoubledSpace E =>
      A (InfoGeometry.Krein.modular_j (E := E) x))
    hExp
  change (cl11DoubledCore E).J
      ((((expFlow (canonicalCl11Generator (E := E)) t : Xc ≃L[ℝ] Xc) : Xc →L[ℝ] Xc) x)) =
    (((expFlow (canonicalCl11Generator (E := E)) (-t) : Xc ≃L[ℝ] Xc) : Xc →L[ℝ] Xc)
      ((cl11DoubledCore E).J x))
  rw [expFlow_toContinuousLinearMap, expFlow_toContinuousLinearMap]
  simpa [canonicalCl11Generator, cl11DoubledCore, ContinuousLinearMap.comp_apply, hJJ] using hApply

/--
Canonical exponential topological Majorana shadow generated by the `Cl(1,1)`
modular sign involution `ε`.
-/
noncomputable def canonicalCl11TopologicalShadow :
    TopologicalMajoranaShadow Xc :=
  { sigma := expFlow (canonicalCl11Generator (E := E))
    sigma_zero := expFlow_zero (canonicalCl11Generator (E := E))
    sigma_add := expFlow_add (canonicalCl11Generator (E := E))
    J_conj_sigma := canonicalCl11Generator_J_conj_expFlow (E := E) }

/--
Canonical `Cl(1,1)` specialization of the exponential modular anomaly bridge.
-/
theorem modularAnomalyGenerator_eq_canonicalCl11_commutator_shadow
    (U : Xc ≃L[ℝ] Xc) :
    (canonicalCl11TopologicalShadow (E := E)).modularAnomalyGenerator U =
      (U.symm : Xc →L[ℝ] Xc).comp
        ((canonicalCl11Generator (E := E)).comp (U : Xc →L[ℝ] Xc)
          - (U : Xc →L[ℝ] Xc).comp (canonicalCl11Generator (E := E))) := by
  apply TopologicalMajoranaShadow.modularAnomalyGenerator_eq_commutator_shadow
    (M := canonicalCl11TopologicalShadow (E := E))
    (U := U)
    (σGen := canonicalCl11Generator (E := E))
  · simpa [canonicalCl11TopologicalShadow, canonicalCl11Generator, expFlow] using
      (hasDerivAt_exp_smul_const
        (x := canonicalCl11Generator (E := E))
        (t := (0 : ℝ)))
  · have hBase :
        HasDerivAt
          (fun t : ℝ => NormedSpace.exp (t • (canonicalCl11Generator (E := E))))
          (canonicalCl11Generator (E := E))
          0 := by
        simpa using
          (hasDerivAt_exp_smul_const
            (x := canonicalCl11Generator (E := E))
            (t := (0 : ℝ)))
    have hBase' :
        HasDerivAt
          (fun t : ℝ => NormedSpace.exp (t • (canonicalCl11Generator (E := E))))
          (canonicalCl11Generator (E := E))
          ((0 : ℝ) - 0) := by
      simpa using hBase
    have hNeg :
        HasDerivAt
          (fun t : ℝ =>
            NormedSpace.exp (((0 : ℝ) - t) • (canonicalCl11Generator (E := E))))
          (-(canonicalCl11Generator (E := E)))
          0 :=
      HasDerivAt.comp_const_sub
        (f := fun u : ℝ => NormedSpace.exp (u • (canonicalCl11Generator (E := E))))
        (a := (0 : ℝ))
        (x := (0 : ℝ))
        hBase'
    simpa [canonicalCl11TopologicalShadow, canonicalCl11Generator, expFlow, zero_sub, neg_smul] using hNeg

/-- Hyperbolic shadow flow generated by an involution `epsCLM`. -/
noncomputable def sigmaMap (epsCLM : Xc →L[ℝ] Xc) (t : ℝ) : Xc →L[ℝ] Xc :=
  (((Real.cosh t : ℝ) • (IdCLM : Xc →L[ℝ] Xc) : Xc →L[ℝ] Xc)
    + ((Real.sinh t : ℝ) • (epsCLM : Xc →L[ℝ] Xc) : Xc →L[ℝ] Xc))

private lemma smul_pow_even_of_sq_eq_id
    (epsCLM : Xc →L[ℝ] Xc)
    (hSq : epsCLM.comp epsCLM = ContinuousLinearMap.id ℝ Xc)
    (t : ℝ) :
    ∀ n : ℕ, (t • epsCLM) ^ (2 * n) = (t ^ (2 * n)) • (1 : Xc →L[ℝ] Xc)
  | 0 => by simp
  | n + 1 => by
      have hSq' : epsCLM * epsCLM = (1 : Xc →L[ℝ] Xc) := by
        simpa using hSq
      have hpow2 : (t • epsCLM) ^ 2 = (t ^ 2) • (1 : Xc →L[ℝ] Xc) := by
        rw [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul, hSq']
        simp [pow_two]
      calc
        (t • epsCLM) ^ (2 * (n + 1))
            = (t • epsCLM) ^ (2 * n) * (t • epsCLM) ^ 2 := by
                rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
        _ = ((t ^ (2 * n)) • (1 : Xc →L[ℝ] Xc)) * ((t ^ 2) • (1 : Xc →L[ℝ] Xc)) := by
              rw [smul_pow_even_of_sq_eq_id epsCLM hSq t n, hpow2]
        _ = (t ^ (2 * (n + 1))) • (1 : Xc →L[ℝ] Xc) := by
              rw [smul_mul_assoc, mul_smul_comm, smul_smul, one_mul]
              rw [← pow_add]
              simp [show 2 * (n + 1) = 2 * n + 2 by omega]

private lemma smul_pow_odd_of_sq_eq_id
    (epsCLM : Xc →L[ℝ] Xc)
    (hSq : epsCLM.comp epsCLM = ContinuousLinearMap.id ℝ Xc)
    (t : ℝ) (n : ℕ) :
    (t • epsCLM) ^ (2 * n + 1) = (t ^ (2 * n + 1)) • epsCLM := by
  calc
    (t • epsCLM) ^ (2 * n + 1)
        = (t • epsCLM) ^ (2 * n) * (t • epsCLM) := by
            rw [pow_succ]
    _ = ((t ^ (2 * n)) • (1 : Xc →L[ℝ] Xc)) * (t • epsCLM) := by
          rw [smul_pow_even_of_sq_eq_id epsCLM hSq t n]
    _ = (t ^ (2 * n + 1)) • epsCLM := by
          rw [smul_mul_assoc, one_mul, smul_smul]
          simp [pow_succ]

/--
If a generator squares to the identity, its exponential flow collapses to the
hyperbolic split form `cosh(t) Id + sinh(t) ε`.
-/
theorem expFlow_eq_sigmaMap_of_sq_eq_id
    (epsCLM : Xc →L[ℝ] Xc)
    (hSq : epsCLM.comp epsCLM = ContinuousLinearMap.id ℝ Xc)
    (t : ℝ) :
    ((expFlow epsCLM t : Xc ≃L[ℝ] Xc) : Xc →L[ℝ] Xc) = sigmaMap epsCLM t := by
  rw [expFlow_toContinuousLinearMap, NormedSpace.exp_eq_tsum ℝ]
  have hsum :
      HasSum
        (fun n : ℕ => ((Nat.factorial n : ℕ) : ℝ)⁻¹ • (t • epsCLM) ^ n)
        (((Real.cosh t : ℝ) • (IdCLM : Xc →L[ℝ] Xc))
          + ((Real.sinh t : ℝ) • epsCLM)) := by
    refine HasSum.even_add_odd ?_ ?_
    · convert (Real.hasSum_cosh t).smul_const (IdCLM : Xc →L[ℝ] Xc) using 1
      ext n
      rw [smul_pow_even_of_sq_eq_id epsCLM hSq t n]
      simp [div_eq_mul_inv, smul_smul, mul_comm]
    · convert (Real.hasSum_sinh t).smul_const epsCLM using 1
      ext n
      rw [smul_pow_odd_of_sq_eq_id epsCLM hSq t n]
      simp [div_eq_mul_inv, smul_smul, mul_comm]
  simpa [sigmaMap, IdCLM] using hsum.tsum_eq

/--
For modular conjugation `J`, the analytic exponential flow agrees exactly with
the hyperbolic shadow `sigmaMap J`.
-/
theorem expFlow_modularConjugationJ_eq_sigmaMap
    (t : ℝ) :
    ((expFlow (modularConjugationJ (E := E)) t : Xc ≃L[ℝ] Xc) : Xc →L[ℝ] Xc) =
      sigmaMap (modularConjugationJ (E := E)) t := by
  exact expFlow_eq_sigmaMap_of_sq_eq_id
    (epsCLM := modularConjugationJ (E := E))
    (hSq := modularConjugationJ_sq (E := E))
    (t := t)

lemma hasDerivAt_sigmaMap_zero (epsCLM : Xc →L[ℝ] Xc) :
    HasDerivAt (fun t => sigmaMap epsCLM t) epsCLM 0 := by
  have h1 : HasDerivAt
      (fun t : ℝ => ((Real.cosh t : ℝ) • (IdCLM : Xc →L[ℝ] Xc) : Xc →L[ℝ] Xc))
      (((Real.sinh 0 : ℝ) • (IdCLM : Xc →L[ℝ] Xc) : Xc →L[ℝ] Xc))
      0 := by
    simpa using (Real.hasDerivAt_cosh 0).smul_const (IdCLM : Xc →L[ℝ] Xc)
  have h2 : HasDerivAt
      (fun t : ℝ => ((Real.sinh t : ℝ) • (epsCLM : Xc →L[ℝ] Xc) : Xc →L[ℝ] Xc))
      (((Real.cosh 0 : ℝ) • (epsCLM : Xc →L[ℝ] Xc) : Xc →L[ℝ] Xc))
      0 := by
    simpa using (Real.hasDerivAt_sinh 0).smul_const (epsCLM : Xc →L[ℝ] Xc)
  simpa [sigmaMap, Real.sinh_zero, Real.cosh_zero, zero_smul, one_smul, zero_add] using h1.add h2

lemma hasDerivAt_sigmaMap_neg_zero (epsCLM : Xc →L[ℝ] Xc) :
    HasDerivAt (fun t => sigmaMap epsCLM (-t)) (-epsCLM) 0 := by
  have heq : (fun t : ℝ => sigmaMap epsCLM (-t))
      = fun t => (Real.cosh t) • IdCLM + (-Real.sinh t) • epsCLM := by
    ext t
    simp [sigmaMap, Real.cosh_neg, Real.sinh_neg, neg_smul]
  rw [heq]
  have h1 : HasDerivAt
      (fun t : ℝ => ((Real.cosh t : ℝ) • (IdCLM : Xc →L[ℝ] Xc) : Xc →L[ℝ] Xc))
      (((Real.sinh 0 : ℝ) • (IdCLM : Xc →L[ℝ] Xc) : Xc →L[ℝ] Xc))
      0 := by
    simpa using (Real.hasDerivAt_cosh 0).smul_const (IdCLM : Xc →L[ℝ] Xc)
  have h2 : HasDerivAt (fun t : ℝ => -Real.sinh t) (-1) 0 := by
    simpa using (Real.hasDerivAt_sinh 0).neg
  have h2' : HasDerivAt (fun t : ℝ => (-Real.sinh t) • epsCLM) ((-1 : ℝ) • epsCLM) 0 := by
    simpa using h2.smul_const (epsCLM : Xc →L[ℝ] Xc)
  simpa [Real.sinh_zero, Real.cosh_zero, zero_smul, one_smul, zero_add, neg_smul] using h1.add h2'

/--
Concrete bridge wiring: if a shadow's flow realizes `sigmaMap epsCLM`,
its modular anomaly generator is the expected commutator shadow with `epsCLM`.
-/
theorem modularAnomalyGenerator_eq_concrete_commutator_shadow
    (M : TopologicalMajoranaShadow Xc)
    (epsCLM : Xc →L[ℝ] Xc)
    (hSigmaMap : ∀ t : ℝ, (M.sigma t : Xc →L[ℝ] Xc) = sigmaMap epsCLM t)
    (U : Xc ≃L[ℝ] Xc) :
    M.modularAnomalyGenerator U =
      (U.symm : Xc →L[ℝ] Xc).comp
        (epsCLM.comp (U : Xc →L[ℝ] Xc) - (U : Xc →L[ℝ] Xc).comp epsCLM) := by
  apply TopologicalMajoranaShadow.modularAnomalyGenerator_eq_commutator_shadow
    (M := M) (U := U) (σGen := epsCLM)
  · simpa [hSigmaMap] using hasDerivAt_sigmaMap_zero epsCLM
  · simpa [hSigmaMap] using hasDerivAt_sigmaMap_neg_zero epsCLM

end Cl11Shadow

namespace Lattice

variable {N : ℕ}

/-- Constant scalar block on `Fin N`. -/
def scalarBlock (r : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal fun _ => r

lemma scalarBlock_eq_smul_one (r : ℝ) :
    scalarBlock (N := N) r = r • (1 : Matrix (Fin N) (Fin N) ℝ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [scalarBlock]
  · simp [scalarBlock, hij]

noncomputable def constInvertible (r : ℝ) [Invertible r] : Invertible (fun _ : Fin N => r) where
  invOf := fun _ => ⅟r
  invOf_mul_self := by
    funext i
    simp
  mul_invOf_self := by
    funext i
    simp

noncomputable def scalarBlockInvertible (r : ℝ) [Invertible r] :
    Invertible (scalarBlock (N := N) r) := by
  letI := constInvertible (N := N) r
  simpa [scalarBlock] using (Matrix.diagonalInvertible (fun _ : Fin N => r))


/--
The finite-dimensional chiral grading operator ε.
On `Fin N ⊕ Fin N`, it acts as `+1` on the left movers and `-1` on the right movers.
-/
def epsMatrix : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  Matrix.fromBlocks
    (1 : Matrix (Fin N) (Fin N) ℝ)
    (0 : Matrix (Fin N) (Fin N) ℝ)
    (0 : Matrix (Fin N) (Fin N) ℝ)
    (-(1 : Matrix (Fin N) (Fin N) ℝ))

/--
A lattice Bogoliubov transformation preserves CAR iff it is orthogonal in dimension `2N`.
-/
def IsBogoliubov (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) : Prop :=
  U * Matrix.transpose U = 1 ∧ Matrix.transpose U * U = 1

/-- Finite-dimensional anomaly generator `[ε, U]`. -/
def latticeAnomalyCommutator
    (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  epsMatrix * U - U * epsMatrix

/-- Block components of `U = [A B; C D]`. -/
def blockA (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.toBlocks₁₁ U

def blockB (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.toBlocks₁₂ U

def blockC (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.toBlocks₂₁ U

def blockD (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.toBlocks₂₂ U

lemma matrix_eq_fromBlocks (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) :
    U = Matrix.fromBlocks (blockA U) (blockB U) (blockC U) (blockD U) := by
  exact Matrix.ext_iff_blocks.mpr ⟨rfl, rfl, rfl, rfl⟩

/--
Block form of the chiral commutator:
`[ε,U] = [0, 2B; -2C, 0]`.
-/
theorem latticeAnomalyCommutator_eq_blocks
    (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) :
    latticeAnomalyCommutator U =
      Matrix.fromBlocks
        (0 : Matrix (Fin N) (Fin N) ℝ)
        ((2 : ℝ) • blockB U)
        ((-2 : ℝ) • blockC U)
        (0 : Matrix (Fin N) (Fin N) ℝ) := by
  unfold latticeAnomalyCommutator epsMatrix
  rw [matrix_eq_fromBlocks U]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks_multiply, sub_eq_add_neg, two_smul, blockA, blockB, blockC, blockD]

/--
Anomaly-free iff the off-diagonal Bogoliubov blocks vanish.
-/
theorem latticeAnomalyCommutator_eq_zero_iff_blocks_zero
    (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) :
    latticeAnomalyCommutator U = 0 ↔ blockB U = 0 ∧ blockC U = 0 := by
  constructor
  · intro hAnomaly
    have hComm :
        Matrix.fromBlocks
            (0 : Matrix (Fin N) (Fin N) ℝ)
            ((2 : ℝ) • blockB U)
            ((-2 : ℝ) • blockC U)
            (0 : Matrix (Fin N) (Fin N) ℝ)
          = (0 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) := by
      rw [← latticeAnomalyCommutator_eq_blocks]
      exact hAnomaly
    have hB : blockB U = 0 := by
      ext i j
      have hij := congrArg
        (fun M : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ => M (Sum.inl i) (Sum.inr j))
        hComm
      change (2 : ℝ) * blockB U i j = 0 at hij
      exact (mul_eq_zero.mp hij).resolve_left two_ne_zero
    have hC : blockC U = 0 := by
      ext i j
      have hij := congrArg
        (fun M : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ => M (Sum.inr i) (Sum.inl j))
        hComm
      change (-2 : ℝ) * blockC U i j = 0 at hij
      have h2 : (2 : ℝ) * blockC U i j = 0 := by linarith [hij]
      exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
    exact ⟨hB, hC⟩
  · rintro ⟨hB, hC⟩
    rw [latticeAnomalyCommutator_eq_blocks, hB, hC]
    simp

/--
`(1,1)` orthogonality block from `Uᵀ U = 1`:
`Aᵀ A + Cᵀ C = 1`.
-/
lemma bogoliubov_ortho_blocks_11
    (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ)
    (hU : IsBogoliubov U) :
  Matrix.transpose (blockA U) * blockA U + Matrix.transpose (blockC U) * blockC U = 1 := by
  have h11 :
      Matrix.toBlocks₁₁ (Matrix.transpose U * U)
        = Matrix.toBlocks₁₁ (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) :=
    congrArg
      (fun M : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ => Matrix.toBlocks₁₁ M)
      hU.right
  rw [matrix_eq_fromBlocks U] at h11
  have h11' :
      Matrix.transpose (blockA U) * blockA U + Matrix.transpose (blockC U) * blockC U
        = Matrix.toBlocks₁₁ (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) := by
    simpa [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, blockA, blockB, blockC, blockD,
      Matrix.toBlocks_fromBlocks₁₁] using h11
  have hOne :
      Matrix.toBlocks₁₁ (1 : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ)
        = (1 : Matrix (Fin N) (Fin N) ℝ) := by
    ext i j
    simp [Matrix.toBlocks₁₁, Matrix.one_apply]
  exact h11'.trans hOne

/--
In the anomaly-free case, the `A` block is orthogonal.
-/
theorem anomaly_free_blockA_is_orthogonal
    (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ)
    (hU : IsBogoliubov U)
    (hAnomaly : latticeAnomalyCommutator U = 0) :
  Matrix.transpose (blockA U) * blockA U = 1 := by
  have h11 := bogoliubov_ortho_blocks_11 U hU
  have hCzero : blockC U = 0 :=
    (latticeAnomalyCommutator_eq_zero_iff_blocks_zero U).mp hAnomaly |>.right
  rw [hCzero] at h11
  simpa [Matrix.transpose_zero, Matrix.zero_mul, add_zero] using h11

/--
Concrete lattice hyperbolic boost shadow on `Fin N ⊕ Fin N`.
This mixes the two chiral sectors with `sinh t` off-diagonal blocks.
-/
noncomputable def sigmaMatrix (t : ℝ) : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  Matrix.fromBlocks
    (scalarBlock (N := N) (Real.cosh t))
    (scalarBlock (N := N) (Real.sinh t))
    (scalarBlock (N := N) (Real.sinh t))
    (scalarBlock (N := N) (Real.cosh t))

@[simp] theorem blockA_sigmaMatrix (t : ℝ) :
    blockA (sigmaMatrix (N := N) t) = scalarBlock (N := N) (Real.cosh t) := by
  simp [sigmaMatrix, blockA]

@[simp] theorem blockB_sigmaMatrix (t : ℝ) :
    blockB (sigmaMatrix (N := N) t) = scalarBlock (N := N) (Real.sinh t) := by
  simp [sigmaMatrix, blockB]

@[simp] theorem blockC_sigmaMatrix (t : ℝ) :
    blockC (sigmaMatrix (N := N) t) = scalarBlock (N := N) (Real.sinh t) := by
  simp [sigmaMatrix, blockC]

@[simp] theorem blockD_sigmaMatrix (t : ℝ) :
    blockD (sigmaMatrix (N := N) t) = scalarBlock (N := N) (Real.cosh t) := by
  simp [sigmaMatrix, blockD]

theorem latticeAnomalyCommutator_sigmaMatrix
    (t : ℝ) :
    latticeAnomalyCommutator (sigmaMatrix (N := N) t) =
      Matrix.fromBlocks
        (0 : Matrix (Fin N) (Fin N) ℝ)
        (scalarBlock (N := N) ((2 : ℝ) * Real.sinh t))
        (scalarBlock (N := N) ((-2 : ℝ) * Real.sinh t))
        (0 : Matrix (Fin N) (Fin N) ℝ) := by
  rw [latticeAnomalyCommutator_eq_blocks]
  ext i j
  cases i <;> cases j <;> simp [scalarBlock, two_smul] <;> ring_nf

/-- Finite-dimensional Witten index extracted from the anomaly-free `A` block. -/
def wittenIndex (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) : ℝ :=
  Matrix.det (blockA U)

theorem wittenIndex_sigmaMatrix (t : ℝ) :
    wittenIndex (sigmaMatrix (N := N) t) = Real.cosh t ^ N := by
  simp [wittenIndex, scalarBlock, Matrix.det_diagonal]

theorem wittenIndex_sigmaMatrix_eq_one_iff
    {t : ℝ} (hN : N ≠ 0) :
    wittenIndex (sigmaMatrix (N := N) t) = 1 ↔ t = 0 := by
  constructor
  · intro hW
    by_contra ht
    rw [wittenIndex_sigmaMatrix] at hW
    have hlt : 1 < Real.cosh t := Real.one_lt_cosh.mpr ht
    have hp : 1 < Real.cosh t ^ N := one_lt_pow₀ hlt hN
    exact (lt_irrefl 1) (hW ▸ hp)
  · intro ht
    subst ht
    simp [wittenIndex_sigmaMatrix]

theorem det_sigmaMatrix (t : ℝ) :
    Matrix.det (sigmaMatrix (N := N) t) = 1 := by
  let c : ℝ := Real.cosh t
  let s : ℝ := Real.sinh t
  have hcp : 0 < c := by
    dsimp [c]
    positivity
  have hcz : c ≠ 0 := ne_of_gt hcp
  letI : Invertible c := invertibleOfNonzero hcz
  letI : Invertible (scalarBlock (N := N) c) := by
    exact scalarBlockInvertible (N := N) c
  have hSchur :
      scalarBlock (N := N) c
        - scalarBlock (N := N) s * ⅟(scalarBlock (N := N) c) * scalarBlock (N := N) s
        = scalarBlock (N := N) (⅟c) := by
    have hInv : ⅟(scalarBlock (N := N) c) = Matrix.diagonal (fun _ : Fin N => ⅟c) := by
      letI := constInvertible (N := N) c
      letI : Invertible (Matrix.diagonal fun _ : Fin N => c) := by
        simpa [scalarBlock] using
          (show Invertible (scalarBlock (N := N) c) from inferInstance)
      simpa [scalarBlock] using (Matrix.invOf_diagonal_eq (v := fun _ : Fin N => c))
    rw [hInv]
    ext i j
    by_cases hij : i = j
    · subst hij
      have hScalar : c - s * c⁻¹ * s = c⁻¹ := by
        field_simp [hcz]
        nlinarith [Real.cosh_sq_sub_sinh_sq t]
      simp [scalarBlock, hScalar]
    · simp [scalarBlock, hij]
  calc
    Matrix.det (sigmaMatrix (N := N) t)
        = Matrix.det (scalarBlock (N := N) c) *
            Matrix.det
              (scalarBlock (N := N) c
                - scalarBlock (N := N) s * ⅟(scalarBlock (N := N) c) * scalarBlock (N := N) s) := by
          rw [sigmaMatrix, Matrix.det_fromBlocks₂₂]
    _ = Matrix.det (scalarBlock (N := N) c) * Matrix.det (scalarBlock (N := N) (⅟c)) := by
          rw [hSchur]
    _ = c ^ N * (⅟c) ^ N := by
          simp [scalarBlock, Matrix.det_diagonal]
    _ = (c * ⅟c) ^ N := by
          rw [mul_pow]
    _ = 1 := by
          simp [hcz]

/-- Lower unitriangular factor in the LDU decomposition of `sigmaMatrix`. -/
noncomputable def sigmaLower (t : ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  Matrix.fromBlocks
    (1 : Matrix (Fin N) (Fin N) ℝ)
    (0 : Matrix (Fin N) (Fin N) ℝ)
    (scalarBlock (N := N) (Real.sinh t / Real.cosh t))
    (1 : Matrix (Fin N) (Fin N) ℝ)

/-- Diagonal factor in the LDU decomposition of `sigmaMatrix`. -/
noncomputable def sigmaDiag (t : ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  Matrix.fromBlocks
    (scalarBlock (N := N) (Real.cosh t))
    (0 : Matrix (Fin N) (Fin N) ℝ)
    (0 : Matrix (Fin N) (Fin N) ℝ)
    (scalarBlock (N := N) ((Real.cosh t)⁻¹))

/-- Upper unitriangular factor in the LDU decomposition of `sigmaMatrix`. -/
noncomputable def sigmaUpper (t : ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  Matrix.fromBlocks
    (1 : Matrix (Fin N) (Fin N) ℝ)
    (scalarBlock (N := N) (Real.sinh t / Real.cosh t))
    (0 : Matrix (Fin N) (Fin N) ℝ)
    (1 : Matrix (Fin N) (Fin N) ℝ)

/-- Candidate LDU product associated to the hyperbolic lattice flow. -/
noncomputable def sigmaLDUProduct (t : ℝ) :
    Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  sigmaLower (N := N) t * sigmaDiag (N := N) t * sigmaUpper (N := N) t

/--
Parity protection through LDU transport: once the explicit factorization is identified,
the determinant is forced to remain `1`.
-/
theorem det_sigmaLDUProduct_eq_one_of_factorization
    (t : ℝ)
    (hLDU : sigmaMatrix (N := N) t = sigmaLDUProduct (N := N) t) :
    Matrix.det (sigmaLDUProduct (N := N) t) = 1 := by
  rw [← hLDU]
  exact det_sigmaMatrix (N := N) t

noncomputable instance sigmaMatrix_blockD_invertible (t : ℝ) :
    Invertible (blockD (sigmaMatrix (N := N) t)) := by
  let c : ℝ := Real.cosh t
  have hcp : 0 < c := by
    dsimp [c]
    positivity
  have hcz : c ≠ 0 := ne_of_gt hcp
  letI : Invertible c := invertibleOfNonzero hcz
  simpa [blockD, sigmaMatrix, c] using (scalarBlockInvertible (N := N) c)

/-- Schur-complement determinant factorization around the bottom-right block. -/
noncomputable def schurDet
    (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ)
    [Invertible (blockD U)] : ℝ :=
  Matrix.det (blockD U) *
    Matrix.det (blockA U - blockB U * ⅟(blockD U) * blockC U)

theorem schurDet_eq_det
    (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ)
    [Invertible (blockD U)] :
    schurDet (N := N) U = Matrix.det U := by
  calc
    schurDet (N := N) U
      = Matrix.det (blockD U) * Matrix.det (blockA U - blockB U * ⅟(blockD U) * blockC U) := rfl
    _ = Matrix.det (Matrix.fromBlocks (blockA U) (blockB U) (blockC U) (blockD U)) := by
      symm
      exact Matrix.det_fromBlocks₂₂ (A := blockA U) (B := blockB U) (C := blockC U) (D := blockD U)
    _ = Matrix.det U := by
      simpa using congrArg Matrix.det (matrix_eq_fromBlocks U).symm

theorem schurDet_sigmaMatrix (t : ℝ) :
    schurDet (N := N) (sigmaMatrix (N := N) t) = 1 := by
  rw [schurDet_eq_det]
  exact det_sigmaMatrix (N := N) t

/-- True Berezinian (superdeterminant) around the bottom-right block. -/
noncomputable def berezinian
    (U : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ)
    [Invertible (blockD U)] : ℝ :=
  Matrix.det (blockA U - blockB U * ⅟(blockD U) * blockC U) /
    Matrix.det (blockD U)

/-- Topological parity index of the lattice modular flow. -/
theorem invariant_parity_index (t : ℝ) :
    Matrix.det (sigmaMatrix (N := N) t) = 1 :=
  det_sigmaMatrix (N := N) t

/--
Thermal Berezinian deformation scalar from the Schur complement ratio.
This captures the non-cancelled chiral weighting.
-/
noncomputable def thermalBerezinianEval (t : ℝ) : ℝ :=
  ((Real.cosh t - (Real.sinh t) ^ 2 / Real.cosh t) ^ N) /
    (Real.cosh t ^ N)

/--
Real-power normal form of the thermal Berezinian deformation:
`((cosh - sinh^2/cosh)^N)/(cosh^N) = cosh^(-2N)`.
-/
theorem thermal_berezinian_index (t : ℝ) :
    thermalBerezinianEval (N := N) t = (Real.cosh t) ^ (-2 * (N : ℝ)) := by
  unfold thermalBerezinianEval
  have hpos : 0 < Real.cosh t := Real.cosh_pos t
  have hschur : Real.cosh t - (Real.sinh t) ^ 2 / Real.cosh t = 1 / Real.cosh t := by
    have hcz : Real.cosh t ≠ 0 := ne_of_gt hpos
    field_simp [hcz]
    nlinarith [Real.cosh_sq_sub_sinh_sq t]
  rw [hschur]
  rw [← Real.rpow_natCast (1 / Real.cosh t) N, ← Real.rpow_natCast (Real.cosh t) N]
  rw [one_div, Real.inv_rpow hpos.le]
  have hneg : ((Real.cosh t) ^ (N : ℝ))⁻¹ = (Real.cosh t) ^ (-(N : ℝ)) := by
    exact (Real.rpow_neg hpos.le (N : ℝ)).symm
  rw [div_eq_mul_inv, hneg]
  rw [← Real.rpow_add hpos (-(N : ℝ)) (-(N : ℝ))]
  congr 1
  ring

end Lattice

namespace Cl11LatticeBridge

open InfoGeometry.Canonical.TomitaTakesaki

variable {N : ℕ}

/-- Finite-dimensional Euclidean model for one chiral sector. -/
abbrev FinModel := EuclideanSpace ℝ (Fin N)

/-- Continuous doubled `Cl(1,1)` carrier over the finite Euclidean model. -/
abbrev ContinuousCarrier := InfoGeometry.Krein.DoubledSpace (FinModel (N := N))

/-- Lattice coordinate carrier for the `2N` real modes. -/
abbrev LatticeCarrier := EuclideanSpace ℝ (Fin N ⊕ Fin N)

noncomputable local instance : NormedAddCommGroup (cl11DoubledCore (FinModel (N := N))) := by
  change NormedAddCommGroup (InfoGeometry.Krein.DoubledSpace (FinModel (N := N)))
  infer_instance

noncomputable local instance : NormedSpace ℝ (cl11DoubledCore (FinModel (N := N))) := by
  change NormedSpace ℝ (InfoGeometry.Krein.DoubledSpace (FinModel (N := N)))
  infer_instance

noncomputable local instance : InnerProductSpace ℝ (cl11DoubledCore (FinModel (N := N))) := by
  change InnerProductSpace ℝ (InfoGeometry.Krein.DoubledSpace (FinModel (N := N)))
  infer_instance

noncomputable local instance : CompleteSpace (cl11DoubledCore (FinModel (N := N))) := by
  change CompleteSpace (InfoGeometry.Krein.DoubledSpace (FinModel (N := N)))
  infer_instance

noncomputable local instance : KreinSpace (cl11DoubledCore (FinModel (N := N))) := by
  change KreinSpace (InfoGeometry.Krein.DoubledSpace (FinModel (N := N)))
  infer_instance

noncomputable local instance :
    NormedRing
      (ContinuousCarrier (N := N) →L[ℝ] ContinuousCarrier (N := N)) := inferInstance

noncomputable local instance :
    NormedAlgebra ℝ
      (ContinuousCarrier (N := N) →L[ℝ] ContinuousCarrier (N := N)) := inferInstance

noncomputable local instance :
    CompleteSpace
      (ContinuousCarrier (N := N) →L[ℝ] ContinuousCarrier (N := N)) := by
  infer_instance

local instance :
    IsTopologicalRing
      (ContinuousCarrier (N := N) →L[ℝ] ContinuousCarrier (N := N)) := inferInstance

/--
Coordinate equivalence from the doubled continuous `Cl(1,1)` carrier to the
`2N`-component lattice coordinate space.
-/
noncomputable def latticeCoordEquiv :
    ContinuousCarrier (N := N) ≃L[ℝ] LatticeCarrier (N := N) :=
  (WithLp.prodContinuousLinearEquiv (2 : ENNReal) ℝ
      (FinModel (N := N)) (FinModel (N := N))).trans
    (EuclideanSpace.sumEquivProd (𝕜 := ℝ) (ι := Fin N) (κ := Fin N)).symm

@[simp] theorem latticeCoordEquiv_to_doubled_apply_inl
    (x y : FinModel (N := N)) (i : Fin N) :
    latticeCoordEquiv (N := N) (InfoGeometry.Krein.to_doubled x y) (Sum.inl i) = x i := by
  rfl

@[simp] theorem latticeCoordEquiv_to_doubled_apply_inr
    (x y : FinModel (N := N)) (i : Fin N) :
    latticeCoordEquiv (N := N) (InfoGeometry.Krein.to_doubled x y) (Sum.inr i) = y i := by
  rfl

@[simp] theorem latticeCoordEquiv_symm_apply
    (v : LatticeCarrier (N := N)) :
    (latticeCoordEquiv (N := N)).symm v =
      InfoGeometry.Krein.to_doubled
        (WithLp.toLp (2 : ENNReal) fun i => v.ofLp (Sum.inl i))
        (WithLp.toLp (2 : ENNReal) fun i => v.ofLp (Sum.inr i)) := by
  rfl

/--
Lattice avatar of a continuous doubled-space operator, obtained by conjugating
it through `latticeCoordEquiv`.
-/
noncomputable def latticeAvatar
    (A : ContinuousCarrier (N := N) →L[ℝ] ContinuousCarrier (N := N)) :
    LatticeCarrier (N := N) →ₗ[ℝ] LatticeCarrier (N := N) :=
  (((latticeCoordEquiv (N := N)).toContinuousLinearMap.comp A).comp
    (latticeCoordEquiv (N := N)).symm.toContinuousLinearMap).toLinearMap

/--
Continuous-linear lattice avatar of a doubled-space operator, obtained by the
same conjugation as `latticeAvatar` but retaining continuity data.
-/
noncomputable def latticeAvatarCLM
    (A : ContinuousCarrier (N := N) →L[ℝ] ContinuousCarrier (N := N)) :
    LatticeCarrier (N := N) →L[ℝ] LatticeCarrier (N := N) :=
  ((latticeCoordEquiv (N := N)).toContinuousLinearMap.comp A).comp
    (latticeCoordEquiv (N := N)).symm.toContinuousLinearMap

@[simp] theorem coe_latticeAvatarCLM
    (A : ContinuousCarrier (N := N) →L[ℝ] ContinuousCarrier (N := N)) :
    ((latticeAvatarCLM (N := N) A : LatticeCarrier (N := N) →L[ℝ] LatticeCarrier (N := N)) :
      LatticeCarrier (N := N) →ₗ[ℝ] LatticeCarrier (N := N)) =
      latticeAvatar (N := N) A := rfl

@[simp] theorem latticeAvatarCLM_apply
    (A : ContinuousCarrier (N := N) →L[ℝ] ContinuousCarrier (N := N))
    (v : LatticeCarrier (N := N)) :
    latticeAvatarCLM (N := N) A v =
      latticeCoordEquiv (N := N) (A ((latticeCoordEquiv (N := N)).symm v)) := rfl

@[simp] theorem latticeAvatarCLM_comp
    (A B : ContinuousCarrier (N := N) →L[ℝ] ContinuousCarrier (N := N)) :
    latticeAvatarCLM (N := N) (A.comp B) =
      (latticeAvatarCLM (N := N) A).comp (latticeAvatarCLM (N := N) B) := by
  ext v i
  simp [latticeAvatarCLM]

@[simp] theorem latticeAvatarCLM_sub
    (A B : ContinuousCarrier (N := N) →L[ℝ] ContinuousCarrier (N := N)) :
    latticeAvatarCLM (N := N) (A - B) =
      latticeAvatarCLM (N := N) A - latticeAvatarCLM (N := N) B := by
  ext v i
  simp [latticeAvatarCLM]

/-- Continuous-linear operator on the lattice carrier associated to a matrix. -/
noncomputable def latticeMatrixCLM
    (A : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ) :
    LatticeCarrier (N := N) →L[ℝ] LatticeCarrier (N := N) :=
  (LinearMap.toContinuousLinearMap
    (𝕜 := ℝ) (E := LatticeCarrier (N := N)) (F' := LatticeCarrier (N := N)))
    (Matrix.toEuclideanLin A)

@[simp] theorem latticeMatrixCLM_apply
    (A : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ)
    (v : LatticeCarrier (N := N)) :
    latticeMatrixCLM (N := N) A v = Matrix.toEuclideanLin A v := rfl

/--
Continuous-linear equivalence avatar of a doubled-space symmetry on the lattice
carrier.
-/
noncomputable def latticeAutomorphismAvatar
    (U : ContinuousCarrier (N := N) ≃L[ℝ] ContinuousCarrier (N := N)) :
    LatticeCarrier (N := N) ≃L[ℝ] LatticeCarrier (N := N) :=
  ((latticeCoordEquiv (N := N)).symm.trans U).trans (latticeCoordEquiv (N := N))

@[simp] theorem latticeAutomorphismAvatar_symm
    (U : ContinuousCarrier (N := N) ≃L[ℝ] ContinuousCarrier (N := N)) :
    latticeAutomorphismAvatar (N := N) U.symm =
      (latticeAutomorphismAvatar (N := N) U).symm := by
  ext v i
  simp [latticeAutomorphismAvatar]

@[simp] theorem latticeAutomorphismAvatar_toContinuousLinearMap
    (U : ContinuousCarrier (N := N) ≃L[ℝ] ContinuousCarrier (N := N)) :
    ((latticeAutomorphismAvatar (N := N) U :
        LatticeCarrier (N := N) ≃L[ℝ] LatticeCarrier (N := N)) :
      LatticeCarrier (N := N) →L[ℝ] LatticeCarrier (N := N)) =
      latticeAvatarCLM (N := N) (U : ContinuousCarrier (N := N) →L[ℝ] ContinuousCarrier (N := N)) := by
  ext v i
  simp [latticeAutomorphismAvatar, latticeAvatarCLM]

theorem latticeAvatarCLM_coe_equiv
    (U : ContinuousCarrier (N := N) ≃L[ℝ] ContinuousCarrier (N := N)) :
    latticeAvatarCLM (N := N) (U : ContinuousCarrier (N := N) →L[ℝ] ContinuousCarrier (N := N)) =
      ((latticeAutomorphismAvatar (N := N) U :
          LatticeCarrier (N := N) ≃L[ℝ] LatticeCarrier (N := N)) :
        LatticeCarrier (N := N) →L[ℝ] LatticeCarrier (N := N)) := by
  symm
  exact latticeAutomorphismAvatar_toContinuousLinearMap (N := N) U

/-- Lattice matrix avatar of the modular conjugation generator `J`. -/
def jMatrix : Matrix (Fin N ⊕ Fin N) (Fin N ⊕ Fin N) ℝ :=
  Matrix.fromBlocks
    (0 : Matrix (Fin N) (Fin N) ℝ)
    (1 : Matrix (Fin N) (Fin N) ℝ)
    (1 : Matrix (Fin N) (Fin N) ℝ)
    (0 : Matrix (Fin N) (Fin N) ℝ)

@[simp] theorem jMatrix_mulVec_inl
    (v : Fin N ⊕ Fin N → ℝ) (j : Fin N) :
    Matrix.mulVec (jMatrix (N := N)) v (Sum.inl j) = v (Sum.inr j) := by
  simp [jMatrix, Matrix.mulVec, dotProduct, Matrix.one_apply]

@[simp] theorem jMatrix_mulVec_inr
    (v : Fin N ⊕ Fin N → ℝ) (j : Fin N) :
    Matrix.mulVec (jMatrix (N := N)) v (Sum.inr j) = v (Sum.inl j) := by
  simp [jMatrix, Matrix.mulVec, dotProduct, Matrix.one_apply]

/--
The continuous `Cl(1,1)` grading operator `ε` is represented in lattice
coordinates by the block-sign matrix `epsMatrix`.
-/
theorem latticeAvatar_canonicalCl11Generator :
    latticeAvatar (N := N) (Cl11Shadow.canonicalCl11Generator (E := FinModel (N := N))) =
      Matrix.toEuclideanLin (Lattice.epsMatrix (N := N)) := by
  ext v i
  unfold latticeAvatar
  cases i using Sum.casesOn with
  | inl j =>
      change latticeCoordEquiv (N := N)
          (InfoGeometry.Krein.spectral_epsilon
            ((latticeCoordEquiv (N := N)).symm v)) (Sum.inl j)
        = (WithLp.toLp (2 : ENNReal)
            (Matrix.mulVec (Lattice.epsMatrix (N := N)) v.ofLp)) (Sum.inl j)
      simp [Lattice.epsMatrix, Matrix.mulVec, dotProduct, Matrix.one_apply]
  | inr j =>
      change latticeCoordEquiv (N := N)
          (InfoGeometry.Krein.spectral_epsilon
            ((latticeCoordEquiv (N := N)).symm v)) (Sum.inr j)
        = (WithLp.toLp (2 : ENNReal)
            (Matrix.mulVec (Lattice.epsMatrix (N := N)) v.ofLp)) (Sum.inr j)
      simp [Lattice.epsMatrix, Matrix.mulVec, dotProduct, Matrix.one_apply]

theorem latticeAvatarCLM_canonicalCl11Generator :
    latticeAvatarCLM (N := N) (Cl11Shadow.canonicalCl11Generator (E := FinModel (N := N))) =
      latticeMatrixCLM (N := N) (Lattice.epsMatrix (N := N)) := by
  ext v i
  simpa [coe_latticeAvatarCLM, latticeMatrixCLM] using
    congrArg
      (fun A : LatticeCarrier (N := N) →ₗ[ℝ] LatticeCarrier (N := N) => A v i)
      (latticeAvatar_canonicalCl11Generator (N := N))

/--
The continuous modular conjugation operator `J` is represented in lattice
coordinates by the swap matrix `jMatrix`.
-/
theorem latticeAvatar_modularConjugationJ :
    latticeAvatar (N := N) (modularConjugationJ (E := FinModel (N := N))) =
      Matrix.toEuclideanLin (jMatrix (N := N)) := by
  ext v i
  unfold latticeAvatar
  cases i using Sum.casesOn with
  | inl j =>
      change latticeCoordEquiv (N := N)
          (InfoGeometry.Krein.modular_j
            ((latticeCoordEquiv (N := N)).symm v)) (Sum.inl j)
        = (WithLp.toLp (2 : ENNReal)
            (Matrix.mulVec (jMatrix (N := N)) v.ofLp)) (Sum.inl j)
      simp [jMatrix, Matrix.mulVec, dotProduct, Matrix.one_apply]
  | inr j =>
      change latticeCoordEquiv (N := N)
          (InfoGeometry.Krein.modular_j
            ((latticeCoordEquiv (N := N)).symm v)) (Sum.inr j)
        = (WithLp.toLp (2 : ENNReal)
            (Matrix.mulVec (jMatrix (N := N)) v.ofLp)) (Sum.inr j)
      simp [jMatrix, Matrix.mulVec, dotProduct, Matrix.one_apply]

/--
The continuous hyperbolic `J`-flow `sigmaMap J t` is represented in lattice
coordinates by the block hyperbolic shadow matrix `sigmaMatrix t`.
-/
theorem latticeAvatar_sigmaMap_modularConjugationJ
    (t : ℝ) :
    latticeAvatar (N := N)
      (Cl11Shadow.sigmaMap (modularConjugationJ (E := FinModel (N := N))) t) =
      Matrix.toEuclideanLin (Lattice.sigmaMatrix (N := N) t) := by
  have hJ :
      ∀ v : LatticeCarrier (N := N),
        latticeCoordEquiv (N := N)
          (modularConjugationJ (E := FinModel (N := N))
            ((latticeCoordEquiv (N := N)).symm v))
          = Matrix.toEuclideanLin (jMatrix (N := N)) v := by
    intro v
    have hApply := congrArg
      (fun A : LatticeCarrier (N := N) →ₗ[ℝ] LatticeCarrier (N := N) => A v)
      (latticeAvatar_modularConjugationJ (N := N))
    simpa [latticeAvatar] using hApply
  have hJsmul :
      ∀ v : LatticeCarrier (N := N),
        latticeCoordEquiv (N := N)
          (((Real.sinh t) • modularConjugationJ (E := FinModel (N := N)))
            ((latticeCoordEquiv (N := N)).symm v))
          = (Real.sinh t) • Matrix.toEuclideanLin (jMatrix (N := N)) v := by
    intro v
    calc
      latticeCoordEquiv (N := N)
          (((Real.sinh t) • modularConjugationJ (E := FinModel (N := N)))
            ((latticeCoordEquiv (N := N)).symm v))
          = (Real.sinh t) •
              latticeCoordEquiv (N := N)
                (modularConjugationJ (E := FinModel (N := N))
                  ((latticeCoordEquiv (N := N)).symm v)) := by
                    simp
      _ = (Real.sinh t) • Matrix.toEuclideanLin (jMatrix (N := N)) v := by
            rw [hJ v]
  ext v i
  unfold latticeAvatar
  cases i using Sum.casesOn with
  | inl j =>
      change latticeCoordEquiv (N := N)
          (Cl11Shadow.sigmaMap
            (modularConjugationJ (E := FinModel (N := N))) t
            ((latticeCoordEquiv (N := N)).symm v)) (Sum.inl j)
        = (WithLp.toLp (2 : ENNReal)
            (Matrix.mulVec (Lattice.sigmaMatrix (N := N) t) v.ofLp)) (Sum.inl j)
      have hJsmulApply :
          (latticeCoordEquiv (N := N)
              (((Real.sinh t) • modularConjugationJ (E := FinModel (N := N)))
                ((latticeCoordEquiv (N := N)).symm v))).ofLp (Sum.inl j)
            = ((Real.sinh t) • Matrix.toEuclideanLin (jMatrix (N := N)) v).ofLp (Sum.inl j) := by
        exact congrArg (fun z : LatticeCarrier (N := N) => z.ofLp (Sum.inl j)) (hJsmul v)
      simp [Cl11Shadow.sigmaMap, Lattice.sigmaMatrix, Lattice.scalarBlock,
        Matrix.mulVec, dotProduct]
      rw [← latticeCoordEquiv_symm_apply (N := N) (v := v)]
      calc
        Real.cosh t * v.ofLp (Sum.inl j) +
            (latticeCoordEquiv (N := N)
                (((Real.sinh t) • modularConjugationJ (E := FinModel (N := N)))
                  ((latticeCoordEquiv (N := N)).symm v))).ofLp (Sum.inl j)
          = Real.cosh t * v.ofLp (Sum.inl j) +
              ((Real.sinh t) • Matrix.toEuclideanLin (jMatrix (N := N)) v).ofLp (Sum.inl j) := by
                rw [hJsmulApply]
        _ = ∑ x, Matrix.diagonal (fun _ : Fin N => Real.cosh t) j x * v.ofLp (Sum.inl x) +
              ∑ x, Matrix.diagonal (fun _ : Fin N => Real.sinh t) j x * v.ofLp (Sum.inr x) := by
                simp [Matrix.diagonal]
  | inr j =>
      change latticeCoordEquiv (N := N)
          (Cl11Shadow.sigmaMap
            (modularConjugationJ (E := FinModel (N := N))) t
            ((latticeCoordEquiv (N := N)).symm v)) (Sum.inr j)
        = (WithLp.toLp (2 : ENNReal)
            (Matrix.mulVec (Lattice.sigmaMatrix (N := N) t) v.ofLp)) (Sum.inr j)
      have hJsmulApply :
          (latticeCoordEquiv (N := N)
              (((Real.sinh t) • modularConjugationJ (E := FinModel (N := N)))
                ((latticeCoordEquiv (N := N)).symm v))).ofLp (Sum.inr j)
            = ((Real.sinh t) • Matrix.toEuclideanLin (jMatrix (N := N)) v).ofLp (Sum.inr j) := by
        exact congrArg (fun z : LatticeCarrier (N := N) => z.ofLp (Sum.inr j)) (hJsmul v)
      simp [Cl11Shadow.sigmaMap, Lattice.sigmaMatrix, Lattice.scalarBlock,
        Matrix.mulVec, dotProduct]
      rw [← latticeCoordEquiv_symm_apply (N := N) (v := v)]
      calc
        Real.cosh t * v.ofLp (Sum.inr j) +
            (latticeCoordEquiv (N := N)
                (((Real.sinh t) • modularConjugationJ (E := FinModel (N := N)))
                  ((latticeCoordEquiv (N := N)).symm v))).ofLp (Sum.inr j)
          = Real.cosh t * v.ofLp (Sum.inr j) +
              ((Real.sinh t) • Matrix.toEuclideanLin (jMatrix (N := N)) v).ofLp (Sum.inr j) := by
                rw [hJsmulApply]
        _ = ∑ x, Matrix.diagonal (fun _ : Fin N => Real.sinh t) j x * v.ofLp (Sum.inl x) +
              ∑ x, Matrix.diagonal (fun _ : Fin N => Real.cosh t) j x * v.ofLp (Sum.inr x) := by
                simp [Matrix.diagonal]
                ring_nf

/--
The analytic exponential modular flow generated by `J` has the same lattice
avatar as the concrete hyperbolic shadow matrix `sigmaMatrix`.
-/
theorem latticeAvatar_exp_modularConjugationJ
    (t : ℝ) :
    latticeAvatar (N := N)
      (NormedSpace.exp (t • modularConjugationJ (E := FinModel (N := N)))) =
      Matrix.toEuclideanLin (Lattice.sigmaMatrix (N := N) t) := by
  rw [← Cl11Shadow.expFlow_toContinuousLinearMap
      (σGen := modularConjugationJ (E := FinModel (N := N))) (t := t)]
  rw [Cl11Shadow.expFlow_modularConjugationJ_eq_sigmaMap (E := FinModel (N := N))]
  exact latticeAvatar_sigmaMap_modularConjugationJ (N := N) t

/--
Lattice-side commutator shadow associated to the canonical `Cl(1,1)` generator
`ε`.
-/
noncomputable def latticeCommutatorShadow
    (V : LatticeCarrier (N := N) ≃L[ℝ] LatticeCarrier (N := N)) :
    LatticeCarrier (N := N) →L[ℝ] LatticeCarrier (N := N) :=
  (V.symm : LatticeCarrier (N := N) →L[ℝ] LatticeCarrier (N := N)).comp
    ((latticeMatrixCLM (N := N) (Lattice.epsMatrix (N := N))).comp
        (V : LatticeCarrier (N := N) →L[ℝ] LatticeCarrier (N := N))
      - (V : LatticeCarrier (N := N) →L[ℝ] LatticeCarrier (N := N)).comp
          (latticeMatrixCLM (N := N) (Lattice.epsMatrix (N := N))))

/--
The canonical continuous modular anomaly generator is represented on the finite
lattice by the transported commutator shadow of the lattice avatar of `U`.

This is the exact lattice realization of the continuous cocycle anomaly: the
bare matrix commutator `[ε, U]` appears inside the `U⁻¹` transport dictated by
the Connes cocycle formula.
-/
theorem latticeAvatar_canonicalCl11_modularAnomalyGenerator
    (U : ContinuousCarrier (N := N) ≃L[ℝ] ContinuousCarrier (N := N)) :
    latticeAvatarCLM (N := N)
      ((Cl11Shadow.canonicalCl11TopologicalShadow (E := FinModel (N := N))).modularAnomalyGenerator U) =
      latticeCommutatorShadow (N := N) (latticeAutomorphismAvatar (N := N) U) := by
  rw [Cl11Shadow.modularAnomalyGenerator_eq_canonicalCl11_commutator_shadow
      (E := FinModel (N := N)) (U := U)]
  rw [latticeAvatarCLM_comp, latticeAvatarCLM_sub, latticeAvatarCLM_comp, latticeAvatarCLM_comp]
  rw [latticeAvatarCLM_coe_equiv (N := N) (U := U.symm)]
  simp [latticeCommutatorShadow, latticeAvatarCLM_canonicalCl11Generator]

end Cl11LatticeBridge

end InfoGeometry.Quantum.ModularAnomaly
