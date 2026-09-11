import Mathlib.Analysis.Normed.Module.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Topology.Algebra.Module.LinearMap
import InfoGeometry.Dynamics.EntropicTokenDynamics

/-!
# Realification of the finite token operator carrier

The analytic context equations are parameterised by `ℝ`, while the token
operators are naturally complex-linear.  This file supplies the canonical
Mathlib scalar restriction, without changing the complex operator owner.
-/

namespace InfoGeometry.Dynamics

noncomputable section

variable {V : Type*} [Fintype V]

abbrev RealTokenHilbertSpace :=
  RestrictScalars ℝ ℂ (TokenHilbertSpace V)

abbrev RealTokenOperator :=
  RealTokenHilbertSpace (V := V) →ₗ[ℝ] RealTokenHilbertSpace (V := V)

def complexOperatorToReal (T : TokenHilbertSpace V →ₗ[ℂ] TokenHilbertSpace V) :
    RealTokenOperator (V := V) :=
  T.restrictScalars ℝ

def realifiedTotalTokenGenerator (gen : TokenGenerator (V := V)) :
    RealTokenOperator (V := V) :=
  complexOperatorToReal (totalTokenGenerator gen)

@[simp] theorem complexOperatorToReal_apply
    (T : TokenHilbertSpace V →ₗ[ℂ] TokenHilbertSpace V)
    (ψ : RealTokenHilbertSpace (V := V)) :
    complexOperatorToReal T ψ = T ψ := rfl

theorem complexOperatorToReal_add
    (T U : TokenHilbertSpace V →ₗ[ℂ] TokenHilbertSpace V) :
    complexOperatorToReal (T + U) =
      complexOperatorToReal T + complexOperatorToReal U := by
  ext ψ
  rfl

theorem complexOperatorToReal_real_smul
    (c : ℝ) (T : TokenHilbertSpace V →ₗ[ℂ] TokenHilbertSpace V) :
    complexOperatorToReal (c • T) = c • complexOperatorToReal T := by
  ext ψ
  rfl

theorem complexOperatorToReal_comp
    (T U : TokenHilbertSpace V →ₗ[ℂ] TokenHilbertSpace V) :
    complexOperatorToReal (T.comp U) =
      (complexOperatorToReal T).comp (complexOperatorToReal U) := by
  ext ψ
  rfl

theorem complexOperatorToReal_commutator
    (T U : TokenHilbertSpace V →ₗ[ℂ] TokenHilbertSpace V) :
    complexOperatorToReal (T.comp U - U.comp T) =
      (complexOperatorToReal T).comp (complexOperatorToReal U) -
        (complexOperatorToReal U).comp (complexOperatorToReal T) := by
  ext ψ
  rfl

theorem realifiedTotalTokenGenerator_apply
    (gen : TokenGenerator (V := V)) (ψ : RealTokenHilbertSpace (V := V)) :
    realifiedTotalTokenGenerator gen ψ =
      ((-Complex.I) • gen.H ψ - gen.Gamma ψ) := rfl

theorem realifiedTotalTokenGenerator_eq_components
    (gen : TokenGenerator (V := V)) :
    realifiedTotalTokenGenerator gen =
      complexOperatorToReal ((-Complex.I) • gen.H) -
        complexOperatorToReal gen.Gamma := by
  rfl

theorem realifiedDissipativeTokenGenerator_real_pairing_nonpos
    (gen : DissipativeTokenGenerator V)
    (ψ : RealTokenHilbertSpace (V := V)) :
    (tokenPairing ψ (realifiedTotalTokenGenerator gen.toTokenGenerator ψ)).re ≤ 0 := by
  exact dissipativeTokenGenerator_real_pairing_nonpos gen ψ

theorem realifiedTotalTokenGenerator_eq_zero_of_components_eq_zero
    (gen : TokenGenerator (V := V))
    (ψ : RealTokenHilbertSpace (V := V))
    (hH : gen.H ψ = 0) (hGamma : gen.Gamma ψ = 0) :
    realifiedTotalTokenGenerator gen ψ = 0 := by
  exact totalTokenGenerator_eq_zero_of_components_eq_zero gen ψ hH hGamma

end
end InfoGeometry.Dynamics
