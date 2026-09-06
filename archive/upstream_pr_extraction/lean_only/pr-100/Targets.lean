import Mathlib

open Complex Filter Topology

namespace InfoGeometry

-- 1) KMS (root thermodynamics)
structure KMSEquation (A : Type*) where
  τ : ℝ → A → A
  ω : A → ℂ
  β : ℝ
  mul : A → A → A
  kms_eq :
    ∀ (t : ℝ) (a b : A),
      ω (mul (τ t a) b) =
        ω (mul b (τ (t + β) a))

theorem KMSEquation.kms_True {A : Type*} (K : KMSEquation A) :
  ∀ t a b, K.ω (K.mul (K.τ t a) b) =
           K.ω (K.mul b (K.τ (t + K.β) a)) :=
  K.kms_eq

-- 2) Tomita–Cartan split
structure TomitaCartanData (H : Type*) where
  J : H → H
  Δ : H → H
  S : H → H
  split_eq :
    ∀ x : H, S x = J (Δ x)

theorem TomitaCartanData.split_True {H : Type*} (T : TomitaCartanData H) :
  ∀ x, T.S x = T.J (T.Δ x) :=
  T.split_eq

-- 3) Susceptibility = Hessian
structure SusceptibilityHessianData where
  F : ℝ → ℝ
  χ : ℝ
  hessian_eq :
    χ = (deriv (deriv F)) 0

theorem SusceptibilityHessianData.hessian_True (S : SusceptibilityHessianData) :
  S.χ = (deriv (deriv S.F)) 0 :=
  S.hessian_eq

-- 4) Kubo conductivity
structure KuboData where
  G_R : ℂ → ℂ
  σ : ℂ → ℂ
  χdia : ℂ
  kubo_eq :
    ∀ ω : ℂ, ω ≠ 0 →
      σ ω = (G_R ω - G_R 0 + χdia) / (Complex.I * ω)

theorem KuboData.kubo_True (K : KuboData) :
  ∀ ω ≠ 0, K.σ ω =
    (K.G_R ω - K.G_R 0 + K.χdia) / (Complex.I * ω) :=
  K.kubo_eq

-- 5) Chiral graph contraction
structure ChiralGraphData where
  weight : ℤ → ℂ
  contract :
    ℤ → ℤ → ℂ
  contract_eq :
    ∀ i j, contract i j = weight i * weight j

theorem ChiralGraphData.contract_True (G : ChiralGraphData) :
  ∀ i j, G.contract i j = G.weight i * G.weight j :=
  G.contract_eq

-- 6) Sinkhorn defect flow
structure SinkhornDefectFlowData where
  D : ℝ → ℝ
  flow : ℝ → ℝ
  flow_eq :
    ∀ t, deriv D t = - flow t

theorem SinkhornDefectFlowData.flow_True (S : SinkhornDefectFlowData) :
  ∀ t, deriv S.D t = - S.flow t :=
  S.flow_eq

-- 7) Doubled space extensionality (anchor repair)
structure DoubledExtData (E : Type*) where
  toPair : E → E → E
  ext_eq :
    ∀ x y : E, toPair x y = toPair y x → x = y

theorem DoubledExtData.ext_True {E : Type*} (D : DoubledExtData E) :
  ∀ x y, D.toPair x y = D.toPair y x → x = y :=
  D.ext_eq

-- 8) L2 completeness (anchor repair)
-- Added [TopologicalSpace E] to satisfy the `𝓝` (nhds) requirement for limits
structure L2CompleteData (E : Type*) [TopologicalSpace E] where
  lim : (ℕ → E) → E
  lim_spec :
    ∀ u, Tendsto u atTop (𝓝 (lim u))

theorem L2CompleteData.complete_True {E : Type*} [TopologicalSpace E] (L : L2CompleteData E) :
  ∀ u, Tendsto u atTop (𝓝 (L.lim u)) :=
  L.lim_spec

-- ==========================================
-- Concrete Instantiation Tests
-- ==========================================

section Tests

-- Test 1: SusceptibilityHessianData with F(x) = x^2.
noncomputable def testSusceptibilityHessian : SusceptibilityHessianData where
  F := fun x => x^2
  χ := 2
  hessian_eq := by
    have h1 : deriv (fun x : ℝ => x^2) = fun x : ℝ => 2 * x := by
      ext x
      simpa [pow_one] using (hasDerivAt_pow (𝕜 := ℝ) 2 x).deriv
    rw [h1]
    have h2 : HasDerivAt (fun x : ℝ => 2 * x) 2 0 := by
      simpa using
        ((hasDerivAt_const (x := (0 : ℝ)) (c := (2 : ℝ))).mul
          (hasDerivAt_id (x := (0 : ℝ))))
    exact h2.deriv.symm

-- Test 2: canonical convergent model on the one-point topological space.
def testL2CompletePUnit : L2CompleteData PUnit where
  lim := fun _ => PUnit.unit
  lim_spec := by
    intro u
    simp

end Tests

end InfoGeometry
