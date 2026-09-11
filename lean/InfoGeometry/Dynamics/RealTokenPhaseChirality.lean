import InfoGeometry.Dynamics.RealTokenCoordinateOperatorTransport
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Internal phase and chiral involutions on the real token carrier

The complex phase is represented internally by a real-linear operator `K` with
`K² = -1`.  The two-valued token factor supplies an independent chirality
involution `Γ` with `Γ² = 1`.  These are operator identities, not scalar-field
extensions.
-/

namespace InfoGeometry.Dynamics

noncomputable section

variable {V : Type*} [Fintype V]

def realTokenPhaseOperator : RealTokenOperator (V := V) where
  toFun ψ := fun i => Complex.I * ψ i
  map_add' ψ φ := by
    funext i
    change Complex.I * (ψ i + φ i) = Complex.I * ψ i + Complex.I * φ i
    rw [mul_add]
  map_smul' r ψ := by
    funext i
    change Complex.I * ((r : ℂ) * ψ i) = (r : ℂ) * (Complex.I * ψ i)
    ring

@[simp] theorem realTokenPhaseOperator_apply
    (ψ : RealTokenHilbertSpace (V := V)) :
    realTokenPhaseOperator ψ = fun i => Complex.I * ψ i := rfl

theorem realTokenPhaseOperator_sq :
    (realTokenPhaseOperator (V := V)).comp
        (realTokenPhaseOperator (V := V)) =
      -(LinearMap.id : RealTokenOperator (V := V)) := by
  apply LinearMap.ext
  intro ψ
  funext i
  change Complex.I * (Complex.I * ψ i) = -ψ i
  rw [← mul_assoc, Complex.I_mul_I]
  simp

def realTokenChiralityOperator :
    RealTokenHilbertSpace (V := V) → RealTokenHilbertSpace (V := V) :=
  fun ψ i => if i.2 = 0 then ψ i else -ψ i

def tokenChiralityComplex : TokenHilbertSpace V →ₗ[ℂ] TokenHilbertSpace V where
  toFun ψ := fun i => if i.2 = 0 then ψ i else -ψ i
  map_add' ψ φ := by
    funext i
    by_cases h : i.2 = 0
    · simp [h]
    · simp [h]
      abel
  map_smul' c ψ := by
    funext i
    by_cases h : i.2 = 0 <;> simp [h]

def realTokenChiralityLinear : RealTokenOperator (V := V) :=
  complexOperatorToReal (tokenChiralityComplex (V := V))

@[simp] theorem realTokenChiralityLinear_apply
    (ψ : RealTokenHilbertSpace (V := V)) :
    realTokenChiralityLinear ψ = realTokenChiralityOperator ψ := rfl

theorem tokenChiralityComplex_sq :
    (tokenChiralityComplex (V := V)).comp
        (tokenChiralityComplex (V := V)) =
      (LinearMap.id : TokenHilbertSpace V →ₗ[ℂ] TokenHilbertSpace V) := by
  apply LinearMap.ext
  intro ψ
  funext i
  by_cases h : i.2 = 0 <;> simp [tokenChiralityComplex, h]

theorem realTokenChiralityLinear_sq :
    (realTokenChiralityLinear (V := V)).comp
        (realTokenChiralityLinear (V := V)) =
      (LinearMap.id : RealTokenOperator (V := V)) := by
  simpa [realTokenChiralityLinear] using
    congrArg (complexOperatorToReal (V := V))
      (tokenChiralityComplex_sq (V := V))

def realTokenChiralityPlusProjector : RealTokenOperator (V := V) :=
  (1 / 2 : ℝ) • (LinearMap.id + realTokenChiralityLinear (V := V))

def realTokenChiralityMinusProjector : RealTokenOperator (V := V) :=
  (1 / 2 : ℝ) • (LinearMap.id - realTokenChiralityLinear (V := V))

theorem realTokenChiralityProjectors_add :
    realTokenChiralityPlusProjector (V := V) +
        realTokenChiralityMinusProjector (V := V) =
      (LinearMap.id : RealTokenOperator (V := V)) := by
  simp only [realTokenChiralityPlusProjector, realTokenChiralityMinusProjector,
    smul_add, sub_eq_add_neg]
  module

theorem realTokenChiralityPlusProjector_idempotent :
    (realTokenChiralityPlusProjector (V := V)).comp
        (realTokenChiralityPlusProjector (V := V)) =
      realTokenChiralityPlusProjector (V := V) := by
  apply LinearMap.ext
  intro ψ
  simp only [realTokenChiralityPlusProjector, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.add_apply, smul_add, map_add,
    map_smul, LinearMap.id_apply]
  have hsq := congrArg (fun T : RealTokenOperator (V := V) => T ψ)
    (realTokenChiralityLinear_sq (V := V))
  change realTokenChiralityLinear (realTokenChiralityLinear ψ) = ψ at hsq
  rw [hsq]
  module

theorem realTokenChiralityMinusProjector_idempotent :
    (realTokenChiralityMinusProjector (V := V)).comp
        (realTokenChiralityMinusProjector (V := V)) =
      realTokenChiralityMinusProjector (V := V) := by
  apply LinearMap.ext
  intro ψ
  simp only [realTokenChiralityMinusProjector, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.sub_apply, smul_sub, map_sub,
    map_smul, LinearMap.id_apply]
  have hsq := congrArg (fun T : RealTokenOperator (V := V) => T ψ)
    (realTokenChiralityLinear_sq (V := V))
  change realTokenChiralityLinear (realTokenChiralityLinear ψ) = ψ at hsq
  rw [hsq]
  module

theorem realTokenChiralityPlusProjector_comp_minus :
    (realTokenChiralityPlusProjector (V := V)).comp
        (realTokenChiralityMinusProjector (V := V)) = 0 := by
  apply LinearMap.ext
  intro ψ
  simp only [realTokenChiralityPlusProjector, realTokenChiralityMinusProjector,
    LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.sub_apply, smul_add, smul_sub, map_sub, map_smul,
    LinearMap.id_apply, LinearMap.zero_apply]
  have hsq := congrArg (fun T : RealTokenOperator (V := V) => T ψ)
    (realTokenChiralityLinear_sq (V := V))
  change realTokenChiralityLinear (realTokenChiralityLinear ψ) = ψ at hsq
  rw [hsq]
  module

theorem realTokenChiralityMinusProjector_comp_plus :
    (realTokenChiralityMinusProjector (V := V)).comp
        (realTokenChiralityPlusProjector (V := V)) = 0 := by
  apply LinearMap.ext
  intro ψ
  simp only [realTokenChiralityPlusProjector, realTokenChiralityMinusProjector,
    LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.sub_apply, smul_add, smul_sub, map_add, map_smul,
    LinearMap.id_apply, LinearMap.zero_apply]
  have hsq := congrArg (fun T : RealTokenOperator (V := V) => T ψ)
    (realTokenChiralityLinear_sq (V := V))
  change realTokenChiralityLinear (realTokenChiralityLinear ψ) = ψ at hsq
  rw [hsq]
  module

theorem realTokenPhaseOperator_commutes_chirality_linear :
    (realTokenPhaseOperator (V := V)).comp
        (realTokenChiralityLinear (V := V)) =
      (realTokenChiralityLinear (V := V)).comp
        (realTokenPhaseOperator (V := V)) := by
  apply LinearMap.ext
  intro ψ
  funext i
  by_cases h : i.2 = 0 <;> simp [realTokenPhaseOperator,
    realTokenChiralityLinear, tokenChiralityComplex, h]

theorem realTokenOperator_commutes_chirality_implies_plusProjector
    (T : RealTokenOperator (V := V))
    (hT : T.comp (realTokenChiralityLinear (V := V)) =
      (realTokenChiralityLinear (V := V)).comp T) :
    T.comp (realTokenChiralityPlusProjector (V := V)) =
      (realTokenChiralityPlusProjector (V := V)).comp T := by
  apply LinearMap.ext
  intro ψ
  simp only [realTokenChiralityPlusProjector, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.add_apply, smul_add, map_add,
    map_smul, LinearMap.id_apply]
  have hc := congrArg (fun U : RealTokenOperator (V := V) => U ψ) hT
  change T (realTokenChiralityLinear ψ) =
    realTokenChiralityLinear (T ψ) at hc
  rw [hc]

theorem realTokenOperator_commutes_chirality_implies_minusProjector
    (T : RealTokenOperator (V := V))
    (hT : T.comp (realTokenChiralityLinear (V := V)) =
      (realTokenChiralityLinear (V := V)).comp T) :
    T.comp (realTokenChiralityMinusProjector (V := V)) =
      (realTokenChiralityMinusProjector (V := V)).comp T := by
  apply LinearMap.ext
  intro ψ
  simp only [realTokenChiralityMinusProjector, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.sub_apply, smul_sub, map_sub,
    map_smul, LinearMap.id_apply]
  have hc := congrArg (fun U : RealTokenOperator (V := V) => U ψ) hT
  change T (realTokenChiralityLinear ψ) =
    realTokenChiralityLinear (T ψ) at hc
  rw [hc]

theorem realTokenPhaseOperator_commutes_chiralityPlusProjector :
    (realTokenPhaseOperator (V := V)).comp
        (realTokenChiralityPlusProjector (V := V)) =
      (realTokenChiralityPlusProjector (V := V)).comp
        (realTokenPhaseOperator (V := V)) := by
  apply LinearMap.ext
  intro ψ
  simp only [realTokenChiralityPlusProjector, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.add_apply, smul_add, map_add,
    map_smul, LinearMap.id_apply]
  have hc := congrArg (fun T : RealTokenOperator (V := V) => T ψ)
    (realTokenPhaseOperator_commutes_chirality_linear (V := V))
  change realTokenPhaseOperator (realTokenChiralityLinear ψ) =
    realTokenChiralityLinear (realTokenPhaseOperator ψ) at hc
  rw [hc]

theorem realTokenPhaseOperator_commutes_chiralityMinusProjector :
    (realTokenPhaseOperator (V := V)).comp
        (realTokenChiralityMinusProjector (V := V)) =
      (realTokenChiralityMinusProjector (V := V)).comp
        (realTokenPhaseOperator (V := V)) := by
  apply LinearMap.ext
  intro ψ
  simp only [realTokenChiralityMinusProjector, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.sub_apply, smul_sub, map_sub,
    map_smul, LinearMap.id_apply]
  have hc := congrArg (fun T : RealTokenOperator (V := V) => T ψ)
    (realTokenPhaseOperator_commutes_chirality_linear (V := V))
  change realTokenPhaseOperator (realTokenChiralityLinear ψ) =
    realTokenChiralityLinear (realTokenPhaseOperator ψ) at hc
  rw [hc]

theorem complexOperatorToReal_commutes_phase
    (T : TokenHilbertSpace V →ₗ[ℂ] TokenHilbertSpace V) :
    (complexOperatorToReal T).comp (realTokenPhaseOperator (V := V)) =
      (realTokenPhaseOperator (V := V)).comp (complexOperatorToReal T) := by
  apply LinearMap.ext
  intro ψ
  funext i
  let ψc : TokenHilbertSpace V := ψ
  change T (fun j => Complex.I * ψc j) i = Complex.I * T ψc i
  have hphase : (fun j => Complex.I * ψc j) =
      (Complex.I : ℂ) • ψc := by
    funext j
    rfl
  rw [hphase, T.map_smul]
  rfl

theorem realifiedTotalTokenGenerator_commutes_phase
    (gen : TokenGenerator (V := V)) :
    (realifiedTotalTokenGenerator gen).comp
        (realTokenPhaseOperator (V := V)) =
      (realTokenPhaseOperator (V := V)).comp
        (realifiedTotalTokenGenerator gen) := by
  exact complexOperatorToReal_commutes_phase
    (totalTokenGenerator gen)

@[simp] theorem realTokenChiralityOperator_apply
    (ψ : RealTokenHilbertSpace (V := V)) (i : V × Fin 2) :
    realTokenChiralityOperator ψ i = if i.2 = 0 then ψ i else -ψ i := rfl

theorem realTokenChiralityOperator_sq :
    ∀ ψ : RealTokenHilbertSpace (V := V),
      realTokenChiralityOperator (realTokenChiralityOperator ψ) = ψ := by
  intro ψ
  funext i
  by_cases h : i.2 = 0 <;> simp [realTokenChiralityOperator, h]

theorem realTokenPhaseOperator_commutes_chirality :
    ∀ ψ : RealTokenHilbertSpace (V := V),
      realTokenPhaseOperator (realTokenChiralityOperator ψ) =
        realTokenChiralityOperator (realTokenPhaseOperator ψ) := by
  intro ψ
  funext i
  by_cases h : i.2 = 0 <;> simp [realTokenPhaseOperator,
    realTokenChiralityOperator, h]

end
end InfoGeometry.Dynamics
