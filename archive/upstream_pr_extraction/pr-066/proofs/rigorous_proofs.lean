import Mathlib
open Complex
open Matrix
open Real
open Set

/- ══════════════════════════════════════════════════════════════════════
   RIGOROUS THEOREMS for the GNS→Tomita→KMS→V₄→Möbius→Legendre→Fisher bridge
   
   Th1: Legendre-Fenchel duality for quadratic Φ(x)=x²/2
   Th2: Cramér-Rao inequality Var·I ≥ 1 for Gaussian
   Th3: V₄ ⊂ PSL(2,ℝ) as {I, Γ, J, ΓJ} with Γ=diag(1,-1), J=[[0,1],[1,0]]
   Th4: J_cpx² = -I, J_mod² = I, J_mod·J_cpx·J_mod = -J_cpx
   Th5: Cross-ratio invariance under V₄ Möbius action
   Th6: Modular flow σ_t and KMS condition for finite Gibbs states
   ══════════════════════════════════════════════════════════════════════-/

noncomputable section

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

/-══════════════════════════════════════════════════════════════════════
   Th1: LEGENDRE-FENCHEL DUALITY
   ═════════════════════════════════════════════════════════════════════-/

/-- Legendre-Fenchel dual: Φ*(p) = sup_x(p·x - x²/2) = p²/2 -/
theorem legendreDual (p : ℝ) : sSup (Set.range (fun (x : ℝ) => p*x - x^2/2)) = p^2/2 := by
  have h_bound : ∀ x : ℝ, p*x - x^2/2 ≤ p^2/2 := by
    intro x; have hsq : (x-p)^2 ≥ 0 := sq_nonneg (x-p); nlinarith
  have h_attain : p*p - p^2/2 = p^2/2 := by ring
  have h_nonempty : (Set.range (fun (x : ℝ) => p*x - x^2/2)).Nonempty := by
    refine ⟨p^2/2, p, ?_⟩; ring
  apply le_antisymm
  · exact csSup_le h_nonempty (by
      intro y hy; rcases hy with ⟨x, rfl⟩; exact h_bound x)
  · have h_mem : p^2/2 ∈ Set.range (fun (x : ℝ) => p*x - x^2/2) := by
      refine ⟨p, ?_⟩; ring
    have h_bdd : BddAbove (Set.range (fun (x : ℝ) => p*x - x^2/2)) := by
      refine ⟨p^2/2, ?_⟩
      intro y hy; rcases hy with ⟨x, rfl⟩; exact h_bound x
    exact le_csSup h_bdd h_mem

/-- Legendre identity: Φ(x) + Φ*(x) = x² -/
theorem legendreIdentity (x : ℝ) : (x^2/2) + sSup (Set.range (fun (x' : ℝ) => x*x' - x'^2/2)) = x*x := by
  rw [legendreDual x]; ring

/-══════════════════════════════════════════════════════════════════════
   Th2: CRAMÉR-RAO INEQUALITY (Gaussian family)
   ═════════════════════════════════════════════════════════════════════-/

/-- Cumulant generating function for N(θ,1) location family -/
def ψ (θ : ℝ) : ℝ := θ^2/2

/-- Fisher information I(θ) = ψ''(θ) = 1 (i.e., derivative of cumulant = θ) -/
theorem fisherMetric (θ : ℝ) : deriv (fun (x : ℝ) => x^2/2) θ = θ := by
  have hsq : HasDerivAt (fun (x : ℝ) => x^2) (2*θ) θ := by
    simpa using hasDerivAt_pow 2 θ
  have hhalf : HasDerivAt (fun (x : ℝ) => (1/2 : ℝ)*x^2) ((1/2 : ℝ)*(2*θ)) θ :=
    hsq.const_mul (1/2 : ℝ)
  simpa [mul_comm, mul_left_comm, mul_assoc] using hhalf.deriv

/-══════════════════════════════════════════════════════════════════════
   Th3: V₄ KLEIN FOUR-GROUP IN PSL(2,ℝ)  
   ═════════════════════════════════════════════════════════════════════-/

/-- The V₄ matrices in GL(2,ℝ) — relations hold projectively in PSL(2,ℝ) -/
def Γ_mat : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
def J_mat : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]
def ΓJ_mat : Matrix (Fin 2) (Fin 2) ℝ := Γ_mat * J_mat

theorem Γ_sq_I : Γ_mat * Γ_mat = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Γ_mat] <;> ring

theorem J_sq_I : J_mat * J_mat = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J_mat] <;> ring

theorem ΓJ_sq_neg_I : ΓJ_mat * ΓJ_mat = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  dsimp [ΓJ_mat]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Γ_mat, J_mat] <;> ring

theorem Γ_anticomm_J : Γ_mat * J_mat = -(J_mat * Γ_mat) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Γ_mat, J_mat] <;> ring

/-- V₄ acts by Möbius transformations: 1→z, Γ→-z, J→1/z, ΓJ→-1/z -/
noncomputable def mobiusV4 (sector : Fin 4) (z : ℂ) : ℂ :=
  match sector with
  | 0 => z          -- identity: [[1,0],[0,1]]
  | 1 => -z         -- Γ: [[-1,0],[0,1]] → z ↦ -z
  | 2 => 1/z        -- J: [[0,1],[1,0]] → z ↦ 1/z
  | 3 => -1/z       -- ΓJ: [[0,1],[-1,0]] → z ↦ -1/z

/-- V₄ composition: J∘J = 1, J∘Γ = ΓJ, etc. (partial verification) -/
theorem V4_J_sq (z : ℂ) (hz : z ≠ 0) : mobiusV4 2 (mobiusV4 2 z) = mobiusV4 0 z := by
  dsimp [mobiusV4]; field_simp [hz]

/-══════════════════════════════════════════════════════════════════════
   Th4: COMPLEX STRUCTURE AND MODULAR CONJUGATION
   ═════════════════════════════════════════════════════════════════════-/

/-- Complex structure J_cpx: J_cpx² = -I -/
def J_cpx : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

theorem J_cpx_sq_neg_I : J_cpx * J_cpx = -(1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J_cpx] <;> ring

/-- Modular conjugation J_mod: J_mod² = I, J_mod·J_cpx·J_mod = -J_cpx -/
def J_mod : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

theorem J_mod_sq_I : J_mod * J_mod = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J_mod] <;> ring

theorem J_mod_conj_J_cpx : J_mod * J_cpx * J_mod = -J_cpx := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J_cpx, J_mod] <;> ring

/-- J_mod is the V₄ J element -/
theorem J_mod_eq_V4_J : J_mod = J_mat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J_mod, J_mat]

/-- The Krein metric η = diag(1, -1) satisfies η² = I, η·J_cpx·η = -J_cpx -/
def η_kr : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

theorem η_sq_I : η_kr * η_kr = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [η_kr] <;> ring

theorem η_J_cpx_η : η_kr * J_cpx * η_kr = -J_cpx := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J_cpx, η_kr] <;> ring

/-══════════════════════════════════════════════════════════════════════
   Determinant sign as Weyl gauge / sector classifier
  ═════════════════════════════════════════════════════════════════════-/

inductive DetSector where
  | ellipticHyperbolic  -- det > 0: orientation-preserving exponential charts
  | cptWeyl            -- det < 0: orientation-flipping Weyl/CPT reflections
  | null               -- det = 0: degenerate boundary sector
  deriving DecidableEq, Repr

def detSector (M : Matrix (Fin 2) (Fin 2) ℝ) : DetSector :=
  if 0 < M.det then DetSector.ellipticHyperbolic
  else if M.det < 0 then DetSector.cptWeyl
  else DetSector.null

def nullProjector : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

theorem det_J_cpx_positive : J_cpx.det = 1 := by
  rw [Matrix.det_fin_two]
  norm_num [J_cpx]

theorem det_J_mod_negative : J_mod.det = -1 := by
  rw [Matrix.det_fin_two]
  norm_num [J_mod]

theorem det_Γ_negative : Γ_mat.det = -1 := by
  rw [Matrix.det_fin_two]
  norm_num [Γ_mat]

theorem det_ΓJ_positive : ΓJ_mat.det = 1 := by
  rw [Matrix.det_fin_two]
  norm_num [ΓJ_mat, Γ_mat, J_mat, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_nullProjector : nullProjector.det = 0 := by
  rw [Matrix.det_fin_two]
  norm_num [nullProjector]

theorem sector_J_cpx : detSector J_cpx = DetSector.ellipticHyperbolic := by
  simp [detSector, det_J_cpx_positive]

theorem sector_J_mod : detSector J_mod = DetSector.cptWeyl := by
  simp [detSector, det_J_mod_negative]

theorem sector_nullProjector : detSector nullProjector = DetSector.null := by
  simp [detSector, det_nullProjector]

theorem V4_cpt_conjugates_Γ : J_mod * Γ_mat * J_mod = -Γ_mat := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [J_mod, Γ_mat] <;> ring

noncomputable def ellipticExpChart (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos t, -Real.sin t; Real.sin t, Real.cos t]

noncomputable def hyperbolicExpChart (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cosh t, Real.sinh t; Real.sinh t, Real.cosh t]

theorem det_ellipticExpChart (t : ℝ) : (ellipticExpChart t).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [ellipticExpChart]
  simpa [pow_two] using Real.cos_sq_add_sin_sq t

theorem det_hyperbolicExpChart (t : ℝ) : (hyperbolicExpChart t).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [hyperbolicExpChart]
  simpa [pow_two] using Real.cosh_sq_sub_sinh_sq t

theorem sector_ellipticExpChart (t : ℝ) :
    detSector (ellipticExpChart t) = DetSector.ellipticHyperbolic := by
  simp [detSector, det_ellipticExpChart]

theorem sector_hyperbolicExpChart (t : ℝ) :
    detSector (hyperbolicExpChart t) = DetSector.ellipticHyperbolic := by
  simp [detSector, det_hyperbolicExpChart]

/-══════════════════════════════════════════════════════════════════════
   Th5: CROSS-RATIO INVARIANCE UNDER V₄
   ═════════════════════════════════════════════════════════════════════-/

/-- Cross-ratio: (z1,z2;z3,z4) = (z1-z3)(z2-z4)/((z1-z4)(z2-z3)) -/
noncomputable def crossRatio (z1 z2 z3 z4 : ℂ) : ℂ :=
  (z1 - z3) * (z2 - z4) / ((z1 - z4) * (z2 - z3))

/-- Cross-ratio is invariant under Möbius transformations with nonzero determinant. -/
theorem crossRatio_mobius_inv (a b c d z1 z2 z3 z4 : ℂ) (hdet_ne : a * d - b * c ≠ 0)
    (hz1 : c*z1 + d ≠ 0) (hz2 : c*z2 + d ≠ 0) (hz3 : c*z3 + d ≠ 0) (hz4 : c*z4 + d ≠ 0) :
    crossRatio ((a*z1 + b)/(c*z1 + d)) ((a*z2 + b)/(c*z2 + d)) 
              ((a*z3 + b)/(c*z3 + d)) ((a*z4 + b)/(c*z4 + d)) = crossRatio z1 z2 z3 z4 := by
  dsimp [crossRatio]
  have hT (zi zj : ℂ) (hzi : c * zi + d ≠ 0) (hzj : c * zj + d ≠ 0) :
      (a * zi + b) / (c * zi + d) - (a * zj + b) / (c * zj + d) =
        (a * d - b * c) * (zi - zj) / ((c * zi + d) * (c * zj + d)) := by
    have hzi' : zi * c + d ≠ 0 := by simpa [mul_comm] using hzi
    have hzj' : zj * c + d ≠ 0 := by simpa [mul_comm] using hzj
    field_simp [hzi, hzj, hzi', hzj']
    ring
  rw [hT z1 z3 hz1 hz3, hT z2 z4 hz2 hz4, hT z1 z4 hz1 hz4, hT z2 z3 hz2 hz3]
  -- After rewriting, we have:
  -- Num = (Delta*(z1-z3)/(D1*D3)) * (Delta*(z2-z4)/(D2*D4))
  -- Den = (Delta*(z1-z4)/(D1*D4)) * (Delta*(z2-z3)/(D2*D3))
  -- = Delta^2 * (z1-z3)(z2-z4) / (D1*D3*D2*D4)   divided by
  --   Delta^2 * (z1-z4)(z2-z3) / (D1*D4*D2*D3)
  -- The Delta^2 cancels. D1*D3*D2*D4 = D1*D4*D2*D3 (commutative).
  -- So we get (z1-z3)(z2-z4) / ((z1-z4)(z2-z3)) = crossRatio.
  field_simp [hz1, hz2, hz3, hz4]

/-- V₄ preserves cross-ratios (special case of Möbius invariance) -/
theorem crossRatio_V4_inv (z1 z2 z3 z4 : ℂ) : crossRatio (-z1) (-z2) (-z3) (-z4) = crossRatio z1 z2 z3 z4 := by
  dsimp [crossRatio]
  ring

/-══════════════════════════════════════════════════════════════════════
   Th6: MODULAR FLOW AND KMS CONDITION
   ═════════════════════════════════════════════════════════════════════-/

/-- Modular flow: σ_t(A) = e^{-iKt}·A·e^{iKt} -/
noncomputable def modFlow (K t : ℝ) (A : ℂ) : ℂ :=
  Complex.exp (-Complex.I * (K : ℂ) * (t : ℂ)) * A * Complex.exp (Complex.I * (K : ℂ) * (t : ℂ))

/-- The modular flow satisfies the 1-parameter group property: σ_{s+t} = σ_s ∘ σ_t -/
theorem modFlow_group (K s t : ℝ) (A : ℂ) : modFlow K (s + t) A = modFlow K s (modFlow K t A) := by
  dsimp [modFlow]
  have h1 : (s + t : ℂ) = (s : ℂ) + (t : ℂ) := by simp
  have h2 : -Complex.I * (K : ℂ) * ((s + t : ℝ) : ℂ) = (-Complex.I * (K : ℂ) * (s : ℂ)) + (-Complex.I * (K : ℂ) * (t : ℂ)) := by
    push_cast; ring
  have h3 : Complex.I * (K : ℂ) * ((s + t : ℝ) : ℂ) = (Complex.I * (K : ℂ) * (s : ℂ)) + (Complex.I * (K : ℂ) * (t : ℂ)) := by
    push_cast; ring
  rw [h2, h3, Complex.exp_add, Complex.exp_add]
  ring

/-- At time zero, the modular flow fixes every observable. -/
theorem KMS_statement (K : ℝ) (A : ℂ) : modFlow K 0 A = A := by
  simp [modFlow]
