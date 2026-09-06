import InfoGeometry.Modular.SchrodingerFlow

/-!
# Dirac square and bounded heat flow

This owner connects a bounded continuous Dirac endomorphism with the existing
exponential flow.  It proves only the bounded semigroup and orbit equation;
positivity, self-adjointness, unbounded operators, and analytic heat kernels
remain separate structures.
-/

noncomputable section

namespace InfoGeometry.Canonical.DiracHeatSemigroupBridge

open InfoGeometry.Modular.SchrodingerFlow

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

local notation "EndE" => E →L[ℝ] E

/-- The bounded continuous square of a Dirac operator. -/
noncomputable def diracSquareEnd (D : EndE) : EndE := D.comp D

/-- The continuous-linear Dirac--Kähler operator `d + d⋆`. -/
noncomputable def diracKahlerEnd (d dstar : EndE) : EndE := d + dstar

/-- The continuous-linear Hodge--de Rham Laplacian. -/
noncomputable def hodgeDeRhamLaplacianEnd (d dstar : EndE) : EndE :=
  d.comp dstar + dstar.comp d

omit [CompleteSpace E] in
theorem diracKahlerSquareEnd_eq_laplacian
    (d dstar : EndE)
    (hd2 : d.comp d = 0)
    (hdstar2 : dstar.comp dstar = 0) :
    diracSquareEnd (diracKahlerEnd d dstar) =
      hodgeDeRhamLaplacianEnd d dstar := by
  unfold diracSquareEnd diracKahlerEnd hodgeDeRhamLaplacianEnd
  ext x
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  have hd_sq : d (d x) = 0 := by
    exact congrArg (fun f => f x) hd2
  have hdstar_sq : dstar (dstar x) = 0 := by
    exact congrArg (fun f => f x) hdstar2
  rw [map_add, map_add, hd_sq, hdstar_sq]
  abel

omit [CompleteSpace E] in
@[simp]
theorem diracSquareEnd_apply (D : EndE) (x : E) :
    diracSquareEnd D x = D (D x) := by
  simp [diracSquareEnd]

/-! Intertwining a Dirac generator automatically intertwines its square. -/

omit [CompleteSpace E] in
theorem diracSquareEnd_intertwines
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (D : EndE) (D' : F →L[ℝ] F) (ι : E →L[ℝ] F)
    (hι : ι.comp D = D'.comp ι) :
    ι.comp (diracSquareEnd D) =
      (diracSquareEnd D').comp ι := by
  unfold diracSquareEnd
  calc
    ι.comp (D.comp D) = (ι.comp D).comp D := by
      rw [ContinuousLinearMap.comp_assoc]
    _ = (D'.comp ι).comp D := by rw [hι]
    _ = D'.comp (ι.comp D) := by rw [ContinuousLinearMap.comp_assoc]
    _ = D'.comp (D'.comp ι) := by rw [hι]

/-! Continuous intertwiners transport the bounded exponential flow. -/

theorem flow_intertwines
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F]
    (A : EndE) (B : F →L[ℝ] F) (ι : E →L[ℝ] F)
    (hι : ι.comp A = B.comp ι) (t : ℝ) (x : E) :
    ι (flow A t x) = flow B t (ι x) := by
  have hscaled : ι.comp (t • A) = (t • B).comp ι := by
    rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, hι]
  have hpow : ∀ n : ℕ,
      ι.comp ((t • A) ^ n) = ((t • B) ^ n).comp ι := by
    intro n
    induction n with
    | zero =>
        change ι.comp (ContinuousLinearMap.id ℝ E) =
          (ContinuousLinearMap.id ℝ F).comp ι
        simp
    | succ n ih =>
        change ι.comp (((t • A) ^ n).comp (t • A)) =
          (((t • B) ^ n).comp (t • B)).comp ι
        rw [← ContinuousLinearMap.comp_assoc, ih,
          ContinuousLinearMap.comp_assoc, hscaled,
          ContinuousLinearMap.comp_assoc]
  rw [flow, flow]
  have hsA := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • A)
  have hsB := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • B)
  let evA := (ContinuousLinearMap.apply ℝ E) x
  let evB := (ContinuousLinearMap.apply ℝ F) (ι x)
  have hsAx := hsA.map evA evA.continuous
  have hAeval : evA (∑' n, (↑n.factorial : ℝ)⁻¹ • (t • A) ^ n) =
      ∑' n, evA ((↑n.factorial : ℝ)⁻¹ • (t • A) ^ n) :=
    ContinuousLinearMap.map_tsum evA hsA.summable
  have hBeval : evB (∑' n, (↑n.factorial : ℝ)⁻¹ • (t • B) ^ n) =
      ∑' n, evB ((↑n.factorial : ℝ)⁻¹ • (t • B) ^ n) :=
    ContinuousLinearMap.map_tsum evB hsB.summable
  rw [← hsA.tsum_eq, ← hsB.tsum_eq]
  rw [← ContinuousLinearMap.apply_apply x,
    ← ContinuousLinearMap.apply_apply (ι x)]
  have hAeval' : ((ContinuousLinearMap.apply ℝ E) x)
      (∑' n, (↑n.factorial : ℝ)⁻¹ • (t • A) ^ n) =
      ∑' n, ((ContinuousLinearMap.apply ℝ E) x)
        ((↑n.factorial : ℝ)⁻¹ • (t • A) ^ n) := by
    simpa [evA] using hAeval
  have hBeval' : ((ContinuousLinearMap.apply ℝ F) (ι x))
      (∑' n, (↑n.factorial : ℝ)⁻¹ • (t • B) ^ n) =
      ∑' n, ((ContinuousLinearMap.apply ℝ F) (ι x))
        ((↑n.factorial : ℝ)⁻¹ • (t • B) ^ n) := by
    simpa [evB] using hBeval
  rw [hAeval', hBeval']
  have hAmap : ι (∑' n, evA ((↑n.factorial : ℝ)⁻¹ • (t • A) ^ n)) =
      ∑' n, ι (evA ((↑n.factorial : ℝ)⁻¹ • (t • A) ^ n)) :=
    ContinuousLinearMap.map_tsum ι hsAx.summable
  rw [hAmap]
  congr 1
  funext n
  rw [ContinuousLinearMap.apply_apply, ContinuousLinearMap.apply_apply]
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
  rw [map_smul]
  rw [← ContinuousLinearMap.comp_apply, hpow]
  simp [ContinuousLinearMap.comp_apply]

/-- The bounded exponential flow generated by `-D²`. -/
noncomputable def diracHeatFlow (D : EndE) (t : ℝ) : EndE :=
  flow (-diracSquareEnd D) t

theorem diracHeatFlow_intertwines
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F]
    (D : EndE) (D' : F →L[ℝ] F) (ι : E →L[ℝ] F)
    (hι : ι.comp D = D'.comp ι) (t : ℝ) (x : E) :
    ι (diracHeatFlow D t x) = diracHeatFlow D' t (ι x) := by
  have hsq := diracSquareEnd_intertwines D D' ι hι
  apply flow_intertwines (-diracSquareEnd D) (-diracSquareEnd D') ι
  · simpa [diracSquareEnd] using hsq

theorem diracHeatFlow_add (D : EndE) (s t : ℝ) :
    diracHeatFlow D (s + t) =
      diracHeatFlow D s * diracHeatFlow D t := by
  exact flow_add (-diracSquareEnd D) s t

theorem hasDerivAt_diracHeatFlow_orbit
    (D : EndE) (x : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => diracHeatFlow D s x)
      ((-diracSquareEnd D) (diracHeatFlow D t x)) t := by
  exact hasDerivAt_orbit (-diracSquareEnd D) x t

theorem diracHeatFlow_orbit_deriv
    (D : EndE) (x : E) (t : ℝ) :
    deriv (fun s : ℝ => diracHeatFlow D s x) t =
      (-diracSquareEnd D) (diracHeatFlow D t x) := by
  exact (hasDerivAt_diracHeatFlow_orbit D x t).deriv

/-! ## Explicit Laplacian specialization -/

theorem diracHeatFlow_orbit_deriv_eq_neg_laplacian
    (D Δ : EndE) (hSquare : diracSquareEnd D = Δ)
    (x : E) (t : ℝ) :
    deriv (fun s : ℝ => diracHeatFlow D s x) t =
      -Δ (diracHeatFlow D t x) := by
  have h := diracHeatFlow_orbit_deriv D x t
  rw [hSquare] at h
  simpa using h

theorem diracHeatFlow_is_heat_solution
    (D Δ : EndE) (hSquare : diracSquareEnd D = Δ)
    (x : E) :
    ∀ t : ℝ,
      deriv (fun s : ℝ => diracHeatFlow D s x) t =
        -Δ (diracHeatFlow D t x) := by
  intro t
  exact diracHeatFlow_orbit_deriv_eq_neg_laplacian D Δ hSquare x t

theorem diracKahlerHeatFlow_is_heat_solution
    (d dstar : EndE)
    (hd2 : d.comp d = 0)
    (hdstar2 : dstar.comp dstar = 0)
    (x : E) :
    ∀ t : ℝ,
      deriv (fun s =>
        diracHeatFlow (diracKahlerEnd d dstar) s x) t =
        -hodgeDeRhamLaplacianEnd d dstar
          (diracHeatFlow (diracKahlerEnd d dstar) t x) := by
  intro t
  apply diracHeatFlow_orbit_deriv_eq_neg_laplacian
    (diracKahlerEnd d dstar)
    (hodgeDeRhamLaplacianEnd d dstar)
  exact diracKahlerSquareEnd_eq_laplacian d dstar hd2 hdstar2

end InfoGeometry.Canonical.DiracHeatSemigroupBridge
