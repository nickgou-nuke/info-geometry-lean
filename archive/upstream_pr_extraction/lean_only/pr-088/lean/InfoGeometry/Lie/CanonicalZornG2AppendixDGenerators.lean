import InfoGeometry.Lie.SplitOctonionGogberashviliDerivationBridge
import InfoGeometry.Lie.SplitOctonionCircularMultiplicationTable

/-!
# Appendix-D generator packet

The paper's Appendix D lists the families `X_nn`, `X_n0`, `X_0n`, and
`X_nm`, with the single diagonal relation `X₁₁ + X₂₂ + X₃₃ = 0`.

The present repository already owns the corresponding paper-side Lie
realisation as `paperDerivationLieHom.range`.  This file records the
generator-level consequences without inventing a second coordinate carrier:
the 14 paper generators are the transported canonical derivation basis.
The source-coordinate carrier below makes the four printed linear operators
literal.  The transported derivation basis is kept separately: it is the
Lie-algebra realization used by the rest of the repository, while these
operators are the paper's seven-coordinate infinitesimal action.
-/

noncomputable section

namespace InfoGeometry.Lie.CanonicalZornG2AppendixDGenerators

open InfoGeometry.Lie.SplitOctonionGogberashviliDerivationBridge
open InfoGeometry.Algebra.Zorn.ParityTwistedLeviCivita

/-! ### The source-coordinate carrier used by Appendix D -/

abbrev AppendixDVector := ℝ × (Fin 3 → ℝ) × (Fin 3 → ℝ)

private def epsilon (i j k : Fin 3) : ℝ := leviCivita3 i j k

private def epsilonAction (n : Fin 3) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => ∑ m : Fin 3, epsilon n m i * v m

private theorem epsilonAction_add (n : Fin 3) (v w : Fin 3 → ℝ) :
    epsilonAction n (v + w) = epsilonAction n v + epsilonAction n w := by
  funext i
  simp only [epsilonAction, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  ring

private theorem epsilonAction_smul (n : Fin 3) (c : ℝ) (v : Fin 3 → ℝ) :
    epsilonAction n (c • v) = c • epsilonAction n v := by
  funext i
  simp only [epsilonAction, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- The two epsilon terms printed in (D.1) combine to `epsilonAction`.
The second summand is the same term after swapping the two contracted
indices and using the alternating Levi--Civita tensor. -/
theorem epsilonAction_appendixD_expansion (n : Fin 3) (v : Fin 3 → ℝ)
    (i : Fin 3) :
    epsilonAction n v i =
      (1 / 2 : ℝ) *
        (∑ m : Fin 3, epsilon n m i * v m -
          ∑ k : Fin 3, epsilon n i k * v k) := by
  fin_cases n <;> fin_cases i <;>
    simp [epsilonAction, epsilon, leviCivita3, Fin.sum_univ_three] <;>
    ring

theorem epsilonAction_appendixD_expansion_public (n : Fin 3) (v : Fin 3 → ℝ)
    (i : Fin 3) :
    epsilonAction n v i =
      (1 / 2 : ℝ) *
        (∑ m : Fin 3, leviCivita3 n m i * v m -
          ∑ k : Fin 3, leviCivita3 n i k * v k) := by
  simpa [epsilon] using epsilonAction_appendixD_expansion n v i

private def diagonalCoordinate (n : Fin 3) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => if n = i then v n else 0

@[simp] theorem diagonalCoordinate_apply (n i : Fin 3) (v : Fin 3 → ℝ) :
    diagonalCoordinate n v i = if n = i then v n else 0 := by
  rfl

private theorem diagonalCoordinate_sum (v : Fin 3 → ℝ) (i : Fin 3) :
    ∑ n : Fin 3, diagonalCoordinate n v i = v i := by
  classical
  simpa [diagonalCoordinate, Fin.sum_univ_three] using
    (Finset.sum_eq_single (s := (Finset.univ : Finset (Fin 3))) i
      (by
        intro b hb hne
        simp [diagonalCoordinate, hne])
      (by intro hi; exact (hi (Finset.mem_univ i)).elim))

/-- The literal `X_nn` source-coordinate operator from Appendix D. -/
noncomputable def appendixDXnn (n : Fin 3) :
    AppendixDVector →ₗ[ℝ] AppendixDVector :=
  { toFun := fun v =>
      (0,
        diagonalCoordinate n v.2.1 - (1 / 3 : ℝ) • v.2.1,
        -(diagonalCoordinate n v.2.2) + (1 / 3 : ℝ) • v.2.2)
    map_add' := by
      intro v w
      apply Prod.ext
      · simp
      · apply Prod.ext
        · funext i
          by_cases h : n = i <;>
            simp [diagonalCoordinate, h, Pi.add_apply, smul_add] <;> ring
        · funext i
          by_cases h : n = i <;>
            simp [diagonalCoordinate, h, Pi.add_apply, smul_add] <;> ring
    map_smul' := by
      intro c v
      apply Prod.ext
      · simp
      · apply Prod.ext
        · funext i
          by_cases h : n = i <;>
            simp [diagonalCoordinate, h, Pi.smul_apply, smul_add, smul_sub] <;> ring
        · funext i
          by_cases h : n = i <;>
            simp [diagonalCoordinate, h, Pi.smul_apply, smul_add, smul_sub] <;> ring }

@[simp] theorem appendixDXnn_apply (n : Fin 3) (v : AppendixDVector) :
    appendixDXnn n v =
      (0,
        diagonalCoordinate n v.2.1 - (1 / 3 : ℝ) • v.2.1,
        -(diagonalCoordinate n v.2.2) + (1 / 3 : ℝ) • v.2.2) := rfl

@[simp] theorem appendixDXnn_a (n : Fin 3) (v : AppendixDVector) :
    (appendixDXnn n v).1 = 0 := rfl

@[simp] theorem appendixDXnn_y (n : Fin 3) (v : AppendixDVector) (i : Fin 3) :
    (appendixDXnn n v).2.1 i =
      (if n = i then v.2.1 n else 0) - (1 / 3 : ℝ) * v.2.1 i := by
  change diagonalCoordinate n v.2.1 i - (1 / 3 : ℝ) • v.2.1 i = _
  rw [diagonalCoordinate_apply]
  simp [Pi.smul_apply, smul_eq_mul]

@[simp] theorem appendixDXnn_z (n : Fin 3) (v : AppendixDVector) (i : Fin 3) :
    (appendixDXnn n v).2.2 i =
      -(if n = i then v.2.2 n else 0) + (1 / 3 : ℝ) * v.2.2 i := by
  change -(diagonalCoordinate n v.2.2 i) + (1 / 3 : ℝ) • v.2.2 i = _
  rw [diagonalCoordinate_apply]
  simp [Pi.smul_apply, smul_eq_mul]

theorem appendixDXnn_diagonal_relation :
    appendixDXnn 0 + appendixDXnn 1 + appendixDXnn 2 = 0 := by
  apply LinearMap.ext
  intro v
  apply Prod.ext
  · simp
  · apply Prod.ext
    · funext i
      have h := diagonalCoordinate_sum v.2.1 i
      rw [Fin.sum_univ_three] at h
      have h' :
          diagonalCoordinate 0 v.2.1 i +
              diagonalCoordinate 1 v.2.1 i +
              diagonalCoordinate 2 v.2.1 i = v.2.1 i := by
        simpa using h
      change
        (diagonalCoordinate 0 v.2.1 i - (1 / 3 : ℝ) • v.2.1 i) +
            (diagonalCoordinate 1 v.2.1 i - (1 / 3 : ℝ) • v.2.1 i) +
            (diagonalCoordinate 2 v.2.1 i - (1 / 3 : ℝ) • v.2.1 i) = 0
      calc
        _ = (diagonalCoordinate 0 v.2.1 i +
              diagonalCoordinate 1 v.2.1 i +
              diagonalCoordinate 2 v.2.1 i) - v.2.1 i := by
                norm_num [smul_eq_mul]
                ring
        _ = 0 := by rw [h']; ring
    · funext i
      have h := diagonalCoordinate_sum v.2.2 i
      rw [Fin.sum_univ_three] at h
      have h' :
          diagonalCoordinate 0 v.2.2 i +
              diagonalCoordinate 1 v.2.2 i +
              diagonalCoordinate 2 v.2.2 i = v.2.2 i := by
        simpa using h
      change
        (-(diagonalCoordinate 0 v.2.2 i) + (1 / 3 : ℝ) • v.2.2 i) +
            (-(diagonalCoordinate 1 v.2.2 i) + (1 / 3 : ℝ) • v.2.2 i) +
            (-(diagonalCoordinate 2 v.2.2 i) + (1 / 3 : ℝ) • v.2.2 i) = 0
      calc
        _ = -(diagonalCoordinate 0 v.2.2 i +
              diagonalCoordinate 1 v.2.2 i +
              diagonalCoordinate 2 v.2.2 i) + v.2.2 i := by
                norm_num [smul_eq_mul]
                ring
        _ = 0 := by rw [h']; ring

/-! The off-diagonal `X_nm` family is unambiguous in (D.1). -/

/-- The literal source-coordinate operator
`X_nm = - z_m ∂/∂z_n + y_n ∂/∂y_m`, for `n ≠ m`. -/
noncomputable def appendixDXnm (n m : Fin 3) (_h : n ≠ m) :
    AppendixDVector →ₗ[ℝ] AppendixDVector :=
  { toFun := fun v =>
      (0, Pi.single m (v.2.1 n), -Pi.single n (v.2.2 m))
    map_add' := by
      intro v w
      apply Prod.ext
      · simp
      · apply Prod.ext
        · funext i
          by_cases h : m = i <;>
            simp [Pi.single_apply, h] <;> ring
        · funext i
          by_cases h : n = i <;>
            simp [Pi.single_apply, h] <;> ring
    map_smul' := by
      intro c v
      apply Prod.ext
      · simp
      · apply Prod.ext
        · funext i
          by_cases h : m = i <;>
            simp [Pi.single_apply, h] <;> ring
        · funext i
          by_cases h : n = i <;>
            simp [Pi.single_apply, h] <;> ring }

@[simp] theorem appendixDXnm_apply (n m : Fin 3) (h : n ≠ m) (v : AppendixDVector) :
    appendixDXnm n m h v =
      (0, Pi.single m (v.2.1 n), -Pi.single n (v.2.2 m)) := rfl

@[simp] theorem appendixDXnm_a (n m : Fin 3) (h : n ≠ m) (v : AppendixDVector) :
    (appendixDXnm n m h v).1 = 0 := rfl

@[simp] theorem appendixDXnm_y (n m : Fin 3) (h : n ≠ m)
    (v : AppendixDVector) (i : Fin 3) :
    (appendixDXnm n m h v).2.1 i =
      (Pi.single m (v.2.1 n) : Fin 3 → ℝ) i := rfl

@[simp] theorem appendixDXnm_z (n m : Fin 3) (h : n ≠ m)
    (v : AppendixDVector) (i : Fin 3) :
    (appendixDXnm n m h v).2.2 i =
      -((Pi.single n (v.2.2 m) : Fin 3 → ℝ) i) := rfl

/-- The `X_n0` source-coordinate operator.  The two antisymmetric epsilon
terms in (D.1) have been combined using the alternating Levi--Civita tensor. -/
noncomputable def appendixDXn0 (n : Fin 3) :
    AppendixDVector →ₗ[ℝ] AppendixDVector :=
  { toFun := fun v =>
      (v.2.1 n, epsilonAction n v.2.2, -2 • Pi.single n v.1)
    map_add' := by
      intro v w
      apply Prod.ext
      · simp
      · apply Prod.ext
        · exact epsilonAction_add n v.2.2 w.2.2
        · funext i
          by_cases h : n = i <;>
            simp [Pi.single_apply, h] <;> ring
    map_smul' := by
      intro c v
      apply Prod.ext
      · simp
      · apply Prod.ext
        · exact epsilonAction_smul n c v.2.2
        · funext i
          by_cases h : n = i <;>
            simp [Pi.single_apply, h] <;> ring }

@[simp] theorem appendixDXn0_apply (n : Fin 3) (v : AppendixDVector) :
    appendixDXn0 n v =
      (v.2.1 n, epsilonAction n v.2.2, -2 • Pi.single n v.1) := rfl

/-- The `X_0n` source-coordinate operator from (D.1), with the same
epsilon-term simplification as `appendixDXn0`. -/
noncomputable def appendixDX0n (n : Fin 3) :
    AppendixDVector →ₗ[ℝ] AppendixDVector :=
  { toFun := fun v =>
      (v.2.2 n, -2 • Pi.single n v.1, epsilonAction n v.2.1)
    map_add' := by
      intro v w
      apply Prod.ext
      · simp
      · apply Prod.ext
        · funext i
          by_cases h : n = i <;>
            simp [Pi.single_apply, h] <;> ring
        · exact epsilonAction_add n v.2.1 w.2.1
    map_smul' := by
      intro c v
      apply Prod.ext
      · simp
      · apply Prod.ext
        · funext i
          by_cases h : n = i <;>
            simp [Pi.single_apply, h] <;> ring
        · exact epsilonAction_smul n c v.2.1 }

@[simp] theorem appendixDX0n_apply (n : Fin 3) (v : AppendixDVector) :
    appendixDX0n n v =
      (v.2.2 n, -2 • Pi.single n v.1, epsilonAction n v.2.1) := rfl

@[simp] theorem appendixDXn0_a (n : Fin 3) (v : AppendixDVector) :
    (appendixDXn0 n v).1 = v.2.1 n := rfl

@[simp] theorem appendixDXn0_y (n : Fin 3) (v : AppendixDVector) (i : Fin 3) :
    (appendixDXn0 n v).2.1 i =
      ∑ m : Fin 3, leviCivita3 n m i * v.2.2 m := rfl

@[simp] theorem appendixDXn0_z (n : Fin 3) (v : AppendixDVector) (i : Fin 3) :
    (appendixDXn0 n v).2.2 i =
      if n = i then -2 * v.1 else 0 := by
  simp only [appendixDXn0_apply]
  change ((-(2 : ℤ) • (Pi.single n v.1 : Fin 3 → ℝ))) i = _
  by_cases h : n = i
  · subst i
    simp only [Pi.smul_apply, Pi.single_eq_same, if_pos]
    ring
  · have h' : i ≠ n := Ne.symm h
    simp only [Pi.smul_apply, Pi.single_eq_of_ne h', h]
    simp

@[simp] theorem appendixDX0n_a (n : Fin 3) (v : AppendixDVector) :
    (appendixDX0n n v).1 = v.2.2 n := rfl

@[simp] theorem appendixDX0n_y (n : Fin 3) (v : AppendixDVector) (i : Fin 3) :
    (appendixDX0n n v).2.1 i =
      if n = i then -2 * v.1 else 0 := by
  simp only [appendixDX0n_apply]
  change ((-(2 : ℤ) • (Pi.single n v.1 : Fin 3 → ℝ))) i = _
  by_cases h : n = i
  · subst i
    simp only [Pi.smul_apply, Pi.single_eq_same, if_pos]
    ring
  · have h' : i ≠ n := Ne.symm h
    simp only [Pi.smul_apply, Pi.single_eq_of_ne h', h]
    simp

@[simp] theorem appendixDX0n_z (n : Fin 3) (v : AppendixDVector) (i : Fin 3) :
    (appendixDX0n n v).2.2 i =
      ∑ m : Fin 3, leviCivita3 n m i * v.2.1 m := rfl

abbrev PaperDer := paperDerivationLieHom.range

/-- The transported 14-dimensional Appendix-D realization.  This is the
Lie-side basis; the literal source-coordinate operators are `appendixDXnn`,
`appendixDXnm`, `appendixDXn0`, and `appendixDX0n` above. -/
noncomputable def appendixDGenerator (i : Fin 14) : PaperDer :=
  paperDerivationBasis i

theorem appendixDGenerator_apply (i : Fin 14) :
    appendixDGenerator i = paperDerivationBasis i := rfl

theorem appendixDGenerator_linearIndependent :
    LinearIndependent ℝ appendixDGenerator := by
  simpa only [appendixDGenerator] using paperDerivationBasis.linearIndependent

theorem appendixDGenerator_span_eq_top :
    Submodule.span ℝ (Set.range appendixDGenerator) = ⊤ := by
  simpa only [appendixDGenerator] using paperDerivationBasis.span_eq

noncomputable def appendixDGenerator_basis :
    Module.Basis (Fin 14) ℝ PaperDer :=
  paperDerivationBasis

theorem appendixDGenerator_finrank :
    Module.finrank ℝ PaperDer = 14 := by
  exact finrank_paperDerivationRange

end InfoGeometry.Lie.CanonicalZornG2AppendixDGenerators
