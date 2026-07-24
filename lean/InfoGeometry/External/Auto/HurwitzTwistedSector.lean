import Mathlib
import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import InfoGeometry.External.Auto.ZetaSpectralBridge

noncomputable section

namespace InfoGeometry.Quantum.HurwitzTwistedSector

open Complex
open scoped BigOperators

/--
A useful analytic lemma for shifted positive real parameters.
-/
lemma one_div_cpow_eq_exp_neg_log (x : ℝ) (s : ℂ) (hx : 0 < x) :
    (1 : ℂ) / ((x : ℂ) ^ s) = Complex.exp (-(s * (Real.log x : ℂ))) := by
  have hxC : (x : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hx)
  calc
    (1 : ℂ) / ((x : ℂ) ^ s) = ((x : ℂ) ^ s)⁻¹ := by
      simp
    _ = (Complex.exp (Complex.log (x : ℂ) * s))⁻¹ := by
      simp [Complex.cpow_def, hxC]
    _ = Complex.exp (-(Complex.log (x : ℂ) * s)) := by
      rw [← Complex.exp_neg]
    _ = Complex.exp (-(s * (Complex.log (x : ℂ)))) := by
      congr 1
      ring
    _ = Complex.exp (-(s * (Real.log x : ℂ))) := by
      simp [Complex.ofReal_log (show 0 ≤ x by exact le_of_lt hx)]

/--
Real-coordinate quaternion used for the Hurwitz/lattice layer.

The genuine Hurwitz order condition is recorded separately by predicates below:
the algebraic norm identities only need the ambient quaternion coordinates.
-/
structure HurwitzQuaternion where
  a0 : ℝ
  a1 : ℝ
  a2 : ℝ
  a3 : ℝ

namespace HurwitzQuaternion

/-- Quaternion conjugation. -/
def conj (q : HurwitzQuaternion) : HurwitzQuaternion :=
  { a0 := q.a0, a1 := -q.a1, a2 := -q.a2, a3 := -q.a3 }

/-- Hamilton quaternion multiplication in real coordinates. -/
def mul (p q : HurwitzQuaternion) : HurwitzQuaternion :=
  { a0 := p.a0 * q.a0 - p.a1 * q.a1 - p.a2 * q.a2 - p.a3 * q.a3
  , a1 := p.a0 * q.a1 + p.a1 * q.a0 + p.a2 * q.a3 - p.a3 * q.a2
  , a2 := p.a0 * q.a2 - p.a1 * q.a3 + p.a2 * q.a0 + p.a3 * q.a1
  , a3 := p.a0 * q.a3 + p.a1 * q.a2 - p.a2 * q.a1 + p.a3 * q.a0 }

instance : Mul HurwitzQuaternion where
  mul := mul

/-- Squared Euclidean/Hurwitz norm. -/
def normSq (q : HurwitzQuaternion) : ℝ :=
  q.a0 ^ 2 + q.a1 ^ 2 + q.a2 ^ 2 + q.a3 ^ 2

/-- A real-coordinate point of the unit 24-cell shell. -/
def IsUnitShell (q : HurwitzQuaternion) : Prop :=
  normSq q = 1

/-- Ambient finite shifted spectrum associated to a Hurwitz-zeta sector. -/
def shiftedWeight (a : ℝ) (n : ℕ) : ℝ :=
  n + a

theorem normSq_nonneg (q : HurwitzQuaternion) : 0 ≤ normSq q := by
  unfold normSq
  nlinarith [sq_nonneg q.a0, sq_nonneg q.a1, sq_nonneg q.a2, sq_nonneg q.a3]

theorem normSq_pos_of_a0_ne_zero (q : HurwitzQuaternion) (h : q.a0 ≠ 0) :
    0 < normSq q := by
  unfold normSq
  have h0 : 0 < q.a0 ^ 2 := sq_pos_of_ne_zero h
  nlinarith [sq_nonneg q.a1, sq_nonneg q.a2, sq_nonneg q.a3]

theorem normSq_conj (q : HurwitzQuaternion) : normSq (conj q) = normSq q := by
  unfold normSq conj
  ring

/-- Hamilton's norm is multiplicative. -/
theorem normSq_mul (p q : HurwitzQuaternion) :
    normSq (p * q) = normSq p * normSq q := by
  change normSq (mul p q) = normSq p * normSq q
  unfold normSq mul
  ring

/-- Unit-shell elements preserve the squared norm by left multiplication. -/
theorem normSq_left_unit_shell (u q : HurwitzQuaternion) (hu : IsUnitShell u) :
    normSq (u * q) = normSq q := by
  rw [normSq_mul, hu, one_mul]

/-- Logarithmic norm energy for nonzero quaternion modes. -/
def logNormEnergy (q : HurwitzQuaternion) : ℝ :=
  Real.log (normSq q)

theorem logNormEnergy_eq (q : HurwitzQuaternion) :
    logNormEnergy q = Real.log (normSq q) := rfl

end HurwitzQuaternion

/-- Finite Hurwitz-zeta style shifted trace. -/
def finiteHurwitzZetaTrace (N : ℕ) (a : ℝ) (s : ℂ) : ℂ :=
  ∑ n : Fin N,
    InfoGeometry.Quantum.ZetaSpectralBridge.gammaNormalizedMellinMode
      s (n.1 + a : ℝ)

/-- Same finite trace, written directly as shifted exponential weights. -/
def finiteShiftedDirichletTrace (N : ℕ) (a : ℝ) (s : ℂ) : ℂ :=
  ∑ n : Fin N, Complex.exp (-s * (Real.log (n.1 + a : ℝ) : ℂ))

/-- Same finite shifted trace in `cpow`-Dirichlet form. -/
def finiteShiftedCpowTrace (N : ℕ) (a : ℝ) (s : ℂ) : ℂ :=
  ∑ n : Fin N, (1 : ℂ) / (((n.1 : ℝ) + a : ℝ) : ℂ) ^ s

/-- The finite Hurwitz-zeta trace is the shifted Dirichlet trace. -/
theorem finiteHurwitzZetaTrace_eq_shiftedDirichlet (N : ℕ) (a : ℝ) (s : ℂ) :
    finiteHurwitzZetaTrace N a s = finiteShiftedDirichletTrace N a s := by
  simp [finiteHurwitzZetaTrace, finiteShiftedDirichletTrace,
    InfoGeometry.Quantum.ZetaSpectralBridge.gammaNormalizedMellinMode]

/-- The finite Hurwitz-zeta trace is equivalently the shifted `cpow`-Dirichlet trace,
for strictly positive shifts.
-/
theorem finiteHurwitzZetaTrace_eq_cpowTrace (N : ℕ) (a : ℝ) (s : ℂ) (ha : 0 < a) :
    finiteHurwitzZetaTrace N a s = finiteShiftedCpowTrace N a s := by
  simp [finiteHurwitzZetaTrace, finiteShiftedCpowTrace,
    InfoGeometry.Quantum.ZetaSpectralBridge.gammaNormalizedMellinMode]
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hn_nonneg : (0 : ℝ) ≤ (n.1 : ℝ) := Nat.cast_nonneg _
  have hn_pos : 0 < (n.1 : ℝ) + a := by linarith
  simpa [one_div] using (one_div_cpow_eq_exp_neg_log (x := (n.1 : ℝ) + a) s hn_pos).symm

/-- The ordinary finite Primon trace is the shift-`1` Hurwitz trace, up to reindexing from `0`. -/
theorem finiteHurwitzZetaTrace_shift_one_eq_primon (n : ℕ) (s : ℂ) :
    finiteHurwitzZetaTrace (n + 1) 1 s =
      InfoGeometry.Quantum.ZetaSpectralBridge.finitePrimonMellinTrace n s := by
  unfold finiteHurwitzZetaTrace
  unfold InfoGeometry.Quantum.ZetaSpectralBridge.finitePrimonMellinTrace
  apply Finset.sum_congr rfl
  intro i _
  congr 1

/-- Half-shifted sector, the finite Neveu-Schwarz/Mobius-style model. -/
def finiteHalfShiftTrace (N : ℕ) (s : ℂ) : ℂ :=
  finiteHurwitzZetaTrace N (1 / 2) s

/-- Infinite shifted Hurwitz trace as an `ℓ¹`-style Dirichlet-series expression. -/
def infiniteHurwitzTrace (a : ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, (1 : ℂ) / (((n : ℝ) + a : ℝ) : ℂ) ^ s

/-- Hurwitz zeta equals the shifted Dirichlet series on the half-plane `Re(s) > 1`. -/
theorem hurwitzTrace_eq_hurwitzZeta (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) {s : ℂ}
    (hs : 1 < s.re) :
    HurwitzZeta.hurwitzZeta a s = infiniteHurwitzTrace a s := by
  simpa [infiniteHurwitzTrace, one_div] using
    (HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re (a := a) ha hs).tsum_eq.symm

/--
Mellin bridge from an explicit shifted heat kernel decomposition to the infinite
Hurwitz trace.
-/
theorem mellin_infiniteHurwitzTrace (a : ℝ) (ha : 0 < a) (heat : ℝ → ℂ)
    {s : ℂ} (hs : 0 < s.re)
    (h_decomp : ∀ t ∈ Set.Ioi 0,
      HasSum (fun n : ℕ => (1 : ℂ) * Real.exp (-((n : ℝ) + a) * t)) (heat t))
    (h_sum : Summable fun n : ℕ => ‖(1 : ℂ)‖ / ((n : ℝ) + a) ^ s.re) :
    mellin heat s = Complex.Gamma s * infiniteHurwitzTrace a s := by
  have hp : ∀ i : ℕ, (1 : ℂ) = 0 ∨ 0 < (i : ℝ) + a := by
    intro i
    right
    have hi : (0 : ℝ) ≤ (i : ℝ) := by exact_mod_cast Nat.zero_le i
    linarith
  have h_mellin := hasSum_mellin (a := fun _ : ℕ => (1 : ℂ)) (p := fun i : ℕ => (i : ℝ) + a)
    (s := s) hp hs (by simpa [mul_assoc] using h_decomp) h_sum
  rw [← h_mellin.tsum_eq]
  have h_factor :
      (∑' n : ℕ, Complex.Gamma s * (1 : ℂ) / (((n : ℝ) + a : ℝ) : ℂ) ^ s)
        = Complex.Gamma s * infiniteHurwitzTrace a s := by
    simpa [infiniteHurwitzTrace, div_eq_mul_inv, mul_assoc] using
      (tsum_mul_left
        (f := fun n : ℕ => (1 : ℂ) / (((n : ℝ) + a : ℝ) : ℂ) ^ s)
        (a := Complex.Gamma s))
  exact h_factor

/-- Mellin bridge from shifted heat to the Hurwitz zeta value (twisted sector form). -/
theorem mellin_infiniteHurwitzTrace_eq_hurwitzZeta (a : ℝ)
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (heat : ℝ → ℂ) {s : ℂ} (hs : 1 < s.re)
    (h_decomp : ∀ t ∈ Set.Ioi 0,
      HasSum (fun n : ℕ => (1 : ℂ) * Real.exp (-((n : ℝ) + a) * t)) (heat t))
    (h_sum : Summable fun n : ℕ => ‖(1 : ℂ)‖ / ((n : ℝ) + a) ^ s.re) :
    mellin heat s = Complex.Gamma s * HurwitzZeta.hurwitzZeta a s := by
  have h_m : mellin heat s = Complex.Gamma s * infiniteHurwitzTrace a s :=
    mellin_infiniteHurwitzTrace (a := a) ha.1 heat
      (s := s) (hs := by linarith) h_decomp h_sum
  have ha' : a ∈ Set.Icc (0 : ℝ) (1 : ℝ) := ⟨ha.1.le, ha.2.le⟩
  rw [h_m, hurwitzTrace_eq_hurwitzZeta a ha' hs]

/-- At zero shift the Hurwitz function is the Riemann zeta. -/
theorem hurwitz_zero_is_riemann (s : ℂ) :
    HurwitzZeta.hurwitzZeta (0 : ℝ) s = riemannZeta s := by
  simpa using congrArg (fun f => f s) HurwitzZeta.hurwitzZeta_zero

/-- A finite fractional boundary charge sector. -/
structure TwistedSector where
  shift : ℝ
  positive_shift : 0 < shift

/-- Finite partition trace of a twisted Hurwitz sector. -/
def TwistedSector.trace (T : TwistedSector) (N : ℕ) (s : ℂ) : ℂ :=
  finiteHurwitzZetaTrace N T.shift s

theorem TwistedSector.trace_eq_shiftedDirichlet (T : TwistedSector) (N : ℕ) (s : ℂ) :
    T.trace N s = finiteShiftedDirichletTrace N T.shift s := by
  exact finiteHurwitzZetaTrace_eq_shiftedDirichlet N T.shift s

/--
Finite Dirichlet-character combination of shifted Hurwitz sectors.

This is the finite analogue of expressing Dirichlet `L`-series as finite
linear combinations of Hurwitz zeta functions.
-/
def finiteHurwitzCharacterCombination
    (k N : ℕ) (χ : Fin k → ℂ) (s : ℂ) : ℂ :=
  ∑ a : Fin k,
    χ a *
      InfoGeometry.Quantum.ZetaSpectralBridge.gammaNormalizedMellinMode s (k : ℝ) *
        finiteHurwitzZetaTrace N (((a.1 : ℝ) + 1) / (k : ℝ)) s

theorem finiteHurwitzCharacterCombination_add
    (k N : ℕ) (χ ψ : Fin k → ℂ) (s : ℂ) :
    finiteHurwitzCharacterCombination k N (fun a => χ a + ψ a) s =
      finiteHurwitzCharacterCombination k N χ s +
        finiteHurwitzCharacterCombination k N ψ s := by
  simp [finiteHurwitzCharacterCombination, add_mul, Finset.sum_add_distrib]

theorem finiteHurwitzCharacterCombination_smul
    (k N : ℕ) (c : ℂ) (χ : Fin k → ℂ) (s : ℂ) :
    finiteHurwitzCharacterCombination k N (fun a => c * χ a) s =
      c * finiteHurwitzCharacterCombination k N χ s := by
  simp [finiteHurwitzCharacterCombination, mul_assoc, Finset.mul_sum]

theorem finiteHurwitzCharacterCombination_eq_shiftedDirichlet
    (k N : ℕ) (χ : Fin k → ℂ) (s : ℂ) :
    finiteHurwitzCharacterCombination k N χ s =
      ∑ a : Fin k,
        χ a *
          InfoGeometry.Quantum.ZetaSpectralBridge.gammaNormalizedMellinMode s (k : ℝ) *
          finiteShiftedDirichletTrace N (((a.1 : ℝ) + 1) / (k : ℝ)) s := by
  simp [finiteHurwitzCharacterCombination, finiteShiftedDirichletTrace,
    finiteHurwitzZetaTrace, InfoGeometry.Quantum.ZetaSpectralBridge.gammaNormalizedMellinMode]

theorem finiteHurwitzCharacterCombination_zero
    (k N : ℕ) (s : ℂ) :
    finiteHurwitzCharacterCombination k N (fun _ => 0) s = 0 := by
  simp [finiteHurwitzCharacterCombination]

/--
Conservative infinite Hurwitz trace interface.

The actual infinite series, convergence, and continuation readout are not
proved here.  This record states the precise bridge data a later
Hestenes--Krein/categorical colimit owner must provide.
-/
structure InfiniteHurwitzTraceModel where
  heatTrace : ℝ → ℂ → ℂ
  infiniteHurwitzTrace : ℝ → ℂ → ℂ
  gamma : ℂ → ℂ
  mellin_bridge :
    ∀ (shift : ℝ) (s : ℂ),
      heatTrace shift s = gamma s * infiniteHurwitzTrace shift s

/-- Short Mellin bridge theorem for the modeled infinite Hurwitz trace. -/
theorem infiniteHurwitzTrace_mellin_bridge
    (M : InfiniteHurwitzTraceModel) (shift : ℝ) (s : ℂ) :
    M.heatTrace shift s = M.gamma s * M.infiniteHurwitzTrace shift s :=
  M.mellin_bridge shift s

/--
Bundled finite Hurwitz/twisted-sector bridge.

It records the norm positivity needed for logarithmic energies, the
multiplicative quaternion norm, and the shifted finite Hurwitz-zeta trace.
-/
theorem hurwitz_twisted_sector_synthesis
    (p q : HurwitzQuaternion) (h_nonzero : q.a0 ≠ 0)
    (N : ℕ) (a : ℝ) (s : ℂ) :
    0 < q.normSq ∧
      (p * q).normSq = p.normSq * q.normSq ∧
      finiteHurwitzZetaTrace N a s = finiteShiftedDirichletTrace N a s ∧
      finiteHurwitzZetaTrace (N + 1) 1 s =
        InfoGeometry.Quantum.ZetaSpectralBridge.finitePrimonMellinTrace N s := by
  exact ⟨HurwitzQuaternion.normSq_pos_of_a0_ne_zero q h_nonzero,
    HurwitzQuaternion.normSq_mul p q,
    finiteHurwitzZetaTrace_eq_shiftedDirichlet N a s,
    finiteHurwitzZetaTrace_shift_one_eq_primon N s⟩

/-- Even/odd split term identity for the half-shifted Dirichlet summand. -/
theorem half_shift_term_identity (n : ℕ) (s : ℂ) :
    (1 : ℂ) / (((n : ℂ) + (1 / 2 : ℂ)) ^ s) =
      (2 : ℂ) ^ s * ((1 : ℂ) / (((2 * n + 1 : ℕ) : ℂ) ^ s)) := by
  have hbase : ((n : ℂ) + (1 / 2 : ℂ)) = (((2 * n + 1 : ℕ) : ℂ) / 2) := by
    have h1 : ((n : ℂ) + (1 / 2 : ℂ)) = ((2 * (n : ℂ) + 1) / 2) := by
      field_simp
    have h2 : (2 * (n : ℂ) + 1 : ℂ) = ((2 * n + 1 : ℕ) : ℂ) := by
      norm_num
    calc
      ((n : ℂ) + (1 / 2 : ℂ)) = ((2 * (n : ℂ) + 1) / 2) := h1
      _ = (((2 * n + 1 : ℕ) : ℂ) / 2) := by
          exact congrArg (fun x : ℂ => x / 2) h2
  rw [hbase]
  have hpow : (((2 * n + 1 : ℕ) : ℂ) / 2) ^ s =
      (((2 * n + 1 : ℕ) : ℂ) ^ s) * ((1 / 2 : ℂ) ^ s) := by
    have hbase2 : (((2 * n + 1 : ℕ) : ℂ) / 2) = (((2 * n + 1 : ℕ) : ℂ) * (1 / 2 : ℂ)) := by
      field_simp
    rw [hbase2]
    simpa using
      (Complex.mul_cpow_ofReal_nonneg (a := (2 * n + 1 : ℝ)) (b := (1 / 2 : ℝ))
        (r := s) (show 0 ≤ (2 * n + 1 : ℝ) by positivity) (show 0 ≤ (1 / 2 : ℝ) by positivity))
  rw [hpow, div_eq_mul_inv]
  have hmul : ((1 / 2 : ℂ) ^ s) * (2 : ℂ) ^ s = (1 : ℂ) := by
    simpa [mul_comm] using
      (Complex.mul_cpow_ofReal_nonneg (a := (1 / 2 : ℝ)) (b := (2 : ℝ)) (r := s)
        (show 0 ≤ (1 / 2 : ℝ) by positivity) (show 0 ≤ (2 : ℝ) by positivity)).symm
  have hhalf_inv : ((1 / 2 : ℂ) ^ s)⁻¹ = (2 : ℂ) ^ s := inv_eq_of_mul_eq_one_right hmul
  calc
    1 / (((2 * n + 1 : ℕ) : ℂ) ^ s * (1 / 2 : ℂ) ^ s)
        = (((2 * n + 1 : ℕ) : ℂ) ^ s)⁻¹ * ((1 / 2 : ℂ) ^ s)⁻¹ := by
          simpa [one_div] using
            (one_div_mul_one_div (((2 * n + 1 : ℕ) : ℂ) ^ s) ((1 / 2 : ℂ) ^ s)).symm
    _ = (2 : ℂ) ^ s * (((2 * n + 1 : ℕ) : ℂ) ^ s)⁻¹ := by
      rw [hhalf_inv]
      ring
    _ = (2 : ℂ) ^ s * ((1 : ℂ) / (((2 * n + 1 : ℕ) : ℂ) ^ s)) := by
      simp [one_div]

/-- Odd-index half-shift decomposition for the Riemann side. -/
theorem odd_shift_term_identity (n : ℕ) (s : ℂ) :
    (1 : ℂ) / ((((2 * n + 1 : ℕ) : ℂ) + 1) ^ s) =
      (2 : ℂ) ^ (-s) * (1 / (((n : ℂ) + 1) ^ s)) := by
  have hnat : (((2 * n + 1 : ℕ) : ℂ) + 1 = (2 : ℂ) * ((n : ℂ) + 1)) := by
    norm_num [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    ring
  have hmul : ((2 : ℂ) * ((n : ℂ) + 1)) ^ s =
      (2 : ℂ) ^ s * (((n : ℂ) + 1) ^ s) := by
    simpa using
      (Complex.mul_cpow_ofReal_nonneg (a := (2:ℝ)) (b := (n:ℝ)+1)
        (r := s) (by norm_num) (by positivity))
  rw [hnat, hmul, div_eq_mul_inv, mul_inv_rev]
  simp [Complex.cpow_neg, one_div]
  ac_rfl

/-- Hurwitz `a = 1/2` specialization on `Re(s) > 1`. -/
theorem hurwitz_half_eq (s : ℂ) (hs : 1 < s.re) :
    HurwitzZeta.hurwitzZeta (1 / 2 : ℝ) s = ((2 : ℂ) ^ s - 1) * riemannZeta s := by
  let f : ℕ → ℂ := fun n => (1 : ℂ) / (((n : ℂ) + 1) ^ s)
  have hf : Summable f := by
    have h0 : Summable (fun n : ℕ => (1 : ℂ) / ((n : ℂ) ^ s)) :=
      (Complex.summable_one_div_nat_cpow (p := s)).2 hs
    have h1 : Summable (fun n : ℕ => (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ s)) :=
      (summable_nat_add_iff (f := fun n : ℕ => (1 : ℂ) / ((n : ℂ) ^ s)) (k := 1)).2 h0
    simpa [f, Nat.cast_add, add_comm, add_left_comm, add_assoc] using h1
  have hEvenSumm : Summable (fun k : ℕ => f (2 * k)) := hf.comp_injective <| by
    intro a b h
    have hmul : 2 * a = 2 * b := by simpa [Nat.mul_comm] using h
    exact Nat.mul_left_cancel (show (0 : ℕ) < 2 by decide) hmul
  have hOddSumm : Summable (fun k : ℕ => f (2 * k + 1)) := hf.comp_injective <| by
    intro a b h
    have h2 : 2 * a = 2 * b := by
      exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one, Nat.mul_add, add_assoc,
        add_comm, add_left_comm] using h)
    exact Nat.mul_left_cancel (show (0 : ℕ) < 2 by decide) h2
  have hdecomp : (∑' k : ℕ, f (2 * k)) + ∑' k : ℕ, f (2 * k + 1) = riemannZeta s := by
    calc
      (∑' k : ℕ, f (2 * k)) + ∑' k : ℕ, f (2 * k + 1) = ∑' k : ℕ, f k := by
        exact tsum_even_add_odd hEvenSumm hOddSumm
      _ = riemannZeta s := by
        rw [zeta_eq_tsum_one_div_nat_add_one_cpow (s := s) hs]
  have hodd : (∑' k : ℕ, f (2 * k + 1)) = (2 : ℂ) ^ (-s) * riemannZeta s := by
    have hsum : (∑' k : ℕ, f (2 * k + 1)) =
        ∑' k : ℕ, (2 : ℂ) ^ (-s) * (1 / (((k : ℂ) + 1) ^ s)) := by
      refine tsum_congr ?_
      intro n
      simpa [f] using (odd_shift_term_identity (n := n) (s := s))
    calc
      (∑' k : ℕ, f (2 * k + 1)) = ∑' k : ℕ, (2 : ℂ) ^ (-s) * (1 / (((k : ℂ) + 1) ^ s)) := hsum
      _ = (2 : ℂ) ^ (-s) * ∑' k : ℕ, (1 / (((k : ℕ) : ℂ) + 1) ^ s) := by
        rw [tsum_mul_left]
      _ = (2 : ℂ) ^ (-s) * riemannZeta s := by
        rw [zeta_eq_tsum_one_div_nat_add_one_cpow (s := s) hs]
  have heven : (∑' k : ℕ, f (2 * k)) = (1 - (2 : ℂ) ^ (-s)) * riemannZeta s := by
    calc
      (∑' k : ℕ, f (2 * k)) = riemannZeta s - ∑' k : ℕ, f (2 * k + 1) := eq_sub_of_add_eq hdecomp
      _ = riemannZeta s - (2 : ℂ) ^ (-s) * riemannZeta s := by rw [hodd]
      _ = (1 - (2 : ℂ) ^ (-s)) * riemannZeta s := by ring
  have hhalf : ∑' n : ℕ, (1 : ℂ) / (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ s =
      (2 : ℂ) ^ s * ∑' k : ℕ, f (2 * k) := by
    have hsum : ∑' n : ℕ, (1 : ℂ) / (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ s =
        ∑' k : ℕ, (2 : ℂ) ^ s * f (2 * k) := by
      refine tsum_congr ?_
      intro n
      have hcnv : (((n : ℝ) + 1 / 2 : ℝ) : ℂ) = ((n : ℂ) + (1 / 2 : ℂ)) := by
        norm_num
      calc
        (1 : ℂ) / (((n : ℝ) + 1 / 2 : ℝ) : ℂ) ^ s
            = (1 : ℂ) / (((n : ℂ) + (1 / 2 : ℂ)) ^ s) := by rw [hcnv]
        _ = (2 : ℂ) ^ s * ((1 : ℂ) / (((2 * n + 1 : ℕ) : ℂ) ^ s)) :=
              half_shift_term_identity (n := n) (s := s)
        _ = (2 : ℂ) ^ s * f (2 * n) := by
          simp [f, Nat.cast_add, Nat.cast_mul, add_comm]
    simpa [mul_assoc, mul_left_comm, mul_comm, tsum_mul_left] using hsum
  calc
    HurwitzZeta.hurwitzZeta (1 / 2 : ℝ) s
      = ∑' n : ℕ, (1 : ℂ) / (((n : ℝ) + (1 / 2 : ℝ)) : ℂ) ^ s :=
        (HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re (a := (1 / 2 : ℝ))
          ⟨by norm_num, by norm_num⟩ hs).tsum_eq.symm
    _ = (2 : ℂ) ^ s * ∑' k : ℕ, f (2 * k) := by
      simpa [f, Nat.cast_add, add_comm] using hhalf
    _ = (2 : ℂ) ^ s * ((1 - (2 : ℂ) ^ (-s)) * riemannZeta s) := by rw [heven]
    _ = ((2 : ℂ) ^ s - 1) * riemannZeta s := by
      have hmul : (2 : ℂ) ^ s * (2 : ℂ) ^ (-s) = (1 : ℂ) := by
        simp [Complex.cpow_neg]
      calc
        (2 : ℂ) ^ s * ((1 - (2 : ℂ) ^ (-s)) * riemannZeta s) =
            ((2 : ℂ) ^ s * (1 - (2 : ℂ) ^ (-s))) * riemannZeta s := by
          ring
        _ = ((2 : ℂ) ^ s - (2 : ℂ) ^ s * (2 : ℂ) ^ (-s)) * riemannZeta s := by
          ring
        _ = ((2 : ℂ) ^ s - 1) * riemannZeta s := by
          simp [hmul]

/-- Corollary in colimit notation: half-shifted infinite Hurwitz trace. -/
theorem half_shift_infiniteHurwitzTrace_eq (s : ℂ) (hs : 1 < s.re) :
    infiniteHurwitzTrace (1 / 2 : ℝ) s = ((2 : ℂ) ^ s - 1) * riemannZeta s := by
  have hhz : HurwitzZeta.hurwitzZeta (1 / 2 : ℝ) s =
      infiniteHurwitzTrace (1 / 2 : ℝ) s :=
    hurwitzTrace_eq_hurwitzZeta (a := (1 / 2 : ℝ)) (ha := ⟨by norm_num, by norm_num⟩) (s := s) hs
  exact hhz.symm.trans (hurwitz_half_eq (s := s) hs)

/-- Infinite Neveu-Schwarz/Mobius half-shifted sector trace. -/
def neveuSchwarzInfiniteTrace (s : ℂ) : ℂ :=
  infiniteHurwitzTrace (1 / 2 : ℝ) s

/-- The NS/Mobius infinite trace is the half-shifted Riemann factor on `Re(s) > 1`. -/
theorem neveuSchwarzInfiniteTrace_eq_riemann (s : ℂ) (hs : 1 < s.re) :
    neveuSchwarzInfiniteTrace s = ((2 : ℂ) ^ s - 1) * riemannZeta s :=
  half_shift_infiniteHurwitzTrace_eq s hs

/--
Generic spectral target for the NS/Mobius twisted sector.

Any later spectral determinant/trace target can opt into the half-shift formula
by proving it realizes the canonical `neveuSchwarzInfiniteTrace`.
-/
structure NeveuSchwarzSpectralTarget where
  targetTrace : ℂ → ℂ
  realizes_half_shift : ∀ s, targetTrace s = neveuSchwarzInfiniteTrace s

/--
Canonical NS/Mobius spectral target, definitionaly equal to
`neveuSchwarzInfiniteTrace`.
-/
def neveuSchwarzCanonicalSpectralTarget : NeveuSchwarzSpectralTarget :=
  { targetTrace := neveuSchwarzInfiniteTrace
  , realizes_half_shift := by
      intro s
      rfl }

namespace NeveuSchwarzSpectralTarget

/-- Twisted-sector formulas propagate automatically to any realized spectral target. -/
theorem targetTrace_eq_riemann
    (T : NeveuSchwarzSpectralTarget) (s : ℂ) (hs : 1 < s.re) :
    T.targetTrace s = ((2 : ℂ) ^ s - 1) * riemannZeta s := by
  rw [T.realizes_half_shift s]
  exact neveuSchwarzInfiniteTrace_eq_riemann s hs

end NeveuSchwarzSpectralTarget

/--
Möbius/NS spectral targets that also satisfy a `a = 1/2` Mellin bridge formula
inherit the half-shift specialization automatically.
-/
structure NeveuSchwarzSpectralTargetWithMellin where
  model : InfiniteHurwitzTraceModel
  targetTrace : ℂ → ℂ
  heatTrace : ℂ → ℂ
  realizes_half_shift : ∀ s, targetTrace s = neveuSchwarzInfiniteTrace s
  realizes_shifted_infinite : ∀ s, model.infiniteHurwitzTrace (1 / 2 : ℝ) s = targetTrace s
  realizes_shifted_heat : ∀ s, heatTrace s = model.heatTrace (1 / 2 : ℝ) s

namespace NeveuSchwarzSpectralTarget

/--
Upgrade an existing NS/Mobius trace target to a Mellin-aware target once a
specific infinite Hurwitz trace model and heat realization are supplied.
-/
def withMellin
    (T : NeveuSchwarzSpectralTarget)
    (model : InfiniteHurwitzTraceModel)
    (heatTrace : ℂ → ℂ)
    (h_infinite : ∀ s, model.infiniteHurwitzTrace (1 / 2 : ℝ) s = T.targetTrace s)
    (h_heat : ∀ s, heatTrace s = model.heatTrace (1 / 2 : ℝ) s) :
    NeveuSchwarzSpectralTargetWithMellin :=
  { model := model
  , targetTrace := T.targetTrace
  , heatTrace := heatTrace
  , realizes_half_shift := T.realizes_half_shift
  , realizes_shifted_infinite := h_infinite
  , realizes_shifted_heat := h_heat }

end NeveuSchwarzSpectralTarget

namespace NeveuSchwarzSpectralTargetWithMellin

/-- Heat-side twisted formula for any concrete target/model pair. -/
theorem heatTrace_eq_riemann
    (T : NeveuSchwarzSpectralTargetWithMellin) (s : ℂ) (hs : 1 < s.re) :
    T.heatTrace s = T.model.gamma s * ((2 : ℂ) ^ s - 1) * riemannZeta s := by
  calc
    T.heatTrace s = T.model.heatTrace (1 / 2 : ℝ) s := T.realizes_shifted_heat s
    _ = T.model.gamma s * T.model.infiniteHurwitzTrace (1 / 2 : ℝ) s :=
      infiniteHurwitzTrace_mellin_bridge T.model (1 / 2 : ℝ) s
    _ = T.model.gamma s * T.targetTrace s := by
      rw [T.realizes_shifted_infinite s]
    _ = T.model.gamma s * (((2 : ℂ) ^ s - 1) * riemannZeta s) := by
      rw [T.realizes_half_shift s, neveuSchwarzInfiniteTrace_eq_riemann s hs]
    _ = T.model.gamma s * ((2 : ℂ) ^ s - 1) * riemannZeta s := by ring

/-- Immediate spectral trace propagation through the same bridge data. -/
theorem targetTrace_eq_riemann
    (T : NeveuSchwarzSpectralTargetWithMellin) (s : ℂ) (hs : 1 < s.re) :
    T.targetTrace s = ((2 : ℂ) ^ s - 1) * riemannZeta s := by
  rw [T.realizes_half_shift s]
  exact neveuSchwarzInfiniteTrace_eq_riemann s hs

end NeveuSchwarzSpectralTargetWithMellin

end InfoGeometry.Quantum.HurwitzTwistedSector
