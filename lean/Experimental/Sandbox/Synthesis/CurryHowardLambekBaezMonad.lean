import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Invertible
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import InfoGeometry.OperatorAlgebra.FiniteMatrixNoncommutativeWitness

open Matrix

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Sandbox finite-matrix algebra identities and retraction certificate

This module records finite-dimensional matrix identities, a permutation of
three coordinates, a Plücker relation, and an abstract retraction law. Its
zero-mode result compares kernels only when the two matrices are equal. These
algebraic models do not by themselves construct D₄ triality, a modular
operator, a Cuntz/Kasparov theory, or a categorical continuum limit.
-/

namespace Experimental.Sandbox.Synthesis.CurryHowardLambekBaezMonad

universe u_V u_R

variable {V : Type u_V} [DecidableEq V] [Fintype V]
variable {R : Type u_R} [CommRing R]

/-! ### Section 1: The Five Functorial Projections of the Split Logos -/

/-! #### 1. Equal-matrix kernel comparison -/

/-- Kernel predicate for a finite matrix acting on coordinate vectors. -/
def isWdwZeroMode (H_wdw : Matrix V V R) (psi : V → R) : Prop :=
  H_wdw.mulVec psi = 0

/-- Kernel predicate for the second matrix in the comparison. -/
def isModularZeroMode (K_mod : Matrix V V R) (psi : V → R) : Prop :=
  K_mod.mulVec psi = 0

/-- Equal matrices have the same kernel on the coordinate carrier. -/
theorem wdw_modular_zero_equivalence (H_wdw K_mod : Matrix V V R)
    (h_eq : H_wdw = K_mod) (psi : V → R) :
    isWdwZeroMode H_wdw psi ↔ isModularZeroMode K_mod psi := by
  dsimp [isWdwZeroMode, isModularZeroMode]
  rw [h_eq]

/-! #### 2. Particle Sector (D4 Triality S3 Cycle & 3 Generations) -/

/-- Particle Sector: $\mathbb{Z}_3$ cyclic permutation of 3 generations under $D_4$ triality. -/
def trialityCycle (v : Fin 3 → R) : Fin 3 → R := fun i =>
  if i = 0 then v 1 else if i = 1 then v 2 else v 0

/-- Order 3 property of the triality cycle: `trialityCycle^3 = id`. -/
theorem trialityCycle_cube (v : Fin 3 → R) :
    trialityCycle (trialityCycle (trialityCycle v)) = v := by
  ext i
  fin_cases i <;> rfl

/-! #### 3. Condensed Matter Sector (Nambu Particle-Hole & Andreev Reversal) -/

/-- Fundamental Nambu particle-hole involution $\tau_1 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$. -/
def nambuTau1 : Matrix (V ⊕ V) (V ⊕ V) R :=
  Matrix.fromBlocks 0 1 1 0

/-- $\tau_1^2 = 1$ involution property. -/
theorem nambuTau1_sq :
    (nambuTau1 (V := V) (R := R)) * nambuTau1 = 1 := by
  rw [nambuTau1, Matrix.fromBlocks_multiply]
  simp

/-- Discrete BdG Hamiltonian with normal generator `h` and pairing `Δ`. -/
def nambuBdG (h Δ : Matrix V V R) : Matrix (V ⊕ V) (V ⊕ V) R :=
  Matrix.fromBlocks h Δ Δᵀ (-hᵀ)

/-- Unconditional block transposition under $\tau_1$ conjugation:
    $\tau_1 \begin{pmatrix} A & B \\ C & D \end{pmatrix} \tau_1 = \begin{pmatrix} D & C \\ B & A \end{pmatrix}$. -/
theorem nambu_swap (A B C D : Matrix V V R) :
    nambuTau1 (V := V) (R := R) * Matrix.fromBlocks A B C D * nambuTau1 =
      Matrix.fromBlocks D C B A := by
  dsimp [nambuTau1]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp

/-- Unconditional block swap of the BdG Hamiltonian under $\tau_1$ conjugation. -/
theorem nambu_bdg_swap (h Δ : Matrix V V R) :
    nambuTau1 (V := V) (R := R) * nambuBdG h Δ * nambuTau1 =
      Matrix.fromBlocks (-hᵀ) Δᵀ Δ h := by
  rw [nambuBdG, nambu_swap]

/-- The Fundamental Nambu-BdG Particle-Hole Antisymmetry:
    For skew-symmetric pairing $\Delta^\top = -\Delta$,
    $\tau_1 H_{\mathrm{BdG}} \tau_1 = - H_{\mathrm{BdG}}^\top$. -/
theorem nambu_bdg_antisymmetry (h Δ : Matrix V V R) (h_skew : Δᵀ = -Δ) :
    nambuTau1 (V := V) (R := R) * nambuBdG h Δ * nambuTau1 = - (nambuBdG h Δ)ᵀ := by
  rw [nambu_bdg_swap]
  rw [nambuBdG, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]
  simp only [Matrix.transpose_transpose, Matrix.transpose_neg, h_skew, neg_neg]

/-- Transpose of the BdG Hamiltonian under symmetric normal generator $h^\top = h$:
    $H_{\mathrm{BdG}}^\top = H_{\mathrm{BdG}}$. -/
theorem nambu_bdg_transpose (h Δ : Matrix V V R) (h_symm : hᵀ = h) :
    (nambuBdG h Δ)ᵀ = nambuBdG h Δ := by
  rw [nambuBdG, Matrix.fromBlocks_transpose]
  simp only [Matrix.transpose_transpose, Matrix.transpose_neg, h_symm]

/-- Nambu-BdG Particle-Hole Sign Reversal:
    For symmetric $h^\top = h$ and skew-symmetric $\Delta^\top = -\Delta$,
    $\tau_1 H_{\mathrm{BdG}} \tau_1 = - H_{\mathrm{BdG}}$. -/
theorem nambu_bdg_particle_hole (h Δ : Matrix V V R) (h_symm : hᵀ = h) (h_skew : Δᵀ = -Δ) :
    nambuTau1 * nambuBdG h Δ * nambuTau1 = - nambuBdG h Δ := by
  rw [nambu_bdg_antisymmetry h Δ h_skew]
  rw [nambu_bdg_transpose h Δ h_symm]

/-! #### 4. S-Matrix Sector (Positive Grassmannian Gr+(2, 4) Plücker Syzygy) -/

/-- $2 \times 2$ Plücker coordinate minor $\Delta_{i j}(C) = C_{0 i} C_{1 j} - C_{0 j} C_{1 i}$. -/
def pluckerMinor (C : Matrix (Fin 2) (Fin 4) R) (i j : Fin 4) : R :=
  C 0 i * C 1 j - C 0 j * C 1 i

/-- Positive Grassmannian $\mathrm{Gr}^+(2, 4)$ 4-term Plücker Syzygy:
    $\Delta_{01} \Delta_{23} - \Delta_{02} \Delta_{13} + \Delta_{03} \Delta_{12} = 0$. -/
theorem plucker_syzygy_4term (C : Matrix (Fin 2) (Fin 4) R) :
    pluckerMinor C 0 1 * pluckerMinor C 2 3 -
    pluckerMinor C 0 2 * pluckerMinor C 1 3 +
    pluckerMinor C 0 3 * pluckerMinor C 1 2 = 0 := by
  dsimp [pluckerMinor]
  ring

/-! #### 5. Foundations Sector (Split (4,4) Zorn-Krein Invariant Metric) -/

/-- Split $(4,4)$ Zorn-Krein invariant metric norm:
    $\mathcal{N}(S, Q, A, v; m) = S^2 - \|A\|^2 + m^2 \|v\|^2 - Q^2$. -/
def zornKreinNorm (S Q : R) (A v : Fin 3 → R) (m : R) : R :=
  S^2 - (∑ i, (A i)^2) + m^2 * (∑ i, (v i)^2) - Q^2

/-- Exact Decoupling of the Split $(4,4)$ Zorn-Krein Invariant Metric:
    Separates $(S^2 - Q^2)$ from the transverse dynamical channels. -/
theorem zornKreinNorm_decoupling (S Q : R) (A v : Fin 3 → R) (m : R) :
    zornKreinNorm S Q A v m = (S^2 - Q^2) + (m^2 * (∑ i, (v i)^2) - (∑ i, (A i)^2)) := by
  dsimp [zornKreinNorm]
  ring

/-! ### Section 2: The Grothendieck AB5 Tracial Colimit Tower -/

/-- Tracial state on `Matrix (Fin 2) (Fin 2) R` normalized by `1/2`:
    $\mathrm{tr}_2(M) = \frac{1}{2} \mathrm{Tr}(M)$. -/
def tracialState2 (M : Matrix (Fin 2) (Fin 2) R) [Invertible (2 : R)] : R :=
  ⅟(2 : R) * Matrix.trace M

/-- Normalized trace of identity is 1: $\mathrm{tr}_2(I_2) = 1$. -/
theorem tracialState2_one [Invertible (2 : R)] :
    tracialState2 (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  dsimp [tracialState2]
  rw [Matrix.trace_one]
  simp only [Fintype.card_fin]
  exact invOf_mul_self (2 : R)

/-- Cyclic property of the normalized tracial state: $\mathrm{tr}_2(AB) = \mathrm{tr}_2(BA)$. -/
theorem tracialState2_cyclic (A B : Matrix (Fin 2) (Fin 2) R) [Invertible (2 : R)] :
    tracialState2 (A * B) = tracialState2 (B * A) := by
  dsimp [tracialState2]
  rw [Matrix.trace_mul_comm]

/-- Moore-Penrose support projector package on `Matrix V V R`. -/
structure MoorePenroseSupport (rho pinv : Matrix V V R) where
  P : Matrix V V R
  hP : P = rho * pinv
  h_idem : P * P = P
  h_supp : P * rho = rho

/-- A nonzero singular support example for the currently stated support
projector fields. This witnesses the package, without asserting the full
Moore–Penrose equations. -/
def standardMoorePenroseSupport :
    MoorePenroseSupport
      (!![(1 : ℚ), 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ)
      (!![(1 : ℚ), 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) where
  P := !![(1 : ℚ), 0; 0, 0]
  hP := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  h_idem := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  h_supp := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- The density matrix in the standard support example is nonzero. -/
theorem standardMoorePenroseSupport_rho_ne_zero :
    (!![(1 : ℚ), 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) ≠ 0 := by
  intro h
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => M 0 0) h
  norm_num at h00

/-- The standard support example has a concrete nonzero kernel vector, hence
the exhibited density matrix is singular as a linear map. -/
theorem standardMoorePenroseSupport_nonzero_kernel :
    ∃ v : Fin 2 → ℚ,
      v ≠ 0 ∧
        (!![(1 : ℚ), 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ).mulVec v = 0 := by
  let v : Fin 2 → ℚ := ![0, 1]
  refine ⟨v, ?_, ?_⟩
  · intro h
    have h1 := congrFun h 1
    norm_num [v] at h1
  · ext i
    fin_cases i <;>
      norm_num [v, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Moore-Penrose support projector orthogonal complement annihilates the density matrix:
    $(1 - P) \rho = 0$. -/
theorem moore_penrose_annihilates_kernel (rho pinv : Matrix V V R) (mp : MoorePenroseSupport rho pinv) :
    (1 - mp.P) * rho = 0 := by
  rw [sub_mul, one_mul, mp.h_supp, sub_self]

/-- Drazin stationary attractor kernel annihilator:
    For $L L^D L = L$, the projector complement satisfies $L (1 - L^D L) = 0$. -/
theorem drazin_kernel_annihilator (L LD : Matrix V V R) (h3 : L * LD * L = L) :
    L * (1 - LD * L) = 0 := by
  rw [mul_sub, mul_one, ← mul_assoc, h3, sub_self]

/-! ### Section 3: The Curry–Howard–Lambek–Baez Retraction -/

/-- A split retraction between a flux carrier and its invariant carrier.
`coagula` embeds invariant data into the flux carrier and `solve` recovers it. -/
structure CHLBRetraction (Flux Invariant : Type*) where
  solve : Flux → Invariant
  coagula : Invariant → Flux
  h_retract : ∀ x : Invariant, solve (coagula x) = x

/-- A concrete split retraction with a nontrivial flux carrier. -/
def standardCHLBRetraction : CHLBRetraction (ℕ × Bool) ℕ where
  solve := Prod.fst
  coagula := fun n => (n, false)
  h_retract := fun _ => rfl

/-- The idempotent endomorphism induced by the split retraction. -/
def monadT {Flux Invariant : Type*} (r : CHLBRetraction Flux Invariant) (f : Flux) : Flux :=
  r.coagula (r.solve f)

/-- Idempotency follows from the retraction law, rather than assuming the
intermediate equality for the particular input. -/
theorem monadT_idempotent {Flux Invariant : Type*} (r : CHLBRetraction Flux Invariant) (f : Flux) :
    monadT r (monadT r f) = monadT r f := by
  dsimp [monadT]
  rw [r.h_retract]

/-! ### Section 4: Master Verification Certificate -/

/-- Master Verification Certificate for Section 78:
    Curry-Howard-Lambek-Baez Synthesis and Monadic Adjunction. -/
structure CurryHowardLambekBaezMonadCertificate : Prop where
  wdw_modular_zero :
    ∀ {V : Type u_V} [DecidableEq V] [Fintype V] {R : Type u_R} [CommRing R]
      (H_wdw K_mod : Matrix V V R) (h_eq : H_wdw = K_mod) (psi : V → R),
      isWdwZeroMode H_wdw psi ↔ isModularZeroMode K_mod psi
  triality_cube :
    ∀ {R : Type u_R} [CommRing R] (v : Fin 3 → R),
      trialityCycle (trialityCycle (trialityCycle v)) = v
  nambu_tau1_sq :
    ∀ {V : Type u_V} [DecidableEq V] [Fintype V] {R : Type u_R} [CommRing R],
      (nambuTau1 (V := V) (R := R)) * nambuTau1 = 1
  nambu_bdg_ph :
    ∀ {V : Type u_V} [DecidableEq V] [Fintype V] {R : Type u_R} [CommRing R]
      (h Δ : Matrix V V R), hᵀ = h → Δᵀ = -Δ →
      nambuTau1 * nambuBdG h Δ * nambuTau1 = - nambuBdG h Δ
  plucker_syzygy :
    ∀ {R : Type u_R} [CommRing R] (C : Matrix (Fin 2) (Fin 4) R),
      pluckerMinor C 0 1 * pluckerMinor C 2 3 -
      pluckerMinor C 0 2 * pluckerMinor C 1 3 +
      pluckerMinor C 0 3 * pluckerMinor C 1 2 = 0
  zorn_krein_decoupling :
    ∀ {R : Type u_R} [CommRing R] (S Q : R) (A v : Fin 3 → R) (m : R),
      zornKreinNorm S Q A v m = (S^2 - Q^2) + (m^2 * (∑ i, (v i)^2) - (∑ i, (A i)^2))
  tracial_state_one :
    ∀ {R : Type u_R} [CommRing R] [Invertible (2 : R)],
      tracialState2 (1 : Matrix (Fin 2) (Fin 2) R) = 1
  tracial_state_cyclic :
    ∀ {R : Type u_R} [CommRing R] [Invertible (2 : R)] (A B : Matrix (Fin 2) (Fin 2) R),
      tracialState2 (A * B) = tracialState2 (B * A)
  mp_annihilates_kernel :
    ∀ {V : Type u_V} [DecidableEq V] [Fintype V] {R : Type u_R} [CommRing R]
      (rho pinv : Matrix V V R) (mp : MoorePenroseSupport rho pinv),
      (1 - mp.P) * rho = 0
  drazin_kernel_annihilates :
    ∀ {V : Type u_V} [DecidableEq V] [Fintype V] {R : Type u_R} [CommRing R]
      (L LD : Matrix V V R), L * LD * L = L →
      L * (1 - LD * L) = 0
  monad_closure :
    ∀ {Flux Invariant : Type*} (r : CHLBRetraction Flux Invariant) (f : Flux),
      monadT r (monadT r f) = monadT r f

/-- Assemble the verified matrix, kernel, and split-retraction laws. -/
theorem compile_chlb_monad_synthesis :
    CurryHowardLambekBaezMonadCertificate where
  wdw_modular_zero := fun H_wdw K_mod h_eq psi =>
    wdw_modular_zero_equivalence H_wdw K_mod h_eq psi
  triality_cube := fun v => trialityCycle_cube v
  nambu_tau1_sq := nambuTau1_sq
  nambu_bdg_ph := fun h Δ h_symm h_skew => nambu_bdg_particle_hole h Δ h_symm h_skew
  plucker_syzygy := fun C => plucker_syzygy_4term C
  zorn_krein_decoupling := fun S Q A v m => zornKreinNorm_decoupling S Q A v m
  tracial_state_one := tracialState2_one
  tracial_state_cyclic := fun A B => tracialState2_cyclic A B
  mp_annihilates_kernel := fun rho pinv mp => moore_penrose_annihilates_kernel rho pinv mp
  drazin_kernel_annihilates := fun L LD h3 => drazin_kernel_annihilator L LD h3
  monad_closure := fun r f => monadT_idempotent r f

end Experimental.Sandbox.Synthesis.CurryHowardLambekBaezMonad
