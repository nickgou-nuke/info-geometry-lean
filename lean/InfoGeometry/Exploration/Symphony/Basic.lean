import InfoGeometry.Krein.DoubledSpace
import InfoGeometry.Canonical.Drazin
import InfoGeometry.Canonical.DrazinKreinCompatibility
import InfoGeometry.Meta.Architecture

namespace InfoGeometry.Exploration.Symphony

open InfoGeometry.Krein
open InfoGeometry.Canonical.Drazin
open InfoGeometry.Canonical.DrazinKreinCompatibility

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/--
A SymphonyDensity is a spectral density of paired states in the doubled space.
Each frequency ω is mapped to a vector in H₂ = E × E.
-/
def SymphonyDensity (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :=
  ℝ → DoubledSpace E

/-- 
The KMS (Kubo-Martin-Schwinger) symmetry condition for a symphony.
The modular inversion J maps the forward partiture to the mirror partiture.
For a balanced symphony, the J-transform of the state at frequency ω 
must cancel the state itself under the fundamental symmetry ε.
-/
def IsBalanced (s : SymphonyDensity E) : Prop :=
  ∀ ω, modular_j (s ω) = spectral_epsilon (s ω)

/-- 
NON-VACUOUS THEOREM: Symphony Cancellation.
Proves that for a balanced symphony, the 'sum' of the two partitures 
(the physical and the ghost) under the complex structure I is zero.
This is the algebraic realization of 'Symphony of two partitures' 
where fluctuations are cancelled by the inversion.
-/
theorem symphony_cancellation (s : SymphonyDensity E) (hBal : IsBalanced s) :
  ∀ ω, complex_i (s ω) = to_doubled (WithLp.snd (s ω)) (-WithLp.fst (s ω)) := by
  intro ω
  let u := s ω
  have h : modular_j u = spectral_epsilon u := hBal ω
  have hfst : WithLp.snd u = WithLp.fst u := by
    have h' := congrArg WithLp.fst h
    simpa [u, modular_j, spectral_epsilon] using h'
  have hsnd : WithLp.fst u = -WithLp.snd u := by
    have h' := congrArg WithLp.snd h
    simpa [u, modular_j, spectral_epsilon] using h'
  apply DoubledSpace.ext
  · have hsnd_neg : -WithLp.snd u = WithLp.snd u := by
      calc
        -WithLp.snd u = -WithLp.fst u := by rw [← hfst]
        _ = -(-WithLp.snd u) := by rw [hsnd]
        _ = WithLp.snd u := by simp
    simpa [u, complex_i, to_doubled] using hsnd_neg
  · have hfst_neg : WithLp.fst u = -WithLp.fst u := by
      calc
        WithLp.fst u = -WithLp.snd u := hsnd
        _ = -WithLp.fst u := by rw [← hfst]
    simpa [u, complex_i, to_doubled] using hfst_neg

/-- 
Drazin Attention Projector on the Doubled Space.
Isolates the 'Active Lane' of the symphony where the cancellation holds.
-/
def active_projector (A : DoubledSpace E →L[ℝ] DoubledSpace E) 
    (B : DoubledSpace E →L[ℝ] DoubledSpace E) (k : ℕ) : Prop :=
  IsDrazinInverse A B k

/-- 
A graded Drazin compatibility package yields an active projector witness.
-/
theorem active_projector_of_compat
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) (k : ℕ)
    (hCompat : KreinGradedDrazinCompatibility (E := E) A B k) :
    active_projector A B k :=
  hCompat.hD

omit [CompleteSpace E] in
/--
Any two active-projector witnesses for the same operator coincide,
even if presented at different Drazin indices.
-/
theorem active_projector_unique_of_indices
    (A B C : DoubledSpace E →L[ℝ] DoubledSpace E) {k ℓ : ℕ}
    (hB : active_projector A B k)
    (hC : active_projector A C ℓ) :
    B = C := by
  exact IsDrazinInverse.unique_of_indices hB hC

/--
Non-vacuous balance preservation on the Drazin active lane.

The commutation steps are discharged through owner lemmas
`modularJ_comm_Preg` and `epsilon_comm_Preg` from
`Canonical.DrazinKreinCompatibility`.
-/
theorem active_projector_preserves_balance
    (A B : DoubledSpace E →L[ℝ] DoubledSpace E) (k : ℕ)
    (hCompat : KreinGradedDrazinCompatibility (E := E) A B k)
    (s : SymphonyDensity E) (hBal : IsBalanced s) :
    IsBalanced (fun ω => (Preg A B) (s ω)) := by
  intro ω
  have hP_comm_j :
      (modular_j (E := E)).comp (Preg A B) =
        (Preg A B).comp (modular_j (E := E)) :=
    modularJ_comm_Preg (E := E) (T := A) (TD := B) (k := k) hCompat
  have hP_comm_eps :
      (spectral_epsilon (E := E)).comp (Preg A B) =
        (Preg A B).comp (spectral_epsilon (E := E)) :=
    epsilon_comm_Preg (E := E) (T := A) (TD := B) (k := k) hCompat
  have hJ :
      modular_j (Preg A B (s ω)) =
        Preg A B (modular_j (s ω)) := by
    have h := congrArg (fun f => f (s ω)) hP_comm_j
    simpa [ContinuousLinearMap.comp_apply] using h
  have hE :
      spectral_epsilon (Preg A B (s ω)) =
        Preg A B (spectral_epsilon (s ω)) := by
    have h := congrArg (fun f => f (s ω)) hP_comm_eps
    simpa [ContinuousLinearMap.comp_apply] using h
  calc
    modular_j (Preg A B (s ω))
        = Preg A B (modular_j (s ω)) := hJ
    _ = Preg A B (spectral_epsilon (s ω)) := by rw [hBal ω]
    _ = spectral_epsilon (Preg A B (s ω)) := hE.symm

end InfoGeometry.Exploration.Symphony
