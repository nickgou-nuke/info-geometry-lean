import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The Primon Coulomb Gas and GUE Level Repulsion

\[
R_2(x)=1-\left(\frac{\sin(\pi x)}{\pi x}\right)^2,
\qquad
H_{\mathrm{Dyson}}=E_{\mathrm{ext}}-2E_{\log}.
\]

\[
\log\Delta = E_{\log},
\qquad
H_{\mathrm{Dyson}} = E_{\mathrm{ext}} - \log \Delta^2.
\]
-/

namespace InfoGeometry.Canonical.PrimonCoulombGas

open Real
open scoped BigOperators

/-- `R_2(x) := 1 - (\sin(\pi x)/(\pi x))^2`. -/
noncomputable def gue_pair_correlation (x : ℝ) : ℝ :=
  1 - (sin (π * x) / (π * x)) ^ 2

/-- `\sin(\pi x)/(\pi x)=1 \to R_2(x)=0`. -/
theorem gue_repulsion_at_origin (x : ℝ) (h_limit : sin (π * x) / (π * x) = 1) :
    gue_pair_correlation x = 0 := by
  unfold gue_pair_correlation
  rw [h_limit]
  have h_one_sq : (1 : ℝ) ^ 2 = 1 := by ring
  rw [h_one_sq]
  ring

section FiniteDysonBridge

variable {N : ℕ}

/-- `E_{\mathrm{ext}}(\lambda,V)`. -/
def external_potential_energy (lam : Fin N → ℝ) (V : ℝ → ℝ) : ℝ :=
  Finset.sum Finset.univ (fun i : Fin N => V (lam i))

/-- `E_{\log}(\lambda)`. -/
noncomputable def log_interaction_energy (lam : Fin N → ℝ) : ℝ :=
  Finset.sum Finset.univ (fun i : Fin N =>
    Finset.sum (Finset.Ioi i) (fun j : Fin N => Real.log |lam j - lam i|))

/-- `|\Delta(\lambda)|`. -/
def vandermonde_product_abs (lam : Fin N → ℝ) : ℝ :=
  Finset.prod Finset.univ (fun i : Fin N =>
    Finset.prod (Finset.Ioi i) (fun j : Fin N => |lam j - lam i|))

/-- `H_{\mathrm{Dyson}}(\lambda,V) := E_{\mathrm{ext}} - 2E_{\log}`. -/
noncomputable def dyson_hamiltonian (lam : Fin N → ℝ) (V : ℝ → ℝ) : ℝ :=
  external_potential_energy lam V - 2 * log_interaction_energy lam

/-- `\log(\prod f)=\sum\log f` under `0<f`. -/
theorem log_prod_of_pos
    {α : Type*}
    (s : Finset α)
    (f : α → ℝ)
    (hf : ∀ a ∈ s, 0 < f a) :
    Real.log (s.prod f) = s.sum (fun a => Real.log (f a)) := by
  refine Real.log_prod ?_
  intro a ha
  exact ne_of_gt (hf a ha)

/-- `\forall i<j,\ \lambda_i\ne\lambda_j \to \log|\Delta| = E_{\log}`. -/
theorem log_vandermonde_product_abs_eq_log_interaction_energy
    (lam : Fin N → ℝ)
    (hsep : ∀ i : Fin N, ∀ j ∈ Finset.Ioi i, lam j ≠ lam i) :
    Real.log (vandermonde_product_abs lam) = log_interaction_energy lam := by
  have hinner :
      ∀ i : Fin N, ∀ j ∈ Finset.Ioi i, 0 < |lam j - lam i| := by
    intro i j hj
    exact abs_pos.mpr (sub_ne_zero.mpr (hsep i j hj))
  have houter :
      ∀ i ∈ (Finset.univ : Finset (Fin N)),
        0 < Finset.prod (Finset.Ioi i) (fun j : Fin N => |lam j - lam i|) := by
    intro i hi
    exact Finset.prod_pos (fun j hj => hinner i j hj)
  unfold vandermonde_product_abs log_interaction_energy
  rw [log_prod_of_pos (s := Finset.univ)
      (f := fun i : Fin N => Finset.prod (Finset.Ioi i) (fun j : Fin N => |lam j - lam i|)) houter]
  apply Finset.sum_congr rfl
  intro i hi
  rw [log_prod_of_pos (s := Finset.Ioi i) (f := fun j : Fin N => |lam j - lam i|) (hinner i)]

/-- `\log|\Delta|^2 = 2E_{\log}`. -/
theorem log_vandermonde_square_eq_two_log_interaction
    (lam : Fin N → ℝ)
    (hsep : ∀ i : Fin N, ∀ j ∈ Finset.Ioi i, lam j ≠ lam i) :
    Real.log ((vandermonde_product_abs lam) ^ 2) = 2 * log_interaction_energy lam := by
  rw [Real.log_pow]
  rw [log_vandermonde_product_abs_eq_log_interaction_energy lam hsep]
  ring

/-- `H_{\mathrm{Dyson}} = E_{\mathrm{ext}} - \log|\Delta|^2`. -/
theorem dyson_to_vandermonde_bridge
    (lam : Fin N → ℝ)
    (V : ℝ → ℝ)
    (hsep : ∀ i : Fin N, ∀ j ∈ Finset.Ioi i, lam j ≠ lam i) :
    dyson_hamiltonian lam V =
      external_potential_energy lam V - Real.log ((vandermonde_product_abs lam) ^ 2) := by
  unfold dyson_hamiltonian
  rw [log_vandermonde_square_eq_two_log_interaction lam hsep]

end FiniteDysonBridge

end InfoGeometry.Canonical.PrimonCoulombGas
