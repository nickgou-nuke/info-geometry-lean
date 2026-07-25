import Mathlib.Tactic

namespace InfoGeometry.Canonical.TriFacetEigenspace

/-
#### BUCKET 1: CLOSED FINITE THEOREMS
- tri_facet_eigenspace_hyp: O·P_hyp = P_hyp (+1 eigenform)
- tri_facet_eigenspace_ell: O·P_ell = -P_ell (-1 eigenform)
- tri_facet_eigenspace_par: O·P_par = 0 (harmonic annihilation)
- tri_facet_spectral_reconstruction: P_hyp - P_ell = O

#### BUCKET 2: CONDITIONAL THEOREMS
- All theorems conditional on hO: O³ = O and h2: (2:A) ≠ 0

#### BUCKET 3: OPEN CLOSURE DEBT — None.
-/

variable {A : Type*} [Field A]

def P_hyp (O : A) : A := (1 / 2 : A) * (O ^ 2 + O)
def P_ell (O : A) : A := (1 / 2 : A) * (O ^ 2 - O)
def P_par (O : A) : A := 1 - O ^ 2

theorem tri_facet_eigenspace_hyp (h2 : (2 : A) ≠ 0) {O : A} (hO : O ^ 3 = O) :
    O * P_hyp O = P_hyp O := by
  unfold P_hyp
  have h_calc : O * ((1 / 2 : A) * (O ^ 2 + O)) = (1 / 2 : A) * (O ^ 3 + O ^ 2) := by ring
  rw [h_calc, hO]; ring

theorem tri_facet_eigenspace_ell (h2 : (2 : A) ≠ 0) {O : A} (hO : O ^ 3 = O) :
    O * P_ell O = - P_ell O := by
  unfold P_ell
  have h_calc : O * ((1 / 2 : A) * (O ^ 2 - O)) = (1 / 2 : A) * (O ^ 3 - O ^ 2) := by ring
  rw [h_calc, hO]; ring

theorem tri_facet_eigenspace_par {O : A} (hO : O ^ 3 = O) : O * P_par O = 0 := by
  unfold P_par
  have h_calc : O * (1 - O ^ 2) = O - O ^ 3 := by ring
  rw [h_calc, hO]; ring

theorem tri_facet_spectral_reconstruction (h2 : (2 : A) ≠ 0) (O : A) :
    P_hyp O - P_ell O = O := by
  unfold P_hyp P_ell; field_simp [h2]; ring

end InfoGeometry.Canonical.TriFacetEigenspace
