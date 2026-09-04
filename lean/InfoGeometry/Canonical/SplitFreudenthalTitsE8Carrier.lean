import Mathlib
import InfoGeometry.Lie.SplitOctonionStandardDerivation
import InfoGeometry.Algebra.H3ZornCarrierBasis
import InfoGeometry.Canonical.F4ActionMatrixRankCertificateCapstone

noncomputable section

namespace InfoGeometry.Canonical.SplitFreudenthalTitsE8Carrier

open InfoGeometry.Algebra
open InfoGeometry.Algebra.H3Zorn
open InfoGeometry.Lie.SplitOctonionStandardDerivation
open InfoGeometry.Canonical.F4ActionMatrix
open InfoGeometry.Canonical.F4ActionMatrixRationalCertificate

abbrev Zorn := ZornVectorMatrix ℝ
abbrev H3 := H3Zorn ℝ

/-- Traceless split-octonions in the native Zorn carrier. -/
def ZornTraceless := {x : Zorn // x.a + x.b = 0}

instance : AddCommGroup ZornTraceless := Subtype.instAddCommGroup
instance : Module ℝ ZornTraceless := Subtype.instModule

/-- Explicit `1+3+3=7` coordinate model of the traceless Zorn subspace. -/
def zornTracelessEquiv :
    ZornTraceless ≃ₗ[ℝ] (ℝ × ((Fin 3 → ℝ) × (Fin 3 → ℝ))) where
  toFun x := (x.1.a, (x.1.v, x.1.w))
  invFun p := ⟨⟨p.1, p.2.1, p.2.2, -p.1⟩, by simp⟩
  left_inv x := by
    apply Subtype.ext
    rcases x with ⟨x,hx⟩
    apply ZornVectorMatrix.ext
    · rfl
    · rfl
    · rfl
    · linarith
  right_inv p := by rcases p with ⟨a,v,w⟩; rfl
  map_add' x y := rfl
  map_smul' r x := rfl

@[simp] theorem zornTraceless_finrank :
    Module.finrank ℝ ZornTraceless = 7 := by
  rw [zornTracelessEquiv.finrank_eq, Module.finrank_prod, Module.finrank_prod]
  simp

/-- Traceless split-Albert elements for the native linear trace. -/
def AlbertTraceless := {x : H3 // linearTrace x = 0}

instance : AddCommGroup AlbertTraceless := Subtype.instAddCommGroup
instance : Module ℝ AlbertTraceless := Subtype.instModule

/-- Explicit `2 + 3*8 = 26` coordinate model of the traceless Albert subspace. -/
def albertTracelessEquiv :
    AlbertTraceless ≃ₗ[ℝ]
      (ℝ × (ℝ × (Zorn × (Zorn × Zorn)))) where
  toFun x := (x.1.α₁, (x.1.α₂, (x.1.a, (x.1.b, x.1.c))))
  invFun p :=
    ⟨⟨p.1, p.2.1, -p.1 - p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩,
      by simp [linearTrace]⟩
  left_inv x := by
    apply Subtype.ext
    rcases x with ⟨x,hx⟩
    apply H3Zorn.ext_h3
    · rfl
    · rfl
    · dsimp [linearTrace] at hx
      linarith
    · rfl
    · rfl
    · rfl
  right_inv p := by
    rcases p with ⟨a1,a2,a,b,c⟩
    rfl
  map_add' x y := rfl
  map_smul' r x := rfl

@[simp] theorem albertTraceless_finrank :
    Module.finrank ℝ AlbertTraceless = 26 := by
  rw [albertTracelessEquiv.finrank_eq]
  simp only [Module.finrank_prod]
  rw [InfoGeometry.Algebra.H3ZornCarrierBasis.zorn_finrank]
  norm_num

/-- Finite coordinate realization of the mixed tensor sector after choosing
bases of the two traceless factors. -/
abbrev MixedCoordinateCarrier := Matrix (Fin 7) (Fin 26) ℝ

@[simp] theorem mixedCoordinateCarrier_finrank :
    Module.finrank ℝ MixedCoordinateCarrier = 182 := by
  simp [MixedCoordinateCarrier, Module.finrank_matrix]

/-- The certified 52-dimensional real action span of the native split-Albert
`F4` derivations. -/
abbrev F4CertifiedCarrier :=
  Submodule.span ℝ (Set.range (fun i : Fin 52 => f4ActionMatrixReal i))

@[simp] theorem f4CertifiedCarrier_finrank :
    Module.finrank ℝ F4CertifiedCarrier = 52 :=
  finrank_f4ActionMatrixReal_span_eq_52

/-- The native split-octonion derivation carrier used for the `G2(2)` summand. -/
abbrev G2CertifiedCarrier := canonicalZornDerivations

@[simp] theorem g2CertifiedCarrier_finrank :
    Module.finrank ℝ G2CertifiedCarrier = 14 :=
  canonicalZornDerivations_finrank

/-- The theorem-safe finite carrier corresponding to the Tits vector-space
decomposition `g2 ⊕ (O'_s ⊗ H3(O_s)') ⊕ f4` after choosing bases in the mixed
sector.  No Lie bracket is installed by this definition. -/
abbrev SplitTitsE8Carrier :=
  G2CertifiedCarrier × (MixedCoordinateCarrier × F4CertifiedCarrier)

/-- Exact dimension packet of the split Freudenthal-Tits decomposition. -/
theorem split_tits_dimension_packet :
    Module.finrank ℝ G2CertifiedCarrier = 14 ∧
    Module.finrank ℝ ZornTraceless = 7 ∧
    Module.finrank ℝ AlbertTraceless = 26 ∧
    Module.finrank ℝ MixedCoordinateCarrier = 182 ∧
    Module.finrank ℝ F4CertifiedCarrier = 52 := by
  exact ⟨g2CertifiedCarrier_finrank, zornTraceless_finrank,
    albertTraceless_finrank, mixedCoordinateCarrier_finrank,
    f4CertifiedCarrier_finrank⟩

/-- The finite Tits carrier has the exceptional dimension `248`. -/
theorem splitTitsE8Carrier_finrank :
    Module.finrank ℝ SplitTitsE8Carrier = 248 := by
  rw [Module.finrank_prod, Module.finrank_prod,
    g2CertifiedCarrier_finrank, mixedCoordinateCarrier_finrank,
    f4CertifiedCarrier_finrank]
  norm_num

/-- The familiar component arithmetic is exposed separately from the carrier
proof. -/
theorem split_tits_dimension_arithmetic : 14 + 7 * 26 + 52 = 248 := by
  norm_num

/-- A socket for the missing mixed Tits bracket.  Supplying this data is the
next obligation before the carrier can be identified with a Lie algebra of
split type `E8`. -/
structure MixedTitsBracketData where
  bracket : SplitTitsE8Carrier → SplitTitsE8Carrier → SplitTitsE8Carrier
  skew : ∀ x y, bracket x y = - bracket y x
  jacobi : ∀ x y z,
    bracket x (bracket y z) + bracket y (bracket z x) +
      bracket z (bracket x y) = 0

/-- Dimension alone does not construct the `E8(8)` bracket. -/
def split_tits_lie_bracket_closure_debt : String :=
  "Open: define the Tits mixed bracket on the certified 248D carrier, prove its action terms land in the native G2/F4 summands, and prove the mixed Jacobi identity."

end InfoGeometry.Canonical.SplitFreudenthalTitsE8Carrier
