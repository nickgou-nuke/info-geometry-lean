import InfoGeometry.Quantum.QutritProjectiveColorBridge
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Topology.MobiusGeometry
import InfoGeometry.Twistor.RollingSpinorMobiusBridge

open scoped LinearAlgebra.Projectivization

noncomputable section

namespace InfoGeometry.Quantum.QutritProjectiveGeometryOwnerBridge

open InfoGeometry.Quantum.QutritProjectiveColorBridge

/-- Projective sphere owner used by Möbius and branching discussions. -/
abbrev CP1Carrier : Type := InfoGeometry.CP1

/-- The Riemann sphere model corresponding to projective `CP¹`. -/
abbrev CP1OnRiemann : Type := InfoGeometry.RiemannSphere

/-- Existing doubled/separated projective sphere owner used for chiral sectors. -/
abbrev BiSplitCP1Carrier : Type := InfoGeometry.Twistor.RollingSpinorMobiusBridge.DoubledCP1

/-- Existing tripled projective sphere owner used for three-frame data. -/
abbrev BiSplitTripleCP1Carrier : Type :=
  InfoGeometry.Twistor.RollingSpinorMobiusBridge.TripledCP1

/-- Twistor projective owner; CP³-like carrier with separate (2,2)-Hermitian geometry. -/
abbrev TwistorProjectiveCarrier : Type := PenroseCP3

/-- Degree-2 Veronese coordinates on raw `Fin 3` vectors.
+
+    CP¹ homogeneous point `[u:v]` maps to `[u², uv, v²]`. -/
def CP1Veronese2 (p : CP1Carrier) : Fin 3 → ℂ :=
  ![p.z1 ^ 2, p.z1 * p.z2, p.z2 ^ 2]

/-- The degree-2 Veronese is nonzero for nonzero homogeneous coordinates. -/
theorem CP1Veronese2_ne_zero (p : CP1Carrier) : CP1Veronese2 p ≠ 0 := by
  intro h
  have hz1 : p.z1 ^ 2 = 0 := by
    have := congrArg (fun v : Fin 3 → ℂ => v 0) h
    simpa [CP1Veronese2] using this
  have hz2 : p.z2 ^ 2 = 0 := by
    have := congrArg (fun v : Fin 3 → ℂ => v 2) h
    simpa [CP1Veronese2] using this
  have hz1' : p.z1 = 0 := (pow_eq_zero_iff (a := p.z1) (n := 2) two_ne_zero).1 hz1
  have hz2' : p.z2 = 0 := (pow_eq_zero_iff (a := p.z2) (n := 2) two_ne_zero).1 hz2
  exact p.not_both_zero.elim (fun hz1nz => hz1nz hz1') (fun hz2nz => hz2nz hz2')

/-- Projective-2 embedding along the canonical CP² ray carrier.

+The qutrit carrier in this repository is `FinKetSpace (Fin 3)`; we therefore
+use the Euclidean coordinate equivalence. -/
def CP1_to_ColorCP2 (p : CP1Carrier) : ColorCP2 :=
  Projectivization.mk ℂ
    ((EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin 3)).symm (CP1Veronese2 p))
    (by
      intro hz
      exact CP1Veronese2_ne_zero p (congrArg (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin 3)) hz))

/-- Degree-3 Veronese coordinates into the triplet-plus-singlet carrier.

+CP¹ coordinate `[u:v]` maps to `(u³,u²v,uv²; v³)`. -/
def CP1Veronese3 (p : CP1Carrier) : ColorSingletCarrier :=
  (![p.z1 ^ 3, p.z1 ^ 2 * p.z2, p.z1 * p.z2 ^ 2], p.z2 ^ 3)

/-- The degree-3 Veronese is nonzero for nonzero homogeneous coordinates. -/
theorem CP1Veronese3_ne_zero (p : CP1Carrier) : CP1Veronese3 p ≠ 0 := by
  intro h
  have hz1 : p.z1 ^ 3 = 0 := by
    have := congrArg (fun v : Fin 3 → ℂ => v 0) (congrArg Prod.fst h)
    simpa [CP1Veronese3] using this
  have hz2 : p.z2 ^ 3 = 0 := by
    have := congrArg (fun v : ColorSingletCarrier => v.2) h
    simpa [CP1Veronese3] using this
  have hz1' : p.z1 = 0 := (pow_eq_zero_iff (a := p.z1) (n := 3) three_ne_zero).1 hz1
  have hz2' : p.z2 = 0 := (pow_eq_zero_iff (a := p.z2) (n := 3) three_ne_zero).1 hz2
  exact p.not_both_zero.elim (fun hz1nz => hz1nz hz1') (fun hz2nz => hz2nz hz2')

/-- Projective-3 Veronese into the triplet-plus-singlet `CP³` carrier.

+This is the symmetric-power family used to separate CP¹-to-CP³ embeddings from
+native CP³ (twistor-style) structures. -/
def CP1_to_ColorSingletCP3 (p : CP1Carrier) : ColorSingletCP3 :=
  Projectivization.mk ℂ (CP1Veronese3 p) (CP1Veronese3_ne_zero p)

/-- Degree-n monomial branch map on homogeneous `CP¹` coordinates.
+
+Not a Möbius transform in general (`n ≠ 1`), but genuine branched cover behavior
+in inhomogeneous charts. -/
def CP1_BranchCover (n : ℕ) (hpos : 0 < n) (p : CP1Carrier) : CP1Carrier :=
  {
    z1 := p.z1 ^ n,
    z2 := p.z2 ^ n,
    not_both_zero := by
      rcases p.not_both_zero with hz1 | hz2
      · exact Or.inl <| by
          intro hz
          exact hz1 ((pow_eq_zero_iff (a := p.z1) (n := n) (Nat.ne_of_gt hpos)).1 hz)
      · exact Or.inr <| by
          intro hz
          exact hz2 ((pow_eq_zero_iff (a := p.z2) (n := n) (Nat.ne_of_gt hpos)).1 hz)
  }

end InfoGeometry.Quantum.QutritProjectiveGeometryOwnerBridge
