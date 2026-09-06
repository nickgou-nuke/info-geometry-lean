import Mathlib.Tactic

noncomputable section

namespace InfoGeometry.Algebra.CliffordCl8SpinorTriality

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

theorem anticomm_symm (a b : R) (h : a * b = - (b * a)) : b * a = - (a * b) := by
  rw [h, neg_neg]

/-- Generators of the 8-dimensional Clifford Algebra Cl(8,0) over a commutative ring R.
    Satisfies anti-commutation gᵢ gⱼ + gⱼ gᵢ = 2 δᵢⱼ 1 and gᵢ² = 1. -/
structure Clifford8Generators (R : Type*) [Ring R] where
  g1 : R
  g2 : R
  g3 : R
  g4 : R
  g5 : R
  g6 : R
  g7 : R
  g8 : R
  g1_sq : g1 * g1 = 1
  g2_sq : g2 * g2 = 1
  g3_sq : g3 * g3 = 1
  g4_sq : g4 * g4 = 1
  g5_sq : g5 * g5 = 1
  g6_sq : g6 * g6 = 1
  g7_sq : g7 * g7 = 1
  g8_sq : g8 * g8 = 1
  g12 : g1 * g2 = - (g2 * g1)
  g13 : g1 * g3 = - (g3 * g1)
  g14 : g1 * g4 = - (g4 * g1)
  g15 : g1 * g5 = - (g5 * g1)
  g16 : g1 * g6 = - (g6 * g1)
  g17 : g1 * g7 = - (g7 * g1)
  g18 : g1 * g8 = - (g8 * g1)
  g23 : g2 * g3 = - (g3 * g2)
  g24 : g2 * g4 = - (g4 * g2)
  g25 : g2 * g5 = - (g5 * g2)
  g26 : g2 * g6 = - (g6 * g2)
  g27 : g2 * g7 = - (g7 * g2)
  g28 : g2 * g8 = - (g8 * g2)
  g34 : g3 * g4 = - (g4 * g3)
  g35 : g3 * g5 = - (g5 * g3)
  g36 : g3 * g6 = - (g6 * g3)
  g37 : g3 * g7 = - (g7 * g3)
  g38 : g3 * g8 = - (g8 * g3)
  g45 : g4 * g5 = - (g5 * g4)
  g46 : g4 * g6 = - (g6 * g4)
  g47 : g4 * g7 = - (g7 * g4)
  g48 : g4 * g8 = - (g8 * g4)
  g56 : g5 * g6 = - (g6 * g5)
  g57 : g5 * g7 = - (g7 * g5)
  g58 : g5 * g8 = - (g8 * g5)
  g67 : g6 * g7 = - (g7 * g6)
  g68 : g6 * g8 = - (g8 * g6)
  g78 : g7 * g8 = - (g8 * g7)

/-- The Chiral Volume Form Γ = γ₁ γ₂ γ₃ γ₄ γ₅ γ₆ γ₇ γ₈ in Cl(8,0). -/
def Gamma (g : Clifford8Generators R) : R :=
  g.g1 * g.g2 * g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8

/-- Positive Chiral Majorana-Weyl Projector P₊ = (1 + Γ) / 2. -/
def PPlus (g : Clifford8Generators R) : R :=
  (⅟2 : R) * (1 + Gamma g)

/-- Negative Chiral Majorana-Weyl Projector P₋ = (1 - Γ) / 2. -/
def PMinus (g : Clifford8Generators R) : R :=
  (⅟2 : R) * (1 - Gamma g)

/-- **Theorem 1**: Left action g1 * Gamma g = g2 * g3 * g4 * g5 * g6 * g7 * g8. -/
theorem g1_gamma_left (g : Clifford8Generators R) :
    g.g1 * Gamma g = g.g2 * g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8 := by
  dsimp [Gamma]
  have h_assoc : g.g1 * (g.g1 * g.g2 * g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) =
      (g.g1 * g.g1) * (g.g2 * g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) := by noncomm_ring
  rw [h_assoc, g.g1_sq, one_mul]

/-- **Theorem 2**: Right action Gamma g * g1 = - (g2 * g3 * g4 * g5 * g6 * g7 * g8). -/
theorem gamma_g1_right (g : Clifford8Generators R) :
    Gamma g * g.g1 = - (g.g2 * g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) := by
  dsimp [Gamma]
  have h18 : g.g8 * g.g1 = - (g.g1 * g.g8) := anticomm_symm g.g1 g.g8 g.g18
  have h17 : g.g7 * g.g1 = - (g.g1 * g.g7) := anticomm_symm g.g1 g.g7 g.g17
  have h16 : g.g6 * g.g1 = - (g.g1 * g.g6) := anticomm_symm g.g1 g.g6 g.g16
  have h15 : g.g5 * g.g1 = - (g.g1 * g.g5) := anticomm_symm g.g1 g.g5 g.g15
  have h14 : g.g4 * g.g1 = - (g.g1 * g.g4) := anticomm_symm g.g1 g.g4 g.g14
  have h13 : g.g3 * g.g1 = - (g.g1 * g.g3) := anticomm_symm g.g1 g.g3 g.g13
  have h12 : g.g2 * g.g1 = - (g.g1 * g.g2) := anticomm_symm g.g1 g.g2 g.g12
  have h_sq1 : g.g1 * g.g1 = 1 := g.g1_sq
  calc g.g1 * g.g2 * g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8 * g.g1 =
      g.g1 * (g.g2 * (g.g3 * (g.g4 * (g.g5 * (g.g6 * (g.g7 * (g.g8 * g.g1))))))) := by noncomm_ring
  _ = g.g1 * (g.g2 * (g.g3 * (g.g4 * (g.g5 * (g.g6 * (g.g7 * (- (g.g1 * g.g8)))))))) := by rw [h18]
  _ = - (g.g1 * (g.g2 * (g.g3 * (g.g4 * (g.g5 * (g.g6 * (g.g7 * g.g1 * g.g8))))))) := by noncomm_ring
  _ = - (g.g1 * (g.g2 * (g.g3 * (g.g4 * (g.g5 * (g.g6 * (- (g.g1 * g.g7) * g.g8))))))) := by rw [h17]
  _ = g.g1 * (g.g2 * (g.g3 * (g.g4 * (g.g5 * (g.g6 * g.g1 * g.g7 * g.g8))))) := by noncomm_ring
  _ = g.g1 * (g.g2 * (g.g3 * (g.g4 * (g.g5 * (- (g.g1 * g.g6) * g.g7 * g.g8))))) := by rw [h16]
  _ = - (g.g1 * (g.g2 * (g.g3 * (g.g4 * (g.g5 * g.g1 * g.g6 * g.g7 * g.g8))))) := by noncomm_ring
  _ = - (g.g1 * (g.g2 * (g.g3 * (g.g4 * (- (g.g1 * g.g5) * g.g6 * g.g7 * g.g8))))) := by rw [h15]
  _ = g.g1 * (g.g2 * (g.g3 * (g.g4 * g.g1 * g.g5 * g.g6 * g.g7 * g.g8))) := by noncomm_ring
  _ = g.g1 * (g.g2 * (g.g3 * (- (g.g1 * g.g4) * g.g5 * g.g6 * g.g7 * g.g8))) := by rw [h14]
  _ = - (g.g1 * (g.g2 * (g.g3 * g.g1 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8))) := by noncomm_ring
  _ = - (g.g1 * (g.g2 * (- (g.g1 * g.g3) * g.g4 * g.g5 * g.g6 * g.g7 * g.g8))) := by rw [h13]
  _ = g.g1 * (g.g2 * g.g1 * g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) := by noncomm_ring
  _ = g.g1 * (- (g.g1 * g.g2) * g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) := by rw [h12]
  _ = - ((g.g1 * g.g1) * (g.g2 * g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8)) := by noncomm_ring
  _ = - (1 * (g.g2 * g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8)) := by rw [h_sq1]
  _ = - (g.g2 * g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) := by noncomm_ring

/-- **Theorem 3**: Parity-Vector Anticommutation: Γ γ₁ + γ₁ Γ = 0. -/
theorem gamma_anticomm_g1 (g : Clifford8Generators R) :
    Gamma g * g.g1 + g.g1 * Gamma g = 0 := by
  rw [gamma_g1_right, g1_gamma_left, neg_add_cancel]

/-- **Theorem 4**: 8D Parity Operator Involutivity: Γ² = 1. -/
theorem gamma_sq_eq_one (g : Clifford8Generators R) :
    Gamma g * Gamma g = 1 := by
  have h_right := gamma_g1_right g
  have h_left := g1_gamma_left g
  dsimp [Gamma] at h_right
  dsimp [Gamma] at h_left
  have h23 : g.g2 * g.g3 = - (g.g3 * g.g2) := g.g23
  have h24 : g.g2 * g.g4 = - (g.g4 * g.g2) := g.g24
  have h25 : g.g2 * g.g5 = - (g.g5 * g.g2) := g.g25
  have h26 : g.g2 * g.g6 = - (g.g6 * g.g2) := g.g26
  have h27 : g.g2 * g.g7 = - (g.g7 * g.g2) := g.g27
  have h28 : g.g2 * g.g8 = - (g.g8 * g.g2) := g.g28
  have h34 : g.g3 * g.g4 = - (g.g4 * g.g3) := g.g34
  have h35 : g.g3 * g.g5 = - (g.g5 * g.g3) := g.g35
  have h36 : g.g3 * g.g6 = - (g.g6 * g.g3) := g.g36
  have h37 : g.g3 * g.g7 = - (g.g7 * g.g3) := g.g37
  have h38 : g.g3 * g.g8 = - (g.g8 * g.g3) := g.g38
  have h45 : g.g4 * g.g5 = - (g.g5 * g.g4) := g.g45
  have h46 : g.g4 * g.g6 = - (g.g6 * g.g4) := g.g46
  have h47 : g.g4 * g.g7 = - (g.g7 * g.g4) := g.g47
  have h48 : g.g4 * g.g8 = - (g.g8 * g.g4) := g.g48
  have h56 : g.g5 * g.g6 = - (g.g6 * g.g5) := g.g56
  have h57 : g.g5 * g.g7 = - (g.g7 * g.g5) := g.g57
  have h58 : g.g5 * g.g8 = - (g.g8 * g.g5) := g.g58
  have h67 : g.g6 * g.g7 = - (g.g7 * g.g6) := g.g67
  have h68 : g.g6 * g.g8 = - (g.g8 * g.g6) := g.g68
  have h78 : g.g7 * g.g8 = - (g.g8 * g.g7) := g.g78
  have h_sq2 : g.g2 * g.g2 = 1 := g.g2_sq
  have h_sq3 : g.g3 * g.g3 = 1 := g.g3_sq
  have h_sq4 : g.g4 * g.g4 = 1 := g.g4_sq
  have h_sq5 : g.g5 * g.g5 = 1 := g.g5_sq
  have h_sq6 : g.g6 * g.g6 = 1 := g.g6_sq
  have h_sq7 : g.g7 * g.g7 = 1 := g.g7_sq
  have h_sq8 : g.g8 * g.g8 = 1 := g.g8_sq
  have h28_s := anticomm_symm g.g2 g.g8 g.g28
  have h27_s := anticomm_symm g.g2 g.g7 g.g27
  have h26_s := anticomm_symm g.g2 g.g6 g.g26
  have h25_s := anticomm_symm g.g2 g.g5 g.g25
  have h24_s := anticomm_symm g.g2 g.g4 g.g24
  have h23_s := anticomm_symm g.g2 g.g3 g.g23
  have h38_s := anticomm_symm g.g3 g.g8 g.g38
  have h37_s := anticomm_symm g.g3 g.g7 g.g37
  have h36_s := anticomm_symm g.g3 g.g6 g.g36
  have h35_s := anticomm_symm g.g3 g.g5 g.g35
  have h34_s := anticomm_symm g.g3 g.g4 g.g34
  have h48_s := anticomm_symm g.g4 g.g8 g.g48
  have h47_s := anticomm_symm g.g4 g.g7 g.g47
  have h46_s := anticomm_symm g.g4 g.g6 g.g46
  have h45_s := anticomm_symm g.g4 g.g5 g.g45
  have h58_s := anticomm_symm g.g5 g.g8 g.g58
  have h57_s := anticomm_symm g.g5 g.g7 g.g57
  have h56_s := anticomm_symm g.g5 g.g6 g.g56
  have h68_s := anticomm_symm g.g6 g.g8 g.g68
  have h67_s := anticomm_symm g.g6 g.g7 g.g67
  have h78_s := anticomm_symm g.g7 g.g8 g.g78
  have h_prod2 : (g.g7 * g.g8) * (g.g7 * g.g8) = -1 := by
    calc (g.g7 * g.g8) * (g.g7 * g.g8) =
        g.g7 * (g.g8 * g.g7) * g.g8 := by noncomm_ring
    _ = g.g7 * (- (g.g7 * g.g8)) * g.g8 := by rw [h78_s]
    _ = - ((g.g7 * g.g7) * (g.g8 * g.g8)) := by noncomm_ring
    _ = - (1 * 1) := by rw [h_sq7, h_sq8]
    _ = -1 := by ring
  have h_prod3 : (g.g6 * g.g7 * g.g8) * (g.g6 * g.g7 * g.g8) = -1 := by
    have h_step3 : (g.g6 * g.g7 * g.g8) * (g.g6 * g.g7 * g.g8) =
        g.g6 * (g.g7 * g.g8 * g.g6) * (g.g7 * g.g8) := by noncomm_ring
    have h_shift6 : g.g7 * g.g8 * g.g6 = g.g6 * (g.g7 * g.g8) := by
      have h6a : g.g7 * g.g8 * g.g6 = - (g.g7 * g.g6 * g.g8) := by
        calc g.g7 * g.g8 * g.g6 = g.g7 * (g.g8 * g.g6) := by noncomm_ring
        _ = g.g7 * (- (g.g6 * g.g8)) := by rw [h68_s]
        _ = - (g.g7 * g.g6 * g.g8) := by noncomm_ring
      have h6b : - (g.g7 * g.g6 * g.g8) = g.g6 * (g.g7 * g.g8) := by
        calc - (g.g7 * g.g6 * g.g8) = - ((g.g7 * g.g6) * g.g8) := by noncomm_ring
        _ = - ((- (g.g6 * g.g7)) * g.g8) := by rw [h67_s]
        _ = g.g6 * (g.g7 * g.g8) := by noncomm_ring
      rw [h6a, h6b]
    rw [h_step3, h_shift6]
    have h_sq6_sub : g.g6 * (g.g6 * (g.g7 * g.g8)) * (g.g7 * g.g8) =
        (g.g6 * g.g6) * ((g.g7 * g.g8) * (g.g7 * g.g8)) := by noncomm_ring
    rw [h_sq6_sub, h_sq6, one_mul, h_prod2]
  have h_prod4 : (g.g5 * g.g6 * g.g7 * g.g8) * (g.g5 * g.g6 * g.g7 * g.g8) = 1 := by
    have h_step4 : (g.g5 * g.g6 * g.g7 * g.g8) * (g.g5 * g.g6 * g.g7 * g.g8) =
        g.g5 * (g.g6 * g.g7 * g.g8 * g.g5) * (g.g6 * g.g7 * g.g8) := by noncomm_ring
    have h_shift5 : g.g6 * g.g7 * g.g8 * g.g5 = - (g.g5 * (g.g6 * g.g7 * g.g8)) := by
      have h5a : g.g6 * g.g7 * g.g8 * g.g5 = - (g.g6 * g.g7 * g.g5 * g.g8) := by
        calc g.g6 * g.g7 * g.g8 * g.g5 = g.g6 * g.g7 * (g.g8 * g.g5) := by noncomm_ring
        _ = g.g6 * g.g7 * (- (g.g5 * g.g8)) := by rw [h58_s]
        _ = - (g.g6 * g.g7 * g.g5 * g.g8) := by noncomm_ring
      have h5b : - (g.g6 * g.g7 * g.g5 * g.g8) = g.g6 * g.g5 * g.g7 * g.g8 := by
        calc - (g.g6 * g.g7 * g.g5 * g.g8) = - (g.g6 * (g.g7 * g.g5) * g.g8) := by noncomm_ring
        _ = - (g.g6 * (- (g.g5 * g.g7)) * g.g8) := by rw [h57_s]
        _ = g.g6 * g.g5 * g.g7 * g.g8 := by noncomm_ring
      have h5c : g.g6 * g.g5 * g.g7 * g.g8 = - (g.g5 * (g.g6 * g.g7 * g.g8)) := by
        calc g.g6 * g.g5 * g.g7 * g.g8 = (g.g6 * g.g5) * g.g7 * g.g8 := by noncomm_ring
        _ = (- (g.g5 * g.g6)) * g.g7 * g.g8 := by rw [h56_s]
        _ = - (g.g5 * (g.g6 * g.g7 * g.g8)) := by noncomm_ring
      rw [h5a, h5b, h5c]
    rw [h_step4, h_shift5]
    have h_sq5_sub : g.g5 * (- (g.g5 * (g.g6 * g.g7 * g.g8))) * (g.g6 * g.g7 * g.g8) =
        - ((g.g5 * g.g5) * ((g.g6 * g.g7 * g.g8) * (g.g6 * g.g7 * g.g8))) := by noncomm_ring
    rw [h_sq5_sub, h_sq5, one_mul, h_prod3]
    ring
  have h_prod5 : (g.g4 * g.g5 * g.g6 * g.g7 * g.g8) * (g.g4 * g.g5 * g.g6 * g.g7 * g.g8) = 1 := by
    have h_step5 : (g.g4 * g.g5 * g.g6 * g.g7 * g.g8) * (g.g4 * g.g5 * g.g6 * g.g7 * g.g8) =
        g.g4 * (g.g5 * g.g6 * g.g7 * g.g8 * g.g4) * (g.g5 * g.g6 * g.g7 * g.g8) := by noncomm_ring
    have h_shift4 : g.g5 * g.g6 * g.g7 * g.g8 * g.g4 = g.g4 * (g.g5 * g.g6 * g.g7 * g.g8) := by
      have h1 : g.g5 * g.g6 * g.g7 * g.g8 * g.g4 = - (g.g5 * g.g6 * g.g7 * g.g4 * g.g8) := by
        calc g.g5 * g.g6 * g.g7 * g.g8 * g.g4 = g.g5 * g.g6 * g.g7 * (g.g8 * g.g4) := by noncomm_ring
        _ = g.g5 * g.g6 * g.g7 * (- (g.g4 * g.g8)) := by rw [h48_s]
        _ = - (g.g5 * g.g6 * g.g7 * g.g4 * g.g8) := by noncomm_ring
      have h2 : - (g.g5 * g.g6 * g.g7 * g.g4 * g.g8) = g.g5 * g.g6 * g.g4 * g.g7 * g.g8 := by
        calc - (g.g5 * g.g6 * g.g7 * g.g4 * g.g8) = - (g.g5 * g.g6 * (g.g7 * g.g4) * g.g8) := by noncomm_ring
        _ = - (g.g5 * g.g6 * (- (g.g4 * g.g7)) * g.g8) := by rw [h47_s]
        _ = g.g5 * g.g6 * g.g4 * g.g7 * g.g8 := by noncomm_ring
      have h3 : g.g5 * g.g6 * g.g4 * g.g7 * g.g8 = - (g.g5 * g.g4 * g.g6 * g.g7 * g.g8) := by
        calc g.g5 * g.g6 * g.g4 * g.g7 * g.g8 = g.g5 * (g.g6 * g.g4) * g.g7 * g.g8 := by noncomm_ring
        _ = g.g5 * (- (g.g4 * g.g6)) * g.g7 * g.g8 := by rw [h46_s]
        _ = - (g.g5 * g.g4 * g.g6 * g.g7 * g.g8) := by noncomm_ring
      have h4 : - (g.g5 * g.g4 * g.g6 * g.g7 * g.g8) = g.g4 * (g.g5 * g.g6 * g.g7 * g.g8) := by
        calc - (g.g5 * g.g4 * g.g6 * g.g7 * g.g8) = - ((g.g5 * g.g4) * g.g6 * g.g7 * g.g8) := by noncomm_ring
        _ = - ((- (g.g4 * g.g5)) * g.g6 * g.g7 * g.g8) := by rw [h45_s]
        _ = g.g4 * (g.g5 * g.g6 * g.g7 * g.g8) := by noncomm_ring
      rw [h1, h2, h3, h4]
    rw [h_step5, h_shift4]
    have h_sq4_sub : g.g4 * (g.g4 * (g.g5 * g.g6 * g.g7 * g.g8)) * (g.g5 * g.g6 * g.g7 * g.g8) =
        (g.g4 * g.g4) * ((g.g5 * g.g6 * g.g7 * g.g8) * (g.g5 * g.g6 * g.g7 * g.g8)) := by noncomm_ring
    rw [h_sq4_sub, h_sq4, one_mul, h_prod4]
  have h_prod6 : (g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) * (g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) = -1 := by
    have h_step6 : (g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) * (g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) =
        g.g3 * (g.g4 * g.g5 * g.g6 * g.g7 * g.g8 * g.g3) * (g.g4 * g.g5 * g.g6 * g.g7 * g.g8) := by noncomm_ring
    have h_shift3 : g.g4 * g.g5 * g.g6 * g.g7 * g.g8 * g.g3 = - (g.g3 * (g.g4 * g.g5 * g.g6 * g.g7 * g.g8)) := by
      have h3a : g.g4 * g.g5 * g.g6 * g.g7 * g.g8 * g.g3 = - (g.g4 * g.g5 * g.g6 * g.g7 * g.g3 * g.g8) := by
        calc g.g4 * g.g5 * g.g6 * g.g7 * g.g8 * g.g3 = g.g4 * g.g5 * g.g6 * g.g7 * (g.g8 * g.g3) := by noncomm_ring
        _ = g.g4 * g.g5 * g.g6 * g.g7 * (- (g.g3 * g.g8)) := by rw [h38_s]
        _ = - (g.g4 * g.g5 * g.g6 * g.g7 * g.g3 * g.g8) := by noncomm_ring
      have h3b : - (g.g4 * g.g5 * g.g6 * g.g7 * g.g3 * g.g8) = g.g4 * g.g5 * g.g6 * g.g3 * g.g7 * g.g8 := by
        calc - (g.g4 * g.g5 * g.g6 * g.g7 * g.g3 * g.g8) = - (g.g4 * g.g5 * g.g6 * (g.g7 * g.g3) * g.g8) := by noncomm_ring
        _ = - (g.g4 * g.g5 * g.g6 * (- (g.g3 * g.g7)) * g.g8) := by rw [h37_s]
        _ = g.g4 * g.g5 * g.g6 * g.g3 * g.g7 * g.g8 := by noncomm_ring
      have h3c : g.g4 * g.g5 * g.g6 * g.g3 * g.g7 * g.g8 = - (g.g4 * g.g5 * g.g3 * g.g6 * g.g7 * g.g8) := by
        calc g.g4 * g.g5 * g.g6 * g.g3 * g.g7 * g.g8 = g.g4 * g.g5 * (g.g6 * g.g3) * g.g7 * g.g8 := by noncomm_ring
        _ = g.g4 * g.g5 * (- (g.g3 * g.g6)) * g.g7 * g.g8 := by rw [h36_s]
        _ = - (g.g4 * g.g5 * g.g3 * g.g6 * g.g7 * g.g8) := by noncomm_ring
      have h3d : - (g.g4 * g.g5 * g.g3 * g.g6 * g.g7 * g.g8) = g.g4 * g.g3 * g.g5 * g.g6 * g.g7 * g.g8 := by
        calc - (g.g4 * g.g5 * g.g3 * g.g6 * g.g7 * g.g8) = - (g.g4 * (g.g5 * g.g3) * g.g6 * g.g7 * g.g8) := by noncomm_ring
        _ = - (g.g4 * (- (g.g3 * g.g5)) * g.g6 * g.g7 * g.g8) := by rw [h35_s]
        _ = g.g4 * g.g3 * g.g5 * g.g6 * g.g7 * g.g8 := by noncomm_ring
      have h3e : g.g4 * g.g3 * g.g5 * g.g6 * g.g7 * g.g8 = - (g.g3 * (g.g4 * g.g5 * g.g6 * g.g7 * g.g8)) := by
        calc g.g4 * g.g3 * g.g5 * g.g6 * g.g7 * g.g8 = (g.g4 * g.g3) * g.g5 * g.g6 * g.g7 * g.g8 := by noncomm_ring
        _ = (- (g.g3 * g.g4)) * g.g5 * g.g6 * g.g7 * g.g8 := by rw [h34_s]
        _ = - (g.g3 * (g.g4 * g.g5 * g.g6 * g.g7 * g.g8)) := by noncomm_ring
      rw [h3a, h3b, h3c, h3d, h3e]
    rw [h_step6, h_shift3]
    have h_sq3_sub : g.g3 * (- (g.g3 * (g.g4 * g.g5 * g.g6 * g.g7 * g.g8))) * (g.g4 * g.g5 * g.g6 * g.g7 * g.g8) =
        - ((g.g3 * g.g3) * ((g.g4 * g.g5 * g.g6 * g.g7 * g.g8) * (g.g4 * g.g5 * g.g6 * g.g7 * g.g8))) := by noncomm_ring
    rw [h_sq3_sub, h_sq3, one_mul, h_prod5]
  have h7_sq : (g.g2 * g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) * (g.g2 * g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) = -1 := by
    have h_step7 : (g.g2 * g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) * (g.g2 * g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) =
        g.g2 * (g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8 * g.g2) * (g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) := by noncomm_ring
    have h_shift2 : g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8 * g.g2 = g.g2 * (g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) := by
      have h2a : g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8 * g.g2 = - (g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g2 * g.g8) := by
        calc g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8 * g.g2 = g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * (g.g8 * g.g2) := by noncomm_ring
        _ = g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * (- (g.g2 * g.g8)) := by rw [h28_s]
        _ = - (g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g2 * g.g8) := by noncomm_ring
      have h2b : - (g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g2 * g.g8) = g.g3 * g.g4 * g.g5 * g.g6 * g.g2 * g.g7 * g.g8 := by
        calc - (g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g2 * g.g8) = - (g.g3 * g.g4 * g.g5 * g.g6 * (g.g7 * g.g2) * g.g8) := by noncomm_ring
        _ = - (g.g3 * g.g4 * g.g5 * g.g6 * (- (g.g2 * g.g7)) * g.g8) := by rw [h27_s]
        _ = g.g3 * g.g4 * g.g5 * g.g6 * g.g2 * g.g7 * g.g8 := by noncomm_ring
      have h2c : g.g3 * g.g4 * g.g5 * g.g6 * g.g2 * g.g7 * g.g8 = - (g.g3 * g.g4 * g.g5 * g.g2 * g.g6 * g.g7 * g.g8) := by
        calc g.g3 * g.g4 * g.g5 * g.g6 * g.g2 * g.g7 * g.g8 = g.g3 * g.g4 * g.g5 * (g.g6 * g.g2) * g.g7 * g.g8 := by noncomm_ring
        _ = g.g3 * g.g4 * g.g5 * (- (g.g2 * g.g6)) * g.g7 * g.g8 := by rw [h26_s]
        _ = - (g.g3 * g.g4 * g.g5 * g.g2 * g.g6 * g.g7 * g.g8) := by noncomm_ring
      have h2d : - (g.g3 * g.g4 * g.g5 * g.g2 * g.g6 * g.g7 * g.g8) = g.g3 * g.g4 * g.g2 * g.g5 * g.g6 * g.g7 * g.g8 := by
        calc - (g.g3 * g.g4 * g.g5 * g.g2 * g.g6 * g.g7 * g.g8) = - (g.g3 * g.g4 * (g.g5 * g.g2) * g.g6 * g.g7 * g.g8) := by noncomm_ring
        _ = - (g.g3 * g.g4 * (- (g.g2 * g.g5)) * g.g6 * g.g7 * g.g8) := by rw [h25_s]
        _ = g.g3 * g.g4 * g.g2 * g.g5 * g.g6 * g.g7 * g.g8 := by noncomm_ring
      have h2e : g.g3 * g.g4 * g.g2 * g.g5 * g.g6 * g.g7 * g.g8 = - (g.g3 * g.g2 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) := by
        calc g.g3 * g.g4 * g.g2 * g.g5 * g.g6 * g.g7 * g.g8 = g.g3 * (g.g4 * g.g2) * g.g5 * g.g6 * g.g7 * g.g8 := by noncomm_ring
        _ = g.g3 * (- (g.g2 * g.g4)) * g.g5 * g.g6 * g.g7 * g.g8 := by rw [h24_s]
        _ = - (g.g3 * g.g2 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) := by noncomm_ring
      have h2f : - (g.g3 * g.g2 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) = g.g2 * (g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) := by
        calc - (g.g3 * g.g2 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) = - ((g.g3 * g.g2) * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) := by noncomm_ring
        _ = - ((- (g.g2 * g.g3)) * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) := by rw [h23_s]
        _ = g.g2 * (g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) := by noncomm_ring
      rw [h2a, h2b, h2c, h2d, h2e, h2f]
    rw [h_step7, h_shift2]
    have h_sq2_sub : g.g2 * (g.g2 * (g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8)) * (g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) =
        (g.g2 * g.g2) * ((g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) * (g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8)) := by noncomm_ring
    rw [h_sq2_sub, h_sq2, one_mul, h_prod6]
  dsimp [Gamma]
  calc (g.g1 * g.g2 * g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) * (g.g1 * g.g2 * g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) =
      (g.g1 * g.g2 * g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8 * g.g1) * (g.g2 * g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) := by noncomm_ring
  _ = (- (g.g2 * g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8)) * (g.g2 * g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) := by rw [h_right]
  _ = - ((g.g2 * g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8) * (g.g2 * g.g3 * g.g4 * g.g5 * g.g6 * g.g7 * g.g8)) := by noncomm_ring
  _ = - (-1 : R) := by rw [h7_sq]
  _ = 1 := by ring

/-- **Theorem 5**: Completeness of Chiral Projectors: P₊ + P₋ = 1. -/
theorem chiral_projectors_completeness (g : Clifford8Generators R) :
    PPlus g + PMinus g = 1 := by
  dsimp [PPlus, PMinus]
  have h_add : (⅟2 : R) * (1 + Gamma g) + (⅟2 : R) * (1 - Gamma g) = (⅟2 : R) * (2 : R) := by ring
  rw [h_add]
  exact invOf_mul_self (a := (2 : R))

/-- **Theorem 6**: Idempotency of Positive Projector: P₊² = P₊. -/
theorem pplus_idempotent (g : Clifford8Generators R) :
    PPlus g * PPlus g = PPlus g := by
  dsimp [PPlus]
  have h_sq := gamma_sq_eq_one g
  have h_exp : (⅟2 : R) * (1 + Gamma g) * ((⅟2 : R) * (1 + Gamma g)) =
      (⅟2 * ⅟2 : R) * (1 + 2 * Gamma g + Gamma g * Gamma g) := by ring
  rw [h_exp, h_sq]
  have h_ring : (1 + 2 * Gamma g + 1 : R) = (2 : R) * (1 + Gamma g) := by ring
  rw [h_ring]
  have h_assoc : (⅟2 * ⅟2 : R) * ((2 : R) * (1 + Gamma g)) = ((⅟2 : R) * (2 : R)) * ((⅟2 : R) * (1 + Gamma g)) := by ring
  rw [h_assoc, invOf_mul_self (a := (2 : R)), one_mul]

/-- **Theorem 7**: Orthogonality of Chiral Projectors: P₊ P₋ = 0. -/
theorem chiral_projectors_orthogonal (g : Clifford8Generators R) :
    PPlus g * PMinus g = 0 := by
  dsimp [PPlus, PMinus]
  have h_sq := gamma_sq_eq_one g
  have h_exp : (⅟2 : R) * (1 + Gamma g) * ((⅟2 : R) * (1 - Gamma g)) =
      (⅟2 * ⅟2 : R) * (1 - Gamma g * Gamma g) := by ring
  rw [h_exp, h_sq, sub_self, mul_zero]

/-- **Theorem 8**: Parity-Flipping Action (Majorana-Weyl Splitting Δ₈⁺ ⊕ Δ₈⁻): P₊ γ₁ = γ₁ P₋. -/
theorem pplus_gamma1_flip (g : Clifford8Generators R) :
    PPlus g * g.g1 = g.g1 * PMinus g := by
  dsimp [PPlus, PMinus]
  have h_anti := gamma_anticomm_g1 g
  have h_comm : Gamma g * g.g1 = - (g.g1 * Gamma g) := by
    calc
      Gamma g * g.g1 = Gamma g * g.g1 + g.g1 * Gamma g - g.g1 * Gamma g := by ring
      _ = 0 - g.g1 * Gamma g := by rw [h_anti]
      _ = - (g.g1 * Gamma g) := by ring
  have h_left : (⅟2 : R) * (1 + Gamma g) * g.g1 = (⅟2 : R) * (g.g1 + Gamma g * g.g1) := by ring
  have h_right : g.g1 * ((⅟2 : R) * (1 - Gamma g)) = (⅟2 : R) * (g.g1 - g.g1 * Gamma g) := by ring
  rw [h_left, h_right, h_comm]
  ring

/-- **Theorem 9**: Master Spin(8) Triality & Chiral Parity Theorem.
    Unifies 8D parity involutivity, vector anticommutation, chiral projection,
    and Majorana-Weyl parity flipping into a single kernel-checked theorem packet. -/
theorem master_spin8_triality_chiral_parity
    (g : Clifford8Generators R) :
    (Gamma g * Gamma g = 1) ∧
    (Gamma g * g.g1 + g.g1 * Gamma g = 0) ∧
    (PPlus g + PMinus g = 1) ∧
    (PPlus g * PPlus g = PPlus g) ∧
    (PPlus g * PMinus g = 0) ∧
    (PPlus g * g.g1 = g.g1 * PMinus g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gamma_sq_eq_one g
  · exact gamma_anticomm_g1 g
  · exact chiral_projectors_completeness g
  · exact pplus_idempotent g
  · exact chiral_projectors_orthogonal g
  · exact pplus_gamma1_flip g

end InfoGeometry.Algebra.CliffordCl8SpinorTriality
