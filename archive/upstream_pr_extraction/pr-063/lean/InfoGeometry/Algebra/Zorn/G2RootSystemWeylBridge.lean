import InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification

namespace InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge

open InfoGeometry.Algebra.Zorn.G2TwoRootSystem
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.Algebra.Zorn.G2TwoBruhatClassification
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

def cActionPowNat : ℕ → G2Root → G2Root
  | 0, r => r
  | n + 1, r => cAction (cActionPowNat n r)

def cActionPow (k : ZMod 6) (r : G2Root) : G2Root :=
  cActionPowNat k.val r

def weylRootAction (p : WeylG2) (r : G2Root) : G2Root :=
  if p.2 then sAction (cActionPow p.1 r) else cActionPow p.1 r

theorem c_pow_rootAut_conj (k : ZMod 6) (r : G2Root) :
    c ^ k.val * rootAut r * (c ^ k.val)⁻¹ = rootAut (cActionPow k r) := by
  have hnat : ∀ n : ℕ,
      c ^ n * rootAut r * (c ^ n)⁻¹ =
        rootAut (cActionPowNat n r) := by
    intro n
    induction n with
    | zero => simp [cActionPowNat]
    | succ n ih =>
        calc
          c ^ n.succ * rootAut r * (c ^ n.succ)⁻¹ =
              c * (c ^ n * rootAut r * (c ^ n)⁻¹) * c⁻¹ := by
                rw [pow_succ, mul_inv_rev]
                group
          _ = c * rootAut (cActionPowNat n r) * c⁻¹ := by rw [ih]
          _ = rootAut (cAction (cActionPowNat n r)) :=
            c_rootAut_c (cActionPowNat n r)
  exact hnat k.val

theorem weylNF_rootAut_conj (p : WeylG2) (r : G2Root) :
    weylNF p.1 p.2 * rootAut r * (weylNF p.1 p.2)⁻¹ =
      rootAut (weylRootAction p r) := by
  by_cases hp : p.2
  · simp only [weylNF, hp, ↓reduceIte, weylRootAction]
    rw [show (s * c ^ p.1.val) * rootAut r * (s * c ^ p.1.val)⁻¹ =
        s * (c ^ p.1.val * rootAut r * (c ^ p.1.val)⁻¹) * s by
          have hs : s⁻¹ = s := by
            rw [inv_eq_iff_mul_eq_one]
            exact s_sq
          simp [mul_assoc, hs]]
    rw [c_pow_rootAut_conj]
    exact s_rootAut_s (cActionPow p.1 r)
  · simp only [weylNF, hp, Bool.false_eq_true, ↓reduceIte, weylRootAction]
    exact c_pow_rootAut_conj p.1 r

end InfoGeometry.Algebra.Zorn.G2RootSystemWeylBridge
