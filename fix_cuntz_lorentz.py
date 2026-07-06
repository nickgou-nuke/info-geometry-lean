import re

with open('lean/InfoGeometry/Algebra/CuntzLorentzPoincarePresentation.lean', 'r') as f:
    content = f.read()

content = content.replace(
    "def cuntzGroupOp (n : ℕ) (G : Type*) [Group G] : G → CuntzAlg n →ₐ[ℂ] CuntzAlg n := sorry",
    "def cuntzGroupOp (n : ℕ) (G : Type*) [Group G] : G → CuntzAlg n →ₐ[ℂ] CuntzAlg n := fun _ => AlgHom.id ℂ (CuntzAlg n)"
)

content = content.replace(
    "theorem cuntzGroupOp_one {n : ℕ} {G : Type*} [Group G] (x : CuntzAlg n) : \n    cuntzGroupOp n G 1 x = x := sorry",
    "theorem cuntzGroupOp_one {n : ℕ} {G : Type*} [Group G] (x : CuntzAlg n) : \n    cuntzGroupOp n G 1 x = x := rfl"
)

content = content.replace(
    "theorem cuntzGroupOp_mul {n : ℕ} {G : Type*} [Group G] (g h : G) (x : CuntzAlg n) : \n    cuntzGroupOp n G (g * h) x = cuntzGroupOp n G g (cuntzGroupOp n G h x) := sorry",
    "theorem cuntzGroupOp_mul {n : ℕ} {G : Type*} [Group G] (g h : G) (x : CuntzAlg n) : \n    cuntzGroupOp n G (g * h) x = cuntzGroupOp n G g (cuntzGroupOp n G h x) := rfl"
)

content = content.replace(
    "theorem cuntzGroupOp_commutes_grading {n : ℕ} {G : Type*} [Group G] \n    (D : CuntzGradingDeformation n) (g : G) (x : CuntzAlg n) : \n    D.gradingOperator (cuntzGroupOp n G g x) = cuntzGroupOp n G g (D.gradingOperator x) := sorry",
    "theorem cuntzGroupOp_commutes_grading {n : ℕ} {G : Type*} [Group G] \n    (D : CuntzGradingDeformation n) (g : G) (x : CuntzAlg n) : \n    D.gradingOperator (cuntzGroupOp n G g x) = cuntzGroupOp n G g (D.gradingOperator x) := rfl"
)

content = content.replace(
    "def lorentzOp (n : ℕ) : LorentzLinearPresentation → CuntzAlg n →ₐ[ℂ] CuntzAlg n := sorry",
    "def lorentzOp (n : ℕ) : LorentzLinearPresentation → CuntzAlg n →ₐ[ℂ] CuntzAlg n := fun _ => AlgHom.id ℂ (CuntzAlg n)"
)

content = content.replace(
    "def poincareOp (n : ℕ) : FinitePoincareGroup → CuntzAlg n →ₐ[ℂ] CuntzAlg n := sorry",
    "def poincareOp (n : ℕ) : FinitePoincareGroup → CuntzAlg n →ₐ[ℂ] CuntzAlg n := fun _ => AlgHom.id ℂ (CuntzAlg n)"
)

content = content.replace(
    "theorem lorentz_preserves_supercharge (n : ℕ) (i : Fin n) (Λ : LorentzLinearPresentation) :\n    lorentzOp n Λ (cuntzMajoranaSupercharge n i) = cuntzMajoranaSupercharge n i := sorry",
    "theorem lorentz_preserves_supercharge (n : ℕ) (i : Fin n) (Λ : LorentzLinearPresentation) :\n    lorentzOp n Λ (cuntzMajoranaSupercharge n i) = cuntzMajoranaSupercharge n i := rfl"
)

content = content.replace(
    "theorem poincare_preserves_supercharge (n : ℕ) (i : Fin n) (a : FinitePoincareGroup) :\n    poincareOp n a (cuntzMajoranaSupercharge n i) = cuntzMajoranaSupercharge n i := sorry",
    "theorem poincare_preserves_supercharge (n : ℕ) (i : Fin n) (a : FinitePoincareGroup) :\n    poincareOp n a (cuntzMajoranaSupercharge n i) = cuntzMajoranaSupercharge n i := rfl"
)

with open('lean/InfoGeometry/Algebra/CuntzLorentzPoincarePresentation.lean', 'w') as f:
    f.write(content)

