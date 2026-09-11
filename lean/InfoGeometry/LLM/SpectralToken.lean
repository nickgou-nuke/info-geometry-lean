import InfoGeometry.Meta.Architecture
import InfoGeometry.Algebra.FiniteSpinAlgebra

namespace InfoGeometry.LLM.SpectralToken

/--
Minimal spectral token carrier with a primal and dual lane.
This is a structural container, not yet a physical/spinorial claim.
-/
structure SpectralToken (V : Type _) where
  primal : V
  dual : V

namespace SpectralToken

variable {V : Type _}

/-- Swap primal and dual lanes. -/
def swap (t : SpectralToken V) : SpectralToken V :=
  ⟨t.dual, t.primal⟩

@[simp] theorem swap_primal (t : SpectralToken V) :
    (swap t).primal = t.dual := rfl

@[simp] theorem swap_dual (t : SpectralToken V) :
    (swap t).dual = t.primal := rfl

@[simp, rep_depth transport]
theorem swap_involutive (t : SpectralToken V) :
    swap (swap t) = t := by
  cases t
  rfl

end SpectralToken

/-- Token encoder into the spectral (primal/dual) carrier. -/
structure TokenEncoder (Tok V : Type _) where
  encode : Tok → SpectralToken V

namespace TokenEncoder

variable {Tok V : Type _}

def primalMap (E : TokenEncoder Tok V) : Tok → V :=
  fun t => (E.encode t).primal

def dualMap (E : TokenEncoder Tok V) : Tok → V :=
  fun t => (E.encode t).dual

@[simp] theorem primalMap_def (E : TokenEncoder Tok V) (t : Tok) :
    E.primalMap t = (E.encode t).primal := rfl

@[simp] theorem dualMap_def (E : TokenEncoder Tok V) (t : Tok) :
    E.dualMap t = (E.encode t).dual := rfl

end TokenEncoder

/-- Involutive grading action on a value carrier. -/
structure SpectralGrading (V : Type _) where
  grade : V → V
  involutive : ∀ x : V, grade (grade x) = x

namespace SpectralGrading

variable {V : Type _}

/-- Grading action lifted to the spectral token lanes. -/
def actToken (G : SpectralGrading V) (t : SpectralToken V) : SpectralToken V :=
  ⟨G.grade t.primal, G.grade t.dual⟩

@[simp] theorem actToken_primal (G : SpectralGrading V) (t : SpectralToken V) :
    (G.actToken t).primal = G.grade t.primal := rfl

@[simp] theorem actToken_dual (G : SpectralGrading V) (t : SpectralToken V) :
    (G.actToken t).dual = G.grade t.dual := rfl

@[simp, rep_depth transport]
theorem actToken_involutive (G : SpectralGrading V) (t : SpectralToken V) :
    G.actToken (G.actToken t) = t := by
  cases t with
  | mk p d =>
      simp [actToken, G.involutive p, G.involutive d]

end SpectralGrading

/--
Minimal Q/K/V triality carrier:
`pair` packages the tri-linear interface down to a binary map from Q and K
into the value lane.
-/
structure QKVTrialityCarrier (Q K Vout : Type _) where
  pair : Q → K → Vout

namespace QKVTrialityCarrier

variable {Q K Vout : Type _}

def evaluate (T : QKVTrialityCarrier Q K Vout) (q : Q) (k : K) : Vout :=
  T.pair q k

@[simp] theorem evaluate_def (T : QKVTrialityCarrier Q K Vout) (q : Q) (k : K) :
    T.evaluate q k = T.pair q k := rfl

end QKVTrialityCarrier

/--
Kramers-style bridge between query and key lanes:
the two maps are mutual inverses.
-/
structure KramersQKBridge (Q K : Type _) where
  toKey : Q → K
  toQuery : K → Q
  left_inv : ∀ q, toQuery (toKey q) = q
  right_inv : ∀ k, toKey (toQuery k) = k

namespace KramersQKBridge

variable {Q K : Type _}

@[simp] theorem toQuery_toKey (B : KramersQKBridge Q K) (q : Q) :
    B.toQuery (B.toKey q) = q :=
  B.left_inv q

@[simp] theorem toKey_toQuery (B : KramersQKBridge Q K) (k : K) :
    B.toKey (B.toQuery k) = k :=
  B.right_inv k

end KramersQKBridge

end InfoGeometry.LLM.SpectralToken
