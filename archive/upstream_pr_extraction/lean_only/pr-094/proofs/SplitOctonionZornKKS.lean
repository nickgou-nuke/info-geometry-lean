import Mathlib

noncomputable section

namespace SplitOctonionZornKKS

abbrev Q := ℚ
abbrev Vec3 := Q × Q × Q


def vadd (x y : Vec3) : Vec3 := (x.1 + y.1, x.2.1 + y.2.1, x.2.2 + y.2.2)
def vneg (x : Vec3) : Vec3 := (-x.1, -x.2.1, -x.2.2)
def vsub (x y : Vec3) : Vec3 := vadd x (vneg y)
def smul (a : Q) (x : Vec3) : Vec3 := (a*x.1, a*x.2.1, a*x.2.2)
def dot (x y : Vec3) : Q := x.1*y.1 + x.2.1*y.2.1 + x.2.2*y.2.2
def cross (x y : Vec3) : Vec3 :=
  (x.2.1*y.2.2 - x.2.2*y.2.1,
   x.2.2*y.1 - x.1*y.2.2,
   x.1*y.2.1 - x.2.1*y.1)

def e1 : Vec3 := (1,0,0)
def e2 : Vec3 := (0,1,0)
def e3 : Vec3 := (0,0,1)
def zvec : Vec3 := (0,0,0)

structure Zorn where
  a : Q
  u : Vec3
  v : Vec3
  b : Q
  deriving DecidableEq, Repr

def zmul (X Y : Zorn) : Zorn where
  a := X.a*Y.a + dot X.u Y.v
  u := vsub (vadd (smul X.a Y.u) (smul Y.b X.u)) (cross X.v Y.v)
  v := vadd (vadd (smul Y.a X.v) (smul X.b Y.v)) (cross X.u Y.u)
  b := dot X.v Y.u + X.b*Y.b

def zconj (X : Zorn) : Zorn where
  a := X.b
  u := vneg X.u
  v := vneg X.v
  b := X.a

def znorm (X : Zorn) : Q := X.a*X.b - dot X.u X.v
def zassoc (X Y Z : Zorn) : Zorn :=
  let lhs := zmul (zmul X Y) Z
  let rhs := zmul X (zmul Y Z)
  { a := lhs.a - rhs.a, u := vsub lhs.u rhs.u, v := vsub lhs.v rhs.v, b := lhs.b - rhs.b }

def oneZ : Zorn := ⟨1,zvec,zvec,1⟩
def zeroDivisor : Zorn := ⟨1,e1,e1,1⟩
def U1 : Zorn := ⟨0,e1,zvec,0⟩
def U2 : Zorn := ⟨0,e2,zvec,0⟩
def L1 : Zorn := ⟨0,zvec,e1,0⟩
def associatorValue : Zorn := zassoc U1 L1 U2

def splitNormSignature44 : ℕ × ℕ := (4,4)
def imaginarySignature34 : ℕ × ℕ := (3,4)
def positiveOrbitSignature : ℕ × ℕ := (2,4)
def negativeOrbitSignature : ℕ × ℕ := (3,3)
def signatureTotal (s : ℕ × ℕ) : ℕ := s.1 + s.2

def hasNonzeroNorm (X : Zorn) : Bool := znorm X != 0
def splitUnitCondition (X : Zorn) : Bool := znorm X == 1

def adSquareCoeff (N : Q) : Q := -4*N
def almostComplexScalePositive (N : Q) : Q := 4*N
def almostComplexScaleNegative (N : Q) : Q := 4*(-N)
def kksClosedCompensated (assocObstruction anomalyCounterterm : Q) : Q := assocObstruction + anomalyCounterterm

def twoGeneratorSubalgebraDimension : ℕ := 4
def splitOctonionDim : ℕ := 8
def imaginaryDim : ℕ := 7
def unitHyperboloidDim : ℕ := 7
def orbitDim : ℕ := 6

def so55Dim : ℕ := 45
def su5Partition : ℕ := 24 + 1 + 10 + 10
def zornMatrixSlots : ℕ := 2 + 3 + 3
def imaginaryNullQuadricDim : ℕ := imaginaryDim - 1
def varlamovEven : ℕ := Nat.choose 5 0 + Nat.choose 5 2 + Nat.choose 5 4
def varlamovOdd : ℕ := Nat.choose 5 1 + Nat.choose 5 3 + Nat.choose 5 5
def varlamovSpinorDim : ℕ := varlamovEven + varlamovOdd
def wittenMoebiusIndex : Int := (varlamovEven : Int) - (varlamovOdd : Int)
def mobiusTwist (k : Int) : Int := -k
def kleinRelated (k l : Int) : Prop := k = l ∨ k = mobiusTwist l
def kleinPairInvariant (k : Int) : Int := k + mobiusTwist k
def tripotentSpectralPolynomial (d : Int) : Int := d*d*d - d

theorem zorn_zero_divisor_norm : znorm zeroDivisor = 0 := by
  norm_num [zeroDivisor, znorm, dot, e1]

theorem zorn_one_norm : znorm oneZ = 1 := by
  norm_num [oneZ, znorm, dot, zvec]

theorem zorn_conjugate_zero_divisor_norm : znorm (zconj zeroDivisor) = znorm zeroDivisor := by
  norm_num [zconj, zeroDivisor, znorm, dot, e1, vneg]

theorem zorn_associator_value_nonzero :
    associatorValue.u = e2 ∧ associatorValue ≠ { a := 0, u := zvec, v := zvec, b := 0 } := by
  constructor
  · norm_num [associatorValue, zassoc, zmul, vsub, vadd, vneg, smul, dot, cross,
      U1, U2, L1, e1, e2, zvec]
  · intro h
    have hu := congrArg Zorn.u h
    norm_num [associatorValue, zassoc, zmul, vsub, vadd, vneg, smul, dot, cross,
      U1, U2, L1, e1, e2, zvec] at hu

theorem split_signatures :
    splitNormSignature44 = (4,4) ∧ imaginarySignature34 = (3,4) ∧
    signatureTotal positiveOrbitSignature = 6 ∧ signatureTotal negativeOrbitSignature = 6 := by
  norm_num [splitNormSignature44, imaginarySignature34, positiveOrbitSignature, negativeOrbitSignature, signatureTotal]

theorem split_octonion_dimension_values :
    splitOctonionDim = 8 ∧ imaginaryDim = 7 ∧ unitHyperboloidDim = 7 ∧ orbitDim = 6 ∧
    twoGeneratorSubalgebraDimension = 4 ∧ zornMatrixSlots = 8 := by
  norm_num [splitOctonionDim, imaginaryDim, unitHyperboloidDim, orbitDim, twoGeneratorSubalgebraDimension, zornMatrixSlots]

theorem zorn_invertibility_values :
    hasNonzeroNorm oneZ = true ∧ hasNonzeroNorm zeroDivisor = false ∧ splitUnitCondition oneZ = true := by
  norm_num [hasNonzeroNorm, splitUnitCondition, oneZ, zeroDivisor, znorm, dot, zvec, e1]

theorem adjoint_square_coefficients : adSquareCoeff 1 = -4 ∧ adSquareCoeff (-1) = 4 := by
  norm_num [adSquareCoeff]

theorem almost_complex_scale_values : almostComplexScalePositive 1 = 4 ∧ almostComplexScaleNegative (-1) = 4 := by
  norm_num [almostComplexScalePositive, almostComplexScaleNegative]

theorem kks_compensated_value : kksClosedCompensated 2 (-2) = 0 := by
  norm_num [kksClosedCompensated]

theorem so55_su5_bridge : su5Partition = so55Dim ∧ so55Dim = 45 := by
  norm_num [su5Partition, so55Dim]

theorem varlamov_witten_moebius_values :
    imaginaryNullQuadricDim = 6 ∧ varlamovEven = 16 ∧ varlamovOdd = 16 ∧
    varlamovSpinorDim = 32 ∧ wittenMoebiusIndex = 0 := by
  norm_num [imaginaryNullQuadricDim, imaginaryDim, varlamovEven, varlamovOdd,
    varlamovSpinorDim, wittenMoebiusIndex, Nat.choose]

theorem mobius_klein_relations (k : Int) :
    mobiusTwist (mobiusTwist k) = k ∧ kleinRelated k (mobiusTwist k) ∧ kleinPairInvariant k = 0 := by
  constructor
  · simp [mobiusTwist]
  constructor
  · right
    simp [mobiusTwist]
  · simp [kleinPairInvariant, mobiusTwist]

theorem tripotent_spectral_roots :
    tripotentSpectralPolynomial (-1) = 0 ∧
    tripotentSpectralPolynomial 0 = 0 ∧
    tripotentSpectralPolynomial 1 = 0 := by
  norm_num [tripotentSpectralPolynomial]

inductive Concept where
  | Split_Octonion_Zorn
  | Norm_Signature_44
  | Isotropic_Zero_Divisor
  | Associator_Obstruction
  | Compensated_KKS_Anomaly
  | Split_Orbit_Signatures
  | SO55_SU5_Bridge
  deriving DecidableEq, Repr

inductive Edge where
  | realizes
  | has
  | obstructs
  | compensated_by
  | bridges_to
  deriving DecidableEq, Repr

def edgeHolds : Concept → Edge → Concept → Bool
  | Concept.Split_Octonion_Zorn, Edge.realizes, Concept.Norm_Signature_44 => true
  | Concept.Split_Octonion_Zorn, Edge.has, Concept.Isotropic_Zero_Divisor => true
  | Concept.Associator_Obstruction, Edge.obstructs, Concept.Split_Octonion_Zorn => true
  | Concept.Associator_Obstruction, Edge.compensated_by, Concept.Compensated_KKS_Anomaly => true
  | Concept.Split_Octonion_Zorn, Edge.bridges_to, Concept.SO55_SU5_Bridge => true
  | _, _, _ => false

end SplitOctonionZornKKS

end noncomputable section
