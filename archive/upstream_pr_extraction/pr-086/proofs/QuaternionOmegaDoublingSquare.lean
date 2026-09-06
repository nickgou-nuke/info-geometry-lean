import proofs.HestenesHyperbolicDoubling

/-!
# The quartic quaternion-doubling square

The two independent data are the sign `ε` of the doubling unit and the
crossing law.  The carrier is always `H × H`; the products are kept as
separate functions so that associative and alternative branches cannot be
confused.
-/

noncomputable section
namespace QuaternionOmegaDoublingSquare

open QuaternionAlgebra

abbrev H := Quaternion ℝ
abbrev Carrier := H × H

def omega : Carrier := (0, 1)

def centralMul (ε : ℝ) (x y : Carrier) : Carrier :=
  (x.1 * y.1 + ε • (x.2 * y.2),
   x.1 * y.2 + x.2 * y.1)

def twistedMul (ε : ℝ) (x y : Carrier) : Carrier :=
  (x.1 * y.1 + ε • (star y.2 * x.2),
   y.2 * x.1 + x.2 * star y.1)

@[simp] theorem central_omega_sq (ε : ℝ) :
    centralMul ε omega omega = ((ε : H), 0) := by
  ext <;> simp [centralMul, omega]

@[simp] theorem twisted_omega_sq (ε : ℝ) :
    twistedMul ε omega omega = ((ε : H), 0) := by
  ext <;> simp [twistedMul, omega]

@[simp] theorem central_omega_cross (ε : ℝ) (a : H) :
    centralMul ε omega (a, 0) = centralMul ε (a, 0) omega := by
  ext <;> simp [centralMul, omega]

@[simp] theorem twisted_omega_cross (ε : ℝ) (a : H) :
    twistedMul ε omega (a, 0) = twistedMul ε (star a, 0) omega := by
  ext <;> simp [twistedMul, omega]

@[simp] theorem central_omega_quartic (ε : ℝ) (hε : ε ^ 2 = 1) :
    centralMul ε (centralMul ε omega omega)
      (centralMul ε omega omega) = (1, 0) := by
  ext <;> simp [centralMul, omega]
  simpa [pow_two] using hε

@[simp] theorem twisted_omega_quartic (ε : ℝ) (hε : ε ^ 2 = 1) :
    twistedMul ε (twistedMul ε omega omega)
      (twistedMul ε omega omega) = (1, 0) := by
  ext <;> simp [twistedMul, omega]
  simpa [pow_two] using hε

abbrev elliptic : ℝ := -1
abbrev hyperbolic : ℝ := 1

theorem elliptic_sq : elliptic ^ 2 = 1 := by norm_num [elliptic]
theorem hyperbolic_sq : hyperbolic ^ 2 = 1 := by norm_num [hyperbolic]

abbrev Biquaternions := Carrier
abbrev SplitBiquaternions := Carrier
abbrev Octonions := Carrier
abbrev SplitOctonions := Carrier

def biquaternionMul := centralMul elliptic
def splitBiquaternionMul := centralMul hyperbolic
def octonionMul := twistedMul elliptic
def splitOctonionMul := twistedMul hyperbolic

end QuaternionOmegaDoublingSquare
end noncomputable section
