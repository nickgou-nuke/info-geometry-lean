import InfoGeometry.Algebra.ZornMatrix

namespace InfoGeometry.Canonical.ZornPotentialEmbedding

open InfoGeometry.Algebra

noncomputable section

structure Potential4 where
  phi : ℝ
  a1 : ℝ
  a2 : ℝ
  a3 : ℝ

def toZorn (p : Potential4) : ZornMatrix ℝ where
  a := p.phi
  v := ![p.a1, p.a2, p.a3]
  w := ![p.a1, -p.a2, p.a3]
  b := -p.phi

theorem toZorn_trace_zero (p : Potential4) :
    ZornMatrix.zornTrace (toZorn p) = 0 := by
  simp [toZorn, ZornMatrix.zornTrace]

theorem toZorn_norm (p : Potential4) :
    ZornMatrix.zornNorm (toZorn p) =
      -p.phi ^ 2 - p.a1 ^ 2 + p.a2 ^ 2 - p.a3 ^ 2 := by
  simp [toZorn, ZornMatrix.zornNorm, Vec3.dot]
  ring

theorem toZorn_reflection (p : Potential4) :
    (toZorn { phi := -p.phi, a1 := p.a1, a2 := p.a2, a3 := p.a3 }).zornTrace = 0 := by
  exact toZorn_trace_zero _

end
end InfoGeometry.Canonical.ZornPotentialEmbedding
