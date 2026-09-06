import Mathlib
namespace Test
noncomputable section
variable {R : Type*} [Ring R] [Algebra ℝ R]
def pp (T:R) := (1/2:ℝ) • (T*T+T)
private lemma p4 {T:R} (h:T*T*T=T) : T*T*T*T=T*T := by simpa [mul_assoc] using congrArg (fun x:R => x*T) h
private lemma ps {T:R} (h:T*T*T=T) : (T*T+T)*(T*T+T) = (2:ℝ) • (T*T+T) := by
  calc
    _ = T*T*T*T + T*T*T + T*T*T + T*T := by noncomm_ring
    _ = T*T + T + T + T*T := by rw [p4 h, h]
    _ = (2:ℝ) • (T*T+T) := by rw [two_smul]; abel
example {T:R} (h:T*T*T=T) : pp T * pp T = pp T := by
  unfold pp
  rw [smul_mul_smul, ps h, smul_smul]
  norm_num
end
end Test
