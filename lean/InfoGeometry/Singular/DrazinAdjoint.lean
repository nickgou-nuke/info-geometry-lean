import InfoGeometry.Singular.Drazin

namespace DrazinAdjoint

section Drazin

variable {R : Type*} [Ring R]

abbrev IsDrazinInverse (A D : R) (k : ℕ) : Prop :=
  InfoGeometry.Singular.Drazin.IsDrazinInverse A D k

namespace IsDrazinInverse

variable {A D : R} {k : ℕ}

theorem mk
    (h1 : D * A * D = D)
    (h2 : A * D = D * A)
    (h3 : A^k = A^(k + 1) * D) :
    IsDrazinInverse A D k :=
  InfoGeometry.Singular.Drazin.IsDrazinInverse.mk h1 h2 h3

theorem dad_eq_d (h : IsDrazinInverse A D k) : D * A * D = D :=
  InfoGeometry.Singular.Drazin.IsDrazinInverse.dad_eq_d h

theorem comm (h : IsDrazinInverse A D k) : A * D = D * A :=
  InfoGeometry.Singular.Drazin.IsDrazinInverse.comm h

theorem pow_eq_pow_succ_mul (h : IsDrazinInverse A D k) : A^k = A^(k + 1) * D :=
  InfoGeometry.Singular.Drazin.IsDrazinInverse.pow_eq_pow_succ_mul h

theorem eq1 (h : IsDrazinInverse A D k) : D * A * D = D :=
  InfoGeometry.Singular.Drazin.IsDrazinInverse.eq1 h

theorem eq2 (h : IsDrazinInverse A D k) : A * D = D * A :=
  InfoGeometry.Singular.Drazin.IsDrazinInverse.eq2 h

theorem eq3 (h : IsDrazinInverse A D k) : A^k = A^(k + 1) * D :=
  InfoGeometry.Singular.Drazin.IsDrazinInverse.eq3 h

end IsDrazinInverse

def Drazin_Projector (A D : R) (k : ℕ) (_h : IsDrazinInverse A D k) : R :=
  InfoGeometry.Singular.Drazin.Drazin_Projector A D k _h

lemma Drazin_Projector_idempotent {A D : R} {k : ℕ} (h : IsDrazinInverse A D k) :
    (Drazin_Projector A D k h) * (Drazin_Projector A D k h) = Drazin_Projector A D k h :=
  InfoGeometry.Singular.Drazin.Drazin_Projector_idempotent h

end Drazin

section DrazinLinear

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem exists_drazinInverse_global (A : Module.End K V) :
    ∃ (k : ℕ) (D : Module.End K V), IsDrazinInverse A D k :=
  InfoGeometry.Singular.Drazin.exists_drazinInverse_global A

end DrazinLinear

section Anomaly

variable {R : Type*} [Ring R] [StarRing R]

def ChiralAnomaly (A B D : R) (k : ℕ)
    (hMP : InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse A B)
    (hD : IsDrazinInverse A D k) : R :=
  InfoGeometry.Singular.Drazin.ChiralAnomaly A B D k hMP hD

def IsNormal (A : R) : Prop :=
  InfoGeometry.Singular.Drazin.IsNormal A

end Anomaly

end DrazinAdjoint
