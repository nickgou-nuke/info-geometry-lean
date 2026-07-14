import InfoGeometry.Singular.MoorePenrose

namespace MoorePenroseAdjoint

section MP
variable {R : Type*} [Ring R] [StarRing R]

abbrev IsMoorePenroseInverse (A B : R) : Prop :=
  InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse A B

namespace IsMoorePenroseInverse

variable {A B : R}

theorem mk
    (h1 : A * B * A = A)
    (h2 : B * A * B = B)
    (h3 : (A * B)† = A * B)
    (h4 : (B * A)† = B * A) :
    IsMoorePenroseInverse A B :=
  InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse.mk h1 h2 h3 h4

theorem aba_eq_a (h : IsMoorePenroseInverse A B) : A * B * A = A :=
  InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse.aba_eq_a h

theorem bab_eq_b (h : IsMoorePenroseInverse A B) : B * A * B = B :=
  InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse.bab_eq_b h

theorem ab_adj_eq (h : IsMoorePenroseInverse A B) : (A * B)† = A * B :=
  InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse.ab_adj_eq h

theorem ba_adj_eq (h : IsMoorePenroseInverse A B) : (B * A)† = B * A :=
  InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse.ba_adj_eq h

theorem eq1 (h : IsMoorePenroseInverse A B) : A * B * A = A :=
  InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse.eq1 h

theorem eq2 (h : IsMoorePenroseInverse A B) : B * A * B = B :=
  InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse.eq2 h

theorem eq3 (h : IsMoorePenroseInverse A B) : (A * B)† = A * B :=
  InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse.eq3 h

theorem eq4 (h : IsMoorePenroseInverse A B) : (B * A)† = B * A :=
  InfoGeometry.Singular.MoorePenrose.IsMoorePenroseInverse.eq4 h

end IsMoorePenroseInverse

lemma adjoint_mul_triple (X Y Z : R) : (X * Y * Z)† = Z† * Y† * X† :=
  InfoGeometry.Singular.MoorePenrose.adjoint_mul_triple X Y Z

theorem MoorePenrose_unique {A B C : R}
    (hB : IsMoorePenroseInverse A B)
    (hC : IsMoorePenroseInverse A C) : B = C :=
  InfoGeometry.Singular.MoorePenrose.MoorePenrose_unique hB hC

def MP_Projector (A B : R) (_h : IsMoorePenroseInverse A B) : R :=
  InfoGeometry.Singular.MoorePenrose.MP_Projector A B _h

lemma MP_Projector_idempotent {A B : R} (h : IsMoorePenroseInverse A B) :
    (MP_Projector A B h) * (MP_Projector A B h) = MP_Projector A B h :=
  InfoGeometry.Singular.MoorePenrose.MP_Projector_idempotent h

lemma MP_Projector_self_adjoint {A B : R} (h : IsMoorePenroseInverse A B) :
    (MP_Projector A B h)† = MP_Projector A B h :=
  InfoGeometry.Singular.MoorePenrose.MP_Projector_self_adjoint h

end MP

end MoorePenroseAdjoint
