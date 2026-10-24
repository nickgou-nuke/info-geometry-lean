import InfoGeometry.Canonical.GrassmannianBundleCyclotomicOrientability

/-!
# Algebraic flows of a reflexive square-zero pair

Associative algebra only. Scalar parameters are central through `Algebra R A`.
No analytic exponential, spectral classification, positivity, Hodge adjoint,
Klein-bottle fundamental group, or exceptional-group identification is asserted.
The four explicit hypotheses describe the pair; no new law-bearing structure is used.
-/
namespace InfoGeometry.Canonical.ReflexiveNilpotentFlows
open GrassmannianBundleCyclotomicOrientability
variable {A : Type*} [Ring A]

def support (d B : A) : A := d * B + B * d
def complement (d B : A) : A := 1 - support d B
def weyl (d B : A) : A := complement d B + (d - B)
def weylInv (d B : A) : A := complement d B - (d - B)

private theorem squareZero_mul {d : A} (h : d*d=0) (x : A) : d*(d*x)=0 := by
  rw [← mul_assoc, h, zero_mul]

private theorem reflexive_mul {d B : A} (h : d*B*d=d) (x : A) :
    d*(B*(d*x))=d*x := by
  simpa only [mul_assoc] using congrArg (fun y : A => y*x) h

private theorem reflexive_assoc {d B : A} (h : d*B*d=d) : d*(B*d)=d := by
  simpa only [mul_assoc] using h

section Pair
variable {d B : A} (hd : d * d = 0) (hB : B * B = 0)
  (hr : d * B * d = d) (hs : B * d * B = B)
include hd hB hr hs

theorem support_sq : support d B * support d B = support d B :=
  (active_support_idempotent hd hB hr hs).eq

theorem complement_annihilates :
    complement d B * d = 0 ∧ d * complement d B = 0 ∧
    complement d B * B = 0 ∧ B * complement d B = 0 := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := active_support_absorbs hd hB hr hs
  simp only [complement, support, sub_mul, mul_sub, one_mul, mul_one,
    h₁, h₂, h₃, h₄, sub_self, and_self]

omit hB hs in
theorem weyl_factorization : (1 + d) * (1 - B) * (1 + d) = weyl d B := by
  unfold weyl complement support
  noncomm_ring [hd, hr]

omit hB hs in
theorem weyl_inverse_factorization :
    (1 - d) * (1 + B) * (1 - d) = weylInv d B := by
  unfold weylInv complement support
  noncomm_ring [hd, hr]

omit hs in
theorem weyl_mul_inverse : weyl d B * weylInv d B = 1 := by
  rw [← weyl_factorization hd hr, ← weyl_inverse_factorization hd hr]
  noncomm_ring [hd, hB];
    simp [squareZero_mul hd, squareZero_mul hB]

omit hs in
theorem inverse_mul_weyl : weylInv d B * weyl d B = 1 := by
  rw [← weyl_factorization hd hr, ← weyl_inverse_factorization hd hr]
  noncomm_ring [hd, hB];
    simp [squareZero_mul hd, squareZero_mul hB]

def weylUnit : Aˣ where
  val := weyl d B
  inv := weylInv d B
  val_inv := weyl_mul_inverse hd hB hr
  inv_val := inverse_mul_weyl hd hB hr

theorem weyl_square : weyl d B * weyl d B = 1 - 2 • support d B := by
  unfold weyl complement support
  simp only [two_nsmul]
  noncomm_ring [hd, hB, hr, hs];
    simp only [squareZero_mul hd, squareZero_mul hB,
      reflexive_assoc hr, reflexive_assoc hs, mul_zero,
      add_zero, zero_add, smul_zero]; abel

theorem weyl_fourth : weyl d B ^ 4 = 1 := by
  have hS := support_sq hd hB hr hs
  calc
    _ = (weyl d B * weyl d B) * (weyl d B * weyl d B) := by noncomm_ring
    _ = (1 - 2 • support d B) * (1 - 2 • support d B) := by rw [weyl_square hd hB hr hs]
    _ = 1 := by simp only [two_nsmul]; noncomm_ring [hS]

omit hB in
theorem weyl_swap_d : weyl d B * d * weylInv d B = -B := by
  unfold weyl weylInv complement support
  noncomm_ring [hd, hr, hs];
    simp only [squareZero_mul hd,
      reflexive_assoc hr, mul_zero,
      zero_add]; abel

omit hd in
theorem weyl_swap_B : weyl d B * B * weylInv d B = -d := by
  unfold weyl weylInv complement support
  noncomm_ring [hB, hr, hs];
    simp only [squareZero_mul hB,
      reflexive_assoc hs, mul_zero,
      zero_add, smul_zero]; abel

theorem weyl_swap_supports :
    weyl d B * (d * B) * weylInv d B = B * d ∧
    weyl d B * (B * d) * weylInv d B = d * B := by
  constructor <;> unfold weyl weylInv complement support <;>
    noncomm_ring [hd, hB, hr, hs] <;>
    simp only [squareZero_mul hd, squareZero_mul hB,
      reflexive_assoc hr, reflexive_assoc hs, mul_zero,
      zero_add, smul_zero] <;> abel
end Pair

/-- Sign normalization of a negative CAR pair gives a reflexive pair.
This is in an associative ring, not an assertion about octonion multiplication. -/
theorem negative_car_reflexive {q c : A}
    (hq : q*q=0) (hc : c*c=0) (hcar : q*c+c*q= -1) :
    q*(-c)*q=q ∧ (-c)*q*(-c)= -c := by
  have hqc := congrArg (fun x : A => x*q) hcar
  have hcq := congrArg (fun x : A => x*c) hcar
  simp only [add_mul,mul_assoc,hq,hc,mul_zero,add_zero,zero_add,neg_mul,one_mul] at hqc hcq
  constructor
  · simpa only [mul_neg,neg_mul,neg_eq_iff_eq_neg,mul_assoc] using hqc
  · simpa only [neg_mul,mul_neg,neg_neg,mul_assoc] using hcq

section Scalars
variable {R : Type*} [CommRing R] [Algebra R A]
def unipotent (s : R) (d : A) : A := 1 + s • d
def diagonal (s t : R) (d B : A) : A :=
  s • (d * B) + t • (B * d) + complement d B

def rotor (c s : R) (d B : A) : A :=
  complement d B + c • support d B + s • (d - B)

theorem unipotent_add {d : A} (hd : d * d = 0) (s t : R) :
    unipotent s d * unipotent t d = unipotent (s + t) d := by
  simp only [unipotent, add_mul, mul_add, one_mul, mul_one, smul_mul_smul,
    hd, smul_zero, add_zero, add_smul]
  abel

theorem unipotent_inverse {d : A} (hd : d * d = 0) (s : R) :
    unipotent s d * unipotent (-s) d = 1 := by
  rw [unipotent_add hd]
  simp [unipotent]

variable {d B : A} (hd : d * d = 0) (hB : B * B = 0)
  (hr : d * B * d = d) (hs : B * d * B = B)
include hd hB hr hs

/-- The complete three-idempotent routing table used by scalar flows. -/
theorem support_table :
    (d*B)*(d*B) = d*B ∧ (B*d)*(B*d) = B*d ∧
    (d*B)*(B*d) = 0 ∧ (B*d)*(d*B) = 0 ∧
    (d*B)*complement d B = 0 ∧ (B*d)*complement d B = 0 ∧
    complement d B*(d*B) = 0 ∧ complement d B*(B*d) = 0 ∧
    complement d B*complement d B = complement d B := by
  obtain ⟨hz₁,hz₂,hz₃,hz₄⟩ := complement_annihilates hd hB hr hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← mul_assoc, hr]
  · rw [← mul_assoc, hs]
  · simp only [mul_assoc, squareZero_mul hB, mul_zero]
  · simp only [mul_assoc, squareZero_mul hd, mul_zero]
  · rw [mul_assoc, hz₄, mul_zero]
  · rw [mul_assoc, hz₂, mul_zero]
  · rw [← mul_assoc, hz₁, zero_mul]
  · rw [← mul_assoc, hz₃, zero_mul]
  · exact InfoGeometry.Core.PeirceDecomposition.complementIdempotent_sq
      (support d B) (support_sq hd hB hr hs)

theorem diagonal_mul (a b c e : R) :
    diagonal a b d B * diagonal c e d B = diagonal (a*c) (b*e) d B := by
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉⟩ := support_table hd hB hr hs
  simp only [diagonal, add_mul, mul_add, smul_mul_assoc,
    mul_smul_comm, h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,h₉, smul_zero, add_zero, zero_add, smul_smul, mul_comm]

theorem diagonal_inverse (a b : R) (hab : a*b=1) :
    diagonal a b d B * diagonal b a d B = 1 := by
  rw [diagonal_mul hd hB hr hs, hab, mul_comm b a, hab]
  simp [diagonal, complement, support]

theorem diagonal_scale_d (a b : R) :
    diagonal a b d B * d * diagonal b a d B = (a*a) • d := by
  obtain ⟨hz₁,hz₂,_,_⟩ := complement_annihilates hd hB hr hs
  have h₁ : (B*d)*d=0 := by rw [mul_assoc,hd,mul_zero]
  have h₂ : d*(d*B)=0 := by rw [← mul_assoc,hd,zero_mul]
  have h₃ : d*(B*d)=d := by rw [← mul_assoc,hr]
  simp only [diagonal, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    hr,h₁,h₂,h₃,hz₁,hz₂,smul_zero,add_zero,zero_add,smul_smul]

theorem diagonal_scale_B (a b : R) :
    diagonal a b d B * B * diagonal b a d B = (b*b) • B := by
  obtain ⟨_,_,hz₁,hz₂⟩ := complement_annihilates hd hB hr hs
  have h₁ : (d*B)*B=0 := by rw [mul_assoc,hB,mul_zero]
  have h₂ : B*(B*d)=0 := by rw [← mul_assoc,hB,zero_mul]
  have h₃ : B*(d*B)=B := by rw [← mul_assoc,hs]
  simp only [diagonal, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    hs,h₁,h₂,h₃,hz₁,hz₂,smul_zero,add_zero,zero_add,smul_smul]

theorem diagonal_scale_unipotent (a b s : R) (hab : a*b=1) :
    diagonal a b d B * unipotent s d * diagonal b a d B =
      unipotent (a*a*s) d := by
  simp only [unipotent, mul_add, mul_one, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [diagonal_inverse hd hB hr hs a b hab, diagonal_scale_d hd hB hr hs,
    smul_smul, mul_comm s (a*a)]

theorem weyl_swap_unipotent (s : R) :
    weyl d B * unipotent s d * weylInv d B = unipotent (-s) B := by
  simp only [unipotent, mul_add, mul_one, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [weyl_mul_inverse hd hB hr, weyl_swap_d hd hr hs]
  simp only [smul_neg, neg_smul]
/-- Weyl conjugation exchanges the diagonal parameters. -/
theorem weyl_diagonal (a b : R) :
    weyl d B * diagonal a b d B * weylInv d B = diagonal b a d B := by
  obtain ⟨hp,hm⟩ := weyl_swap_supports hd hB hr hs
  have hc : weyl d B * complement d B * weylInv d B = complement d B := by
    unfold complement support
    simp only [mul_sub, mul_one, sub_mul, mul_add, add_mul]
    rw [weyl_mul_inverse hd hB hr, hp, hm]
    abel
  simp only [diagonal, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  rw [hp, hm, hc]
  abel

/-- Algebraic circle multiplication, with no analytic or compactness claim. -/
theorem rotor_mul (c s e t : R) :
    rotor c s d B * rotor e t d B = rotor (c*e-s*t) (c*t+s*e) d B := by
  let S := support d B
  let H := complement d B
  let J := d-B
  have hSS : S*S=S := support_sq hd hB hr hs
  have hHH : H*H=H := (support_table hd hB hr hs).2.2.2.2.2.2.2.2
  have hHS : H*S=0 := by dsimp [H,complement]; rw [sub_mul,one_mul,hSS,sub_self]
  have hSH : S*H=0 := by dsimp [H,complement]; rw [mul_sub,mul_one,hSS,sub_self]
  obtain ⟨hdL,hdR,hBL,hBR⟩ := active_support_absorbs hd hB hr hs
  have hSJ : S*J=J := by dsimp [S,J,support]; rw [mul_sub,hdL,hBL]
  have hJS : J*S=J := by dsimp [S,J,support]; rw [sub_mul,hdR,hBR]
  have hHJ : H*J=0 := by dsimp [H,complement]; rw [sub_mul,one_mul,hSJ,sub_self]
  have hJH : J*H=0 := by dsimp [H,complement]; rw [mul_sub,mul_one,hJS,sub_self]
  have hJJ : J*J= -S := by dsimp [J,S,support]; noncomm_ring [hd,hB]
  change (H+c • S+s • J)*(H+e • S+t • J)=H+(c*e-s*t) • S+(c*t+s*e) • J
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,hSS,hHH,hHS,hSH,
    hSJ,hJS,hHJ,hJH,hJJ,smul_zero,zero_add,add_zero,smul_neg,smul_smul,
    sub_smul,add_smul,smul_add]
  rw [mul_comm e c, mul_comm t s, mul_comm t c, mul_comm e s]
  abel

theorem rotor_inverse (c s : R) (hcircle : c*c+s*s=1) :
    rotor c s d B * rotor c (-s) d B = 1 := by
  rw [rotor_mul hd hB hr hs]
  have hc : c*c-s*(-s)=1 := by simpa using hcircle
  have hz : c*(-s)+s*c=0 := by ring
  rw [hc,hz]
  simp [rotor,complement]

end Scalars
end InfoGeometry.Canonical.ReflexiveNilpotentFlows
