theory HolyTrinity
  imports Main Real
begin

(* Null Cone Confinement *)
definition ZornDet :: "real ⇒ real ⇒ real ⇒ real ⇒ real" where
  "ZornDet a b x y = a * b - x * y"

definition confined :: "real ⇒ bool" where
  "confined det ⟷ det = 0"

lemma quark_is_confined:
  shows "confined (ZornDet 0 0 x 0)"
  unfolding confined_def ZornDet_def by simp

(* Hestenes Geometric Algebra Types (Extracted) *)
record HestenesSpinor = 
  hs_scalar :: real
  hs_bivector :: real

datatype ZornMatrix = Zorn 
  (scalar_a: real) 
  (vector_x: "real list") 
  (vector_y: "real list") 
  (scalar_b: real)

(* Instanton to Baryon Mapping *)
type_synonym Instanton = "HestenesSpinor"
type_synonym Baryon = "ZornMatrix"

definition instanton_charge :: "Instanton ⇒ real" where
  "instanton_charge I = hs_scalar I"

definition baryon_number :: "Baryon ⇒ real" where
  "baryon_number B = scalar_a B"

definition atiyah_manton_map :: "Instanton ⇒ Baryon" where
  "atiyah_manton_map I = Zorn (hs_scalar I) [] [] (hs_bivector I)"

lemma instanton_baryon_equivalence:
  shows "baryon_number (atiyah_manton_map I) = instanton_charge I"
  unfolding baryon_number_def atiyah_manton_map_def instanton_charge_def by simp

end
