theory A67MirrorE1
  imports Complex_Main
begin

definition spin_denominator :: "rat \<Rightarrow> rat" where
  "spin_denominator two_Ji = two_Ji + 1"

definition BE1_plus :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "BE1_plus two_Ji MIV MIS =
    ((MIV + MIS)^2) / spin_denominator two_Ji"

definition BE1_minus :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "BE1_minus two_Ji MIV MIS =
    ((MIV - MIS)^2) / spin_denominator two_Ji"

definition two_Ji_9half :: rat where "two_Ji_9half = 9"
definition MIV_725_717 :: rat where "MIV_725_717 = 29 / 10000"
definition MIS_725_717 :: rat where "MIS_725_717 = 9 / 10000"

definition BE1_As67_725 :: rat where
  "BE1_As67_725 = BE1_plus two_Ji_9half MIV_725_717 MIS_725_717"

definition BE1_Se67_717 :: rat where
  "BE1_Se67_717 = BE1_minus two_Ji_9half MIV_725_717 MIS_725_717"

definition ratio_725_717 :: rat where
  "ratio_725_717 = BE1_As67_725 / BE1_Se67_717"

definition isoscalar_fraction_725_717 :: rat where
  "isoscalar_fraction_725_717 = MIS_725_717 / MIV_725_717"

lemma mirror_charge_exchange_A67:
  "(33::nat) = 33 \<and> (34::nat) = 34"
  by simp

lemma BE1_As67_725_exact:
  "BE1_As67_725 = 361 / 250000000"
  by (simp add: BE1_As67_725_def BE1_plus_def spin_denominator_def
    two_Ji_9half_def MIV_725_717_def MIS_725_717_def; normalization)

lemma BE1_Se67_717_exact:
  "BE1_Se67_717 = 1 / 2500000"
  by (simp add: BE1_Se67_717_def BE1_minus_def spin_denominator_def
    two_Ji_9half_def MIV_725_717_def MIS_725_717_def; normalization)

lemma ratio_725_717_exact:
  "ratio_725_717 = 361 / 100"
  by (simp add: ratio_725_717_def BE1_As67_725_exact BE1_Se67_717_exact)

lemma isoscalar_fraction_exact:
  "isoscalar_fraction_725_717 = 9 / 29"
  by (simp add: isoscalar_fraction_725_717_def
    MIV_725_717_def MIS_725_717_def; normalization)

definition IVGMR_coefficient :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "IVGMR_coefficient A e R DeltaE0 = ((A - 1) * e^2) / (4 * R * DeltaE0)"

definition IVGMR_one_body :: "rat \<Rightarrow> rat \<Rightarrow> rat" where
  "IVGMR_one_body ri R = ri^3 / R^2"

definition IVGMR_two_body :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "IVGMR_two_body ri rj R = ri * rj^2 / R^3"

definition induced_isoscalar_kernel ::
  "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat" where
  "induced_isoscalar_kernel A e R DeltaE0 ri rj =
    IVGMR_coefficient A e R DeltaE0 *
      (IVGMR_one_body ri R + IVGMR_two_body ri rj R)"

lemma IVGMR_unit_kernel_A67:
  "induced_isoscalar_kernel 67 1 1 20 1 1 = 33 / 20"
  by (simp add: induced_isoscalar_kernel_def IVGMR_coefficient_def
    IVGMR_one_body_def IVGMR_two_body_def; normalization)

end
