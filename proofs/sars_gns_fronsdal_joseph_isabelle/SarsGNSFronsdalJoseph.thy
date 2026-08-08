theory SarsGNSFronsdalJoseph
  imports Complex_Main
begin

definition sigma1 :: "rat * rat => rat * rat => rat" where
  "sigma1 u v = fst u * snd v - snd u * fst v"

definition normSq1 :: "rat * rat => rat" where
  "normSq1 u = fst u * fst u + snd u * snd u"

definition fockExponentQuarter :: "rat * rat => rat" where
  "fockExponentQuarter u = - normSq1 u / 4"

lemma sigma1_skew:
  "sigma1 v u = - sigma1 u v"
  by (simp add: sigma1_def; algebra)

lemma normSq1_zero:
  "normSq1 (0,0) = 0"
  by (simp add: normSq1_def)

lemma fockExponent_zero:
  "fockExponentQuarter (0,0) = 0"
  by (simp add: fockExponentQuarter_def normSq1_def)

datatype orbit = Orb rat rat rat rat
fun U00 :: "orbit => rat" where "U00 (Orb p0 p1 q0 q1) = p0*q0"
fun U01 :: "orbit => rat" where "U01 (Orb p0 p1 q0 q1) = p0*q1"
fun U10 :: "orbit => rat" where "U10 (Orb p0 p1 q0 q1) = p1*q0"
fun U11 :: "orbit => rat" where "U11 (Orb p0 p1 q0 q1) = p1*q1"
definition josephMinor :: "orbit => rat" where
  "josephMinor x = U00 x * U11 x - U01 x * U10 x"
definition starProductCorrection :: "rat => rat => rat" where
  "starProductCorrection hbar eta = - hbar*hbar*eta"
definition fronsdalQuadraticRelation :: "rat => rat => rat => bool" where
  "fronsdalQuadraticRelation hbar eta lhs = (lhs = starProductCorrection hbar eta)"

lemma rank_one_joseph_minor_zero:
  "josephMinor x = 0"
  by (cases x; simp add: josephMinor_def; algebra)

lemma fronsdal_relation_refl:
  "fronsdalQuadraticRelation hbar eta (starProductCorrection hbar eta)"
  by (simp add: fronsdalQuadraticRelation_def)

datatype concept = Sars_Weyl_Colimit | Regular_Weyl_GNS_State | Fronsdal_2005 | Singular_Coadjoint_Orbit | Joseph_Ideal_Constraints | Rank_One_Moment_Map
datatype edge = GNS_completion | defines_quantization | cut_out_by | annihilates | embeds_as
fun edgeHolds :: "concept => edge => concept => bool" where
  "edgeHolds Sars_Weyl_Colimit GNS_completion Regular_Weyl_GNS_State = True" |
  "edgeHolds Fronsdal_2005 defines_quantization Joseph_Ideal_Constraints = True" |
  "edgeHolds Singular_Coadjoint_Orbit cut_out_by Joseph_Ideal_Constraints = True" |
  "edgeHolds Joseph_Ideal_Constraints annihilates Regular_Weyl_GNS_State = True" |
  "edgeHolds Rank_One_Moment_Map embeds_as Singular_Coadjoint_Orbit = True" |
  "edgeHolds _ _ _ = False"

theorem gns_fronsdal_joseph_kernel:
  "(\<forall>u v. sigma1 v u = - sigma1 u v) \<and>
   normSq1 (0,0) = 0 \<and>
   fockExponentQuarter (0,0) = 0 \<and>
   (\<forall>x. josephMinor x = 0) \<and>
   (\<forall>hbar eta. fronsdalQuadraticRelation hbar eta (starProductCorrection hbar eta))"
proof (intro conjI allI)
  fix u v
  show "sigma1 v u = - sigma1 u v" by (rule sigma1_skew)
next
  show "normSq1 (0, 0) = 0" by (rule normSq1_zero)
next
  show "fockExponentQuarter (0, 0) = 0" by (rule fockExponent_zero)
next
  fix x
  show "josephMinor x = 0" by (rule rank_one_joseph_minor_zero)
next
  fix hbar eta
  show "fronsdalQuadraticRelation hbar eta (starProductCorrection hbar eta)"
    by (rule fronsdal_relation_refl)
qed

theorem graph_kernel:
  "edgeHolds Sars_Weyl_Colimit GNS_completion Regular_Weyl_GNS_State = True \<and>
   edgeHolds Fronsdal_2005 defines_quantization Joseph_Ideal_Constraints = True \<and>
   edgeHolds Singular_Coadjoint_Orbit cut_out_by Joseph_Ideal_Constraints = True \<and>
   edgeHolds Joseph_Ideal_Constraints annihilates Regular_Weyl_GNS_State = True \<and>
   edgeHolds Rank_One_Moment_Map embeds_as Singular_Coadjoint_Orbit = True"
  by simp

end
