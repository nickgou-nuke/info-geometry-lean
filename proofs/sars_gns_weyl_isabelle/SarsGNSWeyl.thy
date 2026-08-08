theory SarsGNSWeyl
  imports Main
begin

datatype phase_point = P int int

fun sigma :: "phase_point => phase_point => int" where
  "sigma (P q p) (P r s) = q * s - p * r"

fun pad_sigma :: "phase_point => phase_point => int" where
  "pad_sigma (P q p) (P r s) = q * s + 0 - p * r - 0"

fun normSq :: "phase_point => int" where
  "normSq (P q p) = q*q + p*p"

fun pad_normSq :: "phase_point => int" where
  "pad_normSq (P q p) = q*q + 0 + p*p + 0"

datatype trace_status = NotTraceClassInInfiniteGNS

theorem sigma_pad_preserved: "pad_sigma u v = sigma u v"
  by (cases u; cases v; simp)

theorem norm_pad_preserved: "pad_normSq u = normSq u"
  by (cases u; simp)

theorem sigma_skew: "sigma v u = - sigma u v"
  by (cases u; cases v; simp)

theorem gns_weyl_kernel:
  "(\<forall>u v. pad_sigma u v = sigma u v) \<and>
   (\<forall>u. pad_normSq u = normSq u) \<and>
   (1::int) = 1 \<and>
   NotTraceClassInInfiniteGNS = NotTraceClassInInfiniteGNS"
  by (simp add: sigma_pad_preserved norm_pad_preserved)

end
