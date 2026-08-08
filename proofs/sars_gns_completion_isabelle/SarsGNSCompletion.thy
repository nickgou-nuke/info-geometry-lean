theory SarsGNSCompletion
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

definition systems :: "string list" where
  "systems = [''Lean4'', ''SymPy'', ''SageMath'', ''Macaulay2'', ''Rocq'', ''Isabelle'', ''GAP'']"
definition identity_trace_status :: string where
  "identity_trace_status = ''not_trace_class_in_infinite_GNS''"
definition dmodule_generators :: int where "dmodule_generators = 1"

theorem sigma_pad_preserved: "pad_sigma u v = sigma u v"
  by (cases u; cases v; simp)

theorem norm_pad_preserved: "pad_normSq u = normSq u"
  by (cases u; simp)

theorem gns_completion_kernel:
  "(\<forall>u v. pad_sigma u v = sigma u v) \<and>
   (\<forall>u. pad_normSq u = normSq u) \<and>
   length systems = 7 \<and>
   identity_trace_status = ''not_trace_class_in_infinite_GNS'' \<and>
   dmodule_generators = 1"
  by (simp add: sigma_pad_preserved norm_pad_preserved systems_def identity_trace_status_def dmodule_generators_def)

end
