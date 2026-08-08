theory CasimirIsospinHamiltonian
  imports Complex_Main
begin

definition massCasimir :: "rat => rat" where "massCasimir m2 = -m2"
definition spinCasimir :: "rat => rat" where "spinCasimir J = J * (J + 1)"
definition isospinCasimir :: "rat => rat" where "isospinCasimir T = T * (T + 1)"
definition seniorityCasimir :: "rat => rat" where "seniorityCasimir v = v * (v + 1)"
definition casimirStiffness :: "rat => rat" where "casimirStiffness C = -C"
definition imme :: "rat => rat => rat => rat => rat" where
  "imme a b c Tz = a + b*Tz + c*Tz*Tz"
definition pairHamiltonian :: "rat => rat => rat" where
  "pairHamiltonian k0 k1 = k0 + k1"
definition casimirHamiltonian :: "rat => rat => rat => rat => rat => rat => rat => rat => rat" where
  "casimirHamiltonian alpha beta gamma delta m2 J T v =
    alpha*massCasimir m2 + beta*spinCasimir J + gamma*isospinCasimir T + delta*seniorityCasimir v"
definition generalizedHamiltonian ::
  "rat => rat => rat => rat => rat => rat => rat => rat => rat => rat => rat => rat => rat => rat => rat => rat" where
  "generalizedHamiltonian alpha beta gamma delta a b c k0 k1 spring m2 J T v Tz =
    casimirHamiltonian alpha beta gamma delta m2 J T v + imme a b c Tz + pairHamiltonian k0 k1 + spring"

theorem casimir_isospin_hamiltonian_kernel:
  "isospinCasimir 1 = 2 \<and>
   isospinCasimir (1/2) = 3/4 \<and>
   (\<forall> m2. casimirStiffness (massCasimir m2) = m2) \<and>
   (\<forall> a b c t. imme a b c t - imme a b c (-t) = 2*b*t) \<and>
   (\<forall> a b c t. imme a b c t + imme a b c (-t) = 2*a + 2*c*t*t) \<and>
   (\<forall> alpha beta gamma delta a b c k0 k1 spring m2 J T v t.
      generalizedHamiltonian alpha beta gamma delta a b c k0 k1 spring m2 J T v t -
      generalizedHamiltonian alpha beta gamma delta a b c k0 k1 spring m2 J T v (-t) = 2*b*t) \<and>
   casimirStiffness (massCasimir 94) = 94"
  by (simp add: massCasimir_def spinCasimir_def isospinCasimir_def seniorityCasimir_def
      casimirStiffness_def imme_def pairHamiltonian_def casimirHamiltonian_def
      generalizedHamiltonian_def algebra_simps)

end
