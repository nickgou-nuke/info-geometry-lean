theory EInfinityParadoxes
  imports Complex_Main
begin

theorem Q_factorization:
  fixes x :: real
  shows "x^5 + 5 * x^2 - 2 = (x^2 + x - 1) * (x^3 - x^2 + 2 * x + 2)"
  by algebra

theorem E_infinity_energy_relation:
  fixes phi :: real
  assumes phi_sq_add_phi: "phi^2 + phi = 1"
  shows "phi^5 + 5 * phi^2 = 2"
proof -
  have H_factor: "(phi^2 + phi - 1) * (phi^3 - phi^2 + 2 * phi + 2) = phi^5 + 5 * phi^2 - 2"
    by algebra
  have H_zero: "phi^2 + phi - 1 = 0"
    using assms by simp
  then have "(phi^2 + phi - 1) * (phi^3 - phi^2 + 2 * phi + 2) = 0"
    by simp
  then have "phi^5 + 5 * phi^2 - 2 = 0"
    using H_factor by simp
  then show ?thesis by simp
qed

theorem E_infinity_energy_conservation:
  fixes phi :: real
  assumes phi_sq_add_phi: "phi^2 + phi = 1"
  shows "(phi^5 / 2) + (5 * phi^2 / 2) = 1"
proof -
  have "phi^5 + 5 * phi^2 = 2"
    by (rule E_infinity_energy_relation [OF assms])
  then show ?thesis by simp
qed

theorem d_P_add_d_W:
  fixes phi :: real
  assumes phi_sq_add_phi: "phi^2 + phi = 1"
  shows "phi + phi^2 = 1"
  using assms by (simp add: algebra_simps)

theorem cantorian_dimension_relation:
  fixes phi UpperPhi :: real
  assumes phi_sq_add_phi: "phi^2 + phi = 1"
    and UpperPhi_def: "UpperPhi = 1 + phi"
  shows "UpperPhi^3 = 4 + phi^3"
  using assms by algebra

theorem castro_fine_structure_relation:
  fixes phi :: real
  assumes phi_sq_add_phi: "phi^2 + phi = 1"
  shows "1 + (1 + phi)^2 + (1 + phi)^4 + (1 + phi)^8 +
         (1 + phi)^3 + (1 + phi)^9 = 100 + 61 * phi"
  using assms by algebra

end
