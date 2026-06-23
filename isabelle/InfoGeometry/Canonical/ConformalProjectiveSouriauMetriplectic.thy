theory ConformalProjectiveSouriauMetriplectic
  imports Complex_Main
begin

locale metriplectic_structure =
  fixes poisson :: "'a => 'a => 'a"
    and metric :: "'a => 'a => 'a"
    and H :: 'a
    and S :: 'a
    and add :: "'a => 'a => 'a" (infixl "+" 65)
    and sub :: "'a => 'a => 'a" (infixl "-" 65)
  assumes poisson_self_zero: "poisson f f = f - f"
      and metric_H_left_zero: "metric H f = f - f"
      and poisson_S_left_zero: "poisson S f = f - f"
begin

definition totalEvolution :: "'a => 'a" where
  "totalEvolution f = poisson f H + metric f S"

end

locale einstein_anomaly_context =
  fixes mul :: "'a => 'a => 'a" (infixl "*" 70)
    and sub :: "'a => 'a => 'a" (infixl "-" 65)
    and star :: "'a => 'a"
    and P_MP :: 'a
    and P_D :: 'a
    and anomaly :: 'a
  assumes anomaly_def: "anomaly = P_MP * P_D - P_D * P_MP"
      and star_mul: "star (f * g) = star g * star f"
      and star_sub: "star (f - g) = star f - star g"
      and star_P_MP: "star P_MP = P_MP"
      and star_P_D: "star P_D = P_D"
begin

end
end
