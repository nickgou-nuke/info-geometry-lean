theory CFTLiouville
  imports Complex_Main
begin

theorem liouville_spectrum_bound:
  fixes c P :: real
  shows "(c - 1) / 24 + P^2 \<ge> (c - 1) / 24"
  by auto

end
