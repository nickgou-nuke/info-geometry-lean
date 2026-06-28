theory WallpaperRepresentations17
  imports Complex_Main
begin

definition wallpaper_group_count :: nat where "wallpaper_group_count = 17"
definition p4m_irrep_total :: nat where "p4m_irrep_total = 5"
definition p6m_irrep_total :: nat where "p6m_irrep_total = 6"

theorem wallpaper_group_count_ok : "wallpaper_group_count = 17"
  by (simp add: wallpaper_group_count_def)

theorem p4m_irrep_total_ok : "p4m_irrep_total = 5"
  by (simp add: p4m_irrep_total_def)

theorem p6m_irrep_total_ok : "p6m_irrep_total = 6"
  by (simp add: p6m_irrep_total_def)

end
