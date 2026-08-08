theory YanevaPd94PnSymmetry
  imports Complex_Main
begin

definition ZPd94 :: nat where "ZPd94 = 46"
definition NPd94 :: nat where "NPd94 = 48"
definition APd94 :: nat where "APd94 = 94"
definition protonHoles :: nat where "protonHoles = 50 - ZPd94"
definition neutronHoles :: nat where "neutronHoles = 50 - NPd94"
definition totalHoles :: nat where "totalHoles = protonHoles + neutronHoles"
definition Tz :: "rat => rat => rat" where "Tz N Z = (N - Z) / 2"
definition doubledTz :: "int => int => int" where "doubledTz N Z = N - Z"
definition inIsospinMultiplet :: "nat => int => bool" where
  "inIsospinMultiplet T twoTz = (\<bar>twoTz\<bar> <= int (2*T))"
definition g92Degeneracy :: nat where "g92Degeneracy = 10"
definition singleJConfigCount :: nat where "singleJConfigCount = 9450"
definition isospinIrrepDim :: "nat => nat" where "isospinIrrepDim T = 2*T + 1"
definition yrast8B :: rat where "yrast8B = 205"
definition yrast8BLower :: rat where "yrast8BLower = 205 - 25"
definition yrast8BUpper :: rat where "yrast8BUpper = 205 + 34"
definition gdsNeutronCharge :: rat where "gdsNeutronCharge = 84 / 100"
definition yrast8Bgds :: rat where "yrast8Bgds = 192"
definition g9full8 :: rat where "g9full8 = 144"
definition g9t0_8 :: rat where "g9t0_8 = 191"
definition g9t1_8 :: rat where "g9t1_8 = 11"

theorem yaneva_pd94_pn_symmetry_kernel:
  "ZPd94 + NPd94 = APd94 \<and>
   NPd94 = ZPd94 + 2 \<and>
   Tz 48 46 = 1 \<and>
   protonHoles = 4 \<and> neutronHoles = 2 \<and> totalHoles = 6 \<and>
   doubledTz 48 46 = 2 \<and> doubledTz 47 47 = 0 \<and>
   inIsospinMultiplet 1 (doubledTz 48 46) \<and>
   inIsospinMultiplet 1 (doubledTz 47 47) \<and>
   g92Degeneracy = 10 \<and> singleJConfigCount = 9450 \<and>
   isospinIrrepDim 0 = 1 \<and> isospinIrrepDim 1 = 3 \<and>
   8 = 6 + 2 \<and> 6 = 4 + 2 \<and> 14 = 12 + 2 \<and>
   yrast8B = 205 \<and> yrast8BLower = 180 \<and> yrast8BUpper = 239 \<and>
   yrast8B < 250 \<and> gdsNeutronCharge = 21 / 25 \<and>
   yrast8BLower <= yrast8Bgds \<and> yrast8Bgds <= yrast8BUpper \<and>
   abs (g9full8 - g9t0_8) < abs (g9full8 - g9t1_8)"
  by (simp add: ZPd94_def NPd94_def APd94_def protonHoles_def neutronHoles_def
      totalHoles_def Tz_def doubledTz_def inIsospinMultiplet_def g92Degeneracy_def
      singleJConfigCount_def isospinIrrepDim_def yrast8B_def yrast8BLower_def
      yrast8BUpper_def gdsNeutronCharge_def yrast8Bgds_def g9full8_def g9t0_8_def
      g9t1_8_def)

end
