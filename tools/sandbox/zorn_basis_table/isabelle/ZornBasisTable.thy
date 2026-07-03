theory ZornBasisTable imports Main begin
record cell = r :: int s :: int x1 :: int x2 :: int x3 :: int y1 :: int y2 :: int y3 :: int
definition mulZ :: "cell => cell => cell" where
"mulZ X Y = (|
  r = r X*r Y + x1 X*y1 Y + x2 X*y2 Y + x3 X*y3 Y,
  s = y1 X*x1 Y + y2 X*x2 Y + y3 X*x3 Y + s X*s Y,
  x1 = r X*x1 Y + s Y*x1 X - (y2 X*y3 Y - y3 X*y2 Y),
  x2 = r X*x2 Y + s Y*x2 X - (y3 X*y1 Y - y1 X*y3 Y),
  x3 = r X*x3 Y + s Y*x3 X - (y1 X*y2 Y - y2 X*y1 Y),
  y1 = r Y*y1 X + s X*y1 Y + (x2 X*x3 Y - x3 X*x2 Y),
  y2 = r Y*y2 X + s X*y2 Y + (x3 X*x1 Y - x1 X*x3 Y),
  y3 = r Y*y3 X + s X*y3 Y + (x1 X*x2 Y - x2 X*x1 Y) |)"
definition negZ :: "cell => cell" where "negZ X = (|r=-r X,s=-s X,x1=-x1 X,x2=-x2 X,x3=-x3 X,y1=-y1 X,y2=-y2 X,y3=-y3 X|)"
definition Z0 :: cell where "Z0=(|r=0,s=0,x1=0,x2=0,x3=0,y1=0,y2=0,y3=0|)"
definition E11 :: cell where "E11=(|r=1,s=0,x1=0,x2=0,x3=0,y1=0,y2=0,y3=0|)"
definition E22 :: cell where "E22=(|r=0,s=1,x1=0,x2=0,x3=0,y1=0,y2=0,y3=0|)"
definition U1 :: cell where "U1=(|r=0,s=0,x1=1,x2=0,x3=0,y1=0,y2=0,y3=0|)"
definition U2 :: cell where "U2=(|r=0,s=0,x1=0,x2=1,x3=0,y1=0,y2=0,y3=0|)"
definition U3 :: cell where "U3=(|r=0,s=0,x1=0,x2=0,x3=1,y1=0,y2=0,y3=0|)"
definition V1 :: cell where "V1=(|r=0,s=0,x1=0,x2=0,x3=0,y1=1,y2=0,y3=0|)"
definition V2 :: cell where "V2=(|r=0,s=0,x1=0,x2=0,x3=0,y1=0,y2=1,y3=0|)"
definition V3 :: cell where "V3=(|r=0,s=0,x1=0,x2=0,x3=0,y1=0,y2=0,y3=1|)"
lemma T_E11_E11: "mulZ E11 E11 = E11" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_E11_E22: "mulZ E11 E22 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_E11_U1: "mulZ E11 U1 = U1" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_E11_U2: "mulZ E11 U2 = U2" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_E11_U3: "mulZ E11 U3 = U3" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_E11_V1: "mulZ E11 V1 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_E11_V2: "mulZ E11 V2 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_E11_V3: "mulZ E11 V3 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_E22_E11: "mulZ E22 E11 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_E22_E22: "mulZ E22 E22 = E22" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_E22_U1: "mulZ E22 U1 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_E22_U2: "mulZ E22 U2 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_E22_U3: "mulZ E22 U3 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_E22_V1: "mulZ E22 V1 = V1" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_E22_V2: "mulZ E22 V2 = V2" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_E22_V3: "mulZ E22 V3 = V3" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_U1_E11: "mulZ U1 E11 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_U1_E22: "mulZ U1 E22 = U1" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_U1_U1: "mulZ U1 U1 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_U1_U2: "mulZ U1 U2 = V3" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_U1_U3: "mulZ U1 U3 = negZ V2" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_U1_V1: "mulZ U1 V1 = E11" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_U1_V2: "mulZ U1 V2 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_U1_V3: "mulZ U1 V3 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_U2_E11: "mulZ U2 E11 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_U2_E22: "mulZ U2 E22 = U2" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_U2_U1: "mulZ U2 U1 = negZ V3" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_U2_U2: "mulZ U2 U2 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_U2_U3: "mulZ U2 U3 = V1" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_U2_V1: "mulZ U2 V1 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_U2_V2: "mulZ U2 V2 = E11" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_U2_V3: "mulZ U2 V3 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_U3_E11: "mulZ U3 E11 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_U3_E22: "mulZ U3 E22 = U3" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_U3_U1: "mulZ U3 U1 = V2" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_U3_U2: "mulZ U3 U2 = negZ V1" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_U3_U3: "mulZ U3 U3 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_U3_V1: "mulZ U3 V1 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_U3_V2: "mulZ U3 V2 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_U3_V3: "mulZ U3 V3 = E11" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_V1_E11: "mulZ V1 E11 = V1" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_V1_E22: "mulZ V1 E22 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_V1_U1: "mulZ V1 U1 = E22" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_V1_U2: "mulZ V1 U2 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_V1_U3: "mulZ V1 U3 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_V1_V1: "mulZ V1 V1 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_V1_V2: "mulZ V1 V2 = negZ U3" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_V1_V3: "mulZ V1 V3 = U2" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_V2_E11: "mulZ V2 E11 = V2" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_V2_E22: "mulZ V2 E22 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_V2_U1: "mulZ V2 U1 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_V2_U2: "mulZ V2 U2 = E22" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_V2_U3: "mulZ V2 U3 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_V2_V1: "mulZ V2 V1 = U3" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_V2_V2: "mulZ V2 V2 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_V2_V3: "mulZ V2 V3 = negZ U1" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_V3_E11: "mulZ V3 E11 = V3" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_V3_E22: "mulZ V3 E22 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_V3_U1: "mulZ V3 U1 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_V3_U2: "mulZ V3 U2 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_V3_U3: "mulZ V3 U3 = E22" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_V3_V1: "mulZ V3 V1 = negZ U2" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_V3_V2: "mulZ V3 V2 = U1" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
lemma T_V3_V3: "mulZ V3 V3 = Z0" by (simp add: mulZ_def Z0_def E11_def E22_def U1_def U2_def U3_def V1_def V2_def V3_def negZ_def)
end
