tauAs:=7/10;; tauSe:=13/10;;
BE1As1:=13/10;; BE1Se1:=1;;
BE1As2:=(81/10)/1000000;; BE1Se2:=(17/10)/1000000;;
if tauSe/tauAs<>13/7 then Error("tau"); fi;
if BE1As1/BE1Se1<>13/10 then Error("be1a"); fi;
if BE1As2/BE1Se2<>81/17 then Error("be1b"); fi;
if BE1As2-BE1Se2<>(32/5)/1000000 then Error("delta"); fi;
Display("OK");
