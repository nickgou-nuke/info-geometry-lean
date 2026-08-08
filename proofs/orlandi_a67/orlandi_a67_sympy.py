#!/usr/bin/env python3
import sympy as sp

tau_As=sp.Rational(7,10)
tau_Se=sp.Rational(13,10)
BE1_As_1=sp.Rational(13,10)
BE1_Se_1=sp.Rational(1,1)
BE1_As_2=sp.Rational(81,10)*sp.Rational(1,10**6)
BE1_Se_2=sp.Rational(17,10)*sp.Rational(1,10**6)

assert sp.simplify(tau_Se/tau_As-sp.Rational(13,7))==0
assert sp.simplify(BE1_As_1/BE1_Se_1-sp.Rational(13,10))==0
assert sp.simplify(BE1_As_2/BE1_Se_2-sp.Rational(81,17))==0
assert sp.simplify(BE1_As_2-BE1_Se_2-sp.Rational(32,5)*sp.Rational(1,10**6))==0
print({
 'tau_ratio_Se_As': tau_Se/tau_As,
 'BE1_725_717_ratio_As_Se': BE1_As_1/BE1_Se_1,
 'BE1_second_7_2_ratio_As_Se': BE1_As_2/BE1_Se_2,
 'BE1_second_delta': BE1_As_2-BE1_Se_2,
})
