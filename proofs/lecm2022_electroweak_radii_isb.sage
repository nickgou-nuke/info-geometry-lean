Q=QQ

def sq(x): return x*x
def ckm_sum(vud,vus,vub): return sq(vud)+sq(vus)+sq(vub)
def ckm_defect(vud,vus,vub): return ckm_sum(vud,vus,vub)-1
def corrected_fermi(delta_c): return Q(2)*(1-delta_c)
def ft_corrected(ft,delta_r,delta_c): return ft*(1+delta_r)*(1-delta_c)
def combined(beta,radius): return beta+radius
def exact_pair(x): return (x,-x)
def deviation(beta,radius): return combined(beta,radius)
def permyriad_to_percent(x): return Q(x)/Q(100)
def isovector_scale(nminusz,A): return Q(nminusz)/Q(A)
def coulomb_scale(Z,R): return Q(Z)/Q(R)

assert ckm_sum(Q(3)/5,Q(4)/5,0)==1
assert ckm_defect(Q(3)/5,Q(4)/5,0)==0
assert permyriad_to_percent(10)==Q(1)/10
assert permyriad_to_percent(100)==1
assert corrected_fermi(0)==2
assert corrected_fermi(Q(1)/100)==Q(99)/50
assert ft_corrected(Q(11)/7,0,0)==Q(11)/7
assert combined(*exact_pair(Q(7)/13))==0
assert deviation(*exact_pair(Q(7)/13))==0
assert combined(Q(3)/10,-Q(1)/5)==Q(1)/10
assert deviation(Q(3)/10,-Q(1)/5)==Q(1)/10
assert isovector_scale(2,40)==Q(1)/20
assert coulomb_scale(20,4)==5
edges=['constrains','measures','corrects','probes','cancels_under_exact_isospin']
print({'ckm_sum_sample': ckm_sum(Q(3)/5,Q(4)/5,0), 'ckm_defect_sample': ckm_defect(Q(3)/5,Q(4)/5,0), 'deltaC_percent_range': (Q(1)/10,1), 'corrected_fermi_1pct': corrected_fermi(Q(1)/100), 'exact_isospin_combined': combined(*exact_pair(Q(7)/13)), 'isb_witness': deviation(Q(3)/10,-Q(1)/5), 'isovector_scale': isovector_scale(2,40), 'coulomb_scale': coulomb_scale(20,4), 'edges': len(edges)})
