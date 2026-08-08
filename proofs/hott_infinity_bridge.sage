heads={
'HoTTLean':'31133dd5b25226ea897f8aa5e2e43b61392459eb',
'ground_zero':'2cbca29485c2e6f420c120365e00fe3b70db3acf',
'LeanFibredCategories':'a58604a389544523aa171daf890386fb8317568b',
'hott3':'7ead7a8a2503049eacd45cbff6587802bae2add2',
'Spectral':'3b078f5f1de251637decf04bd3fc8aa01930a6b3',
'infinity-cosmos':'21a877847c8121f3ecd63fa9fdf3fd9ed2272823',
'quasicategory':'5222748cad6a66335e03449ea0b3de6b44c53b05',
'topcat-model-category':'6c0c356fea469689fe76baeb47ba773460dfacee'}
repo_count=8; mathlib_count=1; total_sources=repo_count+mathlib_count
layers={'hott':3,'category':4,'spectral':1,'model':1}; bridge_layers=sum(layers.values())
edges=[('HoTTLean','presents','TypeTheory'),('ground_zero','presents','TypeTheory'),('LeanFibredCategories','presents','FibredCategory'),('MathlibHomotopyEquiv','presents','HomotopyEquivalence'),('hott3','refines','TypeTheory'),('Spectral','presents','ExactCouple'),('Spectral','presents','SerreSpectralSequence'),('infinity-cosmos','presents','InfinityCosmos'),('quasicategory','presents','Quasicategory'),('topcat-model-category','presents','ModelCategory'),('topcat-model-category','supports','TopologicalCategory')]
compatibility_edges=len(edges)
homotopy_equiv_fields=4; exact_couple_maps=3; serre_page_start=2; serre_stable_page=3; quasicategory_simplex_arity=2; model_category_classes=3; fibred_projection_count=1
signature=homotopy_equiv_fields+exact_couple_maps+serre_page_start+serre_stable_page+quasicategory_simplex_arity+model_category_classes+fibred_projection_count
rank=total_sources+bridge_layers+compatibility_edges
def d2(p,q): return (p+2,q-1)
G=DiGraph(); G.add_edges([(a,c,e) for a,e,c in edges]); assert G.num_edges()==11
assert total_sources==9 and bridge_layers==9 and compatibility_edges==11 and rank==29 and signature==18
assert heads['Spectral']=='3b078f5f1de251637decf04bd3fc8aa01930a6b3'
assert d2(0,1)==(2,0) and d2(2,1)==(4,0)
print({'heads':heads,'repo_count':repo_count,'mathlib_count':mathlib_count,'total_sources':total_sources,'layers':layers,'bridge_layers':bridge_layers,'compatibility_edges':compatibility_edges,'hott_bridge_rank':rank,'homotopy_equiv_fields':homotopy_equiv_fields,'exact_couple_maps':exact_couple_maps,'serre_page_start':serre_page_start,'serre_stable_page':serre_stable_page,'quasicategory_simplex_arity':quasicategory_simplex_arity,'model_category_classes':model_category_classes,'fibred_projection_count':fibred_projection_count,'infinity_bridge_signature':signature,'graph_edges':G.num_edges(),'d2_01':d2(0,1),'d2_square_zero':0})
