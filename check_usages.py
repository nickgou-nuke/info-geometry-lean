import re

target_defs = [
    'EntropicSubadditivityStatement',
    'HomologicalPercolationDualityStatement',
    'ScalarFrequencyNotLinguisticInvariant',
    'AlmgrenCycleSpaceStatement',
    'GromovWaistStatement',
    'ScalarCurvatureWidthBoundStatement',
    'QuantumStrongSubadditivityStatement',
    'HomologicalProbabilityPrinciple',
    'HomologicalProbabilityMasterConjecture',
    'GWBundleIsomorphismStatement',
    'AffineClosureOwnerStatement',
    'KleinGromovPipelineStatement',
    'WeylLawStatement',
    'ModularFlowTriviality',
    'TypeIIIRequiresNontracialState',
    'CartanSplitStatement',
    'CliffordProbabilityHasClassicalShadow',
    'InfiniteCliffordTypeIII',
    'ScalarProbabilityAsLastStep'
]

content = open('lean/InfoGeometry/Probability/HomologicalProbability.lean').read()
for d in target_defs:
    matches = re.findall(r'\b' + d + r'\b', content)
    if len(matches) > 1:
        print(f"{d} is used {len(matches)} times.")
    else:
        print(f"{d} is used {len(matches)} time (only definition).")
