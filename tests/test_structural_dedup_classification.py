from tools.infra.generate_structural_dedup import build_dedup_families


def test_same_module_stationary_family_is_classified_as_compatibility_alias_candidate() -> None:
    atomic_by_id = {
        "atomic:bohm": {
            "sink_names": [
                "InfoGeometry.Canonical.BohmMadelungOperatorialBridge.potentialDatum_constantStateGeneratorField_kSplitReadout_stationary_iff_isPotentialKillingOperator",
                "InfoGeometry.Canonical.BohmMadelungOperatorialBridge.potentialDatum_constantStateGeneratorField_kSplitReadout_stationary_of_equilibriumSeed",
                "InfoGeometry.Canonical.BohmMadelungOperatorialBridge.potentialDatum_constantStateGeneratorField_kSplitReadout_stationary_of_firstVariation_eq_zero_of_probeFaithful",
            ],
            "path_multiplicity": 2,
            "compression_potential": 10.0,
            "source_bundle": ["srcA", "srcB"],
            "sink_modules": ["InfoGeometry.Canonical.BohmMadelungOperatorialBridge"],
            "native_component_representatives": ["RepA"],
            "native_component_ids": ["c1"],
            "native_root_witnesses": ["root1"],
            "motif_signature": "motif:bohm",
        }
    }
    sink_by_name = {
        name: {
            "module": "InfoGeometry.Canonical.BohmMadelungOperatorialBridge",
            "severity": 1,
            "flow_in_degree": 1,
            "category": "theorem",
            "burn_down_rank": 1,
        }
        for name in atomic_by_id["atomic:bohm"]["sink_names"]
    }

    rows = build_dedup_families(atomic_by_id, sink_by_name)
    assert len(rows) == 1
    row = rows[0]
    assert row["relation_subtype"] == "compatibility_alias_candidate"
    assert row["recommended_action"] == "review_as_alias_family"
    assert row["shared_name_stem"].endswith("kSplitReadout_stationary_")


def test_cross_module_family_stays_true_dedup_candidate() -> None:
    atomic_by_id = {
        "atomic:cross": {
            "sink_names": [
                "InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.TopologicalCentralChargePackage.Zop_transport_invariant",
                "InfoGeometry.LLM.SinkhornDefectFlow.operatorInformationNormReadout_le_of_massNormalizedColCounts",
            ],
            "path_multiplicity": 1,
            "compression_potential": 5.0,
            "source_bundle": ["srcX"],
            "sink_modules": [
                "InfoGeometry.Canonical.UnifiedSuperchargeAlgebra",
                "InfoGeometry.LLM.SinkhornDefectFlow",
            ],
            "native_component_representatives": ["RepX"],
            "native_component_ids": ["cx"],
            "native_root_witnesses": ["rootx"],
            "motif_signature": "motif:cross",
        }
    }
    sink_by_name = {
        "InfoGeometry.Canonical.UnifiedSuperchargeAlgebra.TopologicalCentralChargePackage.Zop_transport_invariant": {
            "module": "InfoGeometry.Canonical.UnifiedSuperchargeAlgebra",
            "severity": 1,
            "flow_in_degree": 1,
            "category": "theorem",
            "burn_down_rank": 1,
        },
        "InfoGeometry.LLM.SinkhornDefectFlow.operatorInformationNormReadout_le_of_massNormalizedColCounts": {
            "module": "InfoGeometry.LLM.SinkhornDefectFlow",
            "severity": 1,
            "flow_in_degree": 1,
            "category": "theorem",
            "burn_down_rank": 1,
        },
    }

    rows = build_dedup_families(atomic_by_id, sink_by_name)
    assert len(rows) == 1
    row = rows[0]
    assert row["relation_subtype"] == "true_dedup_candidate"
    assert row["recommended_action"] == "review_for_contraction"
    assert row["shared_name_stem"] == ""
