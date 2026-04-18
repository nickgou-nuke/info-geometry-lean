# LeanTrail Hole Packet Report

- generated_at: `2026-04-16T18:40:08.157501+00:00`
- output_jsonl: `/home/goutev/LEAN4/info-geometry-lean/artifacts/leantrail/hole_packets_smoke.jsonl`
- hole_count: `2709`

## Top Holes

| rank | hole_id | src -> dst | failures | z2 | score | path(exclude_failed) | lock_required | lock_closed |
|---:|---|---|---:|---:|---:|---|---|---|
| 1 | `hole_193ba4193f7e74c18cd4b27d` | `InfoGeometry.LLM.AllTopThermodynamicRouter.allTopWeight_eq_finiteGibbs -> InfoGeometry.Canonical.MoE.ExpertIdx` | 15 | 1 | 96.0 | `True` | `False` | `None` |
| 2 | `hole_293b1da26d72cd98b7231527` | `InfoGeometry.LLM.AllTopThermodynamicRouter.allTopWeight_eq_finiteGibbs -> InfoGeometry.Canonical.MoE.normalizedWeights` | 15 | 1 | 96.0 | `True` | `False` | `None` |
| 3 | `hole_be258266fbe2738763004586` | `InfoGeometry.LLM.KMSSoftmaxBridge.softmaxWeight_eq_kmsWeight -> InfoGeometry.Canonical.MoE.ExpertIdx` | 15 | 1 | 96.0 | `True` | `False` | `None` |
| 4 | `hole_b8994a4873cb011f655925c2` | `InfoGeometry.LLM.AllTopThermodynamicRouter.allTopMixture_eq_normalizedMixture -> InfoGeometry.Canonical.MoE.normalizedMixture` | 9 | 1 | 57.0 | `True` | `False` | `None` |
| 5 | `hole_c88ab6f9c063abec5f28f4c2` | `InfoGeometry.LLM.AllTopThermodynamicRouter.allTopWeight_eq_normalizedWeight -> InfoGeometry.Canonical.MoE.ExpertIdx` | 9 | 1 | 57.0 | `True` | `False` | `None` |
| 6 | `hole_bad508dce9348a77ddc945b8` | `InfoGeometry.LLM.AllTopThermodynamicRouter.allTopWeight_eq_normalizedWeight -> InfoGeometry.Canonical.MoE.normalizedWeights` | 9 | 1 | 57.0 | `True` | `False` | `None` |
| 7 | `hole_7bcfcaffffcc23d8e70235f4` | `InfoGeometry.LLM.AllTopThermodynamicRouter.allTopWeight_sum_one -> InfoGeometry.Canonical.MoE.ExpertIdx` | 9 | 1 | 57.0 | `True` | `False` | `None` |
| 8 | `hole_7f66984960300a476b4dfa2a` | `InfoGeometry.LLM.AllTopThermodynamicTransformer.ReusedAllTopLayer.routedAllTop_eq_normalizedMixture -> InfoGeometry.Canonical.MoE.normalizedMixture` | 9 | 1 | 57.0 | `True` | `False` | `None` |
| 9 | `hole_10ee3c3a3e72f629641fbd48` | `InfoGeometry.LLM.AllTopThermodynamicTransformer.ReusedAllTopLayer.runToken_eq_base_plus_normalizedMixture -> InfoGeometry.Canonical.MoE.normalizedMixture` | 9 | 1 | 57.0 | `True` | `False` | `None` |
| 10 | `hole_bf63bd5e4bd6e9fc457ce124` | `InfoGeometry.LLM.DiscreteRouterBayesStep.bayes_router_update_eq_softmax_shift -> InfoGeometry.Canonical.MoE.ExpertIdx` | 9 | 1 | 57.0 | `True` | `False` | `None` |
| 11 | `hole_100695e7483850d0f9ddb40b` | `InfoGeometry.LLM.DiscreteRouterBayesStep.bayes_router_update_preserves_simplex -> InfoGeometry.Canonical.MoE.ExpertIdx` | 9 | 1 | 57.0 | `True` | `False` | `None` |
| 12 | `hole_2a30f7aacacc039f1beb1c53` | `InfoGeometry.LLM.DiscreteRouterBayesStep.bayes_router_update_preserves_simplex -> InfoGeometry.Canonical.MoE.normalizedWeights` | 9 | 1 | 57.0 | `True` | `False` | `None` |
| 13 | `hole_527a38c7805b7a877493d4f5` | `InfoGeometry.LLM.DiscreteRouterBayesStep.bayes_router_update_preserves_simplex -> InfoGeometry.Canonical.MoE.normalizedWeights_sum_one` | 9 | 1 | 57.0 | `True` | `False` | `None` |
| 14 | `hole_a11278cada94a0549d3b295f` | `InfoGeometry.LLM.HypothesisScaffold70.h70_kms_softmax_normalization -> InfoGeometry.Canonical.MoE.ExpertIdx` | 9 | 1 | 57.0 | `True` | `False` | `None` |
| 15 | `hole_96f20976d9dc9d1288081150` | `InfoGeometry.LLM.HypothesisScaffold70.h70_scale_shape_split -> InfoGeometry.Canonical.MoE.normalizedMixture` | 9 | 1 | 57.0 | `True` | `False` | `None` |
| 16 | `hole_1e68f63c7fdd7a4ebcbb368b` | `InfoGeometry.LLM.KMSSoftmaxBridge.kmsWeight_sum_one -> InfoGeometry.Canonical.MoE.ExpertIdx` | 9 | 1 | 57.0 | `True` | `False` | `None` |
| 17 | `hole_07326fbc3a8f1e554fa2b197` | `InfoGeometry.LLM.KMSSoftmaxBridge.softmaxWeight_eq_exp_routerLogit_div_partition -> InfoGeometry.Canonical.MoE.ExpertIdx` | 9 | 1 | 57.0 | `True` | `False` | `None` |
| 18 | `hole_561b63617f0e63672cd91339` | `InfoGeometry.LLM.KMSSoftmaxBridge.softmaxWeight_eq_exp_routerLogit_div_partition -> InfoGeometry.Canonical.MoE.routerEnergy` | 9 | 1 | 57.0 | `True` | `False` | `None` |
| 19 | `hole_29f71d2dd520a12a7ef1fb3c` | `InfoGeometry.LLM.KMSSoftmaxBridge.softmaxWeight_eq_exp_routerLogit_div_partition -> InfoGeometry.Canonical.MoE.routerPartition` | 9 | 1 | 57.0 | `True` | `False` | `None` |
| 20 | `hole_f0505852455d58305bd1331a` | `InfoGeometry.LLM.KMSSoftmaxBridge.softmaxWeight_eq_exp_routerLogit_div_partition -> InfoGeometry.Canonical.MoE.unnormalizedWeights` | 9 | 1 | 57.0 | `True` | `False` | `None` |
