# LeanTrail Hole Packet Report

- generated_at: `2026-04-16T18:43:07.182051+00:00`
- output_jsonl: `/home/goutev/LEAN4/info-geometry-lean/artifacts/leantrail/hole_packets_verify_lake.jsonl`
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
