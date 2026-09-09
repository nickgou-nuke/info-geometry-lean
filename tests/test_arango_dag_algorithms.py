import unittest
from unittest.mock import MagicMock
from tools.infra.arango_dag_algorithms import community_docs, QuotientGraph

class TestArangoDagAlgorithms(unittest.TestCase):
    def test_community_docs_logic(self):
        # Create a simple dummy graph for clustering
        # Node 0, 1, 2 are a cluster; 3, 4, 5 are another cluster
        nodes = [{"_id": f"id_{i}", "_key": f"key_{i}"} for i in range(6)]
        edge_multiplicity = {
            (0, 1): 1, (1, 2): 1, (2, 0): 1,  # Cluster 1
            (3, 4): 1, (4, 5): 1, (5, 3): 1,  # Cluster 2
            (2, 3): 1,  # Bridge edge
        }
        
        graph = QuotientGraph(
            nodes=nodes,
            node_index={f"id_{i}": i for i in range(6)},
            ids=[f"id_{i}" for i in range(6)],
            keys=[f"key_{i}" for i in range(6)],
            forward=[[] for _ in range(6)], # Not used by community_docs
            preds=[[] for _ in range(6)],   # Not used by community_docs
            edge_rows=[],
            edge_multiplicity=edge_multiplicity,
            edge_witness_counts={},
            layer_counts=[{} for _ in range(6)],
            dominant_layer=[None] * 6,
            dominant_depth=[None] * 6
        )
        
        comm_docs, edge_docs = community_docs(graph, run_id="test_run")
        
        # We expect at least 2 communities
        self.assertGreaterEqual(len(comm_docs), 2)
        
        # Verify edge_docs link nodes to communities
        # Every node should be in exactly one community
        node_to_comm = {}
        for edge in edge_docs:
            src = edge["_from"].split("/")[-1]
            dst = edge["_to"].split("/")[-1]
            self.assertNotIn(src, node_to_comm)
            node_to_comm[src] = dst
        
        self.assertEqual(len(node_to_comm), 6)
        
        # Verify community members field matches edge_docs
        for comm in comm_docs:
            comm_key = comm["_key"]
            members = comm["members"]
            for member in members:
                self.assertEqual(node_to_comm[member], comm_key)

    def test_kuratowski_closure_axioms(self):
        from tools.infra.arango_dag_algorithms import (
            downward_closure,
            verify_kuratowski_axioms,
        )
        # Construct a DAG poset: 0 -> 1 -> 2, 0 -> 3 -> 4, 2 -> 5, 4 -> 5
        preds = [
            [],        # 0 has no preds
            [0],       # 1 <- 0
            [1],       # 2 <- 1
            [0],       # 3 <- 0
            [3],       # 4 <- 3
            [2, 4],    # 5 <- 2, 4
        ]
        # Test downward closure of 5: should be {0, 1, 2, 3, 4, 5}
        cl_5 = downward_closure(preds, [5])
        self.assertEqual(cl_5, {0, 1, 2, 3, 4, 5})

        # Test downward closure of 2: should be {0, 1, 2}
        cl_2 = downward_closure(preds, [2])
        self.assertEqual(cl_2, {0, 1, 2})

        # Test Kuratowski axioms on various subsets
        set_a = {1, 3}
        set_b = {2}
        result = verify_kuratowski_axioms(preds, set_a, set_b)
        self.assertTrue(result["empty_preserved"], "Kuratowski Axiom 1 (empty set) failed")
        self.assertTrue(result["extensivity"], "Kuratowski Axiom 2 (extensivity) failed")
        self.assertTrue(result["union_distributivity"], "Kuratowski Axiom 3 (union distributivity) failed")
        self.assertTrue(result["idempotence"], "Kuratowski Axiom 4 (idempotence) failed")
        self.assertTrue(result["all_axioms_hold"])

    def test_aleksandrov_duality(self):
        from tools.infra.arango_dag_algorithms import verify_aleksandrov_duality
        forward = [
            [1, 3],    # 0 -> 1, 3
            [2],       # 1 -> 2
            [5],       # 2 -> 5
            [4],       # 3 -> 4
            [5],       # 4 -> 5
            [],        # 5
        ]
        preds = [
            [],
            [0],
            [1],
            [0],
            [3],
            [2, 4],
        ]
        all_nodes = {0, 1, 2, 3, 4, 5}
        set_s = {2, 4}
        result = verify_aleksandrov_duality(forward, preds, all_nodes, set_s)
        self.assertTrue(result["compl_lower_is_upper"], "Complement of lower set must be upper set")
        self.assertTrue(result["compl_upper_is_lower"], "Complement of upper set must be lower set")
        self.assertTrue(result["aleksandrov_duality_holds"])

    def test_causal_corridor_and_reflexive_collapse(self):
        from tools.infra.arango_dag_algorithms import causal_corridor
        forward = [
            [1],       # 0 -> 1
            [2],       # 1 -> 2
            [],        # 2
            [],        # 3 (disconnected)
        ]
        preds = [
            [],
            [0],
            [1],
            [],
        ]
        # Reflexive collapse: [a, a] = {a}
        for node in range(4):
            self.assertEqual(causal_corridor(forward, preds, node, node), {node})

        # Path corridor [0, 2] = {0, 1, 2}
        self.assertEqual(causal_corridor(forward, preds, 0, 2), {0, 1, 2})

        # No causal path from 2 to 0 -> empty corridor
        self.assertEqual(causal_corridor(forward, preds, 2, 0), set())

        # No causal path between 0 and 3 -> empty corridor
        self.assertEqual(causal_corridor(forward, preds, 0, 3), set())

    def test_hodge_2_complex_coboundary_exactness(self):
        from tools.infra.arango_dag_algorithms import bounded_two_complex_docs, rank_mod2
        # Build a triangular face (0 -> 1 -> 2 and 0 -> 2)
        nodes = [{"_id": f"id_{i}", "_key": f"key_{i}"} for i in range(3)]
        graph = QuotientGraph(
            nodes=nodes,
            node_index={f"id_{i}": i for i in range(3)},
            ids=[f"id_{i}" for i in range(3)],
            keys=[f"key_{i}" for i in range(3)],
            forward=[[1, 2], [2], []],
            preds=[[], [0], [0, 1]],
            edge_rows=[],
            edge_multiplicity={(0, 1): 1, (1, 2): 1, (0, 2): 1},
            edge_witness_counts={},
            layer_counts=[{} for _ in range(3)],
            dominant_layer=[None] * 3,
            dominant_depth=[0, 1, 2],
        )
        docs = bounded_two_complex_docs(
            graph,
            run_id="test_hodge",
            seed=0,
            radius=2,
            max_nodes=10,
            max_edges=10,
            cell_limit=10,
        )
        summary = docs[0]
        self.assertTrue(summary["computed"])
        self.assertEqual(summary["triangular_faces"], 1)
        self.assertTrue(summary["boundary_squared_zero_mod2"], "d1 o d0 = 0 (or d o d = 0) must hold")


if __name__ == "__main__":
    unittest.main()
