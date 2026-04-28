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

if __name__ == "__main__":
    unittest.main()
