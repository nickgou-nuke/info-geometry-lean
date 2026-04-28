import unittest
import networkx as nx
from tools.infra.generate_theory_spire_viz import compute_layout

class TestGenerateTheorySpireViz(unittest.TestCase):
    def test_compute_layout_layer_alignment(self):
        # Create a graph where nodes are explicitly assigned to layers
        G = nx.DiGraph()
        # Layer 0 (Count)
        G.add_node("n0", dominant_rep_depth=0)
        G.add_node("n1", dominant_rep_depth=0)
        # Layer 5 (Closure)
        G.add_node("n2", dominant_rep_depth=5)
        # Unlabeled (treated as depth 6)
        G.add_node("n3", dominant_rep_depth=None)
        
        pos = compute_layout(G)
        
        # Verify Y coordinates
        self.assertEqual(pos["n0"][1], 0)
        self.assertEqual(pos["n1"][1], 0)
        self.assertEqual(pos["n2"][1], -500)
        self.assertEqual(pos["n3"][1], -600)
        
        # Verify X coordinates (n0 and n1 should be distributed)
        self.assertNotEqual(pos["n0"][0], pos["n1"][0])
        
    def test_compute_layout_empty_graph(self):
        G = nx.DiGraph()
        pos = compute_layout(G)
        self.assertEqual(len(pos), 0)

if __name__ == "__main__":
    unittest.main()
