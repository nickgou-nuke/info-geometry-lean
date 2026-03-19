import asyncio
import json
import random
import networkx as nx
import os
import subprocess

class LeanCategoryMemory:
    def __init__(self, graph_path="full_graph.json"):
        self.graph_path = graph_path
        self.G = nx.DiGraph()
        self.load_graph()

    def load_graph(self):
        if not os.path.exists(self.graph_path):
            print(f"Graph file {self.graph_path} not found. Starting with empty memory.")
            return
            
        with open(self.graph_path, 'r') as f:
            data = json.load(f)
            
        # Parse the output array of array of [idx, name] pairs correctly based on DAG.Indexer
        # We only really care about getting the nodes and edges
        # Depending on the exact Indexer.lean output schema, we reconstruct the networkx Digraph
        
        # A robust way to just take all edges from any JSON schema that lists deps
        if "declarations" in data:
            for decl in data["declarations"]:
                node = decl["name"]
                self.G.add_node(node)
                for dep in decl.get("deps", []):
                    self.G.add_edge(node, dep)
        elif isinstance(data, list):
             for item in data:
                 if isinstance(item, list):
                     for edge in item:
                         if isinstance(edge, list) and len(edge) == 2:
                             self.G.add_edge(edge[0], edge[1])

    def identify_frontier(self) -> str:
        """
        The Curiosity Engine: Uses graph topology to find the bleeding edge of the theory.
        """
        if len(self.G.nodes()) == 0:
             return "InfoGeometry.Basic" # Fallback seed

        # Strategy 1: The Outward Frontier (Leaf Nodes)
        # Find concepts that rely on other math (out_degree > 0) but haven't 
        # been used to prove anything else yet (in_degree == 0).
        leaves = [node for node in self.G.nodes() 
                  if self.G.out_degree(node) > 0 and self.G.in_degree(node) == 0]
        
        if leaves:
            return random.choice(leaves)

        # Strategy 2: The Structural Hole
        nodes_by_centrality = sorted(nx.degree_centrality(self.G).items(), 
                                     key=lambda x: x[1], reverse=True)
        top_nodes = [n[0] for n in nodes_by_centrality[:20]]
        
        for n1 in top_nodes:
            for n2 in top_nodes:
                if n1 != n2 and not nx.has_path(self.G, n1, n2) and not nx.has_path(self.G, n2, n1):
                    return n1 
                    
        return random.choice(list(self.G.nodes()))

# Dummy implementations of Orchestrator to make the script standalone runnable
class SocraticAgents:
    pass

class TsunamiOrchestrator:
    def __init__(self, agents, memory):
        self.agents = agents
        self.memory = memory

    async def run_mcts(self, target):
        print(f"Running MCTS search for {target}...")
        await asyncio.sleep(1)
        # Simulate a successful proof 50% of the time for demonstration
        if random.random() > 0.5:
            return f"theorem auto_gen_{target.replace('.', '_')} : True := trivial"
        return None

    async def commit_to_memory(self, winning_code, target):
        print("Committing generated code to InfoGeometry/Generated.lean...")
        lean_file = "lean/InfoGeometry/Generated.lean"
        
        # Ensure header exists
        if not os.path.exists(lean_file):
             with open(lean_file, "w") as f:
                 f.write("import InfoGeometry.Core\nimport InfoGeometry.Convex\n\n")
                 
        with open(lean_file, "a") as f:
            f.write(f"\n{winning_code}\n")
        
        print("Hot reloading Lean graph memory...")
        subprocess.run(["lake", "env", "lean", "--run", "lean/DAG/ExportDecls.lean", 
                       "InfoGeometry.Core,InfoGeometry.Convex,InfoGeometry.Generated", 
                       "InfoGeometry", "full_graph.json", "InfoGeometry"], check=False)
        self.memory.load_graph()

async def skynet_daemon():
    # Make sure we generate the seed graph first
    print("Generating seed graph...")
    subprocess.run(["lake", "env", "lean", "--run", "lean/DAG/ExportDecls.lean", 
                   "InfoGeometry.Core,InfoGeometry.Convex", 
                   "InfoGeometry", "full_graph.json", "InfoGeometry"], check=False)
                   
    memory = LeanCategoryMemory("full_graph.json")
    agents = SocraticAgents()
    orchestrator = TsunamiOrchestrator(agents, memory)
    
    print("🌐 Initiating Self-Bootstrapping Theory Engine...")
    
    # Run a few iterations for safety rather than an infinite loop while testing
    for _ in range(3):
        target = memory.identify_frontier()
        print(f"\n🎯 [CURIOSITY ENGINE] Selected new topological frontier: {target}")
        
        winning_code = await orchestrator.run_mcts(target)
        
        if winning_code:
            await orchestrator.commit_to_memory(winning_code, target)
        else:
            print(f"🛑 [SKIPPED] The entropic barrier at '{target}' was too high. Moving on.")
            
        await asyncio.sleep(2)

if __name__ == "__main__":
    asyncio.run(skynet_daemon())
