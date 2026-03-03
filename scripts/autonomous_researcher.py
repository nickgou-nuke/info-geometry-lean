import asyncio
import json
import math
import subprocess
import os
import random
import networkx as nx
from typing import List, Optional, Tuple
from openai import AsyncOpenAI

# Set deterministic seed for reproducible MCTS runs
random.seed(42)

# ==========================================
# 0. Safety Sandbox Configurations
# ==========================================
ALLOWED_IMPORTS = ["import InfoGeometry.Library"]
DENY_TOKENS = [
    "#eval", "unsafe", "import Lean", "import System", 
    "IO.", "System.", "run_io", "#print axioms"
]

def sanitize(snippet: str) -> bool:
    """Hard reject any code containing compile-time side effects."""
    return not any(tok in snippet for tok in DENY_TOKENS)

def wrap_lean(snippet: str) -> str:
    """Wraps model output into a controlled namespace and import environment."""
    header = "\n".join(ALLOWED_IMPORTS) + "\n\nnamespace InfoGeometry.Generated\n\n"
    footer = "\n\nend InfoGeometry.Generated\n"
    return header + snippet + footer

# ==========================================
# 1. Deterministic Topological Memory
# ==========================================
class LeanCategoryMemory:
    """Deterministic Graph Memory to prevent context compaction."""
    def __init__(self, json_path: str):
        self.json_path = json_path
        # depends_on: u -> v means u relies on v
        self.depends_on = nx.DiGraph()
        # used_by: u -> v means u is used by v (reversed edge)
        self.used_by = nx.DiGraph()
        self._load_graph()

    def _load_graph(self):
        if not os.path.exists(self.json_path):
            print(f"⚠️ Warning: {self.json_path} not found. Starting with empty memory.")
            return
            
        with open(self.json_path, 'r') as f:
            data = json.load(f)
            
        nodes = data.get("nodes", [])
        for i, node in enumerate(nodes):
            self.depends_on.add_node(i, name=node)
            self.used_by.add_node(i, name=node)
            
        for u, edges in enumerate(data.get("forward", [])):
            for edge in edges:
                v = edge[0]
                kind = edge[1]
                # In InfoGeometry.json, forward edges mean u (src) depends on v (dst)
                self.depends_on.add_edge(u, v, kind=kind)
                self.used_by.add_edge(v, u, kind=kind)
                
        print(f"🧠 [MEMORY] Loaded {self.depends_on.number_of_nodes()} mathematical concepts.")

    def hot_reload(self):
        """Rebuilds the graph from disk after a successful proof."""
        self.depends_on.clear()
        self.used_by.clear()
        self._load_graph()
        print(f"🔄 [MEMORY] Hot-reloaded. Now tracking {self.depends_on.number_of_nodes()} concepts.")

    def get_node_id(self, name: str) -> Optional[int]:
        for n, d in self.depends_on.nodes(data=True):
            if d.get("name") == name:
                return n
        return None

    def identify_frontier(self) -> str:
        """The Curiosity Engine: Uses graph topology to find the bleeding edge of the theory."""
        if self.depends_on.number_of_nodes() == 0:
            return "Init" 

        # Strategy 1: The Outward Frontier (Leaf Nodes)
        # We want things that depend on other blocks (depends_on out_degree > 0)
        # But have NOTHING depending on them (used_by out_degree == 0)
        leaves = [n for n in self.used_by.nodes() if self.used_by.out_degree(n) == 0 and self.depends_on.out_degree(n) > 0]
        if leaves:
            return self.used_by.nodes[random.choice(leaves)]['name']

        # Strategy 2: Structural Holes 
        nodes_by_centrality = sorted(nx.degree_centrality(self.used_by).items(), key=lambda x: x[1], reverse=True)
        top_nodes = [n[0] for n in nodes_by_centrality[:20]]
        
        for n1 in top_nodes:
            for n2 in top_nodes:
                if n1 != n2 and not nx.has_path(self.used_by, n1, n2) and not nx.has_path(self.used_by, n2, n1):
                    return self.used_by.nodes[n1]['name']
                    
        return self.used_by.nodes[random.choice(list(self.used_by.nodes()))]['name']

    def query_local_morphisms(self, target_node: str, radius: int = 2) -> str:
        """Returns the local topological neighborhood up to radius distance."""
        node_id = self.get_node_id(target_node)
        if node_id is None:
            return f"Node '{target_node}' not found in the formal DAG."

        # Up to radius-2 dependencies
        deps = set()
        current_layer = {node_id}
        for _ in range(radius):
            next_layer = set()
            for n in current_layer:
                next_layer.update(self.depends_on.successors(n))
            deps.update(next_layer)
            current_layer = next_layer
            
        # Up to radius-2 usages
        uses = set()
        current_layer = {node_id}
        for _ in range(radius):
            next_layer = set()
            for n in current_layer:
                next_layer.update(self.used_by.successors(n))
            uses.update(next_layer)
            current_layer = next_layer

        ctx = f"=== Formal Context for: {target_node} ===\n"
        ctx += "Dependencies (Concepts this relies on):\n"
        for d in list(deps)[:10]:
            ctx += f"  <- {self.depends_on.nodes[d]['name']}\n"
        ctx += "Usages (Concepts that rely on this):\n"
        for u in list(uses)[:10]:
            ctx += f"  -> {self.used_by.nodes[u]['name']}\n"
        return ctx

# ==========================================
# 2. Local Socratic Agents
# ==========================================
class SocraticAgents:
    def __init__(self, base_url="http://localhost:11434/v1", model="deepseek-coder-v2:16b"):
        self.client = AsyncOpenAI(base_url=base_url, api_key="local-agent")
        self.model = model

    async def generate_hypotheses(self, memory_ctx: str, num: int = 3) -> list[str]:
        system = "You are the Explorer Agent. Propose mathematical connections. Output ONLY a valid JSON array of strings. No markdown."
        prompt = f"Based on this topology, propose {num} distinct, formally verifiable Lean 4 theorems we can write next.\n{memory_ctx}"
        resp = await self._call_llm(system, prompt)
        try:
            return json.loads(resp)
        except:
            return [resp.replace('```json', '').replace('```', '').strip()]

    async def formalize(self, hypothesis: str) -> str:
        system = "You are the Critic. Translate the hypothesis into strictly valid Lean 4 code. Use 'sorry' for open proofs."
        prompt = f"Hypothesis:\n{hypothesis}"
        code = await self._call_llm(system, prompt)
        return code.replace('```lean', '').replace('```', '').strip()

    async def generate_next_steps(self, current_code: str, feedback: str) -> list[str]:
        system = "You are the Critic. Output ONLY a valid JSON array of strings containing modified Lean 4 code snippets fixing the errors."
        prompt = f"The Lean 4 compiler failed.\nCode:\n{current_code}\n\nErrors:\n{feedback}\nProvide 2 alternative ways to rewrite the code to fix these errors."
        resp = await self._call_llm(system, prompt)
        try:
            return json.loads(resp)
        except:
            return [resp.replace('```json', '').replace('```', '').strip()]

    async def _call_llm(self, system: str, user: str) -> str:
        response = await self.client.chat.completions.create(
            model=self.model,
            messages=[
                {"role": "system", "content": system},
                {"role": "user", "content": user}
            ],
            temperature=0.4,
            seed=42 # Enforcing Determinism locally
        )
        return response.choices[0].message.content.strip()

# ==========================================
# 3. Absolute Reality Boundary (Lean 4)
# ==========================================
class LeanEvaluator:
    async def evaluate_state(self, lean_code: str, file_path: str = "TsunamiSearch.lean") -> tuple[float, str, bool, bool]:
        """Runs Lean, extracts objective MDP reward, parses stderr/stdout, blocks unsafe IO."""
        
        # 1. Sandbox check
        if not sanitize(lean_code):
            return -100.0, "[SAFETY SHIELD] Rejecting code containing illegal execution tokens (e.g. #eval, IO).", True, False

        wrapped_code = wrap_lean(lean_code)
        with open(file_path, "w") as f:
            f.write(wrapped_code)
            
        process = await asyncio.create_subprocess_shell(
            f"lake env lean --json {file_path}",
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.STDOUT # Merge stderr into stdout
        )
        stdout, _ = await process.communicate()
        stdout_str = stdout.decode('utf-8')
        
        score = 50.0
        pruned_feedback = []
        is_dead_end = False
        has_errors = False
        has_sorry = False
        
        for line in stdout_str.splitlines():
            if not line.strip(): continue
            try:
                msg = json.loads(line)
                err_text = msg.get("message", "")
                severity = msg.get("severity", "")
                
                if severity == "error":
                    has_errors = True
                    pruned_feedback.append(f"Line {msg.get('pos', {}).get('line', '?')}: {err_text[:300]}")
                    if any(fatal in err_text for fatal in ["type mismatch", "unknown identifier", "failed to synthesize"]):
                        score = -100.0
                        is_dead_end = True
                    elif "tactic" in err_text and "failed" in err_text:
                        score -= 10.0
                    else:
                        score -= 20.0
                elif severity == "warning" and "declaration uses 'sorry'" in err_text:
                    score += 10.0
                    has_sorry = True
            except json.JSONDecodeError:
                pruned_feedback.append(f"Compiler System output: {line[:200]}")
                has_errors = True

        score = max(-100.0, min(100.0, score))
        feedback_str = "\n".join(pruned_feedback) if pruned_feedback else "Warning: Unresolved goals remain."
        
        # Truly rigorous Q.E.D. parameters
        if process.returncode == 0 and not has_errors and not has_sorry:
             return 100.0, "Q.E.D. Proof complete.", True, True
             
        return score, feedback_str, is_dead_end, False

# ==========================================
# 4. Monte Carlo Tree Search (MCTS)
# ==========================================
class ProofNode:
    def __init__(self, code: str, parent: Optional['ProofNode'] = None, prior: float = 1.0):
        self.code = code
        self.parent = parent
        self.children: List['ProofNode'] = []
        
        self.visits = 0
        self.total_value = 0.0
        self.prior = prior
        
        self.score = 0.0
        self.feedback = ""
        self.is_terminal = False
        self.is_success = False
        self.is_evaluated = False

    def uct_value(self, c_puct: float = 1.5) -> float:
        if self.visits == 0: return float('inf')
        q = self.total_value / self.visits
        u = c_puct * self.prior * math.sqrt(self.parent.visits) / (1 + self.visits)
        return q + u

class TsunamiOrchestrator:
    def __init__(self, agents, memory):
        self.agents = agents
        self.memory = memory
        self.evaluator = LeanEvaluator()

    async def run_mcts(self, target_node: str, max_iterations: int = 15) -> Optional[str]:
        print(f"\n🌊 [MCTS] Initializing context wave around '{target_node}'")
        local_ctx = self.memory.query_local_morphisms(target_node, radius=2)
        
        root = ProofNode(code="")
        root.is_evaluated = True 
        
        print("  [EXPLORER] Generating foundation hypotheses...")
        hypotheses = await self.agents.generate_hypotheses(local_ctx, num=3)
        for hyp in hypotheses:
            code = await self.agents.formalize(hyp)
            root.children.append(ProofNode(code=code, parent=root))

        for iteration in range(max_iterations):
            print(f"\n--- MCTS Iteration {iteration + 1}/{max_iterations} ---")
            
            curr = root
            while curr.is_evaluated and curr.children:
                curr = max(curr.children, key=lambda n: n.uct_value())
                
            if curr.is_terminal and curr.is_success:
                return curr.code
            elif curr.is_terminal:
                continue 

            print("  [KERNEL] Evaluating state...")
            score, feedback, is_dead, is_win = await self.evaluator.evaluate_state(curr.code)
            curr.score = score
            curr.feedback = feedback
            curr.is_terminal = is_dead or is_win
            curr.is_success = is_win
            curr.is_evaluated = True
            
            print(f"  [SCORE]: {score} | Terminal: {curr.is_terminal}")

            if is_win:
                print("🚀 [BREAKTHROUGH] Q.E.D. Proof complete!")
                return curr.code

            if not is_dead:
                print("  [CRITIC] Branch viable. Generating next tactical steps...")
                new_codes = await self.agents.generate_next_steps(curr.code, curr.feedback)
                for nc in new_codes:
                    curr.children.append(ProofNode(code=nc, parent=curr, prior=0.8))

            temp = curr
            while temp is not None:
                temp.visits += 1
                temp.total_value += curr.score
                temp = temp.parent

        print("🛑 [MCTS] Exhausted limits. Tsunami collapsed.")
        return None

    async def commit_to_memory(self, winning_code: str, target_name: str):
        print(f"\n🌍 [INTEGRATION] Expanding universe with discoveries from: {target_name}")
        
        generated_file = "lean/InfoGeometry/Generated.lean" 
        
        # Ensure file exists
        if not os.path.exists(generated_file):
            with open(generated_file, "w") as f:
                f.write("import InfoGeometry.Library\n\n")

        with open(generated_file, "a") as f:
            f.write(f"\n/- Discovered via Autonomous MCTS around {target_name} -/\n")
            f.write(f"namespace InfoGeometry.Generated\n{winning_code}\nend InfoGeometry.Generated\n")
            
        print("  [KERNEL] Rebuilding the Categorical DAG...")
        # Since InfoGeometry.lean imports InfoGeometry.Generated, indexing it will pull the graph
        process = await asyncio.create_subprocess_shell(
            "lake env lean --run lean/DAG/ExportDecls.lean InfoGeometry InfoGeometry index full_graph.json",
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE
        )
        await process.communicate()
        
        if process.returncode == 0:
            self.memory.hot_reload()
            print("✨ [SUCCESS] Universe topology updated.")
            
            print("  [PUBLISHER] Generating updated LaTeX blueprint...")
            bp_process = await asyncio.create_subprocess_shell(
                "lake env lean --run lean/Docs/emit_blueprint_tex.lean InfoGeometry docs-map/blueprint.tex",
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE
            )
            await bp_process.communicate()
            if bp_process.returncode == 0:
                print("📄 [SUCCESS] LaTeX Blueprint compiled to docs-map/blueprint.tex")
            else:
                print("⚠️ [ERROR] Blueprint generation failed.")
                
        else:
            print("⚠️ [ERROR] Indexer failed. Graph not updated.")

# ==========================================
# 5. The Skynet Daemon
# ==========================================
async def skynet_daemon():
    print(r"""
     _____ _   _   __   _   _  _____ _____ 
    /  ___| | | | / /  | \ | ||  ___|_   _|
    \ `--.| |/ / / /   |  \| || |__   | |  
     `--. \    \ \ \   | . ` ||  __|  | |  
    /\__/ / |\  \ \ \__| |\  || |___  | |  
    \____/\_| \_/\____/\_| \_/\____/  \_/  
    Autonomous Theory Engine Initiated.
    """)
    
    memory = LeanCategoryMemory("full_graph.json")
    agents = SocraticAgents()
    orchestrator = TsunamiOrchestrator(agents, memory)
    
    while True:
        target = memory.identify_frontier()
        print(f"\n🎯 [CURIOSITY] Selected topological frontier: {target}")
        
        winning_code = await orchestrator.run_mcts(target)
        
        if winning_code:
            await orchestrator.commit_to_memory(winning_code, target)
        else:
            print(f"⏭️  [SKIPPED] Entropic barrier held. Shifting focus.")
            
        await asyncio.sleep(5)

if __name__ == "__main__":
    try:
        asyncio.run(skynet_daemon())
    except KeyboardInterrupt:
        print("\n[DAEMON] Shutting down. Topology preserved.")
