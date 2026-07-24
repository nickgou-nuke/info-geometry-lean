#!/usr/bin/env python3
"""
Sisyphus Knowledge Graph - ArangoDB backed theorem dependency graph
Faithful implementation from Automath Omega
"""

import asyncio
import json
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional, Set
from dataclasses import dataclass, asdict

try:
    from arangojs import ArangoClient
except ImportError:
    ArangoClient = None


@dataclass
class TheoremNode:
    _key: str
    name: str
    paper_tag: str
    chapter: str
    difficulty: str
    lean_signature: str
    proof_commit: str
    timestamp: str
    derivation_depth: int
    type: str = "theorem"


@dataclass
class DependencyEdge:
    _from: str
    _to: str
    type: str = "depends_on"
    weight: float = 1.0


class SisyphusGraph:
    """
    The Sisyphus Knowledge Graph - tracks all theorem dependencies,
    derivation depths, and cross-domain connections.
    
    From Automath: "The 'Sisyphus' system with approximately 20,998 nodes
    tracking theorem dependencies, derivation depth, and cross-domain connections."
    """
    
    def __init__(self, config: Dict[str, Any]):
        self.config = config
        self.client = None
        self.db = None
        self.collections = config.get("collections", [
            "theorems", "dependencies", "concepts", "papers", "agents"
        ])
    
    async def connect(self):
        if ArangoClient is None:
            raise RuntimeError("arangojs not installed. pip install arangojs")
        
        self.client = ArangoClient(hosts=self.config.get("url", "http://localhost:8530"))
        self.db = await self.client.db(
            self.config.get("db", "infogeometry"),
            username=self.config.get("user", "root"),
            password=self.config.get("pass", "hive_brain")
        )
        
        # Ensure collections exist
        for coll_name in self.collections:
            if not await self.db.has_collection(coll_name):
                await self.db.create_collection(coll_name, edge=(coll_name == "dependencies"))
        
        # Create indexes
        await self._create_indexes()
    
    async def _create_indexes(self):
        theorems = self.db.collection("theorems")
        await theorems.add_hash_index(fields=["paper_tag"], unique=False)
        await theorems.add_hash_index(fields=["chapter"], unique=False)
        await theorems.add_hash_index(fields=["derivation_depth"], unique=False)
        await theorems.add_hash_index(fields=["proof_commit"], unique=False)
        
        deps = self.db.collection("dependencies")
        await deps.add_hash_index(fields=["type"], unique=False)
    
    # =========================================================================
    # Theorem Operations
    # =========================================================================
    
    async def store_theorem(self, theorem: TheoremNode, dependencies: List[str]) -> bool:
        """Store theorem with dependency edges"""
        theorems = self.db.collection("theorems")
        deps = self.db.collection("dependencies")
        
        # Upsert theorem
        await theorems.insert(theorem.__dict__, overwrite=True)
        
        # Dependency edges
        for dep in dependencies:
            await deps.insert({
                "_from": f"theorems/{theorem._key}",
                "_to": f"theorems/{dep}",
                "type": "depends_on",
                "timestamp": datetime.utcnow().isoformat()
            }, overwrite=True)
        
        return True
    
    async def get_theorem(self, name: str) -> Optional[TheoremNode]:
        theorems = self.db.collection("theorems")
        doc = await theorems.get(name)
        if doc:
            return TheoremNode(**doc)
        return None
    
    async def get_theorems_by_chapter(self, chapter: str) -> List[TheoremNode]:
        query = """
        FOR t IN theorems
            FILTER t.chapter == @chapter
            RETURN t
        """
        cursor = await self.db.aql.execute(query, bind_vars={"chapter": chapter})
        return [TheoremNode(**doc) async for doc in cursor]
    
    async def get_theorems_by_depth_range(self, min_depth: int, max_depth: int) -> List[TheoremNode]:
        query = """
        FOR t IN theorems
            FILTER t.derivation_depth >= @min AND t.derivation_depth <= @max
            RETURN t
        """
        cursor = await self.db.aql.execute(query, bind_vars={"min": min_depth, "max": max_depth})
        return [TheoremNode(**doc) async for doc in cursor]
    
    # =========================================================================
    # Causal Cone / Dependency Analysis
    # =========================================================================
    
    async def get_causal_cone(self, theorem_name: str, depth: int = 3, 
                             direction: str = "inbound") -> Dict[str, Any]:
        """
        Get upstream (inbound) or downstream (outbound) dependencies
        up to specified depth.
        """
        if direction == "inbound":
            query = """
            FOR v, e IN 1..@depth INBOUND @start dependencies
                RETURN {vertex: v, edge: e, distance: LENGTH(e)}
            """
        else:
            query = """
            FOR v, e IN 1..@depth OUTBOUND @start dependencies
                RETURN {vertex: v, edge: e, distance: LENGTH(e)}
            """
        
        cursor = await self.db.aql.execute(query, bind_vars={
            "start": f"theorems/{theorem_name}",
            "depth": depth
        })
        results = [doc async for doc in cursor]
        
        return {
            "theorem": theorem_name,
            "direction": direction,
            "depth": depth,
            "nodes": results,
            "count": len(results)
        }
    
    async def get_derivation_depth(self, theorem_name: str) -> int:
        """Distance from seed equation x²=x+1"""
        seed = self.config.get("seed_theorem", "seed_x2_eq_x_plus_1")
        
        query = """
        FOR v, e IN 1..100 INBOUND @start dependencies
            FILTER v._key == @seed
            RETURN LENGTH(e)
        """
        cursor = await self.db.aql.execute(query, bind_vars={
            "start": f"theorems/{theorem_name}",
            "seed": seed
        })
        result = [doc async for doc in cursor]
        return min(result) if result else -1
    
    async def compute_all_derivation_depths(self) -> Dict[str, int]:
        """Compute derivation depth for all theorems from seed"""
        seed = self.config.get("seed_theorem", "seed_x2_eq_x_plus_1")
        
        query = """
        FOR v IN theorems
            LET depth = (
                FOR u, e IN 1..100 INBOUND v dependencies
                    FILTER u._key == @seed
                    RETURN LENGTH(e)
            )
            FILTER LENGTH(depth) > 0
            RETURN {theorem: v._key, depth: MIN(depth)}
        """
        cursor = await self.db.aql.execute(query, bind_vars={"seed": seed})
        results = {doc["theorem"]: doc["depth"] async for doc in cursor}
        
        # Update theorems with computed depths
        for name, depth in results.items():
            await self.db.collection("theorems").update({"_key": name}, {"derivation_depth": depth})
        
        return results
    
    # =========================================================================
    # Cross-Domain Bridges
    # =========================================================================
    
    async def add_bridge(self, from_theorem: str, to_theorem: str, 
                        bridge_type: str, description: str):
        """Add cross-domain bridge edge"""
        deps = self.db.collection("dependencies")
        await deps.insert({
            "_from": f"theorems/{from_theorem}",
            "_to": f"theorems/{to_theorem}",
            "type": f"bridge_{bridge_type}",
            "description": description,
            "timestamp": datetime.utcnow().isoformat()
        })
    
    async def get_bridges(self, theorem_name: str) -> List[Dict]:
        query = """
        FOR v, e IN 1..3 OUTBOUND @start dependencies
            FILTER STARTS_WITH(e.type, "bridge_")
            RETURN {target: v._key, bridge_type: e.type, description: e.description}
        """
        cursor = await self.db.aql.execute(query, bind_vars={"start": f"theorems/{theorem_name}"})
        return [doc async for doc in cursor]
    
    # =========================================================================
    # Statistics & Metrics
    # =========================================================================
    
    async def get_statistics(self) -> Dict[str, Any]:
        theorems = self.db.collection("theorems")
        deps = self.db.collection("dependencies")
        
        theorem_count = await theorems.count()
        dep_count = await deps.count()
        
        # Depth distribution
        depth_query = """
        FOR t IN theorems
            COLLECT depth = t.derivation_depth WITH COUNT INTO count
            RETURN {depth, count}
        """
        cursor = await self.db.aql.execute(depth_query)
        depth_dist = {doc["depth"]: doc["count"] async for doc in cursor}
        
        # Chapter distribution
        chapter_query = """
        FOR t IN theorems
            COLLECT chapter = t.chapter WITH COUNT INTO count
            RETURN {chapter, count}
        """
        cursor = await self.db.aql.execute(chapter_query)
        chapter_dist = {doc["chapter"]: doc["count"] async for doc in cursor}
        
        # Difficulty distribution
        diff_query = """
        FOR t IN theorems
            COLLECT diff = t.difficulty WITH COUNT INTO count
            RETURN {difficulty: diff, count}
        """
        cursor = await self.db.aql.execute(diff_query)
        diff_dist = {doc["difficulty"]: doc["count"] async for doc in cursor}
        
        return {
            "theorems": theorem_count,
            "dependencies": dep_count,
            "depth_distribution": depth_dist,
            "chapter_distribution": chapter_dist,
            "difficulty_distribution": diff_dist
        }
    
    # =========================================================================
    # Export / Import
    # =========================================================================
    
    async def export_graphml(self, output_path: str):
        """Export graph for visualization (Gephi, Cytoscape, etc.)"""
        query = """
        FOR t IN theorems
            RETURN {id: t._key, label: t.name, chapter: t.chapter, 
                   depth: t.derivation_depth, difficulty: t.difficulty}
        """
        cursor = await self.db.aql.execute(query)
        nodes = [doc async for doc in cursor]
        
        query = """
        FOR e IN dependencies
            RETURN {source: e._from.split('/')[1], target: e._to.split('/')[1], type: e.type}
        """
        cursor = await self.db.aql.execute(query)
        edges = [doc async for doc in cursor]
        
        # Write GraphML
        with open(output_path, 'w') as f:
            f.write('<?xml version="1.0" encoding="UTF-8"?>\n')
            f.write('<graphml xmlns="http://graphml.graphdrawing.org/xmlns">\n')
            f.write('  <graph id="sisyphus" edgedefault="directed">\n')
            
            for node in nodes:
                f.write(f'    <node id="{node["id"]}">\n')
                f.write(f'      <data key="label">{node["label"]}</data>\n')
                f.write(f'      <data key="chapter">{node["chapter"]}</data>\n')
                f.write(f'      <data key="depth">{node["depth"]}</data>\n')
                f.write(f'      <data key="difficulty">{node["difficulty"]}</data>\n')
                f.write('    </node>\n')
            
            for edge in edges:
                f.write(f'    <edge source="{edge["source"]}" target="{edge["target"]}">\n')
                f.write(f'      <data key="type">{edge["type"]}</data>\n')
                f.write('    </edge>\n')
            
            f.write('  </graph>\n')
            f.write('</graphml>\n')
    
    async def export_json(self, output_path: str):
        """Export full graph as JSON"""
        query = "FOR t IN theorems RETURN t"
        cursor = await self.db.aql.execute(query)
        theorems = [doc async for doc in cursor]
        
        query = "FOR e IN dependencies RETURN e"
        cursor = await self.db.aql.execute(query)
        edges = [doc async for doc in cursor]
        
        with open(output_path, 'w') as f:
            json.dump({"nodes": theorems, "edges": edges}, f, indent=2)
    
    # =========================================================================
    # LaTeX Annotation Sync
    # =========================================================================
    
    async def get_unannotated_theorems(self, theory_root: Path) -> List[TheoremNode]:
        """Find theorems in Lean that lack \leanverified annotation in LaTeX"""
        # Get all formalized theorems from Lean
        lean_theorems = await self._scan_lean_for_tags()
        
        # Check LaTeX for annotations
        unannotated = []
        for theorem in lean_theorems:
            annotated = await self._check_latex_annotation(theorem.paper_tag, theory_root)
            if not annotated:
                unannotated.append(theorem)
        
        return unannotated
    
    async def _scan_lean_for_tags(self) -> List[TheoremNode]:
        """Scan Lean files for paper tags in docstrings"""
        lean_root = Path("external_refs/automath/lean4/Omega")
        theorems = []
        
        for lean_file in lean_root.rglob("*.lean"):
            content = lean_file.read_text()
            # Find docstrings with paper tags
            import re
            tags = re.findall(r'(prop|thm|cor|def|lem|bridge):([\w-]+)', content)
            for prefix, tag in tags:
                # Get theorem name from context
                theorems.append(TheoremNode(
                    _key=tag,
                    name=tag,
                    paper_tag=f"{prefix}:{tag}",
                    chapter="unknown",
                    difficulty="unknown",
                    lean_signature="",
                    proof_commit="",
                    timestamp=datetime.utcnow().isoformat(),
                    derivation_depth=-1
                ))
        
        return theorems
    
    async def _check_latex_annotation(self, tag: str, theory_root: Path) -> bool:
        """Check if LaTeX file has \leanverified{tag} annotation"""
        for tex_file in theory_root.rglob("*.tex"):
            content = tex_file.read_text()
            if f"\\leanverified{{{tag}}}" in content or f"\\leanpartial{{{tag}}}" in content:
                return True
        return False


# =============================================================================
# CLI
# =============================================================================

async def main():
    import argparse
    parser = argparse.ArgumentParser(description="Sisyphus Knowledge Graph")
    parser.add_argument("--config", default="omega_config.json")
    parser.add_argument("--stats", action="store_true")
    parser.add_argument("--export-graphml", help="Export to GraphML file")
    parser.add_argument("--export-json", help="Export to JSON file")
    parser.add_argument("--compute-depths", action="store_true")
    parser.add_argument("--unannotated", action="store_true")
    args = parser.parse_args()
    
    with open(args.config) as f:
        config = json.load(f)
    
    kg = SisyphusGraph(config.get("knowledge_graph", {}))
    await kg.connect()
    
    if args.stats:
        stats = await kg.get_statistics()
        print(json.dumps(stats, indent=2))
    
    if args.export_graphml:
        await kg.export_graphml(args.export_graphml)
        print(f"Exported to {args.export_graphml}")
    
    if args.export_json:
        await kg.export_json(args.export_json)
        print(f"Exported to {args.export_json}")
    
    if args.compute_depths:
        depths = await kg.compute_all_derivation_depths()
        print(f"Computed depths for {len(depths)} theorems")
    
    if args.unannotated:
        unannotated = await kg.get_unannotated_theorems(Path("external_refs/automath/theory"))
        print(f"Unannotated theorems: {len(unannotated)}")
        for t in unannotated:
            print(f"  {t.paper_tag}")


if __name__ == "__main__":
    asyncio.run(main())