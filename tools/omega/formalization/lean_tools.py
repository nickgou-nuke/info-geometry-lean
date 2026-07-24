#!/usr/bin/env python3
"""
Lean 4 Formalization Tools - Bridge between pi-omega-extension and Lake build system
Implements the formalization commands with proper timeout, retry, and verification
"""

import asyncio
import json
import os
import subprocess
import tempfile
import time
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Any, Tuple

import httpx


@dataclass
class LeanConfig:
    repo_root: Path = Path("/home/goutev/repos/info-geometry-lean")
    lake_timeout_seconds: int = 180
    lean_timeout_seconds: int = 60
    mathlib_rev: str = "8f9d9cff6bd728b17a24e163c9402775d9e6a365"


@dataclass
class LeanResult:
    success: bool
    output: str
    errors: List[str]
    warnings: List[str]
    duration: float


class LeanTools:
    """Lean 4 formalization toolkit for the Omega pipeline"""
    
    def __init__(self, config: LeanConfig):
        self.config = config
        self.lean4_root = config.repo_root
    
    async def build(self, module: str) -> LeanResult:
        """Build a Lean 4 module with timeout"""
        return await self._run_command(["lake", "build", module], self.config.lake_timeout_seconds)
    
    async def build_all(self) -> LeanResult:
        """Build entire project"""
        return await self._run_command(["lake", "build"], self.config.lake_timeout_seconds)
    
    async def check_file(self, file_path: str) -> LeanResult:
        """Type-check a single Lean file"""
        full_path = self.lean4_root / file_path
        if not full_path.exists():
            return LeanResult(False, "", [f"File not found: {file_path}"], [], 0.0)
        
        return await self._run_command(
            ["lake", "env", "lean", str(full_path)],
            self.config.lean_timeout_seconds
        )
    
    async def run_script(self, script_name: str) -> LeanResult:
        """Run a Lake script"""
        return await self._run_command(
            ["lake", "script", "run", script_name],
            self.config.lake_timeout_seconds
        )
    
    async def extract_theorems(self, module_path: str) -> List[Dict[str, Any]]:
        """Extract theorem/lemma declarations from a Lean file"""
        full_path = self.lean4_root / module_path
        if not full_path.exists():
            return []
        
        content = full_path.read_text()
        theorems = []
        
        import re
        lines = content.split("\n")
        for i, line in enumerate(lines):
            # Match theorem/lemma declarations
            match = re.match(r'^\s*(theorem|lemma|def|structure|class)\s+(\w+)', line)
            if match:
                theorems.append({
                    "keyword": match.group(1),
                    "name": match.group(2),
                    "file": module_path,
                    "line": i + 1,
                    "statement": line.strip()
                })
        
        return theorems
    
    async def extract_all_theorems(self) -> List[Dict[str, Any]]:
        """Extract all theorems from the Lean 4 project"""
        all_theorems = []
        for lean_file in (self.lean4_root / "Omega").rglob("*.lean"):
            theorems = await self.extract_theorems(str(lean_file.relative_to(self.lean4_root)))
            all_theorems.extend(theorems)
        return all_theorems
    
    async def check_axioms(self, module: str = "Omega") -> Dict[str, Any]:
        """Check for axioms in compiled theorems"""
        # Run axiom audit script
        result = await self._run_command(
            ["lake", "env", "lean", "--run", "scripts/axiom_audit.lean"],
            60
        )
        
        # Parse output for axioms
        axioms = []
        for line in result.output.split("\n"):
            if "axiom" in line.lower() and "sorry" not in line.lower():
                axioms.append(line.strip())
        
        return {
            "success": result.success,
            "axioms": axioms,
            "axiom_count": len(axioms)
        }
    
    async def get_compilation_stats(self) -> Dict[str, Any]:
        """Get compilation statistics"""
        result = await self._run_command(["lake", "build"], self.config.lake_timeout_seconds)
        
        stats = {
            "success": result.success,
            "duration": result.duration,
            "warnings": len(result.warnings),
            "errors": len(result.errors)
        }
        
        # Parse job count from output
        for line in result.output.split("\n"):
            if "jobs" in line and "Building" in line:
                import re
                match = re.search(r'(\d+)\s+jobs', line)
                if match:
                    stats["jobs"] = int(match.group(1))
        
        return stats
    
    async def _run_command(self, cmd: List[str], timeout: int) -> LeanResult:
        """Run command with timeout and capture output"""
        start = time.time()
        
        try:
            proc = await asyncio.create_subprocess_exec(
                *cmd,
                cwd=self.lean4_root,
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE
            )
            
            stdout, stderr = await asyncio.wait_for(
                proc.communicate(),
                timeout=timeout
            )
            
            duration = time.time() - start
            
            output = stdout.decode() if stdout else ""
            error_output = stderr.decode() if stderr else ""
            
            warnings = [w for w in error_output.split("\n") if "warning:" in w.lower()]
            errors = [e for e in error_output.split("\n") if "error:" in e.lower()]
            
            return LeanResult(
                success=proc.returncode == 0,
                output=output,
                errors=errors,
                warnings=warnings,
                duration=duration
            )
            
        except asyncio.TimeoutError:
            return LeanResult(
                success=False,
                output="",
                errors=[f"Timeout after {timeout}s"],
                warnings=[],
                duration=time.time() - start
            )
        except Exception as e:
            return LeanResult(
                success=False,
                output="",
                errors=[str(e)],
                warnings=[],
                duration=time.time() - start
            )


class LeanTheoremExtractor:
    """Advanced theorem extraction with dependency analysis"""
    
    def __init__(self, lean_tools: LeanTools):
        self.lean = lean_tools
    
    async def extract_with_dependencies(self, module_path: str) -> List[Dict[str, Any]]:
        """Extract theorems with their dependency chains"""
        theorems = await self.lean.extract_theorems(module_path)
        
        # For each theorem, try to find its dependencies
        for thm in theorems:
            thm["dependencies"] = await self._find_dependencies(thm)
        
        return theorems
    
    async def _find_dependencies(self, theorem: Dict[str, Any]) -> List[str]:
        """Find dependencies of a theorem using Lean's #print axioms or similar"""
        # This would use lean --run to print dependencies
        return []
    
    async def get_theorem_graph(self, module: str = "Omega") -> Dict[str, Any]:
        """Build a dependency graph of all theorems in a module"""
        all_theorems = await self.lean.extract_all_theorems()
        
        nodes = []
        edges = []
        
        for thm in all_theorems:
            nodes.append({
                "id": f"{thm['file']}::{thm['name']}",
                "label": thm['name'],
                "file": thm['file'],
                "type": thm['keyword']
            })
        
        return {"nodes": nodes, "edges": edges}


# =============================================================================
# CLI
# =============================================================================

async def main():
    import argparse
    parser = argparse.ArgumentParser(description="Lean 4 Formalization Tools")
    parser.add_argument("--repo", default="/home/goutev/repos/info-geometry-lean")
    parser.add_argument("--action", choices=[
        "build", "check", "theorems", "script", "axioms", "stats", "graph"
    ], required=True)
    parser.add_argument("--module", help="Module name for build")
    parser.add_argument("--file", help="File path for check")
    parser.add_argument("--script", help="Script name for run")
    args = parser.parse_args()
    
    config = LeanConfig(repo_root=Path(args.repo))
    lean = LeanTools(config)
    
    if args.action == "build":
        module = args.module or "Omega"
        result = await lean.build(module)
    elif args.action == "check":
        result = await lean.check_file(args.file)
    elif args.action == "theorems":
        theorems = await lean.extract_theorems(args.file or "Omega.lean")
        print(json.dumps(theorems, indent=2))
        return
    elif args.action == "script":
        result = await lean.run_script(args.script)
    elif args.action == "axioms":
        result = await lean.check_axioms()
        print(json.dumps(result, indent=2))
        return
    elif args.action == "stats":
        result = await lean.get_compilation_stats()
        print(json.dumps(result, indent=2))
        return
    elif args.action == "graph":
        extractor = LeanTheoremExtractor(lean)
        graph = await extractor.get_theorem_graph()
        print(json.dumps(graph, indent=2))
        return
    else:
        result = LeanResult(False, "", [f"Unknown action: {args.action}"], [], 0.0)
    
    print(json.dumps({
        "success": result.success,
        "output": result.output[:5000],
        "errors": result.errors,
        "warnings": result.warnings,
        "duration": result.duration
    }, indent=2))


if __name__ == "__main__":
    import asyncio
    asyncio.run(main())