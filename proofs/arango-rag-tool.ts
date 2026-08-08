import type { ExtensionAPI } from "@earendil-works/pi-coding-agent";
import { Type } from "typebox";
import { DigitalBrain } from "./openclaw-brain";

/**
 * ArangoDB Graph-RAG Oracle (OpenClaw Architecture)
 *
 * Unified multi-model brain backed by ArangoDB or file-based graph.
 * 
 * Architecture (OpenClaw-style):
 *   - Named graph `brain_graph` with vertex collections (memories, entities, sessions)
 *   - Edge collections (memory_edges, entity_edges) for typed relationships  
 *   - Inline embeddings for vector search
 *   - Single AQL query combines graph traversal + vector similarity
 *
 * File-based fallback mirrors the same graph structure using knowledge_base.json.
 * ArangoDB mode enabled when ARANGO_HOST env var is set.
 */

export default function (pi: ExtensionAPI) {
  pi.registerTool({
    name: "query_graph_rag",
    label: "DigitalBrain Graph-RAG Oracle (OpenClaw)",
    description:
      "USE THIS TOOL to retrieve deeply linked knowledge from a unified multi-model graph. " +
      "Combines vector similarity, graph traversal, and entity linking in a single query. " +
      "Every result includes graph neighbors (related theorems, concepts, papers).",
    promptSnippet: "Retrieve deeply linked knowledge from the multi-model graph brain",
    promptGuidelines: [
      "Use query_graph_rag when you need connected knowledge — theorems, their dependencies, related concepts.",
      "Results include graph neighbors so you can explore the knowledge mesh around any result.",
    ],
    parameters: Type.Object({
      queryText: Type.String({
        description: "The conceptual or technical question to search for.",
      }),
      maxResults: Type.Optional(
        Type.Number({ description: "Maximum number of results (default: 5)." })
      ),
      maxHops: Type.Optional(
        Type.Number({ description: "Graph traversal depth (default: 1)." })
      ),
      memoryType: Type.Optional(
        Type.String({ description: "Filter by memory type: theorem, fact, paper, concept." })
      ),
      mode: Type.Optional(
        Type.String({ description: "search | graph | hybrid (default: hybrid)" })
      ),
    }),
    required: ["queryText"],

    async execute(
      _toolCallId: string,
      params: { queryText: string; maxResults?: number; maxHops?: number; memoryType?: string; mode?: string },
      _signal: AbortSignal,
      onUpdate: any,
      _ctx: any
    ) {
      const maxResults = params.maxResults || 5;
      const maxHops = params.maxHops || 1;
      const mode = params.mode || "hybrid";

      // ── Initialize DigitalBrain (ArangoDB backend) ──
      const brain = new DigitalBrain({
        backend: "arangodb",
      });

      const stats = await brain.stats();
      onUpdate?.({
        content: [{
          type: "text" as const,
          text: `[DigitalBrain] Loaded: ${stats.memories} memories, ${stats.entities} entities, ${stats.edges} edges across ${stats.vertices} total vertices.`
        }],
      });

      // ── Mode: Entity Graph Traversal ──
      if (mode === "graph") {
        // Try exact entity match first
        const entity = await brain.getEntity(params.queryText);
        if (entity) {
          const graph = await brain.traverseEntity(entity._key, maxHops);
          const memories = graph.vertices.filter((v: any) => v.type === "memory");
          const relatedTags = graph.vertices.filter((v: any) => v.type === "entity" && v._key !== entity._key);

          let output = `[ENTITY GRAPH] '${entity.name}' (${entity.entity_type})\n`;
          output += `  Connected to ${memories.length} memories, ${relatedTags.length} related entities\n\n`;

          if (memories.length > 0) {
            output += `── Related Memories ──\n`;
            for (const m of memories.slice(0, maxResults)) {
              output += `  • ${(m.content || "").substring(0, 200)}...\n`;
            }
            output += "\n";
          }

          if (relatedTags.length > 0) {
            output += `── Related Entities ──\n`;
            for (const e of relatedTags.slice(0, 10)) {
              output += `  • ${e.name} (${e.entity_type})\n`;
            }
          }

          return { content: [{ type: "text" as const, text: output }] };
        }

        return {
          content: [{ type: "text" as const, text: `[GRAPH] No entity found matching '${params.queryText}'.` }],
        };
      }

      // ── Mode: Hybrid (vector search + graph traversal) ──
      const full = await brain.queryGraph(params.queryText, maxResults, maxHops);

      if (full.results.length === 0) {
        return {
          content: [{ type: "text" as const, text: `[DIGITAL BRAIN] No matches for '${params.queryText}'. Try a different query or use 'mode: \"graph\"' for entity lookup.` }],
        };
      }

      // Format results
      let output = `[DIGITAL BRAIN] ${full.results.length} results (${full.graph.vertices.length} vertices, ${full.graph.edges.length} edges in neighborhood)\n\n`;

      for (let i = 0; i < full.results.length; i++) {
        const r = full.results[i];
        const mtype = r.memory.memory_type;
        const tags = r.memory.tags?.join(", ") || "";
        const neighbors = r.neighbors.filter(n => n.type === "memory");

        output += `═══ Result ${i + 1} ═══ (score: ${(r.score * 100).toFixed(0)}%)\n`;
        output += `  Type: ${mtype}\n`;
        output += `  Content: ${(r.memory.content || "").substring(0, 500)}...\n`;
        if (tags) output += `  Tags: ${tags}\n`;

        if (neighbors.length > 0) {
          output += `  Graph neighbors:\n`;
          for (const n of neighbors.slice(0, 3)) {
            const nm = n as any;
            output += `    → ${(nm.content || "").substring(0, 150)}...\n`;
          }
          if (neighbors.length > 3) {
            output += `    → ... and ${neighbors.length - 3} more\n`;
          }
        }
        output += "\n";
      }

      // Stats footer
      output += `──\nGraph stats: ${stats.vertices} vertices, ${stats.edges} edges`;
      output += ` | ${stats.memories} memories, ${stats.entities} entities`;

      return { content: [{ type: "text" as const, text: output }] };
    },
  });
}
