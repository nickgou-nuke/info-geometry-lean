/**
 * DigitalBrain — Unified multi-model memory layer
 *
 * Inspired by ArangoDB OpenClaw architecture:
 *   - Documents (memories, entities, sessions, daily logs)
 *   - Vectors (inline embeddings for semantic search)
 *   - Graph (typed edges between entities and memories)
 *
 * Two modes:
 *   1. ArangoDB mode: full graph+vector+document using arangojs + AQL
 *   2. File-based mode: JSON-backed graph with in-memory vector search
 *
 * The file-based mode mirrors the ArangoDB schema so both paths
 * use the same data model. When ArangoDB is available, switch
 * by passing `{ backend: "arangodb" }` to the constructor.
 */

import { existsSync, readFileSync } from "fs";

// ══════════════════════════════════════════════════════════════════════
// DATA TYPES
// ══════════════════════════════════════════════════════════════════════

interface Embedding {
  vector: number[];
  model: string;     // e.g. "Xenova/all-MiniLM-L6-v2"
  dimensions: number;
}

interface BaseDocument {
  _key?: string;
  _id?: string;
  created_at: string;
  agent_id: string;
}

interface Memory extends BaseDocument {
  type: "memory";
  content: string;
  memory_type: "fact" | "event" | "note" | "conversation" | "decision" | "preference" | "daily_summary" | "theorem";
  tags: string[];
  source: string;
  embedding?: Embedding;
  confidence: number;
  access_count: number;
  last_accessed: string;
}

interface Entity extends BaseDocument {
  type: "entity";
  name: string;
  entity_type: "person" | "organization" | "concept" | "theorem" | "paper" | "tag";
  description?: string;
}

interface Session extends BaseDocument {
  type: "session";
  channel?: string;
  started_at: string;
  message_count: number;
}

interface DailyLog extends BaseDocument {
  type: "daily_log";
  date: string;
  entry_count: number;
  summary: string;
  embedding?: Embedding;
}

interface Edge {
  _from: string;
  _to: string;
  _key?: string;
  relation: string;
  created_at: string;
  weight?: number;
}

type Vertex = Memory | Entity | Session | DailyLog;

interface BrainConfig {
  backend: "file" | "arangodb";
  dbName?: string;
  embedPath?: string;  // path to knowledge_base.json for file mode
}

// ══════════════════════════════════════════════════════════════════════
// GRAPH SCHEMA CONSTANTS
// ══════════════════════════════════════════════════════════════════════

const VERTEX_COLLECTIONS = ["memories", "entities", "sessions", "daily_logs"] as const;
const EDGE_COLLECTIONS = ["memory_edges", "entity_edges"] as const;
type VertexCollection = typeof VERTEX_COLLECTIONS[number];
type EdgeCollection = typeof EDGE_COLLECTIONS[number];

const GRAPH_NAME = "brain_graph";

// ══════════════════════════════════════════════════════════════════════
// FILE-BACKED GRAPH ENGINE
// ══════════════════════════════════════════════════════════════════════

class FileGraphEngine {
  private vertices: Map<string, Vertex> = new Map();
  private edges: Edge[] = [];
  private kbPath: string;

  constructor(kbPath: string) {
    this.kbPath = kbPath;
    this.loadFromKB();
  }

  /** Load knowledge_base.json into the graph. */
  private loadFromKB() {
    try {
      if (!existsSync(this.kbPath)) return;
      const raw = JSON.parse(readFileSync(this.kbPath, "utf-8"));
      if (!Array.isArray(raw)) return;

      const now = new Date().toISOString();

      for (const entry of raw) {
        // Each KB entry becomes a Memory vertex
        const key = entry.id || this.sha1(entry.title || "") || `kb_${Math.random().toString(36).slice(2, 10)}`;
        const memory: Memory = {
          _key: key,
          type: "memory",
          content: entry.content || "",
          memory_type: entry.status === "verified_conscious_truth" ? "theorem" : "fact",
          tags: entry.tags || [],
          source: entry.source || "knowledge_base",
          confidence: 1.0,
          access_count: 0,
          last_accessed: now,
          created_at: now,
          agent_id: "default",
        };
        this.vertices.set(`memories/${key}`, memory);

        // Tags become Entity vertices with edges
        const tags = Array.isArray(entry.tags) ? entry.tags : [entry.tags].filter(Boolean);
        for (const tag of tags) {
          const tagKey = `tag_${tag.toLowerCase().replace(/[^a-z0-9_-]/g, "_")}`;
          if (!this.vertices.has(`entities/${tagKey}`)) {
            this.vertices.set(`entities/${tagKey}`, {
              _key: tagKey,
              type: "entity",
              name: tag,
              entity_type: "tag",
              created_at: now,
              agent_id: "default",
            });
          }
          // Edge: tag → tagged_in → memory
          this.edges.push({
            _from: `entities/${tagKey}`,
            _to: `memories/${key}`,
            relation: "tagged_in",
            created_at: now,
          });
        }

        // Title-based entity
        if (entry.title && typeof entry.title === "string") {
          const titleKey = `title_${entry.title.toLowerCase().replace(/[^a-z0-9_-]/g, "_").slice(0, 64)}`;
          if (!this.vertices.has(`entities/${titleKey}`)) {
            this.vertices.set(`entities/${titleKey}`, {
              _key: titleKey,
              type: "entity",
              name: entry.title,
              entity_type: "concept",
              created_at: now,
              agent_id: "default",
            });
          }
          this.edges.push({
            _from: `entities/${titleKey}`,
            _to: `memories/${key}`,
            relation: "describes",
            created_at: now,
          });
        }
      }

      // Build dependency edges between theorems
      this.buildDependencyEdges(raw, now);
    } catch (e) {
      console.warn("[FileGraphEngine] Could not load KB:", (e as Error).message);
    }
  }

  /** Connect theorems that share tags or reference each other. */
  private buildDependencyEdges(raw: any[], now: string) {
    const theorems = raw.filter((e: any) => e.status === "verified_conscious_truth");
    for (let i = 0; i < theorems.length; i++) {
      for (let j = i + 1; j < theorems.length; j++) {
        const a = theorems[i];
        const b = theorems[j];
        const sharedTags = (a.tags || []).filter((t: string) => (b.tags || []).includes(t));
        if (sharedTags.length > 0) {
          const keyA = `memories/${a.id || this.sha1(a.title || "")}`;
          const keyB = `memories/${b.id || this.sha1(b.title || "")}`;
          if (this.vertices.has(keyA) && this.vertices.has(keyB)) {
            this.edges.push({
              _from: keyA,
              _to: keyB,
              relation: "shares_tag",
              weight: sharedTags.length,
              created_at: now,
            });
          }
        }
      }
    }
  }

  private sha1(str: string): string {
    let hash = 0;
    for (let i = 0; i < str.length; i++) {
      const char = str.charCodeAt(i);
      hash = ((hash << 5) - hash) + char;
      hash |= 0;
    }
    return Math.abs(hash).toString(16).slice(0, 16);
  }

  // ── Query API ──

  getVertex(id: string): Vertex | undefined {
    return this.vertices.get(id);
  }

  getEdges(from?: string, to?: string, relation?: string): Edge[] {
    return this.edges.filter(e => {
      if (from && e._from !== from) return false;
      if (to && e._to !== to) return false;
      if (relation && e.relation !== relation) return false;
      return true;
    });
  }

  /** BFS traversal from a vertex. */
  traverse(startId: string, maxHops: number = 2): { vertices: Vertex[]; edges: Edge[] } {
    const visited = new Set<string>();
    const resultVerts: Vertex[] = [];
    const resultEdges: Edge[] = [];
    let frontier = [startId];
    visited.add(startId);

    for (let hop = 0; hop < maxHops && frontier.length > 0; hop++) {
      const nextFrontier: string[] = [];
      for (const f of frontier) {
        const outEdges = this.edges.filter(e => e._from === f);
        for (const e of outEdges) {
          if (!visited.has(e._to)) {
            visited.add(e._to);
            const v = this.vertices.get(e._to);
            if (v) resultVerts.push(v);
            resultEdges.push(e);
            nextFrontier.push(e._to);
          }
        }
        const inEdges = this.edges.filter(e => e._to === f);
        for (const e of inEdges) {
          if (!visited.has(e._from)) {
            visited.add(e._from);
            const v = this.vertices.get(e._from);
            if (v) resultVerts.push(v);
            resultEdges.push(e);
            nextFrontier.push(e._from);
          }
        }
      }
      frontier = nextFrontier;
    }

    // Include the start vertex
    const startV = this.vertices.get(startId);
    if (startV) resultVerts.unshift(startV);

    return { vertices: resultVerts, edges: resultEdges };
  }

  /** Cosine similarity search over memory content (keyword-based fallback). */
  search(query: string, topK: number = 5): { vertex: Memory; score: number }[] {
    const q = query.toLowerCase();
    const qWords = q.split(/\s+/).filter(w => w.length > 2);

    const scored: { vertex: Memory; score: number }[] = [];
    for (const [, v] of this.vertices) {
      if (v.type !== "memory") continue;
      const m = v as Memory;
      const tagStr = Array.isArray(m.tags) ? m.tags.join(" ") : (m.tags || "");
      const text = `${m.content} ${tagStr} ${m.source}`.toLowerCase();
      let score = 0;
      for (const word of qWords) {
        if (text.includes(word)) score += 1;
      }
      if (score > 0) {
        // Normalize by query length and title match bonus
        const titleWords = (m.tags || []).join(" ").toLowerCase();
        const titleBonus = qWords.filter(w => titleWords.includes(w)).length * 0.5;
        scored.push({ vertex: m, score: (score + titleBonus) / qWords.length });
      }
    }

    return scored.sort((a, b) => b.score - a.score).slice(0, topK);
  }

  /** Get all vertices of a given type. */
  getVerticesByType(type: Vertex["type"]): Vertex[] {
    const result: Vertex[] = [];
    for (const [, v] of this.vertices) {
      if (v.type === type) result.push(v);
    }
    return result;
  }

  /** Get the count of total vertices and edges. */
  stats(): { vertices: number; edges: number; memories: number; entities: number } {
    let memories = 0, entities = 0;
    for (const [, v] of this.vertices) {
      if (v.type === "memory") memories++;
      if (v.type === "entity") entities++;
    }
    return { vertices: this.vertices.size, edges: this.edges.length, memories, entities };
  }
}

// ══════════════════════════════════════════════════════════════════════
// DIGITAL BRAIN
// ══════════════════════════════════════════════════════════════════════

export class DigitalBrain {
  private config: BrainConfig;
  private fileEngine: FileGraphEngine | null = null;
  private arangoEngine: ArangoGraphEngine | null = null;

  constructor(config: BrainConfig = { backend: "file", embedPath: "knowledge_base.json" }) {
    this.config = config;
    if (config.backend === "file") {
      this.fileEngine = new FileGraphEngine(config.embedPath || "knowledge_base.json");
    } else if (config.backend === "arangodb") {
      this.arangoEngine = new ArangoGraphEngine();
    }
  }

  // ── Store ──────────────────────────────────────────────────────────────

  async store(memory: Omit<Memory, "_key" | "created_at" | "access_count" | "last_accessed">): Promise<string> {
    const now = new Date().toISOString();
    const key = this.sha1(`${memory.agent_id}:${memory.content}`).slice(0, 16);
    const doc: Memory = {
      ...memory,
      _key: key,
      created_at: now,
      access_count: 0,
      last_accessed: now,
    } as Memory;

    if (this.fileEngine) {
      this.fileEngine["vertices"].set(`memories/${key}`, doc);
    }
    // TODO: ArangoDB mode — single atomic write
    return key;
  }

  // ── Search ─────────────────────────────────────────────────────────────

  async search(query: string, topK: number = 5, memoryType?: string): Promise<{ memory: any; score: number; neighbors: any[] }[]> {
    if (this.arangoEngine) {
      return this.arangoEngine.search(query, topK);
    }
    if (!this.fileEngine) return [];
    const results = this.fileEngine.search(query, topK);

    return results
      .filter(r => !memoryType || r.vertex.memory_type === memoryType)
      .map(r => {
        const graph = this.fileEngine!.traverse(`memories/${r.vertex._key}`, 1);
        return {
          memory: r.vertex,
          score: r.score,
          neighbors: graph.vertices.filter(v => v._key !== r.vertex._key),
        };
      });
  }

  // ── Graph traversal ────────────────────────────────────────────────────

  traverse(startKey: string, maxHops: number = 2): { vertices: Vertex[]; edges: Edge[] } {
    if (!this.fileEngine) return { vertices: [], edges: [] };
    return this.fileEngine.traverse(`memories/${startKey}`, maxHops);
  }

  async traverseEntity(entityKey: string, maxHops: number = 2): Promise<{ vertices: any[]; edges: Edge[] }> {
    if (this.arangoEngine) {
      return this.arangoEngine.traverse(`entities/${entityKey}`, maxHops);
    }
    if (!this.fileEngine) return { vertices: [], edges: [] };
    return this.fileEngine.traverse(`entities/${entityKey}`, maxHops);
  }

  // ── Entity queries ─────────────────────────────────────────────────────

  async getEntity(name: string): Promise<any> {
    if (this.arangoEngine) {
      return this.arangoEngine.getEntity(name);
    }
    if (!this.fileEngine) return undefined;
    const key = `tag_${name.toLowerCase().replace(/[^a-z0-9_-]/g, "_")}`;
    const v = this.fileEngine.getVertex(`entities/${key}`);
    return v?.type === "entity" ? v as any : undefined;
  }

  getMemoriesByTag(tag: string): Memory[] {
    if (!this.fileEngine) return [];
    const key = `tag_${tag.toLowerCase().replace(/[^a-z0-9_-]/g, "_")}`;
    const edges = this.fileEngine.getEdges(`entities/${key}`, undefined, "tagged_in");
    return edges
      .map(e => this.fileEngine!.getVertex(e._to))
      .filter(v => v && v.type === "memory")
      .map(v => v as Memory);
  }

  /** Get the full graph neighborhood of a query. */
  async queryGraph(query: string, topK: number = 3, maxHops: number = 1): Promise<{
    results: { memory: any; score: number; neighbors: any[] }[];
    graph: { vertices: any[]; edges: Edge[] };
  }> {
    if (this.arangoEngine) {
      return this.arangoEngine.queryGraph(query, topK, maxHops);
    }
    const results = await this.search(query, topK);
    const allVerts = new Map<string, any>();
    const allEdges: Edge[] = [];

    for (const r of results) {
      const g = this.traverse(r.memory._key!, maxHops);
      for (const v of g.vertices) allVerts.set(v._id || v._key || "", v);
      for (const e of g.edges) allEdges.push(e);
    }

    return {
      results,
      graph: { vertices: Array.from(allVerts.values()), edges: allEdges },
    };
  }

  // ── Stats ──────────────────────────────────────────────────────────────

  async stats(): Promise<{ vertices: number; edges: number; memories: number; entities: number }> {
    if (this.arangoEngine) {
      return this.arangoEngine.stats();
    }
    if (this.fileEngine) {
      return this.fileEngine.stats();
    }
    return { vertices: 0, edges: 0, memories: 0, entities: 0 };
  }

  private sha1(str: string): string {
    let hash = 0;
    for (let i = 0; i < str.length; i++) {
      const char = str.charCodeAt(i);
      hash = ((hash << 5) - hash) + char;
      hash |= 0;
    }
    return Math.abs(hash).toString(16).slice(0, 16);
  }
}

export default DigitalBrain;

// ══════════════════════════════════════════════════════════════════════
// ARANGODB GRAPH ENGINE
// ══════════════════════════════════════════════════════════════════════

class ArangoGraphEngine {
  private baseUrl: string;
  private dbName: string;

  constructor(baseUrl: string = "http://localhost:8529", dbName: string = "brain_graph") {
    this.baseUrl = baseUrl;
    this.dbName = dbName;
  }

  private get dbUrl(): string {
    return `${this.baseUrl}/_db/${this.dbName}`;
  }

  private async aql(query: string, bindVars: Record<string, any> = {}): Promise<any[]> {
    const resp = await fetch(`${this.baseUrl}/_db/${this.dbName}/_api/cursor`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ query, bindVars }),
    });
    const data = await resp.json() as any;
    return data.result || [];
  }

  async search(query: string, topK: number = 5): Promise<any[]> {
    const q = query.toLowerCase();
    const qWords = q.split(/\s+/).filter((w: string) => w.length > 2);
    
    // AQL: keyword search + graph neighbors in one query
    const aqlQuery = `
      FOR m IN memories
        LET score = ${qWords.map((w: string, i: number) => 
          `(CONTAINS(LOWER(m.content), "${w}") ? ${1/qWords.length} : 0) + (CONTAINS(LOWER(m.title), "${w}") ? ${0.5/qWords.length} : 0)`
        ).join(" + ")}
        FILTER score > 0
        SORT score DESC
        LIMIT @topK
        RETURN {
          memory: m,
          score: score,
          neighbors: (FOR v IN 1..1 ANY m._id entity_edges RETURN DISTINCT v)
        }
    `;
    
    return this.aql(aqlQuery, { topK });
  }

  async traverse(startId: string, maxHops: number = 2): Promise<{ vertices: any[]; edges: any[] }> {
    const result = await this.aql(`
      LET start = DOCUMENT(@startId)
      LET vertices = (FOR v IN 1..@maxHops ANY @startId entity_edges OPTIONS {bfs: true, uniqueVertices: "path"} RETURN DISTINCT v)
      LET edges = (FOR v, e IN 1..@maxHops ANY @startId entity_edges OPTIONS {bfs: true} RETURN DISTINCT e)
      RETURN { start: start, vertices: vertices, edges: edges }
    `, { startId, maxHops });
    
    if (result.length === 0) return { vertices: [], edges: [] };
    return { vertices: result[0].vertices || [], edges: result[0].edges || [] };
  }

  async getEntity(name: string): Promise<any> {
    const key = `tag_${name.toLowerCase().replace(/[^a-z0-9_-]/g, "_")}`;
    const result = await this.aql(`RETURN DOCUMENT("entities/${key}")`);
    return result[0] || null;
  }

  async getMemoriesByTag(tag: string): Promise<any[]> {
    const key = `tag_${tag.toLowerCase().replace(/[^a-z0-9_-]/g, "_")}`;
    return this.aql(`
      FOR v IN 1..1 OUTBOUND "entities/${key}" entity_edges
        FILTER v.type == "memory" OR IS_DOCUMENT(v)
        RETURN v
    `);
  }

  async stats(): Promise<{ vertices: number; edges: number; memories: number; entities: number }> {
    const result = await this.aql(`
      LET mems = LENGTH(FOR m IN memories RETURN 1)
      LET ents = LENGTH(FOR e IN entities RETURN 1)
      LET edgs = LENGTH(FOR e IN entity_edges RETURN 1)
      RETURN { memories: mems, entities: ents, edges: edgs }
    `);
    const s = result[0] || { memories: 0, entities: 0, edges: 0 };
    return {
      vertices: s.memories + s.entities,
      edges: s.edges,
      memories: s.memories,
      entities: s.entities,
    };
  }

  async queryGraph(query: string, topK: number = 3, maxHops: number = 1): Promise<any> {
    const results = await this.search(query, topK);
    const allVerts = new Map<string, any>();
    const allEdges: any[] = [];
    
    for (const r of results) {
      allVerts.set(r.memory._id, r.memory);
      for (const n of (r.neighbors || [])) {
        allVerts.set(n._id, n);
      }
    }
    
    // Get edges between vertices
    const ids = Array.from(allVerts.keys());
    if (ids.length > 0) {
      const edges = await this.aql(`
        FOR e IN entity_edges
          FILTER e._from IN @ids AND e._to IN @ids
          RETURN e
      `, { ids });
      allEdges.push(...edges);
    }
    
    return {
      results: results.map((r: any) => ({
        memory: r.memory,
        score: r.score,
        neighbors: (r.neighbors || []).filter((n: any) => n._id !== r.memory._id),
      })),
      graph: { vertices: Array.from(allVerts.values()), edges: allEdges },
    };
  }
}
