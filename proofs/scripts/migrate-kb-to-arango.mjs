#!/usr/bin/env node
/**
 * Migrate knowledge_base.json into ArangoDB brain_graph database.
 * Creates the full OpenClaw-style multi-model graph:
 *   - memories (vertices)
 *   - entities (vertices) — tags + titles
 *   - entity_edges (edges) — tagged_in, describes
 *   - memory_edges (edges) — shares_tag (between theorems)
 */

import { readFileSync } from "fs";
import { resolve, dirname } from "path";
import { fileURLToPath } from "url";

const __dirname = dirname(fileURLToPath(import.meta.url));
const BASE = "http://localhost:8529/_db/brain_graph";
const KB_PATH = resolve(__dirname, "..", "knowledge_base.json");

function hash(str) {
  let h = 0;
  for (let i = 0; i < (str || "").length; i++) {
    h = ((h << 5) - h) + str.charCodeAt(i);
    h |= 0;
  }
  return Math.abs(h).toString(16).slice(0, 12);
}

function getTags(entry) {
  return Array.isArray(entry.tags) ? entry.tags : (entry.tags ? [entry.tags] : []);
}

async function postDoc(collection, body) {
  const resp = await fetch(BASE + "/_api/document?collection=" + collection + "&overwrite=true", {
    method: "POST",
    headers: { "Content-Type": "application/json", "Accept": "application/json" },
    body: JSON.stringify(body)
  });
  return resp.json();
}

async function main() {
  const raw = JSON.parse(readFileSync(KB_PATH, "utf-8"));
  const now = new Date().toISOString();
  
  // Also get ArangoDB version for display
  const vresp = await fetch("http://localhost:8529/_api/version");
  const vdata = await vresp.json();
  console.log("ArangoDB:", vdata.server, vdata.version);
  console.log("Migrating", raw.length, "entries...");
  
  let memCount = 0, entCount = 0, edgeCount = 0;

  for (const entry of raw) {
    const key = entry.id || ("kb_" + hash(entry.title));
    const tags = getTags(entry);
    
    // Insert memory
    const memResult = await postDoc("memories", {
      _key: key,
      content: entry.content || "",
      memory_type: entry.status === "verified_conscious_truth" ? "theorem" : 
                   entry.status === "literature" ? "fact" : "note",
      tags: tags,
      source: entry.source || "knowledge_base",
      confidence: 1.0,
      access_count: 0,
      last_accessed: now,
      created_at: now,
      agent_id: "default",
      title: entry.title || ""
    });
    if (memResult._key) memCount++;
    
    // Tag entities + edges
    for (const tag of tags) {
      const tagKey = "tag_" + tag.toLowerCase().replace(/[^a-z0-9_-]/g, "_").slice(0, 64);
      await postDoc("entities", { _key: tagKey, name: tag, entity_type: "tag", created_at: now, agent_id: "default" });
      entCount++;
      await postDoc("entity_edges", { _from: "entities/" + tagKey, _to: "memories/" + key, relation: "tagged_in", created_at: now });
      edgeCount++;
    }
    
    // Title entity + edge
    if (entry.title) {
      const titleKey = "title_" + entry.title.toLowerCase().replace(/[^a-z0-9_-]/g, "_").slice(0, 64);
      await postDoc("entities", { 
        _key: titleKey, name: entry.title, entity_type: "concept",
        description: (entry.content || "").substring(0, 200),
        created_at: now, agent_id: "default" 
      });
      entCount++;
      await postDoc("entity_edges", { _from: "entities/" + titleKey, _to: "memories/" + key, relation: "describes", created_at: now });
      edgeCount++;
    }
    
    if (memCount % 20 === 0) console.log("  " + memCount + "/" + raw.length + " memories...");
  }
  
  // Dependency edges between verified theorems sharing tags
  console.log("Building dependency edges...");
  const theorems = raw.filter(e => e.status === "verified_conscious_truth");
  let depCount = 0;
  
  for (let i = 0; i < theorems.length; i++) {
    for (let j = i + 1; j < theorems.length; j++) {
      const a = theorems[i], b = theorems[j];
      const aTags = getTags(a), bTags = getTags(b);
      const shared = aTags.filter(t => bTags.includes(t));
      if (shared.length > 0) {
        const keyA = a.id || ("kb_" + hash(a.title));
        const keyB = b.id || ("kb_" + hash(b.title));
        await postDoc("entity_edges", { 
          _from: "memories/" + keyA, _to: "memories/" + keyB, 
          relation: "shares_tag", weight: shared.length, created_at: now 
        });
        depCount++;
      }
    }
  }
  
  // Drop the test doc
  await fetch(BASE + "/_api/document/memories/test_doc", { method: "DELETE" }).catch(() => {});
  
  console.log("\n✅ Migration complete!");
  console.log("  Memories:", memCount);
  console.log("  Entities:", entCount);
  console.log("  Tag edges:", edgeCount);
  console.log("  Dependency edges:", depCount);
  console.log("  Total edges:", edgeCount + depCount);
}

main().catch(console.error);
