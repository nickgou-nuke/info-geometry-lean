// Bootstrap the InfoGeometry GraphRAG KM/hash overlay.
//
// This script intentionally extends the existing ExprArangoExport surface:
//   ig_nodes / ig_edges
// It does not replace the Lean-owned expression/declaration graph.  The new
// collections are audit and retrieval overlays for concepts, public reasoning
// lineage, build snapshots, and content-addressable hash records.

"use strict";

const db = require("@arangodb").db;

const vertexCollections = [
  "ig_nodes",
  "ig_hashes",
  "ig_concepts",
  "ig_principles",
  "ig_phases",
  "ig_builds"
];

const edgeCollections = ["ig_edges"];

function ensureCollection(name, edge) {
  if (!db._collection(name)) {
    if (edge) {
      db._createEdgeCollection(name);
    } else {
      db._create(name);
    }
  }
}

function ensurePersistentIndex(collectionName, fields, opts = {}) {
  const collection = db._collection(collectionName);
  if (!collection) {
    throw new Error("missing collection: " + collectionName);
  }
  collection.ensureIndex(Object.assign({ type: "persistent", fields }, opts));
}

function ensureHashSeedRows() {
  const concepts = db._collection("ig_concepts");
  const principles = db._collection("ig_principles");
  const phases = db._collection("ig_phases");

  const conceptRows = [
    {
      _key: "concept_projector_split",
      kind: "Concept",
      label: "Projector split",
      slug: "projector-split",
      domain: "DrazinLightConeDictionary",
      status: "seed",
      description: "Complementary idempotent projectors P and P0 used to split regular and defect sectors."
    },
    {
      _key: "concept_drazin_lightcone_arrow",
      kind: "Concept",
      label: "Drazin lightcone arrow",
      slug: "drazin-lightcone-arrow",
      domain: "DrazinLightConeDictionary",
      status: "seed",
      aliases: ["uPlus", "uMinus", "Peirce off-diagonal arrow"],
      description: "Off-diagonal projector channel P X P0 or P0 X P."
    },
    {
      _key: "concept_o55_affine_closure",
      kind: "Concept",
      label: "Affine O55 closure",
      slug: "affine-o55-closure",
      domain: "HestenesAffineO55ClosureBridge",
      status: "seed",
      description: "Witness-gated affine D4 closure requiring a supplied O(5,5) / Cl(5,5) backend certificate."
    },
    {
      _key: "concept_typeiii_omega_readout",
      kind: "Concept",
      label: "Type III Omega readout",
      slug: "typeiii-omega-readout",
      domain: "StandardFormOmegaVolumeBridge",
      status: "seed",
      description: "Trace replacement by normalized Omega expectation in the standard-form/Krein lane."
    }
  ];

  for (const row of conceptRows) {
    concepts.save(row, { overwriteMode: "update" });
  }

  const principleRows = [
    {
      _key: "principle_lean_is_authority",
      kind: "ArchitecturalPrinciple",
      label: "Lean is proof authority",
      severity: "hard",
      rule: "Arango GraphRAG is a derived navigation and audit layer. Lean source and kernel certificates remain proof authority."
    },
    {
      _key: "principle_no_trace_det_typeiii",
      kind: "ArchitecturalPrinciple",
      label: "No trace/determinant in Type III lane",
      severity: "hard",
      rule: "Type III layers must use modular weights, Connes cocycles, standard-form cone vectors, or supplied readout witnesses. Trace/determinant claims require explicit finite/core/semifinite witness."
    },
    {
      _key: "principle_hashes_are_not_vectors",
      kind: "ArchitecturalPrinciple",
      label: "Cryptographic hashes are addresses, not cosine vectors",
      severity: "hard",
      rule: "Use exact de Bruijn hashes for equality/content addressing. Use deterministic logicVector feature hashes over sub-expression multisets for approximate theorem discovery."
    },
    {
      _key: "principle_witness_gated_affine_o55",
      kind: "ArchitecturalPrinciple",
      label: "Affine O55 closure is witness-gated",
      severity: "hard",
      rule: "Cl(5,5)/O(5,5) affine closure claims require explicit backend certificates; the bridge only records local consequences."
    }
  ];

  for (const row of principleRows) {
    principles.save(row, { overwriteMode: "update" });
  }

  const phaseRows = [
    {
      _key: "phase_hestenes_krein_arithmetic_closure",
      kind: "Phase",
      label: "Hestenes-Krein arithmetic closure",
      date: "2026-05-13",
      status: "seed",
      summary: "Drazin/Hodge, Souriau, KMS, Hestenes-Krein, Connes-Wilson, Moebius, D4/Hurwitz, CPT/O(N,N), and affine O55 sockets were installed as theorem-safe layers."
    }
  ];

  for (const row of phaseRows) {
    phases.save(row, { overwriteMode: "update" });
  }
}

function ensureGraph() {
  const graphName = "InfoGeometryTheoryGraph";
  const graphs = require("@arangodb/general-graph");
  if (!graphs._exists(graphName)) {
    graphs._create(graphName, [
      graphs._relation("ig_edges", vertexCollections, vertexCollections)
    ]);
  }
}

for (const name of vertexCollections) {
  ensureCollection(name, false);
}
for (const name of edgeCollections) {
  ensureCollection(name, true);
}

ensurePersistentIndex("ig_nodes", ["graphKind"]);
ensurePersistentIndex("ig_nodes", ["name"]);
ensurePersistentIndex("ig_nodes", ["decl"]);
ensurePersistentIndex("ig_nodes", ["module"]);
ensurePersistentIndex("ig_nodes", ["path"]);
ensurePersistentIndex("ig_nodes", ["deBruijnHash"]);
ensurePersistentIndex("ig_nodes", ["alphaLocalHash"]);
ensurePersistentIndex("ig_nodes", ["shapeHash"]);
ensurePersistentIndex("ig_nodes", ["typeHash"]);
ensurePersistentIndex("ig_nodes", ["valueHash"]);

ensurePersistentIndex("ig_hashes", ["hash"], { unique: true, sparse: false });
ensurePersistentIndex("ig_hashes", ["hashKind"]);
ensurePersistentIndex("ig_hashes", ["normalization"]);
ensurePersistentIndex("ig_hashes", ["quality"]);

ensurePersistentIndex("ig_concepts", ["slug"], { unique: true, sparse: true });
ensurePersistentIndex("ig_concepts", ["label"]);
ensurePersistentIndex("ig_concepts", ["domain"]);
ensurePersistentIndex("ig_concepts", ["status"]);

ensurePersistentIndex("ig_principles", ["severity"]);
ensurePersistentIndex("ig_principles", ["label"]);

ensurePersistentIndex("ig_phases", ["date"]);
ensurePersistentIndex("ig_phases", ["status"]);

ensurePersistentIndex("ig_builds", ["gitRev"]);
ensurePersistentIndex("ig_builds", ["status"]);
ensurePersistentIndex("ig_builds", ["command"]);

ensurePersistentIndex("ig_edges", ["kind"]);
ensurePersistentIndex("ig_edges", ["_from"]);
ensurePersistentIndex("ig_edges", ["_to"]);
ensurePersistentIndex("ig_edges", ["hashRole"]);
ensurePersistentIndex("ig_edges", ["source"]);
ensurePersistentIndex("ig_edges", ["orientation"]);

ensureGraph();
ensureHashSeedRows();

return {
  ok: true,
  graph: "InfoGeometryTheoryGraph",
  vertexCollections,
  edgeCollections
};
