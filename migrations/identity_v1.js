/*
migrations/identity_v1.js

Identity Protocol v1 collections.

Stores measurable invariant-basin packets. Does not store mystical or
psychological claims; all fields are operational metrics/fingerprints.
*/

const db = require("@arangodb").db;

function ensureCollection(name) {
  const existing = db._collection(name);
  if (existing) return existing;
  return db._create(name);
}

function ensureEdgeCollection(name) {
  const existing = db._collection(name);
  if (existing) return existing;
  return db._createEdgeCollection(name);
}

const packets = ensureCollection("hive_majorana_identity_packets");
const basins = ensureCollection("hive_invariant_basins");
const links = ensureEdgeCollection("pulse_identity_link");
void links;

packets.ensureIndex({
  type: "persistent",
  fields: ["verdict"],
});

packets.ensureIndex({
  type: "persistent",
  fields: ["metrics.kappa"],
});

packets.ensureIndex({
  type: "persistent",
  fields: ["metrics.epsilon_majorana"],
});

packets.ensureIndex({
  type: "persistent",
  fields: ["created_at"],
});

packets.ensureIndex({
  type: "persistent",
  fields: ["packet_id"],
  unique: true,
});

packets.ensureIndex({
  type: "persistent",
  fields: ["episode_id"],
});

basins.ensureIndex({
  type: "persistent",
  fields: ["centroid_hash"],
  unique: true,
});

basins.ensureIndex({
  type: "persistent",
  fields: ["stability_score"],
});
