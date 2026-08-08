import { useCallback, useEffect, useMemo, useRef, useState } from 'react';
import ForceGraph3D from 'react-force-graph-3d';
import HolographicView from './HolographicView';
import './App.css';

const KIND_COLORS = {
  theorem: '#ff4d6d',
  definition: '#00ffaa',
  def: '#00ffaa',
  structure: '#4dabf7',
  inductive: '#c77dff',
  axiom: '#ffd43b',
  opaque: '#8e8e8e',
  other: '#aab0bc',
};

const SOURCE_MODES = {
  lean: {
    label: 'Lean DAG',
    files: ['/proof_graph.json'],
    prefixFilter: null,
  },
  arango: {
    label: 'Arango graph',
    files: ['/graph.json'],
    prefixFilter: null,
  },
  focused: {
    label: 'NonAbelian/Thermodynamic',
    files: ['/proof_graph.json'],
    prefixFilter: ['NonAbelian', 'Thermodynamic'],
  },
  holographic: {
    label: 'Holographic JWST Stream',
    isHolographic: true,
  },
};

const normalizeKind = (kind) => (kind ?? 'other').toString().toLowerCase();
const nodeName = (node) => node?.lean_name || node?.name || node?.label || node?.id || '';

const nodeId = (value) => {
  if (value && typeof value === 'object') {
    return value.id ?? value._id ?? value.name ?? value._key ?? null;
  }
  return value ?? null;
};

const matchesPrefix = (name, prefixes) => {
  if (!prefixes?.length) return true;
  return prefixes.some((prefix) => name.startsWith(prefix));
};

function App() {
  const [sourceMode, setSourceMode] = useState('lean');
  const [rawGraph, setRawGraph] = useState({ nodes: [], links: [] });
  const [hoverNode, setHoverNode] = useState(null);
  const [selectedNode, setSelectedNode] = useState(null);
  const [query, setQuery] = useState('');
  const fgRef = useRef(null);
  const didFitRef = useRef(false);

  const normalizeGraph = useCallback((data) => {
    if (Array.isArray(data)) {
      const nodes = data.map((entry) => {
        const name = entry.name ?? entry.lean_name ?? entry.id;
        return {
          ...entry,
          id: name,
          name,
          kind: normalizeKind(entry.kind),
          type: entry.kind,
        };
      });

      const links = data.flatMap((entry) =>
        (entry.deps ?? []).map((dep) => ({
          source: dep,
          target: entry.name,
          id: `${dep}->${entry.name}`,
        }))
      );

      return { nodes, links };
    }

    const nodes = (data?.nodes ?? []).map((node, index) => {
      const id = node.id ?? node._id ?? node.lean_name ?? node.name ?? `node-${index}`;
      return {
        ...node,
        id,
        name: node.name ?? node.lean_name ?? node.label ?? id,
        kind: normalizeKind(node.kind),
      };
    });

    const links = (data?.links ?? []).map((link, index) => {
      const source = nodeId(link.source ?? link._from ?? link.from ?? `source-${index}`);
      const target = nodeId(link.target ?? link._to ?? link.to ?? `target-${index}`);
      return {
        ...link,
        source,
        target,
        id: link.id ?? `${source}->${target}`,
      };
    });

    return { nodes, links };
  }, []);

  useEffect(() => {
    let cancelled = false;
    const mode = SOURCE_MODES[sourceMode] ?? SOURCE_MODES.lean;
    
    if (mode.isHolographic) return;

    const load = async () => {
      for (const endpoint of mode.files) {
        try {
          const response = await fetch(endpoint);
          if (!response.ok) continue;
          const data = await response.json();
          if (!cancelled) {
            setRawGraph(normalizeGraph(data));
          }
          return;
        } catch {
          // try the next endpoint
        }
      }
      if (!cancelled) setRawGraph({ nodes: [], links: [] });
    };

    load();
    return () => {
      cancelled = true;
    };
  }, [normalizeGraph, sourceMode]);

  const sourceModeMeta = SOURCE_MODES[sourceMode] ?? SOURCE_MODES.lean;

  const filteredGraph = useMemo(() => {
    const prefixes = sourceModeMeta.prefixFilter;
    if (!prefixes?.length) return rawGraph;

    const nodes = rawGraph.nodes.filter((node) => matchesPrefix(nodeName(node), prefixes));
    const allowed = new Set(nodes.map((node) => node.id));
    const links = rawGraph.links.filter((link) => {
      const source = nodeId(link.source);
      const target = nodeId(link.target);
      return allowed.has(source) && allowed.has(target);
    });

    return { nodes, links };
  }, [rawGraph, sourceModeMeta.prefixFilter]);

  const adjacency = useMemo(() => {
    const map = new Map();
    const add = (a, b) => {
      if (!a || !b) return;
      if (!map.has(a)) map.set(a, new Set());
      map.get(a).add(b);
    };

    for (const link of filteredGraph.links) {
      const source = nodeId(link.source);
      const target = nodeId(link.target);
      add(source, target);
      add(target, source);
    }

    return map;
  }, [filteredGraph.links]);

  const degreeMap = useMemo(() => {
    const map = new Map();
    for (const link of filteredGraph.links) {
      const source = nodeId(link.source);
      const target = nodeId(link.target);
      if (source) map.set(source, (map.get(source) ?? 0) + 1);
      if (target) map.set(target, (map.get(target) ?? 0) + 1);
    }
    return map;
  }, [filteredGraph.links]);

  const kindCounts = useMemo(() => {
    const counts = {};
    for (const node of filteredGraph.nodes) {
      const kind = normalizeKind(node.kind);
      counts[kind] = (counts[kind] ?? 0) + 1;
    }
    return counts;
  }, [filteredGraph.nodes]);

  const searchQuery = query.trim().toLowerCase();

  const searchHits = useMemo(() => {
    if (!searchQuery) return [];
    return filteredGraph.nodes.filter((node) => {
      const haystack = [nodeName(node), node.kind, node.type, node.module, node.namespace]
        .filter(Boolean)
        .join(' ')
        .toLowerCase();
      return haystack.includes(searchQuery);
    });
  }, [filteredGraph.nodes, searchQuery]);

  const largeGraph = filteredGraph.nodes.length > 3000;

  const condensedIds = useMemo(() => {
    if (searchQuery || !largeGraph) return null;
    const sorted = [...filteredGraph.nodes].sort(
      (a, b) => (degreeMap.get(b.id) ?? 0) - (degreeMap.get(a.id) ?? 0)
    );
    const ids = new Set();
    sorted.slice(0, 400).forEach((node) => {
      ids.add(node.id);
      adjacency.get(node.id)?.forEach((neighbor) => ids.add(neighbor));
    });
    return ids;
  }, [adjacency, degreeMap, filteredGraph.nodes, largeGraph, searchQuery]);

  const visibleIds = useMemo(() => {
    if (searchQuery) {
      const ids = new Set();
      for (const node of searchHits) {
        ids.add(node.id);
        adjacency.get(node.id)?.forEach((neighbor) => ids.add(neighbor));
      }
      return ids;
    }
    return condensedIds;
  }, [adjacency, condensedIds, searchHits, searchQuery]);

  const visibleGraph = useMemo(() => {
    if (!visibleIds) return filteredGraph;
    return {
      nodes: filteredGraph.nodes.filter((node) => visibleIds.has(node.id)),
      links: filteredGraph.links.filter((link) => {
        const source = nodeId(link.source);
        const target = nodeId(link.target);
        return visibleIds.has(source) && visibleIds.has(target);
      }),
    };
  }, [filteredGraph, visibleIds]);

  const activeIds = useMemo(() => {
    const ids = new Set();
    const seed = selectedNode || hoverNode;
    if (seed?.id) {
      ids.add(seed.id);
      adjacency.get(seed.id)?.forEach((neighbor) => ids.add(neighbor));
    }
    for (const node of searchHits) {
      ids.add(node.id);
      adjacency.get(node.id)?.forEach((neighbor) => ids.add(neighbor));
    }
    return ids;
  }, [adjacency, hoverNode, searchHits, selectedNode]);

  const focusNode = useCallback((node) => {
    if (!node || !fgRef.current) return;
    const x = node.x ?? 0;
    const y = node.y ?? 0;
    const z = node.z ?? 0;
    const radius = Math.max(1, Math.hypot(x, y, z));
    const distance = 90;
    const ratio = 1 + distance / radius;

    fgRef.current.cameraPosition(
      { x: x * ratio, y: y * ratio, z: z * ratio },
      node,
      1800
    );
  }, []);

  const handleNodeClick = useCallback((node) => {
    setSelectedNode(node);
    focusNode(node);
  }, [focusNode]);

  const handleSearchSubmit = useCallback((event) => {
    event.preventDefault();
    const firstMatch = searchHits[0];
    if (firstMatch) {
      setSelectedNode(firstMatch);
      focusNode(firstMatch);
    }
  }, [focusNode, searchHits]);

  const switchSourceMode = useCallback((mode) => {
    setSourceMode(mode);
    setSelectedNode(null);
    setHoverNode(null);
    setQuery('');
    didFitRef.current = false;
  }, []);

  useEffect(() => {
    if (!didFitRef.current && visibleGraph.nodes.length > 0 && fgRef.current) {
      didFitRef.current = true;
      fgRef.current.zoomToFit(700, 70);
    }
  }, [visibleGraph.nodes.length]);

  const detailNode = selectedNode || hoverNode || searchHits[0] || null;
  const visibleCount = visibleGraph.nodes.length;
  const totalCount = filteredGraph.nodes.length;

  const getNodeColor = useCallback((node) => {
    const kind = normalizeKind(node.kind);
    const base = KIND_COLORS[kind] ?? KIND_COLORS.other;
    if (activeIds.size === 0) return base;
    return activeIds.has(node.id) ? base : 'rgba(170, 176, 188, 0.14)';
  }, [activeIds]);

  const getLinkColor = useCallback((link) => {
    if (activeIds.size === 0) return 'rgba(255, 255, 255, 0.14)';
    const source = nodeId(link.source);
    const target = nodeId(link.target);
    return activeIds.has(source) && activeIds.has(target)
      ? 'rgba(120, 255, 230, 0.34)'
      : 'rgba(255, 255, 255, 0.04)';
  }, [activeIds]);

  const resetView = () => {
    setQuery('');
    setSelectedNode(null);
    setHoverNode(null);
    didFitRef.current = false;
    setTimeout(() => fgRef.current?.zoomToFit?.(700, 70), 0);
  };

  return (
    <div className="app-shell">
      <div className="overlay">
        <div className="panel">
          <div className="title">Goutev Graph Atlas</div>
          <div className="subtitle">Lean DAG / Arango graph / focused subgraph</div>

          <div className="mode-switcher">
            {Object.entries(SOURCE_MODES).map(([key, mode]) => (
              <button
                key={key}
                type="button"
                className={`mode-btn ${sourceMode === key ? 'active' : ''}`}
                onClick={() => switchSourceMode(key)}
              >
                {mode.label}
              </button>
            ))}
          </div>

          <form className="search-form" onSubmit={handleSearchSubmit}>
            <input
              className="search-input"
              value={query}
              onChange={(e) => setQuery(e.target.value)}
              placeholder="Search theorem, module, kind..."
              spellCheck={false}
            />
            <button className="btn btn-primary" type="submit">Focus</button>
            <button className="btn" type="button" onClick={resetView}>Reset</button>
          </form>

          <div className="stats-grid">
            <div className="stat-box">
              <div className="stat-value">{visibleCount}</div>
              <div className="stat-label">Visible nodes</div>
            </div>
            <div className="stat-box">
              <div className="stat-value">{filteredGraph.links.length}</div>
              <div className="stat-label">Links</div>
            </div>
          </div>

          <div className="kind-chips">
            {Object.entries(kindCounts)
              .sort((a, b) => b[1] - a[1])
              .slice(0, 6)
              .map(([kind, count]) => (
                <span key={kind} className={`chip kind-${kind}`}>
                  {kind}: {count}
                </span>
              ))}
          </div>

          <div className="node-info">
            {detailNode ? (
              <>
                <div className="node-name" style={{ color: getNodeColor(detailNode) }}>
                  {nodeName(detailNode)}
                </div>
                <div className="node-meta">Kind: {detailNode.kind ?? 'other'}</div>
                {detailNode.type && <div className="node-meta">Type: {detailNode.type}</div>}
                <div className="node-meta">Degree: {degreeMap.get(detailNode.id) ?? 0}</div>
                {detailNode.deps && <div className="node-meta">Deps: {detailNode.deps.length}</div>}
              </>
            ) : (
              <span className="node-placeholder">Hover or search to inspect a node.</span>
            )}
          </div>

          <div className="legend">
            <div className="legend-item"><span className="dot theorem"></span> Theorem</div>
            <div className="legend-item"><span className="dot definition"></span> Definition</div>
            <div className="legend-item"><span className="dot structure"></span> Structure</div>
            <div className="legend-item"><span className="dot axiom"></span> Axiom / Opaque / Other</div>
          </div>

          <div className="status-line">
            Source: {sourceModeMeta.label}
            {' '}• Showing {visibleCount}/{totalCount}
          </div>
        </div>
      </div>

      <ForceGraph3D
        ref={fgRef}
        graphData={visibleGraph}
        nodeLabel={(node) => {
          const pieces = [nodeName(node), `Kind: ${node.kind ?? 'other'}`];
          if (node.type) pieces.push(`Type: ${node.type}`);
          pieces.push(`Degree: ${degreeMap.get(node.id) ?? 0}`);
          return pieces.join('\n');
        }}
        nodeColor={getNodeColor}
        nodeRelSize={5}
        nodeVal={(node) => (degreeMap.get(node.id) ?? 1) + (activeIds.has(node.id) ? 6 : 0)}
        linkWidth={(link) => {
          if (activeIds.size === 0) return 1;
          const source = nodeId(link.source);
          const target = nodeId(link.target);
          return activeIds.has(source) && activeIds.has(target) ? 2 : 0.3;
        }}
        linkColor={getLinkColor}
        linkDirectionalParticles={activeIds.size ? 3 : 1}
        linkDirectionalParticleWidth={1.4}
        linkDirectionalParticleSpeed={0.003}
        onNodeHover={setHoverNode}
        onNodeClick={handleNodeClick}
        backgroundColor="#00000000"
        enableNodeDrag={false}
      />
      {sourceModeMeta.isHolographic && <HolographicView />}
    </div>
  );
}

export default App;
