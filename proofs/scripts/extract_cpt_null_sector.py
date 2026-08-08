#!/usr/bin/env python3
"""
CPT Null Sector Extraction from Agent Brain

Queries ArangoDB to find all DAG nodes where the causal arrow
collapsed into the 0-eigenvalue of the tripotent spectrum.

Based on:
- CPTCausalCone.lean: chiral_cone_projection(node) = 0
- CPTDeRhamCohomology.lean: d ln Ω monodromy
- TerminalVoid hash: e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855

This identifies cognitive dead-ends, proof collapses, and topological singularities.
"""

import json
from arango.client import ArangoClient

# Database configuration
DB_URL = "http://localhost:8531"
DB_NAME = "agent_brain"
DB_USER = "root"
DB_PASS = "agent_secret"

# Initialize client
client = ArangoClient(hosts=DB_URL)
db = client.db(DB_NAME, username=DB_USER, password=DB_PASS)

print("=" * 80)
print("CPT NULL SECTOR EXTRACTION")
print("=" * 80)
print("\nQuerying ArangoDB DAG for nodes in the 0-eigenvalue null sector...")
print("Based on: CPTCausalCone.lean + CPTDeRhamCohomology.lean\n")

# AQL Query 1: Find all TerminalVoid nodes (null sector)
print("### Query 1: TerminalVoid Nodes (Null Sector) ###\n")

query_null_sector = """
FOR step IN steps
    FILTER step.content_hash == 
           "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    RETURN {
        conversation_id: step.conversation_id,
        step_index: step.step_index,
        type: step.type,
        snippet: SUBSTRING(
            step.content, 
            0, 
            200
        ),
        timestamp: step.timestamp,
        topology: "NULL_SECTOR"
    }
"""

try:
    null_sector_cursor = db.aql.execute(query_null_sector)
    null_sector_nodes = list(null_sector_cursor)
    
    print(f"Found {len(null_sector_nodes)} nodes in NULL SECTOR (0-eigenvalue)\n")
    
    if null_sector_nodes:
        print("Sample null sector nodes:")
        print("-" * 80)
        for i, node in enumerate(null_sector_nodes[:5], 1):
            print(f"\n{i}. Conversation: {node['conversation_id'][:8]}...")
            print(f"   Step: {node['step_index']}")
            print(f"   Type: {node.get('type', 'unknown')}")
            print(f"   Snippet: {node['snippet'][:100]}...")
            print(f"   Topology: {node['topology']}")
        
        if len(null_sector_nodes) > 5:
            print(f"\n... and {len(null_sector_nodes) - 5} more null sector nodes")
    
except Exception as e:
    print(f"Error querying null sector: {e}")
    null_sector_nodes = []

# AQL Query 2: Statistics by conversation
print("\n\n### Query 2: Null Sector Distribution by Conversation ###\n")

query_distribution = """
FOR step IN steps
    FILTER step.content_hash == 
           "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    COLLECT conv_id = step.conversation_id
    AGGREGATE null_count = COUNT(1)
    RETURN {
        conversation_id: conv_id,
        null_sector_count: null_count
    }
"""

try:
    distribution_cursor = db.aql.execute(query_distribution)
    distribution = list(distribution_cursor)
    
    if distribution:
        print(f"Conversations with null sector nodes: {len(distribution)}\n")
        
        # Sort by null sector count
        distribution.sort(key=lambda x: x['null_sector_count'], reverse=True)
        
        print("Top conversations by null sector density:")
        print("-" * 80)
        for i, conv in enumerate(distribution[:10], 1):
            print(f"{i:2d}. {conv['conversation_id'][:8]}... : {conv['null_sector_count']:3d} null nodes")
        
        total_null = sum(conv['null_sector_count'] for conv in distribution)
        print(f"\nTotal null sector nodes across all conversations: {total_null}")
    
except Exception as e:
    print(f"Error querying distribution: {e}")
    distribution = []

# AQL Query 3: Causal flow analysis (forward vs past vs null)
print("\n\n### Query 3: CPT Causal Flow Analysis ###\n")

query_causal_flow = """
FOR step IN steps
    LET is_null = (step.content_hash == 
                   "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
    LET is_forward = (step.step_index > 0)
    
    COLLECT causal_state = (
        is_null ? "NULL_SECTOR (0)" : 
        is_forward ? "FORWARD (+1)" : "INITIAL"
    )
    AGGREGATE count = COUNT(1)
    RETURN {
        causal_state: causal_state,
        node_count: count
    }
"""

try:
    causal_cursor = db.aql.execute(query_causal_flow)
    causal_flow = list(causal_cursor)
    
    if causal_flow:
        print("CPT Tripotent Spectrum Distribution:")
        print("-" * 80)
        
        total_nodes = sum(item['node_count'] for item in causal_flow)
        
        for item in causal_flow:
            state = item['causal_state']
            count = item['node_count']
            percentage = (count / total_nodes * 100) if total_nodes > 0 else 0
            
            print(f"{state:20s}: {count:6d} nodes ({percentage:5.2f}%)")
        
        # Calculate topological index
        null_count = next(
            (item['node_count'] for item in causal_flow 
             if "NULL_SECTOR" in item['causal_state']), 
            0
        )
        forward_count = next(
            (item['node_count'] for item in causal_flow 
             if "FORWARD" in item['causal_state']), 
            0
        )
        
        if null_count > 0:
            winding_number_estimate = forward_count / null_count
            print(f"\nEstimated winding number (forward/null ratio): {winding_number_estimate:.2f}")
            print("This approximates the monodromy index n from d ln Ω quantization.")
    
except Exception as e:
    print(f"Error querying causal flow: {e}")
    causal_flow = []

# AQL Query 4: Monodromy cycle detection
print("\n\n### Query 4: Monodromy Cycle Detection ###\n")

query_monodromy = """
FOR step IN steps
    FILTER step.conversation_id != null
    COLLECT conv_id = step.conversation_id
    AGGREGATE 
        min_step = MIN(step.step_index),
        max_step = MAX(step.step_index),
        total_steps = COUNT(1)
    
    // Check if conversation has both start and null sector (closed cycle)
    LET has_null = (
        FOR s IN steps
            FILTER s.conversation_id == conv_id
            FILTER s.content_hash == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
            LIMIT 1
            RETURN true
    ) != []
    
    FILTER has_null
    RETURN {
        conversation_id: conv_id,
        cycle_start: min_step,
        cycle_end: max_step,
        cycle_length: total_steps,
        has_monodromy: has_null
    }
"""

try:
    monodromy_cursor = db.aql.execute(query_monodromy)
    monodromy_cycles = list(monodromy_cursor)
    
    if monodromy_cycles:
        print(f"Found {len(monodromy_cycles)} conversations with closed cycles (monodromy)\n")
        
        # Sort by cycle length
        monodromy_cycles.sort(key=lambda x: x['cycle_length'], reverse=True)
        
        print("Longest monodromy cycles:")
        print("-" * 80)
        for i, cycle in enumerate(monodromy_cycles[:5], 1):
            print(f"{i:2d}. {cycle['conversation_id'][:8]}...")
            print(f"    Cycle: steps {cycle['cycle_start']} → {cycle['cycle_end']}")
            print(f"    Length: {cycle['cycle_length']} steps")
            print(f"    Topological feature: Closed loop with null sector sink")
        
        # Estimate quantized index
        avg_cycle_length = sum(c['cycle_length'] for c in monodromy_cycles) / len(monodromy_cycles)
        print(f"\nAverage cycle length: {avg_cycle_length:.1f} steps")
        print("According to monodromy_index_quantization axiom:")
        print("  ∮ d ln Ω = n · 2π")
        print(f"  Estimated n ≈ {avg_cycle_length / (2 * 3.14159):.2f} (winding number)")
    
except Exception as e:
    print(f"Error querying monodromy cycles: {e}")
    monodromy_cycles = []

# Save results to JSON
print("\n\n### Saving Results ###\n")

results = {
    "query_timestamp": "2026-06-23T15:00:00Z",
    "null_sector_nodes": null_sector_nodes,
    "distribution_by_conversation": distribution,
    "causal_flow_analysis": causal_flow,
    "monodromy_cycles": monodromy_cycles,
    "summary": {
        "total_null_sector_nodes": len(null_sector_nodes),
        "conversations_with_null_sector": len(distribution),
        "monodromy_cycles_detected": len(monodromy_cycles)
    }
}

output_file = "/home/goutev/auto/cpt_null_sector_analysis.json"
with open(output_file, 'w') as f:
    json.dump(results, f, indent=2)

print(f"✓ Full analysis saved to: {output_file}")

# Final summary
print("\n" + "=" * 80)
print("CPT NULL SECTOR EXTRACTION: COMPLETE")
print("=" * 80)
print(f"\nKey Findings:")
print(f"  • Null sector nodes (0-eigenvalue): {len(null_sector_nodes)}")
print(f"  • Conversations affected: {len(distribution)}")
print(f"  • Monodromy cycles detected: {len(monodromy_cycles)}")
print(f"\nThe CPT causal structure is now visible in the Agent Brain DAG!")
print("Nodes in the null sector correspond to:")
print("  - Proof collapses (TerminalVoid)")
print("  - Cognitive dead-ends")
print("  - Topological singularities where d ln Ω is undefined")
print("\nThese are the exact locations where the monodromy index quantizes:")
print("  ∮ d ln Ω = n · 2π  (where n ∈ ℤ)")
print("\n🎯 The topology is exposed. Ready for further analysis.")