#!/usr/bin/env python3
"""
Deep Mine ArangoDB for B(M1), B(E1), and GT Mirror Ratio Data

This script searches the Agent Brain DAG for any previously extracted
experimental data on:
1. B(M1) mirror ratios (Fujita 2018, etc.)
2. B(E1) mirror ratios (beyond A=31,35,39)
3. Gamow-Teller beta decay mirror ratios
4. MED (Mirror Energy Differences) for A=27, 43

Focus: Extract numerical values that can test TKK predictions.
"""

import json
from datetime import datetime
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
print("DEEP MINING ARANGODB FOR MIRROR RATIO DATA")
print("=" * 80)
print(f"Timestamp: {datetime.now().isoformat()}")
print("\nSearching for: B(M1), B(E1), GT ratios, MED values\n")

# ============================================================================
# Query 1: Search for B(M1) mentions
# ============================================================================
print("### Query 1: B(M1) Data ###\n")

query_bm1 = """
FOR step IN steps
    FILTER CONTAINS(LOWER(step.content), "b(m1)") 
       OR CONTAINS(LOWER(step.content), "m1 transition")
       OR CONTAINS(LOWER(step.content), "fujita")
    
    LIMIT 20
    
    RETURN {
        conversation_id: step.conversation_id,
        step_index: step.step_index,
        content_hash: step.content_hash,
        type: step.type,
        preview: SUBSTRING(step.content, 0, 300)
    }
"""

try:
    bm1_results = list(db.aql.execute(query_bm1))
    print(f"B(M1) related steps found: {len(bm1_results)}\n")
    
    for i, result in enumerate(bm1_results[:5], 1):
        print(f"{i}. Conversation: {result['conversation_id']}, Step: {result['step_index']}")
        print(f"   Type: {result['type']}")
        print(f"   Preview: {result['preview'][:150]}...")
        print()
    
    # Save full results
    with open('/tmp/arango_bm1_results.json', 'w') as f:
        json.dump(bm1_results, f, indent=2)
    print(f"✓ Full B(M1) results saved to: /tmp/arango_bm1_results.json\n")
    
except Exception as e:
    print(f"Error: {e}")
    bm1_results = []

# ============================================================================
# Query 2: Search for Gamow-Teller mentions
# ============================================================================
print("\n### Query 2: Gamow-Teller (GT) Data ###\n")

query_gt = """
FOR step IN steps
    FILTER CONTAINS(LOWER(step.content), "gamow-teller") 
       OR CONTAINS(LOWER(step.content), "gamow teller")
       OR CONTAINS(LOWER(step.content), "b(gt)")
       OR CONTAINS(LOWER(step.content), "beta decay mirror")
    
    LIMIT 20
    
    RETURN {
        conversation_id: step.conversation_id,
        step_index: step.step_index,
        content_hash: step.content_hash,
        type: step.type,
        preview: SUBSTRING(step.content, 0, 300)
    }
"""

try:
    gt_results = list(db.aql.execute(query_gt))
    print(f"GT related steps found: {len(gt_results)}\n")
    
    for i, result in enumerate(gt_results[:5], 1):
        print(f"{i}. Conversation: {result['conversation_id']}, Step: {result['step_index']}")
        print(f"   Type: {result['type']}")
        print(f"   Preview: {result['preview'][:150]}...")
        print()
    
    with open('/tmp/arango_gt_results.json', 'w') as f:
        json.dump(gt_results, f, indent=2)
    print(f"✓ Full GT results saved to: /tmp/arango_gt_results.json\n")
    
except Exception as e:
    print(f"Error: {e}")
    gt_results = []

# ============================================================================
# Query 3: Search for A=27 specific data
# ============================================================================
print("\n### Query 3: A=27 Specific Data ###\n")

query_a27 = """
FOR step IN steps
    FILTER (CONTAINS(LOWER(step.content), "a=27") OR CONTAINS(LOWER(step.content), "a = 27"))
       AND (CONTAINS(LOWER(step.content), "silicon") OR CONTAINS(LOWER(step.content), "27si") 
            OR CONTAINS(LOWER(step.content), "27 al"))
    
    LIMIT 20
    
    RETURN {
        conversation_id: step.conversation_id,
        step_index: step.step_index,
        content_hash: step.content_hash,
        type: step.type,
        preview: SUBSTRING(step.content, 0, 300)
    }
"""

try:
    a27_results = list(db.aql.execute(query_a27))
    print(f"A=27 specific steps found: {len(a27_results)}\n")
    
    for i, result in enumerate(a27_results[:5], 1):
        print(f"{i}. Conversation: {result['conversation_id']}, Step: {result['step_index']}")
        print(f"   Type: {result['type']}")
        print(f"   Preview: {result['preview'][:150]}...")
        print()
    
    with open('/tmp/arango_a27_results.json', 'w') as f:
        json.dump(a27_results, f, indent=2)
    print(f"✓ Full A=27 results saved to: /tmp/arango_a27_results.json\n")
    
except Exception as e:
    print(f"Error: {e}")
    a27_results = []

# ============================================================================
# Query 4: Search for numerical ratios (pattern matching)
# ============================================================================
print("\n### Query 4: Numerical Mirror Ratios ###\n")

# Search for patterns like "ratio = X.XX" or "ratio of X.X"
query_ratios = """
FOR step IN steps
    FILTER CONTAINS(LOWER(step.content), "ratio")
       AND (CONTAINS(step.content, "=") OR CONTAINS(step.content, "is") OR CONTAINS(step.content, "was"))
    
    // Look for decimal numbers in the content
    LET words = SPLIT(step.content, " ")
    LET has_decimal := ANY(words, w => TEST(w, "^[0-9]+\\\\.[0-9]+$"))
    
    FILTER has_decimal
    LIMIT 15
    
    RETURN {
        conversation_id: step.conversation_id,
        step_index: step.step_index,
        preview: SUBSTRING(step.content, 0, 400)
    }
"""

try:
    ratio_results = list(db.aql.execute(query_ratios))
    print(f"Steps with numerical ratios found: {len(ratio_results)}\n")
    
    for i, result in enumerate(ratio_results[:5], 1):
        print(f"{i}. Conversation: {result['conversation_id']}, Step: {result['step_index']}")
        print(f"   Preview: {result['preview'][:200]}...")
        print()
    
    with open('/tmp/arango_ratio_results.json', 'w') as f:
        json.dump(ratio_results, f, indent=2)
    print(f"✓ Full ratio results saved to: /tmp/arango_ratio_results.json\n")
    
except Exception as e:
    print(f"Error: {e}")
    ratio_results = []

# ============================================================================
# Summary and Next Steps
# ============================================================================
print("\n" + "=" * 80)
print("MINING SUMMARY")
print("=" * 80)

print(f"\n📊 Results:")
print(f"  • B(M1) related steps: {len(bm1_results)}")
print(f"  • GT related steps: {len(gt_results)}")
print(f"  • A=27 specific steps: {len(a27_results)}")
print(f"  • Numerical ratio steps: {len(ratio_results)}")

if bm1_results or gt_results or a27_results:
    print(f"\n✅ SUCCESS! Data found in ArangoDB!")
    print(f"\n📁 JSON files saved:")
    if bm1_results:
        print(f"   • /tmp/arango_bm1_results.json ({len(bm1_results)} entries)")
    if gt_results:
        print(f"   • /tmp/arango_gt_results.json ({len(gt_results)} entries)")
    if a27_results:
        print(f"   • /tmp/arango_a27_results.json ({len(a27_results)} entries)")
    
    print(f"\n🔍 Next: Examine these JSON files to extract numerical B(M1) values!")
else:
    print(f"\n⚠️ No relevant data found in ArangoDB.")
    print(f"   The PDFs may not have been fully digested yet.")
    print(f"   Next step: Manually extract from Fujita 2018 PDF.")

print(f"\n{'='*80}")
print("MINING COMPLETE")
print(f"{'='*80}")