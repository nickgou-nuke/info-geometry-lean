from __future__ import annotations

import os

from arango import ArangoClient

ARANGO_HOST = os.environ.get("ARANGO_URL", os.environ.get("ARANGO_ENDPOINT", "http://127.0.0.1:8530"))
ARANGO_DB = os.environ.get("ARANGO_DATABASE", os.environ.get("ARANGO_DB", "LeanAST"))
ARANGO_USER = os.environ.get("ARANGO_USER", os.environ.get("ARANGO_USERNAME", "root"))
ARANGO_PASSWORD = os.environ.get("ARANGO_PASSWORD", "")


def _connect_graph(graph_name: str = "QuantumTopology"):
    try:
        client = ArangoClient(hosts=ARANGO_HOST)
        sys_db = client.db("_system", username=ARANGO_USER, password=ARANGO_PASSWORD)
        if not sys_db.has_database(ARANGO_DB):
            sys_db.create_database(ARANGO_DB)
        db = client.db(ARANGO_DB, username=ARANGO_USER, password=ARANGO_PASSWORD)

        if not db.has_graph(graph_name):
            db.create_graph(graph_name)
        topo_graph = db.graph(graph_name)
        if not topo_graph.has_vertex_collection("Theorems"):
            topo_graph.create_vertex_collection("Theorems")
        if not topo_graph.has_edge_definition("ProofSteps"):
            topo_graph.create_edge_definition(
                edge_collection="ProofSteps",
                from_vertex_collections=["Theorems"],
                to_vertex_collections=["Theorems"],
            )
        return db, topo_graph
    except Exception as exc:
        print(f"Skipping Arango ingest (unavailable): {ARANGO_HOST} :: {exc}")
        return None


def ingest_master_equation():
    connected = _connect_graph("QuantumTopology")
    if connected is None:
        return
    db, topo_graph = connected

    v_coll = topo_graph.vertex_collection("Theorems")
    e_coll = topo_graph.edge_collection("ProofSteps")

    nodes = [
        {
            "_key": "Projective_KMS_State",
            "lean_name": "projective KMS gauge state",
            "type": "Thermodynamic",
            "kind": "State",
        },
        {
            "_key": "Relative_Modular_Hamiltonian",
            "lean_name": "K = log Delta",
            "type": "Operator",
            "kind": "Generator",
        },
        {
            "_key": "Connes_Cocycle",
            "lean_name": "exp(i t K)",
            "type": "Operator",
            "kind": "ParallelTransport",
        },
        {
            "_key": "Modular_Burg_Generator",
            "lean_name": "modularBurgGenerator",
            "type": "Theorem",
            "kind": "EdgeWeight",
        },
        {
            "_key": "Itakura_Saito_Divergence",
            "lean_name": "scalarItakuraSaito",
            "type": "InformationGeometry",
            "kind": "Divergence",
        },
        {
            "_key": "Unnormalized_KL_Correction",
            "lean_name": "unnormalizedKL",
            "type": "InformationGeometry",
            "kind": "Divergence",
        },
        {
            "_key": "Fenchel_Duality",
            "lean_name": "Legendre-Fenchel primal-dual mirror",
            "type": "ConvexOptimization",
            "kind": "Duality",
        },
        {
            "_key": "Fenchel_Young_Inequality",
            "lean_name": "fenchelYoung_quadratic",
            "type": "LeanTheorem",
            "kind": "ConvexBound",
        },
        {
            "_key": "Fenchel_Biconjugate",
            "lean_name": "fenchel_biconjugate_quadratic",
            "type": "LeanTheorem",
            "kind": "Involution",
        },
        {
            "_key": "Quadratic_Gradient_Inverse",
            "lean_name": "quadratic_gradient_inverse",
            "type": "LeanTheorem",
            "kind": "GradientChart",
        },
        {
            "_key": "Fenchel_J_Closure",
            "lean_name": "fenchel_J_closure",
            "type": "LeanTheorem",
            "kind": "TomitaFenchelBridge",
        },
        {
            "_key": "modularBurgGenerator_nonnegative",
            "lean_name": "modularBurgGenerator_nonnegative",
            "type": "LeanTheorem",
            "kind": "Positivity",
        },
        {
            "_key": "scalarItakuraSaito_scale_invariant",
            "lean_name": "scalarItakuraSaito_scale_invariant",
            "type": "LeanTheorem",
            "kind": "GaugeInvariance",
        },
        {
            "_key": "modularBurgGenerator_eq_log_ItakuraSaito",
            "lean_name": "modularBurgGenerator_eq_log_ItakuraSaito",
            "type": "LeanTheorem",
            "kind": "Equivalence",
        },
        {
            "_key": "evaluatedBurg_eq_unnormalizedKL",
            "lean_name": "evaluatedBurg_eq_unnormalizedKL",
            "type": "LeanTheorem",
            "kind": "Evaluation",
        },
        {
            "_key": "thermo_gauge_flow_minimizes_entropy",
            "lean_name": "thermo_gauge_flow_minimizes_entropy",
            "type": "LeanTheorem",
            "kind": "OptimalTransportCost",
        },
        {
            "_key": "Primon_Log_Scale",
            "lean_name": "logPrimeEnergy",
            "type": "ArithmeticGeometry",
            "kind": "LogScale",
        },
        {
            "_key": "Primon_Fock_Mode",
            "lean_name": "Primon",
            "type": "ArithmeticGeometry",
            "kind": "PrimeMode",
        },
        {
            "_key": "Fermionic_Primon_Mode",
            "lean_name": "FermionicPrimon",
            "type": "ArithmeticGeometry",
            "kind": "BoundedOccupation",
        },
        {
            "_key": "Padic_Prime_Measure",
            "lean_name": "padicDistance",
            "type": "ArithmeticGeometry",
            "kind": "PrimeMeasure",
        },
        {
            "_key": "Mellin_Log_Fourier",
            "lean_name": "mellin_is_log_fourier",
            "type": "LeanTheorem",
            "kind": "LogScaleTransform",
        },
        {
            "_key": "Primon_Synthesis",
            "lean_name": "primon_synthesis",
            "type": "LeanTheorem",
            "kind": "ArithmeticQuantization",
        },
        {
            "_key": "Souriau_Complex_Temperature",
            "lean_name": "complexTemperature",
            "type": "Thermodynamic",
            "kind": "ComplexBetaVector",
        },
        {
            "_key": "Souriau_Modular_Exp",
            "lean_name": "souriauModularExp",
            "type": "Operator",
            "kind": "ComplexModularCocycle",
        },
        {
            "_key": "Riemann_Sphere_Beta_Chart",
            "lean_name": "riemannSphereChart",
            "type": "Geometry",
            "kind": "AffineSphereChart",
        },
        {
            "_key": "souriau_complex_temperature_theorem",
            "lean_name": "souriau_complex_temperature_theorem",
            "type": "LeanTheorem",
            "kind": "SouriauFlow",
        },
    ]

    for node in nodes:
        if not v_coll.has(node["_key"]):
            v_coll.insert(node)

    edges = [
        {
            "_from": "Theorems/Projective_KMS_State",
            "_to": "Theorems/Relative_Modular_Hamiltonian",
            "relation": "has_log_generator",
        },
        {
            "_from": "Theorems/Relative_Modular_Hamiltonian",
            "_to": "Theorems/Connes_Cocycle",
            "relation": "exponentiates_to_parallel_transport",
        },
        {
            "_from": "Theorems/Relative_Modular_Hamiltonian",
            "_to": "Theorems/Modular_Burg_Generator",
            "relation": "generates_edge_weight",
        },
        {
            "_from": "Theorems/Modular_Burg_Generator",
            "_to": "Theorems/Itakura_Saito_Divergence",
            "relation": "equals_in_log_coordinates",
        },
        {
            "_from": "Theorems/Modular_Burg_Generator",
            "_to": "Theorems/Unnormalized_KL_Correction",
            "relation": "evaluates_to",
        },
        {
            "_from": "Theorems/scalarItakuraSaito_scale_invariant",
            "_to": "Theorems/Itakura_Saito_Divergence",
            "relation": "certifies_projective_gauge_invariance",
        },
        {
            "_from": "Theorems/modularBurgGenerator_nonnegative",
            "_to": "Theorems/Modular_Burg_Generator",
            "relation": "certifies_nonnegative_cost",
        },
        {
            "_from": "Theorems/modularBurgGenerator_eq_log_ItakuraSaito",
            "_to": "Theorems/Modular_Burg_Generator",
            "relation": "certifies_log_chart_equivalence",
        },
        {
            "_from": "Theorems/evaluatedBurg_eq_unnormalizedKL",
            "_to": "Theorems/Unnormalized_KL_Correction",
            "relation": "certifies_trace_evaluation",
        },
        {
            "_from": "Theorems/thermo_gauge_flow_minimizes_entropy",
            "_to": "Theorems/Modular_Burg_Generator",
            "relation": "uses_as_optimal_transport_cost",
        },
        {
            "_from": "Theorems/Modular_Burg_Generator",
            "_to": "Theorems/WeylSector",
            "relation": "weights_causal_sector_edges",
        },
        {
            "_from": "Theorems/Fenchel_Duality",
            "_to": "Theorems/Itakura_Saito_Divergence",
            "relation": "supplies_bregman_primal_dual_geometry",
        },
        {
            "_from": "Theorems/Fenchel_Young_Inequality",
            "_to": "Theorems/Fenchel_Duality",
            "relation": "certifies_convex_bound",
        },
        {
            "_from": "Theorems/Fenchel_Biconjugate",
            "_to": "Theorems/Fenchel_Duality",
            "relation": "certifies_dual_involution",
        },
        {
            "_from": "Theorems/Quadratic_Gradient_Inverse",
            "_to": "Theorems/Fenchel_Duality",
            "relation": "certifies_primal_dual_gradient_inverse",
        },
        {
            "_from": "Theorems/Fenchel_J_Closure",
            "_to": "Theorems/Fenchel_Duality",
            "relation": "links_tomita_J_to_biconjugation",
        },
        {
            "_from": "Theorems/Fenchel_J_Closure",
            "_to": "Theorems/Connes_Cocycle",
            "relation": "closes_visible_ghost_duality",
        },
        {
            "_from": "Theorems/Primon_Fock_Mode",
            "_to": "Theorems/Primon_Log_Scale",
            "relation": "has_energy",
        },
        {
            "_from": "Theorems/Fermionic_Primon_Mode",
            "_to": "Theorems/Primon_Fock_Mode",
            "relation": "bounds_occupation_by_one",
        },
        {
            "_from": "Theorems/Padic_Prime_Measure",
            "_to": "Theorems/Primon_Log_Scale",
            "relation": "measures_prime_scale_lattice",
        },
        {
            "_from": "Theorems/Mellin_Log_Fourier",
            "_to": "Theorems/Primon_Log_Scale",
            "relation": "quantizes_hyperbolic_dilation",
        },
        {
            "_from": "Theorems/Primon_Synthesis",
            "_to": "Theorems/Padic_Prime_Measure",
            "relation": "certifies_prime_measure_layer",
        },
        {
            "_from": "Theorems/Primon_Synthesis",
            "_to": "Theorems/Mellin_Log_Fourier",
            "relation": "links_arithmetic_to_log_scale_transform",
        },
        {
            "_from": "Theorems/Souriau_Complex_Temperature",
            "_to": "Theorems/Relative_Modular_Hamiltonian",
            "relation": "pairs_with_modular_hamiltonian",
        },
        {
            "_from": "Theorems/Souriau_Complex_Temperature",
            "_to": "Theorems/Riemann_Sphere_Beta_Chart",
            "relation": "is_affine_chart_vector",
        },
        {
            "_from": "Theorems/Souriau_Modular_Exp",
            "_to": "Theorems/Connes_Cocycle",
            "relation": "complexifies_modular_cocycle",
        },
        {
            "_from": "Theorems/souriau_complex_temperature_theorem",
            "_to": "Theorems/Souriau_Modular_Exp",
            "relation": "certifies_exponential_addition_law",
        },
        {
            "_from": "Theorems/souriau_complex_temperature_theorem",
            "_to": "Theorems/Riemann_Sphere_Beta_Chart",
            "relation": "certifies_real_vector_chart",
        },
    ]

    for edge in edges:
        try:
            e_coll.insert(edge)
        except Exception as exc:
            print(f"Edge exists or error: {exc}")

    print("Successfully ingested the master-equation Burg/KL edge weights into ArangoDB!")


if __name__ == "__main__":
    ingest_master_equation()
