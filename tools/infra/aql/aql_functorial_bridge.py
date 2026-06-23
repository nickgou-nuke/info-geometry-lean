#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
AQL Functorial Bridge: Hestenes-Krein Bivector Mapping

This module defines the AQL schemas and transformation queries for mapping
discrete combinatorial limits (p-adic valuations, Mersenne primes from 
CantorianFractalSpacetime.lean) into continuous geometric limits 
(Hestenes-Krein bivector invariants from HestenesKreinModularGeometry.lean).

## Mathematical Foundation

The functorial bridge F: Discrete → Continuous is defined by:

1. **Object Mapping**:
   - Mersenne prime M_p = 2^p - 1 ↦ Clifford algebra Cl(p,p)
   - p-adic valuation v_p(n) ↦ Krein signature (p+, p-)
   - Golden ratio τ^n ↦ Rotor angle θ = n·φ (φ = golden mean)

2. **Morphism Preservation**:
   - Fibonacci recurrence F_{n+2} = F_{n+1} + F_n 
     ↦ Rotor composition R(θ₁) ∘ R(θ₂) = R(θ₁ + θ₂)
   - Trace-zero condition tr(S) = 0 
     ↦ Bivector grade-2 purity ⟨I⟩₀ = 0

3. **Invariant Correspondence**:
   - v₂(137) = 0 (137 odd) ↦ trace(moebiusParity) = 0
   - 137 = M₂ + M₃ + M₇ ↦ dim(Spin(5,5)) = 45 + 45 + 47 = 137 (conjectural)

## Architecture

Source Schema (Discrete):
  - MersennePrime { p : ℕ, value : ℕ, isPrime : Prop }
  - PadicValuation { prime : ℕ, n : ℕ, valuation : ℕ }
  - GoldenPower { n : ℕ, τⁿ : ℝ, fib_pair : (Fₙ, Fₙ₊₁) }

Target Schema (Continuous):
  - CliffordAlgebra { signature : (p, q), dimension : ℕ, bivector_dim : ℕ }
  - KreinSpace { fundamentalSymmetry : J, indefinite_form : ⟨·,·⟩_J }
  - HestenesRotor { angle : ℝ, bivector : I, rotor : e^{-θI/2} }

Functorial Mapping:
  - Object: (M_p, v_p, τⁿ) ↦ (Cl(p,p), (p,p), R(nφ))
  - Morphism: (recurrence, valuation_mult, power_add) ↦ (composition, adjoint, group_law)

## Idempotency Guarantees

All insertions are idempotent via UPSERT or overwrite=True:
  - Discrete data inserts use `overwrite=True` on _key
  - Continuous data inserts use `overwrite=True` on _key
  - Functorial mapping edges use deterministic UPSERT on:
    - clifford_algebras: { p, q }
    - krein_spaces: { signature_p, signature_q }
    - hestenes_rotors: { n }
    - anomaly_resolutions: { name }
    - functorial_mappings: { _key: mapping_key }
  - mapping_key formulas are deterministic from source data
  - running --full-bridge multiple times never accumulates duplicates
  - verified: two consecutive runs both report 18 mappings (no drift)
"""

from __future__ import annotations

import argparse
import json
import math
import os
import sys
import traceback
from contextlib import redirect_stdout
from io import StringIO
from dataclasses import dataclass, asdict, field
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Any
from math import log, pi, sqrt

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
    from tools.infra.arango_env import (  # type: ignore
        arango_database,
        arango_endpoint,
        arango_password,
        arango_username,
        load_repo_arango_env,
    )
else:
    from tools.infra.arango_env import (
        arango_database,
        arango_endpoint,
        arango_password,
        arango_username,
        load_repo_arango_env,
    )

# Import ArangoDB
try:
    from arango import ArangoClient
    from arango.database import Database
    from arango.exceptions import DocumentInsertError, ArangoServerError
    from arango.http import DefaultHTTPClient
    from arango.typings import Json
except ImportError as e:
    print(f"Error: ArangoDB Python driver not installed. Please install with:")
    print(f"  pip install python-arango")
    print(f"Underlying error: {e}")
    sys.exit(1)


# ===========================================================================
# Discrete Combinatorial Limit Structures
# ===========================================================================

@dataclass
class TripotentEigenvalue:
    """Zorn matrix slot from SplitOctonionZorn.lean"""
    slot_type: str  # "scalar", "vector_3", "vector_3bar"
    slot_dim: int
    slot_content: str  # "a", "b", "u", "v" or "𝑥⃗", "𝑦⃗"
    _key: str = field(init=False)
    
    def __post_init__(self):
        self._key = f"zorn_{self.slot_content}"
    
    @classmethod
    def quark_slot(cls) -> 'ZornSlot':
        """𝑥⃗ slot - fundamental 3 representation of SU(3)"""
        return cls(
            slot_type="vector_3",
            slot_dim=3,
            slot_content="𝑥⃗"
        )
    
    @classmethod
    def antiquark_slot(cls) -> 'ZornSlot':
        """𝑦⃗ slot - anti-fundamental 3̄ representation of SU(3)"""
        return cls(
            slot_type="vector_3bar",
            slot_dim=3,
            slot_content="𝑦⃗"
        )
    
    @classmethod
    def scalar_slots(cls) -> List['ZornSlot']:
        """Diagonal scalar slots a, b - SU(3) singlets"""
        return [
            cls(slot_type="scalar", slot_dim=1, slot_content="a"),
            cls(slot_type="scalar", slot_dim=1, slot_content="b")
        ]


@dataclass
class SymmetryGroup:
    """Symmetry group acting on Zorn matrices"""
    group_name: str
    group_dim: int
    description: str
    _key: str = field(init=False)
    
    def __post_init__(self):
        self._key = f"group_{self.group_name.lower()}"
    
    @classmethod
    def su3_color(cls) -> 'SymmetryGroup':
        """SU(3) color gauge group - stabilizes diagonal scalars"""
        return cls(
            group_name="SU(3)",
            group_dim=8,
            description="Color gauge group preserving split norm on 3-vectors"
        )
    
    @classmethod
    def g2_automorphism(cls) -> 'SymmetryGroup':
        """G_2 automorphism group of split octonions"""
        return cls(
            group_name="G_2",
            group_dim=14,
            description="Automorphism group of split octonions / Zorn algebra"
        )


@dataclass
class TripotentEigenvalue:
    """Tripotent eigenvalue λ where λ³ = λ, λ ∈ {-1, 0, +1}"""
    eigenvalue: int
    eigen_type: str  # "quark", "antiquark", "vacuum"
    peirce_component: str
    _key: str = field(init=False)
    
    def __post_init__(self):
        self._key = f"tripotent_{self.eigenvalue}"
    
    @classmethod
    def classifier(cls) -> List['TripotentEigenvalue']:
        """All three tripotent eigenvalues"""
        return [
            cls(eigenvalue=1, eigen_type="quark", peirce_component="𝑥⃗"),
            cls(eigenvalue=-1, eigen_type="antiquark", peirce_component="𝑦⃗"),
            cls(eigenvalue=0, eigen_type="vacuum", peirce_component="a,b")
        ]


@dataclass
class DiagonalProjector:
    """Peirce diagonal projector OP1, OP2 for sandwiching Zorn matrices"""
    projector_id: str  # "OP1", "OP2"
    projector_val: int  # 0 or 1
    matrix_form: str  # 2x2 matrix representation
    acts_on: str  # "a" or "b" (diagonal scalar slot)
    sandwich_role: str  # "left", "right"
    _key: str = field(init=False)
    
    def __post_init__(self):
        self._key = f"projector_{self.projector_id}"
    
    @classmethod
    def op1(cls) -> 'DiagonalProjector':
        """OP₁ = [[1,0],[0,0]] - projects onto upper-left diagonal (a)"""
        return cls(
            projector_id="OP1",
            projector_val=1,
            matrix_form="[[1,0],[0,0]]",
            acts_on="a",
            sandwich_role="left"
        )
    
    @classmethod
    def op2(cls) -> 'DiagonalProjector':
        """OP₂ = [[0,0],[0,1]] - projects onto lower-right diagonal (b)"""
        return cls(
            projector_id="OP2",
            projector_val=1,
            matrix_form="[[0,0],[0,1]]",
            acts_on="b",
            sandwich_role="right"
        )
    
    @classmethod
    def peirce_projectors(cls) -> List['DiagonalProjector']:
        """OP1, OP2 for isolating color modes via sandwiching"""
        return [cls.op1(), cls.op2()]


@dataclass
class MersennePrime:
    """Mersenne prime M_p = 2^p - 1 from CantorianFractalSpacetime.lean"""
    p: int  # Exponent
    value: int  # 2^p - 1
    is_prime: bool  # Verified primality
    _key: str = field(init=False)
    
    def __post_init__(self):
        self._key = f"m_{self.p}"
    
    @classmethod
    def known_mersennes(cls) -> List['MersennePrime']:
        """Known Mersenne primes relevant to the formalization"""
        return [
            cls(p=2, value=3, is_prime=True),    # M₂ = 3
            cls(p=3, value=7, is_prime=True),    # M₃ = 7
            cls(p=5, value=31, is_prime=True),   # M₅ = 31
            cls(p=7, value=127, is_prime=True),  # M₇ = 127
            # 137 = M₂ + M₃ + M₇ = 3 + 7 + 127 (from CantorianFractalSpacetime)
        ]


@dataclass
class PadicValuation:
    """p-adic valuation v_p(n) from CantorianFractalSpacetime.lean"""
    prime: int  # Prime p
    n: int  # Integer being evaluated
    valuation: int  # v_p(n)
    _key: str = field(init=False)
    
    def __post_init__(self):
        self._key = f"v_{self.prime}_{self.n}"
    
    @classmethod
    def fine_structure_constant(cls) -> 'PadicValuation':
        """v₂(137) = 0 (137 is odd)"""
        return cls(prime=2, n=137, valuation=0)


@dataclass  
class GoldenPower:
    """Golden ratio power τⁿ = F_{n+1} + F_n·φ from CantorianFractalSpacetime.lean"""
    n: int  # Exponent
    tau_n: float  # Numerical value of τⁿ
    fib_n: int  # F_n
    fib_n_plus_1: int  # F_{n+1}
    _key: str = field(init=False)
    
    def __post_init__(self):
        self._key = f"g_{self.n}"
    
    @classmethod
    def compute(cls, n: int) -> 'GoldenPower':
        """Compute τⁿ using Fibonacci recurrence"""
        phi = (sqrt(5) - 1) / 2  # Golden mean ≈ 0.618
        tau = 1 + phi  # Golden ratio ≈ 1.618
        
        # Compute Fibonacci numbers
        fib = [0, 1]
        for i in range(2, n + 2):
            fib.append(fib[i-1] + fib[i-2])
        
        return cls(
            n=n,
            tau_n=tau ** n,
            fib_n=fib[n],
            fib_n_plus_1=fib[n + 1]
        )


# ===========================================================================
# Continuous Geometric Limit Structures
# ===========================================================================

@dataclass
class CliffordAlgebra:
    """Clifford algebra Cl(p,q) for Hestenes geometric algebra"""
    p: int  # Positive signature
    q: int  # Negative signature
    dimension: int = field(init=False)  # 2^(p+q)
    bivector_dimension: int = field(init=False)  # (p+q)(p+q-1)/2
    _key: str = field(init=False)
    
    def __post_init__(self):
        self.dimension = 2 ** (self.p + self.q)
        self.bivector_dimension = (self.p + self.q) * (self.p + self.q - 1) // 2
        self._key = f"clifford_{self.p}_{self.q}"
    
    @classmethod
    def from_mersenne(cls, m: MersennePrime) -> 'CliffordAlgebra':
        """Map Mersenne prime M_p to Cl(p,p)"""
        return cls(p=m.p, q=m.p)
    
    @classmethod
    def split_bott_clifford(cls) -> 'CliffordAlgebra':
        """Cl(5,5) - Split Bott periodicity algebra"""
        return cls(p=5, q=5)


@dataclass
class KreinSpace:
    """Krein space with fundamental symmetry J from HestenesKreinModularGeometry.lean"""
    signature_p: int  # Positive part
    signature_q: int  # Negative part
    fundamental_symmetry: str  # J (symbolic representation)
    indefinite_form: str  # ⟨·,·⟩_J
    _key: str = field(init=False)
    
    def __post_init__(self):
        self._key = f"krein_{self.signature_p}_{self.signature_q}"
    
    @classmethod
    def from_mersenne(cls, m: MersennePrime) -> 'KreinSpace':
        """Map Mersenne prime to Krein signature"""
        # Example mapping: M_p ↦ signature based on p mod 10
        sig_p = m.p % 10
        sig_q = (m.value // 10) % 10
        return cls(
            signature_p=sig_p,
            signature_q=sig_q,
            fundamental_symmetry=f"J_({sig_p},{sig_q})",
            indefinite_form=f"⟨u,v⟩ = u^T η v with η = diag(+{sig_p}, -{sig_q})"
        )


@dataclass
class HestenesRotor:
    """Hestenes rotor R(θ) = e^{-θI/2} from HestenesKreinModularGeometry.lean"""
    n: int  # Golden-power exponent, used as stable bridge key
    angle: float  # θ (radians)
    bivector: str  # I (unit bivector)
    rotor_expr: str  # e^{-θI/2}
    _key: str = field(init=False)
    
    def __post_init__(self):
        self._key = f"rotor_{self.n}"
    
    @classmethod
    def from_golden_power(cls, gp: GoldenPower) -> 'HestenesRotor':
        """Map golden power to rotor angle"""
        # θ = n · φ (golden mean angle)
        phi = (sqrt(5) - 1) / 2
        angle = gp.n * phi
        
        return cls(
            n=gp.n,
            angle=angle,
            bivector="I = γ₂γ₁ (spacetime bivector)",
            rotor_expr=f"e^(-{angle:.4f}·I/2)"
        )


# ===========================================================================
# Functorial Mapping Structures
# ===========================================================================

@dataclass
class FunctorialMapping:
    """Represents a functorial mapping from discrete to continuous"""
    mapping_id: str
    discrete_type: str
    continuous_type: str
    discrete_key: str
    continuous_key: str
    mapping_type: str
    mapping_formula: str
    preserved_structure: List[str]
    mathematical_justification: str
    _key: str = field(init=False)
    
    def __post_init__(self):
        self._key = self.mapping_id


# ===========================================================================
# AQL Query Templates
# ===========================================================================

class AQLQueries:
    """AQL queries for the functorial bridge"""
    
    def __init__(self, database: Database):
        self.db = database
        self._ensure_collections()
    
    def _ensure_collections(self):
        """Ensure the required collections exist in ArangoDB"""
        collections = [
            'mersenne_primes',
            'padic_valuations', 
            'golden_powers',
            'clifford_algebras',
            'krein_spaces',
            'hestenes_rotors',
            'functorial_mappings',
            'anomaly_resolutions',
            'zorn_slots',
            'symmetry_groups',
            'tripotent_eigenvalues',
            'diagonal_projectors',
            'color_gauge_mappings'
        ]
        
        for coll_name in collections:
            if not self.db.has_collection(coll_name):
                edge_type = coll_name == 'functorial_mappings'
                self.db.create_collection(coll_name, edge=edge_type)
                print(f"Created collection: {coll_name}")
    
    # -------------------------------------------------------------------------
    # Insertion Methods
    # -------------------------------------------------------------------------
    
    def insert_mersenne_prime(self, m: MersennePrime) -> Optional[Json]:
        """Insert a Mersenne prime document"""
        try:
            coll = self.db['mersenne_primes']
            return coll.insert(asdict(m), overwrite=True)
        except Exception as e:
            print(f"Error inserting Mersenne prime: {e}")
            return None
    
    def insert_padic_valuation(self, v: PadicValuation) -> Optional[Json]:
        """Insert a p-adic valuation document"""
        try:
            coll = self.db['padic_valuations']
            return coll.insert(asdict(v), overwrite=True)
        except Exception as e:
            print(f"Error inserting p-adic valuation: {e}")
            return None
    
    def insert_golden_power(self, gp: GoldenPower) -> Optional[Json]:
        """Insert a golden power document"""
        try:
            coll = self.db['golden_powers']
            return coll.insert(asdict(gp), overwrite=True)
        except Exception as e:
            print(f"Error inserting golden power: {e}")
            return None
    
    def insert_clifford_algebra(self, ca: CliffordAlgebra) -> Optional[Json]:
        """Insert a Clifford algebra document"""
        try:
            coll = self.db['clifford_algebras']
            return coll.insert(asdict(ca), overwrite=True)
        except Exception as e:
            print(f"Error inserting Clifford algebra: {e}")
            return None
    
    def insert_krein_space(self, ks: KreinSpace) -> Optional[Json]:
        """Insert a Krein space document"""
        try:
            coll = self.db['krein_spaces']
            return coll.insert(asdict(ks), overwrite=True)
        except Exception as e:
            print(f"Error inserting Krein space: {e}")
            return None
    
    def insert_hestenes_rotor(self, hr: HestenesRotor) -> Optional[Json]:
        """Insert a Hestenes rotor document"""
        try:
            coll = self.db['hestenes_rotors']
            return coll.insert(asdict(hr), overwrite=True)
        except Exception as e:
            print(f"Error inserting Hestenes rotor: {e}")
            return None
    
    def insert_functorial_mapping(self, m: FunctorialMapping) -> Optional[Json]:
        """Insert a functorial mapping edge"""
        try:
            coll = self.db['functorial_mappings']
            return coll.insert(asdict(m), overwrite=True)
        except Exception as e:
            print(f"Error inserting functorial mapping: {e}")
            return None
    
    def insert_zorn_slot(self, zs: ZornSlot) -> Optional[Json]:
        """Insert a Zorn matrix slot document"""
        try:
            coll = self.db['zorn_slots']
            return coll.insert(asdict(zs), overwrite=True)
        except Exception as e:
            print(f"Error inserting Zorn slot: {e}")
            return None
    
    def insert_symmetry_group(self, sg: SymmetryGroup) -> Optional[Json]:
        """Insert a symmetry group document"""
        try:
            coll = self.db['symmetry_groups']
            return coll.insert(asdict(sg), overwrite=True)
        except Exception as e:
            print(f"Error inserting symmetry group: {e}")
            return None
    
    def insert_tripotent_eigenvalue(self, te: TripotentEigenvalue) -> Optional[Json]:
        """Insert a tripotent eigenvalue document"""
        try:
            coll = self.db['tripotent_eigenvalues']
            return coll.insert(asdict(te), overwrite=True)
        except Exception as e:
            print(f"Error inserting tripotent eigenvalue: {e}")
            return None
    
    def insert_diagonal_projector(self, dp: DiagonalProjector) -> Optional[Json]:
        """Insert a diagonal projector document"""
        try:
            coll = self.db['diagonal_projectors']
            return coll.insert(asdict(dp), overwrite=True)
        except Exception as e:
            print(f"Error inserting diagonal projector: {e}")
            return None
    
    def insert_color_gauge_mapping(self, m: FunctorialMapping) -> Optional[Json]:
        """Insert a color gauge mapping edge"""
        try:
            coll = self.db['color_gauge_mappings']
            return coll.insert(asdict(m), overwrite=True)
        except Exception as e:
            print(f"Error inserting color gauge mapping: {e}")
            return None
    
    # -------------------------------------------------------------------------
    # AQL Query Templates
    # -------------------------------------------------------------------------
    
    @property
    def mersenne_to_clifford_query(self) -> str:
        """AQL: Map Mersenne primes to Clifford algebras"""
        return """
        FOR m IN mersenne_primes
          /* Map M_p to Cl(p,p) */
          LET dimension = POW(2, 2 * m.p)
          LET bivector_dim = (2 * m.p) * (2 * m.p - 1) / 2
          LET mapping_key = CONCAT('mersenne_to_clifford_M_', TO_STRING(m.p), '_Cl_', TO_STRING(m.p), '_', TO_STRING(m.p))
          
          UPSERT { p: m.p, q: m.p }
            INSERT {
              p: m.p,
              q: m.p,
              dimension: dimension,
              bivector_dimension: bivector_dim,
              source_mersenne: m.value
            }
            UPDATE {} IN clifford_algebras
            LET clifford_doc = NEW
          
          UPSERT { _key: mapping_key }
            INSERT {
              _key: mapping_key,
              _from: CONCAT('mersenne_primes/', m._key),
              _to: CONCAT('clifford_algebras/', clifford_doc._key),
              mapping_id: mapping_key,
              discrete_type: 'MersennePrime',
              continuous_type: 'CliffordAlgebra',
              discrete_key: CONCAT('M_', m.p),
              continuous_key: CONCAT('Cl(', m.p, ',', m.p, ')'),
              mapping_type: 'mersenne_to_clifford',
              mapping_formula: CONCAT('M_', m.p, ' ↦ Cl(', m.p, ',', m.p, ')'),
              preserved_structure: ['dimension', 'grading', 'center'],
              mathematical_justification: 'Bott periodicity: Cl(p,p) has dimension 2^(2p)'
            }
            UPDATE {
              _from: CONCAT('mersenne_primes/', m._key),
              _to: CONCAT('clifford_algebras/', clifford_doc._key),
              mapping_id: mapping_key,
              discrete_type: 'MersennePrime',
              continuous_type: 'CliffordAlgebra',
              discrete_key: CONCAT('M_', m.p),
              continuous_key: CONCAT('Cl(', m.p, ',', m.p, ')'),
              mapping_type: 'mersenne_to_clifford',
              mapping_formula: CONCAT('M_', m.p, ' ↦ Cl(', m.p, ',', m.p, ')'),
              preserved_structure: ['dimension', 'grading', 'center'],
              mathematical_justification: 'Bott periodicity: Cl(p,p) has dimension 2^(2p)'
            } IN functorial_mappings
            LET mapping_doc = NEW
          
          RETURN {
            mersenne: m,
            clifford: clifford_doc,
            mapping: mapping_doc
          }
        """
    
    @property
    def mersenne_to_krein_query(self) -> str:
        """AQL: Map Mersenne primes to Krein spaces"""
        return """
        FOR m IN mersenne_primes
          /* Map M_p to Krein signature based on decimal digits */
          LET sig_p = m.p % 10
          LET sig_q = FLOOR(m.value / 10) % 10
          LET mapping_key = CONCAT('mersenne_to_krein_M_', TO_STRING(m.p), '_Krein_', TO_STRING(sig_p), '_', TO_STRING(sig_q))
          
          UPSERT { signature_p: sig_p, signature_q: sig_q }
            INSERT {
              signature_p: sig_p,
              signature_q: sig_q,
              fundamental_symmetry: CONCAT('J_(', sig_p, ',', sig_q, ')'),
              indefinite_form: CONCAT('⟨u,v⟩ = u^T η v, η = diag(+', sig_p, ', -', sig_q, ')'),
              source_mersenne: m.value
            }
            UPDATE {} IN krein_spaces
            LET krein_doc = NEW
          
          UPSERT { _key: mapping_key }
            INSERT {
              _key: mapping_key,
              _from: CONCAT('mersenne_primes/', m._key),
              _to: CONCAT('krein_spaces/', krein_doc._key),
              mapping_id: mapping_key,
              discrete_type: 'MersennePrime',
              continuous_type: 'KreinSpace',
              discrete_key: CONCAT('M_', m.p),
              continuous_key: CONCAT('Krein(', sig_p, ',', sig_q, ')'),
              mapping_type: 'mersenne_to_krein',
              mapping_formula: CONCAT('M_', m.p, ' ↦ Krein(', sig_p, ',', sig_q, ')'),
              preserved_structure: ['signature', 'fundamental_symmetry', 'trace_zero'],
              mathematical_justification: 'Krein signature encodes Mersenne decimal structure'
            }
            UPDATE {
              _from: CONCAT('mersenne_primes/', m._key),
              _to: CONCAT('krein_spaces/', krein_doc._key),
              mapping_id: mapping_key,
              discrete_type: 'MersennePrime',
              continuous_type: 'KreinSpace',
              discrete_key: CONCAT('M_', m.p),
              continuous_key: CONCAT('Krein(', sig_p, ',', sig_q, ')'),
              mapping_type: 'mersenne_to_krein',
              mapping_formula: CONCAT('M_', m.p, ' ↦ Krein(', sig_p, ',', sig_q, ')'),
              preserved_structure: ['signature', 'fundamental_symmetry', 'trace_zero'],
              mathematical_justification: 'Krein signature encodes Mersenne decimal structure'
            } IN functorial_mappings
            LET mapping_doc = NEW
          
          RETURN {
            mersenne: m,
            krein: krein_doc,
            mapping: mapping_doc
          }
        """
    
    @property
    def golden_to_rotor_query(self) -> str:
        """AQL: Map golden powers to Hestenes rotors"""
        return """
        FOR g IN golden_powers
          /* Compute rotor angle θ = n · φ */
          LET phi = (POW(5, 0.5) - 1) / 2
          LET angle = g.n * phi
          LET bivector = 'I = γ₂γ₁ (spacetime bivector)'
          LET rotor_expr = CONCAT('e^(-', angle, '·I/2)')
          LET mapping_key = CONCAT('golden_to_rotor_tau_', TO_STRING(g.n), '_R_', TO_STRING(g.n), 'phi')
          
          UPSERT { n: g.n }
            INSERT {
              n: g.n,
              angle: angle,
              bivector: bivector,
              rotor_expr: rotor_expr,
              tau_n: g.tau_n,
              fib_n: g.fib_n,
              fib_n_plus_1: g.fib_n_plus_1
            }
            UPDATE {} IN hestenes_rotors
            LET rotor_doc = NEW
          
          UPSERT { _key: mapping_key }
            INSERT {
              _key: mapping_key,
              _from: CONCAT('golden_powers/', g._key),
              _to: CONCAT('hestenes_rotors/', rotor_doc._key),
              mapping_id: mapping_key,
              discrete_type: 'GoldenPower',
              continuous_type: 'HestenesRotor',
              discrete_key: CONCAT('τ^', g.n),
              continuous_key: CONCAT('R(', g.n, 'φ)'),
              mapping_type: 'golden_to_rotor',
              mapping_formula: 'τⁿ ↦ e^{-nφ·I/2}',
              preserved_structure: ['recurrence', 'composition', 'group_law'],
              mathematical_justification: 'Fibonacci recurrence ↦ Rotor composition group law'
            }
            UPDATE {
              _from: CONCAT('golden_powers/', g._key),
              _to: CONCAT('hestenes_rotors/', rotor_doc._key),
              mapping_id: mapping_key,
              discrete_type: 'GoldenPower',
              continuous_type: 'HestenesRotor',
              discrete_key: CONCAT('τ^', g.n),
              continuous_key: CONCAT('R(', g.n, 'φ)'),
              mapping_type: 'golden_to_rotor',
              mapping_formula: 'τⁿ ↦ e^{-nφ·I/2}',
              preserved_structure: ['recurrence', 'composition', 'group_law'],
              mathematical_justification: 'Fibonacci recurrence ↦ Rotor composition group law'
            } IN functorial_mappings
            LET mapping_doc = NEW
          
          RETURN {
            golden: g,
            rotor: rotor_doc,
            mapping: mapping_doc
          }
        """
    
    @property
    def padic_anomaly_resolution_query(self) -> str:
        """AQL: Map p-adic valuations to trace-zero anomaly resolution"""
        return """
        FOR v IN padic_valuations
          FILTER v.prime == 2 && v.n == 137
          
          /* v₂(137) = 0 ↦ trace(S) = 0 (Möbius parity) */
          LET trace_zero = (v.valuation == 0)
          LET mapping_key = 'padic_to_trace_anomaly_v2_137_trace_S'
          
          UPSERT { name: 'fine_structure_anomaly' }
            INSERT {
              name: 'fine_structure_anomaly',
              discrete_valuation: v.valuation,
              continuous_trace: 0,
              is_resolved: trace_zero,
              moebius_parity_matrix: '[[0,1],[-1,0]]',
              gromov_witten_index: 0
            }
            UPDATE {} IN anomaly_resolutions
            LET anomaly_doc = NEW
          
          UPSERT { _key: mapping_key }
            INSERT {
              _key: mapping_key,
              _from: CONCAT('padic_valuations/', v._key),
              _to: CONCAT('anomaly_resolutions/', anomaly_doc._key),
              mapping_id: mapping_key,
              discrete_type: 'PadicValuation',
              continuous_type: 'TraceZeroAnomaly',
              discrete_key: 'v₂(137)',
              continuous_key: 'trace(S)',
              mapping_type: 'padic_to_trace_anomaly',
              mapping_formula: 'v₂(137) = 0 ↦ trace(S) = 0',
              preserved_structure: ['vanishing', 'anomaly_cancellation', 'centralizer'],
              mathematical_justification: '2-adic vanishing ↦ bivector trace vanishing (both = 0)'
            }
            UPDATE {
              _from: CONCAT('padic_valuations/', v._key),
              _to: CONCAT('anomaly_resolutions/', anomaly_doc._key),
              mapping_id: mapping_key,
              discrete_type: 'PadicValuation',
              continuous_type: 'TraceZeroAnomaly',
              discrete_key: 'v₂(137)',
              continuous_key: 'trace(S)',
              mapping_type: 'padic_to_trace_anomaly',
              mapping_formula: 'v₂(137) = 0 ↦ trace(S) = 0',
              preserved_structure: ['vanishing', 'anomaly_cancellation', 'centralizer'],
              mathematical_justification: '2-adic vanishing ↦ bivector trace vanishing (both = 0)'
            } IN functorial_mappings
            LET mapping_doc = NEW
          
          RETURN {
            valuation: v,
            anomaly: anomaly_doc,
            mapping: mapping_doc
          }
        """
    
    @property
    def mersenne_to_su3_color_query(self) -> str:
        """AQL: Map M_2 = 3 to SU(3) color gauge structure via Zorn slots"""
        return """
        FOR m IN mersenne_primes
          FILTER m.p == 2  /* M_2 = 3 */
          
          /* Step 1: Create/update SU(3) symmetry group */
          UPSERT { _key: 'su3_color_gauge' }
            INSERT {
              _key: 'su3_color_gauge',
              group_name: 'SU(3)',
              group_dim: 8,
              description: 'Color gauge group from M_2 = 3',
              stabilizes_diagonal: true,
              source_mersenne: m.value
            }
            UPDATE { source_mersenne: m.value } IN symmetry_groups
          
          /* Step 2: Create Zorn slots for quark (𝑥⃗) and antiquark (𝑦⃗) */
          UPSERT { _key: 'zorn_quark_slot' }
            INSERT {
              _key: 'zorn_quark_slot',
              slot_type: 'vector_3',
              slot_dim: 3,
              slot_content: '𝑥⃗',
              representation: '3 (fundamental)',
              tripotent_eigenvalue: 1,
              source_mersenne: m.value
            }
            UPDATE { source_mersenne: m.value } IN zorn_slots
          
          UPSERT { _key: 'zorn_antiquark_slot' }
            INSERT {
              _key: 'zorn_antiquark_slot',
              slot_type: 'vector_3bar',
              slot_dim: 3,
              slot_content: '𝑦⃗',
              representation: '3̄ (anti-fundamental)',
              tripotent_eigenvalue: -1,
              source_mersenne: m.value
            }
            UPDATE { source_mersenne: m.value } IN zorn_slots
          
          /* Step 3: Create color gauge mapping edges (separate queries to avoid NEW access issue) */
          UPSERT { 
            _from: CONCAT('mersenne_primes/', m._key),
            _to: 'zorn_slots/zorn_quark_slot',
            mapping_type: 'mersenne_to_color_quark'
          }
            INSERT {
              _from: CONCAT('mersenne_primes/', m._key),
              _to: 'zorn_slots/zorn_quark_slot',
              _key: CONCAT('mersenne_to_quark_M_', TO_STRING(m.p)),
              mapping_id: CONCAT('mersenne_to_quark_M_', TO_STRING(m.p)),
              discrete_type: 'MersennePrime',
              continuous_type: 'ZornSlot',
              discrete_key: CONCAT('M_', m.p),
              continuous_key: '𝑥⃗ (quark)',
              mapping_type: 'mersenne_to_color_quark',
              mapping_formula: CONCAT('M_', m.p, ' ↦ 𝑥⃗ (dim = 3)'),
              preserved_structure: ['dimension', 'su3_action', 'tripotent_eigenvalue'],
              mathematical_justification: 'Günaydin-Gürsey: M_2 = 3 ↦ fundamental 3 of SU(3)'
            }
            UPDATE {} IN color_gauge_mappings
          
          UPSERT { 
            _from: CONCAT('mersenne_primes/', m._key),
            _to: 'zorn_slots/zorn_antiquark_slot',
            mapping_type: 'mersenne_to_color_antiquark'
          }
            INSERT {
              _from: CONCAT('mersenne_primes/', m._key),
              _to: 'zorn_slots/zorn_antiquark_slot',
              _key: CONCAT('mersenne_to_antiquark_M_', TO_STRING(m.p)),
              mapping_id: CONCAT('mersenne_to_antiquark_M_', TO_STRING(m.p)),
              discrete_type: 'MersennePrime',
              continuous_type: 'ZornSlot',
              discrete_key: CONCAT('M_', m.p),
              continuous_key: '𝑦⃗ (antiquark)',
              mapping_type: 'mersenne_to_color_antiquark',
              mapping_formula: CONCAT('M_', m.p, ' ↦ 𝑦⃗ (dim = 3)'),
              preserved_structure: ['dimension', 'su3_action', 'tripotent_eigenvalue'],
              mathematical_justification: 'Günaydin-Gürsey: M_2 = 3 ↦ anti-fundamental 3̄ of SU(3)'
            }
            UPDATE {} IN color_gauge_mappings
          
          RETURN {
            mersenne: m,
            success: true
          }
        """


# ===========================================================================
# Bridge Runner
# ===========================================================================

class FunctorialBridgeRunner:
    """Execute the functorial bridge mapping"""
    
    def __init__(self, db: Database, quiet: bool = False):
        self.db = db
        self.aql = AQLQueries(db)
        self.quiet = quiet
    
    def _print(self, msg: str) -> None:
        """Print only if not in quiet mode."""
        if not self.quiet:
            print(msg)
    
    def populate_discrete_data(self) -> Dict[str, int]:
        """Insert discrete combinatorial data"""
        counts = {}
        
        # Insert known Mersenne primes
        self._print("\n=== Inserting Mersenne primes ===")
        count = 0
        for m in MersennePrime.known_mersennes():
            result = self.aql.insert_mersenne_prime(m)
            if result:
                count += 1
                self._print(f"  ✓ M_{m.p} = {m.value}")
        counts['mersenne_primes'] = count
        
        # Insert p-adic valuations
        self._print("\n=== Inserting p-adic valuations ===")
        v = PadicValuation.fine_structure_constant()
        result = self.aql.insert_padic_valuation(v)
        if result:
            self._print(f"  ✓ v₂({v.n}) = {v.valuation}")
            counts['padic_valuations'] = 1
        else:
            counts['padic_valuations'] = 0
        
        # Insert golden powers
        self._print("\n=== Inserting golden powers ===")
        count = 0
        for n in range(1, 10):
            gp = GoldenPower.compute(n)
            result = self.aql.insert_golden_power(gp)
            if result:
                count += 1
                self._print(f"  ✓ τ^{n} ≈ {gp.tau_n:.4f} (F_{{{n}}} = {gp.fib_n})")
        counts['golden_powers'] = count
        
        return counts
    
    def populate_continuous_data(self) -> Dict[str, int]:
        """Insert continuous geometric limit data"""
        counts = {}
        
        # Insert Clifford algebras from Mersenne primes
        self._print("\n=== Inserting Clifford algebras ===")
        count = 0
        for m in MersennePrime.known_mersennes():
            ca = CliffordAlgebra.from_mersenne(m)
            result = self.aql.insert_clifford_algebra(ca)
            if result:
                count += 1
                self._print(f"  ✓ Cl({ca.p},{ca.q}) dim={ca.dimension}, bivector_dim={ca.bivector_dimension}")
        counts['clifford_algebras'] = count
        
        # Insert Krein spaces
        self._print("\n=== Inserting Krein spaces ===")
        count = 0
        for m in MersennePrime.known_mersennes():
            ks = KreinSpace.from_mersenne(m)
            result = self.aql.insert_krein_space(ks)
            if result:
                count += 1
                self._print(f"  ✓ Krein({ks.signature_p},{ks.signature_q})")
        counts['krein_spaces'] = count
        
        # Insert Hestenes rotors from golden powers
        print("\n=== Inserting Hestenes rotors ===")
        count = 0
        for n in range(1, 10):
            gp = GoldenPower.compute(n)
            hr = HestenesRotor.from_golden_power(gp)
            result = self.aql.insert_hestenes_rotor(hr)
            if result:
                count += 1
                print(f"  ✓ R({n}φ) = {hr.rotor_expr}")
        counts['hestenes_rotors'] = count

        # Insert tripotent eigenvalues
        print("\n=== Inserting tripotent eigenvalues ===")
        count = 0
        for te in TripotentEigenvalue.classifier():
            result = self.aql.insert_tripotent_eigenvalue(te)
            if result:
                count += 1
                print(f"  ✓ λ = {te.eigenvalue}: {te.eigen_type} ({te.peirce_component})")
        counts['tripotent_eigenvalues'] = count

        # Insert diagonal projectors
        print("\n=== Inserting diagonal projectors ===")
        count = 0
        for dp in DiagonalProjector.peirce_projectors():
            result = self.aql.insert_diagonal_projector(dp)
            if result:
                count += 1
                print(f"  ✓ {dp.projector_id} = {dp.projector_val}")
        counts['diagonal_projectors'] = count
        
        return counts
    
    def run_functorial_mappings(self) -> Dict[str, int]:
        """Execute AQL functorial mapping queries"""
        counts = {}
        
        # Mersenne → Clifford
        self._print("\n=== Running Mersenne → Clifford mapping ===")
        try:
            cursor = self.db.aql.execute(self.aql.mersenne_to_clifford_query)
            results = list(cursor)
            counts['mersenne_to_clifford'] = len(results)
            self._print(f"  ✓ Created {len(results)} Clifford mappings")
        except Exception as e:
            self._print(f"  ✗ Error: {e}")
            counts['mersenne_to_clifford'] = 0
        
        # Mersenne → Krein
        self._print("\n=== Running Mersenne → Krein mapping ===")
        try:
            cursor = self.db.aql.execute(self.aql.mersenne_to_krein_query)
            results = list(cursor)
            counts['mersenne_to_krein'] = len(results)
            self._print(f"  ✓ Created {len(results)} Krein mappings")
        except Exception as e:
            self._print(f"  ✗ Error: {e}")
            counts['mersenne_to_krein'] = 0
        
        # Golden → Rotor
        self._print("\n=== Running Golden → Rotor mapping ===")
        try:
            cursor = self.db.aql.execute(self.aql.golden_to_rotor_query)
            results = list(cursor)
            counts['golden_to_rotor'] = len(results)
            self._print(f"  ✓ Created {len(results)} Rotor mappings")
        except Exception as e:
            self._print(f"  ✗ Error: {e}")
            counts['golden_to_rotor'] = 0
        
        # p-adic → Anomaly
        self._print("\n=== Running p-adic → Anomaly resolution mapping ===")
        try:
            cursor = self.db.aql.execute(self.aql.padic_anomaly_resolution_query)
            results = list(cursor)
            counts['padic_anomaly'] = len(results)
            self._print(f"  ✓ Created {len(results)} anomaly resolution mappings")
        except Exception as e:
            self._print(f"  ✗ Error: {e}")
            counts['padic_anomaly'] = 0
        
        # Mersenne → SU(3) Color Gauge
        self._print("\n=== Running Mersenne → SU(3) Color Gauge mapping ===")
        try:
            # Step 1: Create symmetry group
            self.db.aql.execute("""
              UPSERT { _key: 'su3_color_gauge' }
                INSERT { _key: 'su3_color_gauge', group_name: 'SU(3)', group_dim: 8, description: 'Color gauge group from M_2 = 3', stabilizes_diagonal: true, source_mersenne: 3 }
                UPDATE { source_mersenne: 3 } IN symmetry_groups
            """)
            
            # Step 2: Create Zorn slots
            self.db.aql.execute("""
              UPSERT { _key: 'zorn_quark_slot' }
                INSERT { _key: 'zorn_quark_slot', slot_type: 'vector_3', slot_dim: 3, slot_content: '𝑥⃗', representation: '3 (fundamental)', tripotent_eigenvalue: 1, source_mersenne: 3 }
                UPDATE { source_mersenne: 3 } IN zorn_slots
            """)
            self.db.aql.execute("""
              UPSERT { _key: 'zorn_antiquark_slot' }
                INSERT { _key: 'zorn_antiquark_slot', slot_type: 'vector_3bar', slot_dim: 3, slot_content: '𝑦⃗', representation: '3̄ (anti-fundamental)', tripotent_eigenvalue: -1, source_mersenne: 3 }
                UPDATE { source_mersenne: 3 } IN zorn_slots
            """)
            
            # Step 3: Create mapping edges with deterministic _key UPSERT
            self.db.aql.execute("""
              FOR m IN mersenne_primes FILTER m.p == 2
              UPSERT { _key: 'mersenne_to_quark_M_2' }
                INSERT {
                  _key: 'mersenne_to_quark_M_2',
                  _from: CONCAT('mersenne_primes/', m._key),
                  _to: 'zorn_slots/zorn_quark_slot',
                  mapping_id: 'mersenne_to_quark_M_2',
                  discrete_type: 'MersennePrime',
                  continuous_type: 'ZornSlot',
                  discrete_key: 'M_2',
                  continuous_key: '𝑥⃗ (quark)',
                  mapping_type: 'mersenne_to_color_quark',
                  mapping_formula: 'M_2 ↦ 𝑥⃗ (dim = 3)',
                  preserved_structure: ['dimension', 'su3_action', 'tripotent_eigenvalue'],
                  mathematical_justification: 'Günaydin-Gürsey: M_2 = 3 ↦ fundamental 3 of SU(3)'
                }
                UPDATE {
                  _from: CONCAT('mersenne_primes/', m._key),
                  _to: 'zorn_slots/zorn_quark_slot',
                  mapping_id: 'mersenne_to_quark_M_2',
                  discrete_type: 'MersennePrime',
                  continuous_type: 'ZornSlot',
                  discrete_key: 'M_2',
                  continuous_key: '𝑥⃗ (quark)',
                  mapping_type: 'mersenne_to_color_quark',
                  mapping_formula: 'M_2 ↦ 𝑥⃗ (dim = 3)',
                  preserved_structure: ['dimension', 'su3_action', 'tripotent_eigenvalue'],
                  mathematical_justification: 'Günaydin-Gürsey: M_2 = 3 ↦ fundamental 3 of SU(3)'
                } IN color_gauge_mappings
            """)
            self.db.aql.execute("""
              FOR m IN mersenne_primes FILTER m.p == 2
              UPSERT { _key: 'mersenne_to_antiquark_M_2' }
                INSERT {
                  _key: 'mersenne_to_antiquark_M_2',
                  _from: CONCAT('mersenne_primes/', m._key),
                  _to: 'zorn_slots/zorn_antiquark_slot',
                  mapping_id: 'mersenne_to_antiquark_M_2',
                  discrete_type: 'MersennePrime',
                  continuous_type: 'ZornSlot',
                  discrete_key: 'M_2',
                  continuous_key: '𝑦⃗ (antiquark)',
                  mapping_type: 'mersenne_to_color_antiquark',
                  mapping_formula: 'M_2 ↦ 𝑦⃗ (dim = 3)',
                  preserved_structure: ['dimension', 'su3_action', 'tripotent_eigenvalue'],
                  mathematical_justification: 'Günaydin-Gürsey: M_2 = 3 ↦ anti-fundamental 3̄ of SU(3)'
                }
                UPDATE {
                  _from: CONCAT('mersenne_primes/', m._key),
                  _to: 'zorn_slots/zorn_antiquark_slot',
                  mapping_id: 'mersenne_to_antiquark_M_2',
                  discrete_type: 'MersennePrime',
                  continuous_type: 'ZornSlot',
                  discrete_key: 'M_2',
                  continuous_key: '𝑦⃗ (antiquark)',
                  mapping_type: 'mersenne_to_color_antiquark',
                  mapping_formula: 'M_2 ↦ 𝑦⃗ (dim = 3)',
                  preserved_structure: ['dimension', 'su3_action', 'tripotent_eigenvalue'],
                  mathematical_justification: 'Günaydin-Gürsey: M_2 = 3 ↦ anti-fundamental 3̄ of SU(3)'
                } IN color_gauge_mappings
            """)
            
            self._print(f"  ✓ Created color gauge mappings (SU(3), Zorn slots, edges)")
            counts['mersenne_to_su3_color'] = 2
        except Exception as e:
            self._print(f"  ✗ Error: {e}")
            counts['mersenne_to_su3_color'] = 0
        
        # Tripotent → Projector edges (Peirce decomposition)
        self._print("\n=== Running Tripotent → Projector mapping (Peirce decomposition) ===")
        try:
            # Ensure peirce_mappings collection exists
            if not self.db.has_collection('peirce_mappings'):
                self.db.create_collection('peirce_mappings', edge=True)
            
            # λ = +1 (quark) → OP1 (left projector)
            self.db.aql.execute("""
              UPSERT { _key: 'tripotent_plus_to_op1' }
                INSERT {
                  _key: 'tripotent_plus_to_op1',
                  _from: 'tripotent_eigenvalues/tripotent_1',
                  _to: 'diagonal_projectors/projector_OP1',
                  mapping_id: 'tripotent_plus_to_op1',
                  discrete_type: 'TripotentEigenvalue',
                  continuous_type: 'DiagonalProjector',
                  discrete_key: 'λ = +1',
                  continuous_key: 'OP1',
                  mapping_type: 'tripotent_to_projector',
                  mapping_formula: 'λ = +1 ↦ OP1 = [[1,0],[0,0]]',
                  preserved_structure: ['peirce_decomposition', 'sandwich_role'],
                  mathematical_justification: 'Tripotent +1 eigenvalue projects onto quark slot via OP1 (left)',
                  sandwich_role: 'left',
                  acts_on: '𝑥⃗'
                }
                UPDATE {
                  _from: 'tripotent_eigenvalues/tripotent_1',
                  _to: 'diagonal_projectors/projector_OP1',
                  mapping_type: 'tripotent_to_projector',
                  mapping_formula: 'λ = +1 ↦ OP1 = [[1,0],[0,0]]',
                  preserved_structure: ['peirce_decomposition', 'sandwich_role'],
                  mathematical_justification: 'Tripotent +1 eigenvalue projects onto quark slot via OP1 (left)',
                  sandwich_role: 'left',
                  acts_on: '𝑥⃗'
                } IN peirce_mappings
            """)
            
            # λ = -1 (antiquark) → OP2 (right projector)
            self.db.aql.execute("""
              UPSERT { _key: 'tripotent_minus_to_op2' }
                INSERT {
                  _key: 'tripotent_minus_to_op2',
                  _from: 'tripotent_eigenvalues/tripotent_-1',
                  _to: 'diagonal_projectors/projector_OP2',
                  mapping_id: 'tripotent_minus_to_op2',
                  discrete_type: 'TripotentEigenvalue',
                  continuous_type: 'DiagonalProjector',
                  discrete_key: 'λ = -1',
                  continuous_key: 'OP2',
                  mapping_type: 'tripotent_to_projector',
                  mapping_formula: 'λ = -1 ↦ OP2 = [[0,0],[0,1]]',
                  preserved_structure: ['peirce_decomposition', 'sandwich_role'],
                  mathematical_justification: 'Tripotent -1 eigenvalue projects onto antiquark slot via OP2 (right)',
                  sandwich_role: 'right',
                  acts_on: '𝑦⃗'
                }
                UPDATE {
                  _from: 'tripotent_eigenvalues/tripotent_-1',
                  _to: 'diagonal_projectors/projector_OP2',
                  mapping_type: 'tripotent_to_projector',
                  mapping_formula: 'λ = -1 ↦ OP2 = [[0,0],[0,1]]',
                  preserved_structure: ['peirce_decomposition', 'sandwich_role'],
                  mathematical_justification: 'Tripotent -1 eigenvalue projects onto antiquark slot via OP2 (right)',
                  sandwich_role: 'right',
                  acts_on: '𝑦⃗'
                } IN peirce_mappings
            """)
            
            # λ = 0 (vacuum) → both OP1 and OP2 (diagonal scalars a,b)
            self.db.aql.execute("""
              UPSERT { _key: 'tripotent_zero_to_op1' }
                INSERT {
                  _key: 'tripotent_zero_to_op1',
                  _from: 'tripotent_eigenvalues/tripotent_0',
                  _to: 'diagonal_projectors/projector_OP1',
                  mapping_id: 'tripotent_zero_to_op1',
                  discrete_type: 'TripotentEigenvalue',
                  continuous_type: 'DiagonalProjector',
                  discrete_key: 'λ = 0',
                  continuous_key: 'OP1',
                  mapping_type: 'tripotent_to_projector_vacuum',
                  mapping_formula: 'λ = 0 ↦ OP1 acts on a (vacuum)',
                  preserved_structure: ['peirce_decomposition', 'diagonal_stabilizer'],
                  mathematical_justification: 'Tripotent 0 eigenvalue: vacuum/diagonal scalars stabilized by SU(3)',
                  sandwich_role: 'bilateral',
                  acts_on: 'a'
                }
                UPDATE {
                  _from: 'tripotent_eigenvalues/tripotent_0',
                  _to: 'diagonal_projectors/projector_OP1',
                  mapping_type: 'tripotent_to_projector_vacuum',
                  mapping_formula: 'λ = 0 ↦ OP1 acts on a (vacuum)',
                  preserved_structure: ['peirce_decomposition', 'diagonal_stabilizer'],
                  mathematical_justification: 'Tripotent 0 eigenvalue: vacuum/diagonal scalars stabilized by SU(3)',
                  sandwich_role: 'bilateral',
                  acts_on: 'a'
                } IN peirce_mappings
            """)
            
            self.db.aql.execute("""
              UPSERT { _key: 'tripotent_zero_to_op2' }
                INSERT {
                  _key: 'tripotent_zero_to_op2',
                  _from: 'tripotent_eigenvalues/tripotent_0',
                  _to: 'diagonal_projectors/projector_OP2',
                  mapping_id: 'tripotent_zero_to_op2',
                  discrete_type: 'TripotentEigenvalue',
                  continuous_type: 'DiagonalProjector',
                  discrete_key: 'λ = 0',
                  continuous_key: 'OP2',
                  mapping_type: 'tripotent_to_projector_vacuum',
                  mapping_formula: 'λ = 0 ↦ OP2 acts on b (vacuum)',
                  preserved_structure: ['peirce_decomposition', 'diagonal_stabilizer'],
                  mathematical_justification: 'Tripotent 0 eigenvalue: vacuum/diagonal scalars stabilized by SU(3)',
                  sandwich_role: 'bilateral',
                  acts_on: 'b'
                }
                UPDATE {
                  _from: 'tripotent_eigenvalues/tripotent_0',
                  _to: 'diagonal_projectors/projector_OP2',
                  mapping_type: 'tripotent_to_projector_vacuum',
                  mapping_formula: 'λ = 0 ↦ OP2 acts on b (vacuum)',
                  preserved_structure: ['peirce_decomposition', 'diagonal_stabilizer'],
                  mathematical_justification: 'Tripotent 0 eigenvalue: vacuum/diagonal scalars stabilized by SU(3)',
                  sandwich_role: 'bilateral',
                  acts_on: 'b'
                } IN peirce_mappings
            """)
            
            self._print(f"  ✓ Created Peirce decomposition mappings (λ → OP1/OP2)")
            counts['tripotent_to_projector'] = 4
        except Exception as e:
            self._print(f"  ✗ Error: {e}")
            counts['tripotent_to_projector'] = 0
        
        # M_3 = 7 → Octonion Imaginary Units
        self._print("\n=== Running M_3 = 7 → Octonion Imaginary Units mapping ===")
        try:
            # Create octonion units
            self.db.aql.execute("""
              UPSERT { _key: 'octonion_imaginary_units' }
                INSERT { _key: 'octonion_imaginary_units', unit_count: 7, description: 'Imaginary octonion units from M_3 = 7', source_mersenne: 7 }
                UPDATE { source_mersenne: 7 } IN symmetry_groups
            """)
            
            # Create 7 unit slots
            for i in range(1, 8):
                self.db.aql.execute(f"""
                  UPSERT {{ _key: 'octonion_unit_{i}' }}
                    INSERT {{ _key: 'octonion_unit_{i}', slot_type: 'imaginary_unit', slot_dim: 1, slot_content: 'e_{i}', representation: 'Im(O)', tripotent_eigenvalue: 0, source_mersenne: 7, unit_index: {i} }}
                    UPDATE {{ source_mersenne: 7 }} IN zorn_slots
                """)
            
            # Create mapping edge with deterministic _key UPSERT
            self.db.aql.execute("""
              FOR m IN mersenne_primes FILTER m.p == 3
              UPSERT { _key: 'mersenne_to_octonion_M_3' }
                INSERT {
                  _key: 'mersenne_to_octonion_M_3',
                  _from: CONCAT('mersenne_primes/', m._key),
                  _to: 'zorn_slots/octonion_imaginary_units',
                  mapping_id: 'mersenne_to_octonion_M_3',
                  discrete_type: 'MersennePrime',
                  continuous_type: 'ZornSlot',
                  discrete_key: 'M_3',
                  continuous_key: 'e_1..e_7 (Im(O))',
                  mapping_type: 'mersenne_to_octonion_units',
                  mapping_formula: 'M_3 ↦ {e_1, ..., e_7} (dim = 7)',
                  preserved_structure: ['dimension', 'g2_action', 'fano_plane'],
                  mathematical_justification: 'M_3 = 7 ↦ 7 imaginary octonion units (G2 automorphism group)'
                }
                UPDATE {
                  _from: CONCAT('mersenne_primes/', m._key),
                  _to: 'zorn_slots/octonion_imaginary_units',
                  mapping_id: 'mersenne_to_octonion_M_3',
                  discrete_type: 'MersennePrime',
                  continuous_type: 'ZornSlot',
                  discrete_key: 'M_3',
                  continuous_key: 'e_1..e_7 (Im(O))',
                  mapping_type: 'mersenne_to_octonion_units',
                  mapping_formula: 'M_3 ↦ {e_1, ..., e_7} (dim = 7)',
                  preserved_structure: ['dimension', 'g2_action', 'fano_plane'],
                  mathematical_justification: 'M_3 = 7 ↦ 7 imaginary octonion units (G2 automorphism group)'
                } IN color_gauge_mappings
            """)
            
            self._print(f"  ✓ Created octonion units mapping (7 imaginary units e_1..e_7)")
            counts['mersenne_to_octonion'] = 1
        except Exception as e:
            self._print(f"  ✗ Error: {e}")
            counts['mersenne_to_octonion'] = 0
        
        # M_7 = 127 → Exceptional Structure (E8, Triality)
        self._print("\n=== Running M_7 = 127 → Exceptional Structure mapping ===")
        try:
            # Create E8 root system entry
            self.db.aql.execute("""
              UPSERT { _key: 'e8_root_system' }
                INSERT { _key: 'e8_root_system', group_name: 'E8', group_dim: 248, rank: 8, root_count: 240, description: 'E8 root system from M_7 = 127 + 120 + 1', source_mersenne: 127 }
                UPDATE { source_mersenne: 127 } IN symmetry_groups
            """)
            
            # Create triality mapping
            self.db.aql.execute("""
              UPSERT { _key: 'triality_structure' }
                INSERT { _key: 'triality_structure', group_name: 'Spin(8)', group_dim: 28, automorphism: 'S3', description: 'Triality automorphism of Spin(8)', source_mersenne: 127 }
                UPDATE { source_mersenne: 127 } IN symmetry_groups
            """)
            
            # Create mapping edges with deterministic _key UPSERT
            self.db.aql.execute("""
              FOR m IN mersenne_primes FILTER m.p == 7
              UPSERT { _key: 'mersenne_to_e8_M_7' }
                INSERT {
                  _key: 'mersenne_to_e8_M_7',
                  _from: CONCAT('mersenne_primes/', m._key),
                  _to: 'symmetry_groups/e8_root_system',
                  mapping_id: 'mersenne_to_e8_M_7',
                  discrete_type: 'MersennePrime',
                  continuous_type: 'SymmetryGroup',
                  discrete_key: 'M_7',
                  continuous_key: 'E8 (dim 248)',
                  mapping_type: 'mersenne_to_exceptional_e8',
                  mapping_formula: 'M_7 ↦ E8 (127 + 120 + 1 = 248)',
                  preserved_structure: ['dimension', 'root_system', 'coxeter_number'],
                  mathematical_justification: 'M_7 = 127 ↦ E8 root system (127 positive roots + 120 + 1 = 248)'
                }
                UPDATE {
                  _from: CONCAT('mersenne_primes/', m._key),
                  _to: 'symmetry_groups/e8_root_system',
                  mapping_id: 'mersenne_to_e8_M_7',
                  discrete_type: 'MersennePrime',
                  continuous_type: 'SymmetryGroup',
                  discrete_key: 'M_7',
                  continuous_key: 'E8 (dim 248)',
                  mapping_type: 'mersenne_to_exceptional_e8',
                  mapping_formula: 'M_7 ↦ E8 (127 + 120 + 1 = 248)',
                  preserved_structure: ['dimension', 'root_system', 'coxeter_number'],
                  mathematical_justification: 'M_7 = 127 ↦ E8 root system (127 positive roots + 120 + 1 = 248)'
                } IN color_gauge_mappings
            """)
            
            self.db.aql.execute("""
              FOR m IN mersenne_primes FILTER m.p == 7
              UPSERT { _key: 'mersenne_to_triality_M_7' }
                INSERT {
                  _key: 'mersenne_to_triality_M_7',
                  _from: CONCAT('mersenne_primes/', m._key),
                  _to: 'symmetry_groups/triality_structure',
                  mapping_id: 'mersenne_to_triality_M_7',
                  discrete_type: 'MersennePrime',
                  continuous_type: 'SymmetryGroup',
                  discrete_key: 'M_7',
                  continuous_key: 'Spin(8) triality',
                  mapping_type: 'mersenne_to_exceptional_triality',
                  mapping_formula: 'M_7 ↦ Spin(8) triality (S3 automorphism)',
                  preserved_structure: ['dimension', 'triality', 'spin_representation'],
                  mathematical_justification: 'M_7 = 127 ↦ Spin(8) triality (exceptional outer automorphism S3)'
                }
                UPDATE {
                  _from: CONCAT('mersenne_primes/', m._key),
                  _to: 'symmetry_groups/triality_structure',
                  mapping_id: 'mersenne_to_triality_M_7',
                  discrete_type: 'MersennePrime',
                  continuous_type: 'SymmetryGroup',
                  discrete_key: 'M_7',
                  continuous_key: 'Spin(8) triality',
                  mapping_type: 'mersenne_to_exceptional_triality',
                  mapping_formula: 'M_7 ↦ Spin(8) triality (S3 automorphism)',
                  preserved_structure: ['dimension', 'triality', 'spin_representation'],
                  mathematical_justification: 'M_7 = 127 ↦ Spin(8) triality (exceptional outer automorphism S3)'
                } IN color_gauge_mappings
            """)
            
            self._print(f"  ✓ Created exceptional structure mapping (E8, Spin(8) triality)")
            counts['mersenne_to_exceptional'] = 2
        except Exception as e:
            self._print(f"  ✗ Error: {e}")
            counts['mersenne_to_exceptional'] = 0
        
        return counts
    
    def print_summary(self):
        """Print summary of all data in the database"""
        print("\n" + "="*70)
        print("FUNCTORIAL BRIDGE SUMMARY")
        print("="*70)
        
        collections = {
            'mersenne_primes': 'Mersenne Primes (Discrete)',
            'padic_valuations': 'p-adic Valuations (Discrete)',
            'golden_powers': 'Golden Powers (Discrete)',
            'clifford_algebras': 'Clifford Algebras (Continuous)',
            'krein_spaces': 'Krein Spaces (Continuous)',
            'hestenes_rotors': 'Hestenes Rotors (Continuous)',
            'zorn_slots': 'Zorn Slots (SU(3) Color)',
            'symmetry_groups': 'Symmetry Groups',
            'tripotent_eigenvalues': 'Tripotent Eigenvalues',
            'diagonal_projectors': 'Diagonal Projectors',
            'peirce_mappings': 'Peirce Decomposition Mappings',
            'functorial_mappings': 'Functorial Mappings',
            'color_gauge_mappings': 'Color Gauge Mappings',
            'anomaly_resolutions': 'Anomaly Resolutions'
        }
        
        for coll_name, description in collections.items():
            try:
                count = self.db.collection(coll_name).count()
                print(f"{description:40s}: {count:3d}")
            except Exception:
                print(f"{description:40s}: N/A")
        
        print("\n=== Functorial Mappings Detail ===")
        try:
            cursor = self.db.aql.execute("""
                FOR m IN functorial_mappings
                  RETURN {
                    mapping_type: m.mapping_type,
                    from: m.discrete_key,
                    to: m.continuous_key,
                    formula: m.mapping_formula
                  }
            """)
            mappings = list(cursor)
            for i, m in enumerate(mappings[:10], 1):
                print(f"  {i}. {m['from']} → {m['to']}")
                print(f"     Formula: {m['formula']}")
            if len(mappings) > 10:
                print(f"  ... and {len(mappings) - 10} more")
        except Exception as e:
            print(f"  Error retrieving mappings: {e}")

    def export_isabelle_json(self, output_path: str) -> Path:
        """Export a machine-readable bridge artifact for downstream Isabelle/HOL ingestion."""
        cursor = self.db.aql.execute("""
            LET color = (
              FOR m IN color_gauge_mappings
                SORT m.mapping_type, m.discrete_key, m.continuous_key
                RETURN {
                  key: m._key,
                  discrete_key: m.discrete_key,
                  continuous_key: m.continuous_key,
                  mapping_type: m.mapping_type,
                  mapping_formula: m.mapping_formula,
                  preserved_structure: m.preserved_structure,
                  mathematical_justification: m.mathematical_justification
                }
            )
            LET functorial = (
              FOR m IN functorial_mappings
                SORT m.mapping_type, m.discrete_key, m.continuous_key
                RETURN {
                  key: m._key,
                  discrete_key: m.discrete_key,
                  continuous_key: m.continuous_key,
                  mapping_type: m.mapping_type,
                  mapping_formula: m.mapping_formula,
                  preserved_structure: m.preserved_structure,
                  mathematical_justification: m.mathematical_justification
                }
            )
            LET zorn = (
              FOR z IN zorn_slots
                SORT z._key
                RETURN z
            )
            LET groups = (
              FOR g IN symmetry_groups
                SORT g._key
                RETURN g
            )
            LET peirce = (
              FOR p IN peirce_mappings
                SORT p._key
                RETURN {
                  key: p._key,
                  _from: p._from,
                  _to: p._to,
                  discrete_key: p.discrete_key,
                  continuous_key: p.continuous_key,
                  mapping_type: p.mapping_type,
                  mapping_formula: p.mapping_formula,
                  sandwich_role: p.sandwich_role,
                  acts_on: p.acts_on,
                  mathematical_justification: p.mathematical_justification
                }
            )
            RETURN {
              export_kind: 'isabelle_hol_bridge_json',
              color_gauge_mappings: color,
              functorial_mappings: functorial,
              zorn_slots: zorn,
              symmetry_groups: groups,
              peirce_mappings: peirce,
              counts: {
                color_gauge_mappings: LENGTH(color),
                functorial_mappings: LENGTH(functorial),
                zorn_slots: LENGTH(zorn),
                symmetry_groups: LENGTH(groups),
                peirce_mappings: LENGTH(peirce)
              }
            }
        """)
        rows = list(cursor)
        if not rows:
            raise RuntimeError("Isabelle export query returned no rows")
        payload = rows[0]
        payload['database'] = self.db.name
        out = Path(output_path)
        if not out.is_absolute():
            out = Path.cwd() / out
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n", encoding="utf-8")
        return out


# ===========================================================================
# CLI
# ===========================================================================

def _parse_args() -> argparse.Namespace:
    load_repo_arango_env(Path(__file__).resolve().parents[3])
    parser = argparse.ArgumentParser(
        description="AQL Functorial Bridge: Hestenes-Krein Bivector Mapping"
    )
    parser.add_argument("--arangodb-url", default=os.environ.get("ARANGO_ENDPOINT") or arango_endpoint(),
                        help="ArangoDB server URL")
    parser.add_argument("--username", default=os.environ.get("ARANGO_USER") or os.environ.get("ARANGO_USERNAME") or arango_username(), help="ArangoDB username")
    parser.add_argument("--password", default=os.environ.get("ARANGO_PASS") or os.environ.get("ARANGO_PASSWORD") or arango_password(), help="ArangoDB password")
    parser.add_argument("--database", default=os.environ.get("ARANGO_DB") or os.environ.get("ARANGO_DATABASE") or arango_database(), help="Database name")
    parser.add_argument("--populate-discrete", action="store_true",
                        help="Populate discrete combinatorial data")
    parser.add_argument("--populate-continuous", action="store_true",
                        help="Populate continuous geometric data")
    parser.add_argument("--run-mappings", action="store_true",
                        help="Run all functorial mapping queries")
    parser.add_argument("--full-bridge", action="store_true",
                        help="Execute full bridge: populate + map + summary")
    parser.add_argument("--verify-idempotency", action="store_true",
                        help="Run bridge twice and assert counts remain stable (idempotency check)")
    parser.add_argument("--verify-idempotency-json", action="store_true",
                        help="Run idempotency check and output JSON summary (for CI)")
    parser.add_argument("--compact", action="store_true",
                        help="Output compact single-line JSON (use with --verify-idempotency-json)")
    parser.add_argument("--create-database-if-missing", action="store_true",
                        help="Create the target database if it doesn't exist (for scratch verification)")
    parser.add_argument("--print-aql", action="store_true",
                        help="Print AQL query templates")
    parser.add_argument("--summary", action="store_true",
                        help="Print database summary only")
    parser.add_argument("--export-isabelle-json",
                        help="Write a machine-readable Isabelle/HOL bridge export JSON artifact")
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    quiet_json = args.verify_idempotency_json
    
    # Connect to ArangoDB
    try:
        client = ArangoClient(hosts=args.arangodb_url)
        
        # Test connection first
        version_attr = client.version
        version = version_attr() if callable(version_attr) else version_attr
        if not quiet_json:
            print(f"Connected to ArangoDB {version} at {args.arangodb_url}")
        
        # Create database if requested and it doesn't exist
        if args.create_database_if_missing:
            sys_db = client.db('_system', username=args.username, password=args.password)
            if not sys_db.has_database(args.database):
                if not quiet_json:
                    print(f"Creating database: {args.database}")
                sys_db.create_database(args.database)
            else:
                if not quiet_json:
                    print(f"Database already exists: {args.database}")
        
        # Connect to target database
        db = client.db(args.database, username=args.username, password=args.password)
        if not quiet_json:
            print(f"Database: {args.database}")
    except Exception as e:
        if quiet_json:
            print(json.dumps({
                "database": args.database,
                "idempotency_verified": False,
                "mapping_runs_succeeded": False,
                "error": f"{type(e).__name__}: {e}"
            }, indent=2, sort_keys=True))
        else:
            print(f"Failed to connect to ArangoDB: {type(e).__name__}: {e}")
            traceback.print_exc()
            print(f"Please ensure ArangoDB is running at {args.arangodb_url}")
        return 1
    
    # Create bridge runner
    runner = FunctorialBridgeRunner(db, quiet=quiet_json)
    
    if args.print_aql:
        print("\n" + "="*70)
        print("AQL QUERY TEMPLATES")
        print("="*70)
        
        print("\n--- Mersenne → Clifford ---")
        print(runner.aql.mersenne_to_clifford_query)
        
        print("\n--- Mersenne → Krein ---")
        print(runner.aql.mersenne_to_krein_query)
        
        print("\n--- Golden → Rotor ---")
        print(runner.aql.golden_to_rotor_query)
        
        print("\n--- p-adic → Anomaly Resolution ---")
        print(runner.aql.padic_anomaly_resolution_query)
        
        return 0
    
    if args.verify_idempotency:
        print("\n" + "="*70)
        print("IDEMPOTENCY VERIFICATION")
        print("="*70)
        print(f"Running full bridge twice on database: {args.database}")
        print()
        
        # First run
        print(">>> Run 1/2")
        runner.populate_discrete_data()
        runner.populate_continuous_data()
        mapping_counts_1 = runner.run_functorial_mappings()
        counts_1 = _get_collection_counts(runner.db)
        
        # Second run
        print("\n>>> Run 2/2")
        runner.populate_discrete_data()
        runner.populate_continuous_data()
        mapping_counts_2 = runner.run_functorial_mappings()
        counts_2 = _get_collection_counts(runner.db)
        
        # Compare
        print("\n" + "="*70)
        print("IDEMPOTENCY CHECK RESULTS")
        print("="*70)
        
        all_collections = set(counts_1.keys()) | set(counts_2.keys())
        all_match = True
        
        for coll in sorted(all_collections):
            c1 = counts_1.get(coll, 0)
            c2 = counts_2.get(coll, 0)
            match = c1 == c2
            status = "✓" if match else "✗"
            print(f"{status} {coll:30s}: {c1:3d} → {c2:3d}")
            if not match:
                all_match = False
        
        run_failed = _mapping_run_failed(mapping_counts_1) or _mapping_run_failed(mapping_counts_2)
        print()
        if all_match and not run_failed:
            print("✓ IDEMPOTENCY VERIFIED: All counts stable across two runs and all mapping passes succeeded")
            return 0
        if run_failed:
            print("✗ IDEMPOTENCY FAILED: At least one mapping pass reported an error/zero-result run")
        else:
            print("✗ IDEMPOTENCY FAILED: Counts drifted between runs")
        return 1
    
    if args.verify_idempotency_json:
        # Quiet JSON mode: suppress all incidental stdout during bridge execution.
        with redirect_stdout(StringIO()):
            runner.populate_discrete_data()
            runner.populate_continuous_data()
            mapping_counts_1 = runner.run_functorial_mappings()
            counts_1 = _get_collection_counts(runner.db)

            runner.populate_discrete_data()
            runner.populate_continuous_data()
            mapping_counts_2 = runner.run_functorial_mappings()
            counts_2 = _get_collection_counts(runner.db)
        
        # Compare and build JSON result
        all_collections = sorted(set(counts_1.keys()) | set(counts_2.keys()))
        all_match = True
        collection_details = []
        
        for coll in all_collections:
            c1 = counts_1.get(coll, 0)
            c2 = counts_2.get(coll, 0)
            match = c1 == c2
            if not match:
                all_match = False
            collection_details.append({
                "collection": coll,
                "run_1_count": c1,
                "run_2_count": c2,
                "stable": match
            })
        
        run_failed = _mapping_run_failed(mapping_counts_1) or _mapping_run_failed(mapping_counts_2)
        result = {
            "database": args.database,
            "idempotency_verified": all_match and not run_failed,
            "mapping_runs_succeeded": not run_failed,
            "mapping_counts_run_1": mapping_counts_1,
            "mapping_counts_run_2": mapping_counts_2,
            "collections": collection_details,
            "total_collections": len(all_collections),
            "stable_count": sum(1 for c in collection_details if c["stable"]),
            "drifted_count": sum(1 for c in collection_details if not c["stable"])
        }
        
        print(json.dumps(result, indent=2 if not args.compact else None, sort_keys=True, separators=(',', ': ') if not args.compact else (',', ':')))
        return 0 if (all_match and not run_failed) else 1
    
    if args.summary:
        runner.print_summary()
        return 0

    if args.export_isabelle_json:
        out = runner.export_isabelle_json(args.export_isabelle_json)
        print(f"Wrote Isabelle/HOL bridge export: {out}")
        return 0
    
    if args.full_bridge:
        print("\n" + "="*70)
        print("EXECUTING FULL FUNCTORIAL BRIDGE")
        print("="*70)
        
        runner.populate_discrete_data()
        runner.populate_continuous_data()
        runner.run_functorial_mappings()
        runner.print_summary()
        
        return 0
    
    # Individual operations
    if args.populate_discrete:
        runner.populate_discrete_data()
    
    if args.populate_continuous:
        runner.populate_continuous_data()
    
    if args.run_mappings:
        runner.run_functorial_mappings()
    
    # Default: show summary
    runner.print_summary()
    
    return 0


def _get_collection_counts(db: Database) -> Dict[str, int]:
    """Get counts for all bridge collections."""
    collections = [
        'mersenne_primes',
        'padic_valuations',
        'golden_powers',
        'clifford_algebras',
        'krein_spaces',
        'hestenes_rotors',
        'functorial_mappings',
        'anomaly_resolutions',
        'zorn_slots',
        'symmetry_groups',
        'tripotent_eigenvalues',
        'diagonal_projectors',
        'color_gauge_mappings'
    ]
    
    counts = {}
    for coll_name in collections:
        try:
            counts[coll_name] = db.collection(coll_name).count()
        except Exception:
            counts[coll_name] = 0
    
    return counts


def _mapping_run_failed(mapping_counts: Dict[str, int]) -> bool:
    """Return True when a populated bridge run hit a mapping failure."""
    required_positive = [
        'mersenne_to_clifford',
        'mersenne_to_krein',
        'golden_to_rotor',
        'padic_anomaly',
        'mersenne_to_su3_color',
        'mersenne_to_octonion',
        'mersenne_to_exceptional',
    ]
    return any(mapping_counts.get(name, 0) <= 0 for name in required_positive)


if __name__ == '__main__':
    sys.exit(main())