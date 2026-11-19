"""E2E verification package for Primary-Source Mathematical Foundations (info-geometry-lean)."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

REPO_ROOT: Path = Path(__file__).resolve().parents[2]
SCRATCH_DIR: Path = REPO_ROOT / "scratch" / "primary_sources_e2e"
PROBES_DIR: Path = SCRATCH_DIR / "probes"
REPORTS_DIR: Path = SCRATCH_DIR / "reports"

ALLOWED_AXIOMS: frozenset[str] = frozenset({"propext", "Classical.choice", "Quot.sound"})

REQUIRED_LEAN_COPYRIGHT_HEADER: str = (
    "/-\n"
    "Copyright (c) 2026 InfoGeometry Authors. All rights reserved.\n"
    "Released under Apache 2.0 license as described in the file LICENSE.\n"
    "Authors: InfoGeometry Engine Contributors\n"
    "-/\n"
)

PILLARS: tuple[str, ...] = ("r2_f25", "r3", "r1", "r2_m35")

PILLAR_DIR_MAP: dict[str, str] = {
    "r2_f25": "pillar_r2_f25",
    "r3": "pillar_r3",
    "r1": "pillar_r1",
    "r2_m35": "pillar_r2_m35",
}

PILLAR_DIR_TO_KEY: dict[str, str] = {v: k for k, v in PILLAR_DIR_MAP.items()}

PILLAR_HEADING_PATTERNS: dict[str, tuple[str, ...]] = {
    "r2_f25": (r"R2\s*/\s*F2\.5", r"pillar_r2_f25", r"Grassmann"),
    "r3": (r"\bR3\b", r"pillar_r3", r"Clifford"),
    "r1": (r"\bR1\b", r"pillar_r1", r"Peirce"),
    "r2_m35": (r"R2\s*/\s*M3\.[2-5]", r"pillar_r2_m35", r"Pontryagin"),
}

MANIFEST_REL: str = ".papers/primary_sources/MANIFEST.json"
ARCHETYPES_DOC_REL: str = "docs/PRIMARY_SOURCE_ARCHETYPES.md"
PAPERS_ROOT_REL: str = ".papers/primary_sources"
BRIDGE_FILE_REL: str = "lean/InfoGeometry/Canonical/PrimarySourceFourPillarBridge.lean"
TRIANGLE_BRIDGE_REL: str = "lean/InfoGeometry/Canonical/R1R2R3UnifiedTriangleBridge.lean"
CANONICAL_ALL_REL: str = "lean/InfoGeometry/Canonical/All.lean"

PRIMARY_LEAN_FILES: tuple[str, ...] = (
    "lean/InfoGeometry/Projective/GrassmannPrimarySources.lean",
    "lean/InfoGeometry/Erlangen/LieKleinPfaffCartanPrimary.lean",
    "lean/InfoGeometry/Clifford/LipschitzWittRieszPrimary.lean",
    "lean/InfoGeometry/Clifford/KahlerHestenesJWABSPrimary.lean",
    "lean/InfoGeometry/OperatorAlgebra/PeirceCartanKoszulDVPrimary.lean",
    "lean/InfoGeometry/Thermo/OnsagerCasimirKBMPrimary.lean",
    "lean/InfoGeometry/Krein/PontryaginSpace.lean",
    "lean/InfoGeometry/KK/KreinSpectralTriplePrimary.lean",
    BRIDGE_FILE_REL,
)

TARGET_MODULES: tuple[str, ...] = (
    "InfoGeometry.Projective.GrassmannPrimarySources",
    "InfoGeometry.Erlangen.LieKleinPfaffCartanPrimary",
    "InfoGeometry.Clifford.LipschitzWittRieszPrimary",
    "InfoGeometry.Clifford.KahlerHestenesJWABSPrimary",
    "InfoGeometry.OperatorAlgebra.PeirceCartanKoszulDVPrimary",
    "InfoGeometry.Thermo.OnsagerCasimirKBMPrimary",
    "InfoGeometry.Krein.PontryaginSpace",
    "InfoGeometry.KK.KreinSpectralTriplePrimary",
    "InfoGeometry.Canonical.PrimarySourceFourPillarBridge",
    "InfoGeometry.Canonical.R1R2R3UnifiedTriangleBridge",
    "InfoGeometry.Canonical.All",
)

ANCHOR_MODULES: tuple[dict[str, str], ...] = (
    {
        "module": "InfoGeometry.Canonical.R1R2R3UnifiedTriangleBridge",
        "path": "lean/InfoGeometry/Canonical/R1R2R3UnifiedTriangleBridge.lean",
        "pillar": "all",
    },
    {
        "module": "InfoGeometry.KK.ClNNFredholmBridge",
        "path": "lean/InfoGeometry/KK/ClNNFredholmBridge.lean",
        "pillar": "r2_m35",
    },
    {
        "module": "InfoGeometry.OperatorAlgebra.SpectralTriple",
        "path": "lean/InfoGeometry/OperatorAlgebra/SpectralTriple.lean",
        "pillar": "r2_m35",
    },
    {
        "module": "InfoGeometry.Krein.KreinSpace",
        "path": "lean/InfoGeometry/Krein/KreinSpace.lean",
        "pillar": "r2_m35",
    },
    {
        "module": "InfoGeometry.Algebra.DerivationLieLane",
        "path": "lean/InfoGeometry/Algebra/DerivationLieLane.lean",
        "pillar": "r1",
    },
    {
        "module": "InfoGeometry.Erlangen.GrassmannPluckerKleinCrossPillarBridges",
        "path": "lean/InfoGeometry/Erlangen/GrassmannPluckerKleinCrossPillarBridges.lean",
        "pillar": "r2_f25",
    },
    {
        "module": "InfoGeometry.Clifford.CoordinateLessCliffordInvariance",
        "path": "lean/InfoGeometry/Clifford/CoordinateLessCliffordInvariance.lean",
        "pillar": "r3",
    },
    {
        "module": "InfoGeometry.Clifford.Cl11GradedTensorMorita",
        "path": "lean/InfoGeometry/Clifford/Cl11GradedTensorMorita.lean",
        "pillar": "r3",
    },
)

MILESTONES: dict[str, dict[str, object]] = {
    "M1": {
        "name": "Primary-Source Retrieval & Archetype Extraction",
        "pillar": "all",
        "features": (1, 2),
        "required_files": (MANIFEST_REL, ARCHETYPES_DOC_REL),
        "required_dirs": tuple(f"{PAPERS_ROOT_REL}/{d}" for d in PILLAR_DIR_MAP.values()),
    },
    "M2": {
        "name": "Pillar R2 / F2.5 Formalization",
        "pillar": "r2_f25",
        "features": (3, 4, 5, 6, 7),
        "required_files": (
            "lean/InfoGeometry/Projective/GrassmannPrimarySources.lean",
            "lean/InfoGeometry/Erlangen/LieKleinPfaffCartanPrimary.lean",
        ),
        "required_dirs": (),
    },
    "M3": {
        "name": "Pillar R3 Formalization",
        "pillar": "r3",
        "features": (8, 9, 10, 11, 12),
        "required_files": (
            "lean/InfoGeometry/Clifford/LipschitzWittRieszPrimary.lean",
            "lean/InfoGeometry/Clifford/KahlerHestenesJWABSPrimary.lean",
        ),
        "required_dirs": (),
    },
    "M4": {
        "name": "Pillar R1 Formalization",
        "pillar": "r1",
        "features": (13, 14, 15, 16, 17, 18),
        "required_files": (
            "lean/InfoGeometry/OperatorAlgebra/PeirceCartanKoszulDVPrimary.lean",
            "lean/InfoGeometry/Thermo/OnsagerCasimirKBMPrimary.lean",
        ),
        "required_dirs": (),
    },
    "M5": {
        "name": "Pillar R2 / M3.2-M3.5 Formalization",
        "pillar": "r2_m35",
        "features": (19, 20, 21, 22),
        "required_files": (
            "lean/InfoGeometry/Krein/PontryaginSpace.lean",
            "lean/InfoGeometry/KK/KreinSpectralTriplePrimary.lean",
        ),
        "required_dirs": (),
    },
    "M6": {
        "name": "Cross-Pillar Integration, Traceability & Final Verification",
        "pillar": "all",
        "features": (23,),
        "required_files": (BRIDGE_FILE_REL,),
        "required_dirs": (),
    },
}


@dataclass(frozen=True)
class FounderWorkSpec:
    spec_id: str
    pillar: str
    pillar_dir: str
    feature_id: int
    label: str
    author_patterns: tuple[str, ...]
    required_year_groups: tuple[tuple[str, ...], ...]
    work_id: str = ""


EXPECTED_M1_WORK_IDS: frozenset[str] = frozenset(
    {f"S2-{i:02d}" for i in range(1, 19)} | {f"S3-{i:02d}" for i in range(1, 29)}
)

# 46 primary-source works across all 4 pillars from ORIGINAL_REQUEST.md § R1 (S2-01..S2-18, S3-01..S3-28).
FOUNDER_YEAR_SPEC: tuple[FounderWorkSpec, ...] = (
    # Pillar R2 / F2.5 (10 specs: S2-01..S2-10)
    FounderWorkSpec("r2f25_grassmann_1844", "r2_f25", "pillar_r2_f25", 3, "Grassmann (1844)", (r"grassmann",), (("1844",),), "S2-01"),
    FounderWorkSpec("r2f25_grassmann_1862", "r2_f25", "pillar_r2_f25", 3, "Grassmann (1862)", (r"grassmann",), (("1862",),), "S2-02"),
    FounderWorkSpec("r2f25_plucker_1865", "r2_f25", "pillar_r2_f25", 4, "Plücker (1865)", (r"pl[uü]cker",), (("1865",),), "S2-03"),
    FounderWorkSpec("r2f25_plucker_1868_1869", "r2_f25", "pillar_r2_f25", 4, "Plücker (1868-1869)", (r"pl[uü]cker",), (("1868", "1869"),), "S2-04"),
    FounderWorkSpec("r2f25_lie_1872", "r2_f25", "pillar_r2_f25", 5, "Lie (1872)", (r"\blie\b",), (("1872",),), "S2-05"),
    FounderWorkSpec("r2f25_klein_1872", "r2_f25", "pillar_r2_f25", 5, "Klein (1872)", (r"klein",), (("1872",),), "S2-06"),
    FounderWorkSpec("r2f25_klein_1871_1873", "r2_f25", "pillar_r2_f25", 5, "Klein (1871, 1873)", (r"klein",), (("1871",), ("1873",)), "S2-07"),
    FounderWorkSpec("r2f25_pfaff_darboux_1814_1882", "r2_f25", "pillar_r2_f25", 6, "Pfaff & Darboux (1814-1815, 1882)", (r"pfaff", r"darboux"), (("1814", "1815"), ("1882",)), "S2-08"),
    FounderWorkSpec("r2f25_cartan_1910_1914", "r2_f25", "pillar_r2_f25", 7, "É. Cartan (1910, 1914)", (r"cartan",), (("1910",), ("1914",)), "S2-09"),
    FounderWorkSpec("r2f25_zorn_1930_1933", "r2_f25", "pillar_r2_f25", 7, "Zorn (1930-1933)", (r"zorn",), (("1930", "1931", "1933"),), "S2-10"),
    # Pillar R3 (8 specs: S2-11..S2-18)
    FounderWorkSpec("r3_clifford_1873_1878", "r3", "pillar_r3", 8, "Clifford (1873, 1878)", (r"clifford",), (("1873",), ("1878",)), "S2-11"),
    FounderWorkSpec("r3_lipschitz_1880_1886", "r3", "pillar_r3", 8, "Lipschitz (1880, 1886)", (r"lipschitz",), (("1880",), ("1886",)), "S2-12"),
    FounderWorkSpec("r3_witt_1937", "r3", "pillar_r3", 9, "Witt (1937)", (r"witt",), (("1937",),), "S2-13"),
    FounderWorkSpec("r3_riesz_1946_1958", "r3", "pillar_r3", 9, "Riesz (1946, 1958)", (r"riesz",), (("1946", "1958"),), "S2-14"),
    FounderWorkSpec("r3_kahler_1960_1962", "r3", "pillar_r3", 10, "Kähler (1960, 1962)", (r"k[aäe]hler",), (("1960",), ("1962",)), "S2-15"),
    FounderWorkSpec("r3_hestenes_darboux_1966_1887", "r3", "pillar_r3", 11, "Hestenes & Darboux (1966, 1887)", (r"hestenes", r"darboux"), (("1966",), ("1887",)), "S2-16"),
    FounderWorkSpec("r3_jordan_wigner_1928", "r3", "pillar_r3", 12, "Jordan-Wigner (1928)", (r"jordan", r"wigner"), (("1928",),), "S2-17"),
    FounderWorkSpec("r3_atiyah_bott_shapiro_1964", "r3", "pillar_r3", 12, "Atiyah-Bott-Shapiro (1964)", (r"atiyah", r"bott", r"shapiro"), (("1964",),), "S2-18"),
    # Pillar R1 (17 specs: S3-01..S3-17)
    FounderWorkSpec("r1_b_peirce_1870_1881", "r1", "pillar_r1", 13, "B. Peirce (1870/1881)", (r"b\.\s*peirce|benjamin\s+peirce",), (("1870", "1881"),), "S3-01"),
    FounderWorkSpec("r1_cs_peirce_1870_1883", "r1", "pillar_r1", 13, "C. S. Peirce (1870, 1880, 1883)", (r"c\.\s*s\.\s*peirce|charles\s+s",), (("1870",), ("1880",), ("1883",)), "S3-02"),
    FounderWorkSpec("r1_maurer_1888", "r1", "pillar_r1", 14, "Maurer (1888)", (r"maurer",), (("1888",),), "S3-03"),
    FounderWorkSpec("r1_cartan_1899_1904", "r1", "pillar_r1", 14, "É. Cartan (1899, 1904)", (r"cartan",), (("1899",), ("1904",)), "S3-04"),
    FounderWorkSpec("r1_chevalley_eilenberg_1948", "r1", "pillar_r1", 15, "Chevalley-Eilenberg (1948)", (r"chevalley", r"eilenberg"), (("1948",),), "S3-05"),
    FounderWorkSpec("r1_koszul_1960", "r1", "pillar_r1", 15, "Koszul (1960)", (r"koszul",), (("1960",),), "S3-06"),
    FounderWorkSpec("r1_kahler_1953", "r1", "pillar_r1", 16, "Kähler (1953)", (r"k[aäe]hler",), (("1953",),), "S3-07"),
    FounderWorkSpec("r1_karoubi_1983", "r1", "pillar_r1", 16, "Karoubi (1983)", (r"karoubi",), (("1983",),), "S3-08"),
    FounderWorkSpec("r1_connes_1985", "r1", "pillar_r1", 16, "Connes (1985)", (r"connes",), (("1985",),), "S3-09"),
    FounderWorkSpec("r1_dubois_violette_1988_1996", "r1", "pillar_r1", 16, "Dubois-Violette (1988, 1990, 1996)", (r"dubois[-\s]?violette",), (("1988",), ("1990",), ("1996",)), "S3-10"),
    FounderWorkSpec("r1_frechet_1925", "r1", "pillar_r1", 17, "Fréchet (1925)", (r"fr[eé]chet",), (("1925",),), "S3-11"),
    FounderWorkSpec("r1_h_cartan_1967", "r1", "pillar_r1", 17, "H. Cartan (1967)", (r"cartan",), (("1967",),), "S3-12"),
    FounderWorkSpec("r1_onsager_1931", "r1", "pillar_r1", 18, "Onsager (1931)", (r"onsager",), (("1931",),), "S3-13"),
    FounderWorkSpec("r1_casimir_1945", "r1", "pillar_r1", 18, "Casimir (1945)", (r"casimir",), (("1945",),), "S3-14"),
    FounderWorkSpec("r1_kubo_1957", "r1", "pillar_r1", 18, "Kubo (1957)", (r"kubo",), (("1957",),), "S3-15"),
    FounderWorkSpec("r1_bogoliubov_1961", "r1", "pillar_r1", 18, "Bogoliubov (1961)", (r"bogoliubov",), (("1961", "1962"),), "S3-16"),
    FounderWorkSpec("r1_mori_1965", "r1", "pillar_r1", 18, "Mori (1965)", (r"mori",), (("1965",),), "S3-17"),
    # Pillar R2 / M3.2-M3.5 (11 specs: S3-18..S3-28)
    FounderWorkSpec("r2m35_dirac_1942", "r2_m35", "pillar_r2_m35", 19, "Dirac (1942)", (r"dirac",), (("1942",),), "S3-18"),
    FounderWorkSpec("r2m35_pauli_1943", "r2_m35", "pillar_r2_m35", 19, "Pauli (1943)", (r"pauli",), (("1943",),), "S3-19"),
    FounderWorkSpec("r2m35_pontryagin_1944", "r2_m35", "pillar_r2_m35", 20, "Pontryagin (1944)", (r"pontryagin",), (("1944",),), "S3-20"),
    FounderWorkSpec("r2m35_krein_1950_1964", "r2_m35", "pillar_r2_m35", 19, "Krein (1950, 1964)", (r"krein",), (("1950",), ("1964",)), "S3-21"),
    FounderWorkSpec("r2m35_iokhvidov_krein_1956", "r2_m35", "pillar_r2_m35", 19, "Iokhvidov-Krein (1956)", (r"iokhvidov", r"krein"), (("1956",),), "S3-22"),
    FounderWorkSpec("r2m35_tomita_takesaki_1967_1970", "r2_m35", "pillar_r2_m35", 21, "Tomita (1967) / Takesaki (1970)", (r"tomita", r"takesaki"), (("1967", "1970"),), "S3-23"),
    FounderWorkSpec("r2m35_kasparov_1980", "r2_m35", "pillar_r2_m35", 21, "Kasparov (1980)", (r"kasparov",), (("1980",),), "S3-24"),
    FounderWorkSpec("r2m35_connes_1995", "r2_m35", "pillar_r2_m35", 22, "Connes (1995)", (r"connes",), (("1995",),), "S3-25"),
    FounderWorkSpec("r2m35_strohmaier_2001_2006", "r2_m35", "pillar_r2_m35", 22, "Strohmaier (2001/2006)", (r"strohmaier",), (("2001", "2006"),), "S3-26"),
    FounderWorkSpec("r2m35_paschke_sitarz_2006", "r2_m35", "pillar_r2_m35", 22, "Paschke-Sitarz (2006)", (r"paschke", r"sitarz"), (("2006",),), "S3-27"),
    FounderWorkSpec("r2m35_vd_dungen_paschke_rennie_2013", "r2_m35", "pillar_r2_m35", 22, "van den Dungen-Paschke-Rennie (2013)", (r"dungen", r"paschke", r"rennie"), (("2013",),), "S3-28"),
)

assert len(FOUNDER_YEAR_SPEC) == 46, f"Expected 46 founder works, got {len(FOUNDER_YEAR_SPEC)}"


@dataclass(frozen=True)
class FeatureSpec:
    feature_id: int
    name: str
    milestone: str
    pillar: str
    owner_file: str
    concept_patterns: tuple[str, ...]
    alt_owner_files: tuple[str, ...] = ()


FEATURE_SPECS: tuple[FeatureSpec, ...] = (
    FeatureSpec(1, "Primary-Source Archive & Manifest", "M1", "all", MANIFEST_REL, ()),
    FeatureSpec(2, "Primary-Source Archetypes Doc", "M1", "all", ARCHETYPES_DOC_REL, ()),
    FeatureSpec(
        3,
        "Grassmann (1844, 1862)",
        "M2",
        "r2_f25",
        "lean/InfoGeometry/Projective/GrassmannPrimarySources.lean",
        (r"regressive|contractLeft|syncyclic", r"\bSL\b|SpecialLinear|LinearMap\.det|\bdet\b"),
    ),
    FeatureSpec(
        4,
        "Plücker (1865, 1868-1869)",
        "M2",
        "r2_f25",
        "lean/InfoGeometry/Projective/GrassmannPrimarySources.lean",
        (r"plucker|Plucker|kleinQuadric|KleinQuadric|wedge|decompos",),
    ),
    FeatureSpec(
        5,
        "Lie (1872) & Klein (1872)",
        "M2",
        "r2_f25",
        "lean/InfoGeometry/Erlangen/LieKleinPfaffCartanPrimary.lean",
        (r"lineSphere|LineSphere|erlangen|Erlangen|cayleyKlein|CayleyKlein|\bSubgroup\b",),
    ),
    FeatureSpec(
        6,
        "Pfaff (1814-1815) & Darboux (1882)",
        "M2",
        "r2_f25",
        "lean/InfoGeometry/Erlangen/LieKleinPfaffCartanPrimary.lean",
        (r"pfaff|Pfaff|darboux|Darboux|characteristic|derived",),
    ),
    FeatureSpec(
        7,
        "É. Cartan (1910, 1914) & Zorn (1930-1933)",
        "M2",
        "r2_f25",
        "lean/InfoGeometry/Erlangen/LieKleinPfaffCartanPrimary.lean",
        (r"cartan|Cartan|\bg2\b|\bG2\b|cartanG2|pfaff", r"zorn|Zorn|moufang|Moufang|octonion|Octonion"),
    ),
    FeatureSpec(
        8,
        "Clifford (1873, 1878) & Lipschitz (1880, 1886)",
        "M3",
        "r3",
        "lean/InfoGeometry/Clifford/LipschitzWittRieszPrimary.lean",
        (r"lipschitzGroup|lipschitz|Lipschitz|IsometryEquiv|spinor",),
    ),
    FeatureSpec(
        9,
        "Witt (1937) & Riesz (1946, 1958)",
        "M3",
        "r3",
        "lean/InfoGeometry/Clifford/LipschitzWittRieszPrimary.lean",
        (r"witt|Witt|hyperbolic|cancel", r"riesz|Riesz|equivExterior|grade|reverse|involute"),
    ),
    FeatureSpec(
        10,
        "Kähler (1960, 1962)",
        "M3",
        "r3",
        "lean/InfoGeometry/Clifford/KahlerHestenesJWABSPrimary.lean",
        (r"kahler|Kahler|codiff|contractLeft|innerOuter|dirac",),
    ),
    FeatureSpec(
        11,
        "Hestenes (1966) & Darboux (1887)",
        "M3",
        "r3",
        "lean/InfoGeometry/Clifford/KahlerHestenesJWABSPrimary.lean",
        (r"hestenes|Hestenes|rotor|Rotor|movingFrame|bivector",),
    ),
    FeatureSpec(
        12,
        "Jordan-Wigner (1928) & ABS (1964)",
        "M3",
        "r3",
        "lean/InfoGeometry/Clifford/KahlerHestenesJWABSPrimary.lean",
        (r"jordanWigner|JordanWigner|parity|evenOdd|GradedTensorProduct", r"\babs\b|\bABS\b|absGraded|AtiyahBottShapiro|grothendieck|Grothendieck"),
    ),
    FeatureSpec(
        13,
        "B. & C. S. Peirce (1870/1881, 1883)",
        "M4",
        "r1",
        "lean/InfoGeometry/OperatorAlgebra/PeirceCartanKoszulDVPrimary.lean",
        (r"peirce|Peirce|idempotent|nilpotent|matrixUnit",),
    ),
    FeatureSpec(
        14,
        "Maurer (1888) & É. Cartan (1899, 1904)",
        "M4",
        "r1",
        "lean/InfoGeometry/OperatorAlgebra/PeirceCartanKoszulDVPrimary.lean",
        (r"maurerCartan|MaurerCartan|actionThetaL|coframe|solder|torsion",),
    ),
    FeatureSpec(
        15,
        "Chevalley-Eilenberg (1948) & Koszul (1960)",
        "M4",
        "r1",
        "lean/InfoGeometry/OperatorAlgebra/PeirceCartanKoszulDVPrimary.lean",
        (r"LieActionLane|chevalley|Chevalley|koszul|Koszul|connection|curvature",),
    ),
    FeatureSpec(
        16,
        "Kähler (1953), Karoubi (1983), Connes (1985), DV (1988-1996)",
        "M4",
        "r1",
        "lean/InfoGeometry/OperatorAlgebra/PeirceCartanKoszulDVPrimary.lean",
        (r"duboisViolette|DuboisViolette|karoubi|Karoubi|connes|Connes|universalOneForm|center|LieRinehart",),
    ),
    FeatureSpec(
        17,
        "Fréchet (1925) & H. Cartan (1967)",
        "M4",
        "r1",
        "lean/InfoGeometry/Thermo/OnsagerCasimirKBMPrimary.lean",
        (r"frechet|Frechet|fderiv|cartanHomotopy|AlternatingMap|banach",),
        alt_owner_files=("lean/InfoGeometry/OperatorAlgebra/PeirceCartanKoszulDVPrimary.lean",),
    ),
    FeatureSpec(
        18,
        "Onsager-Casimir-Kubo-Bogoliubov-Mori (1931-1965)",
        "M4",
        "r1",
        "lean/InfoGeometry/Thermo/OnsagerCasimirKBMPrimary.lean",
        (r"onsager|Onsager|casimir|Casimir|reciprocity", r"kubo|Kubo|bogoliubov|Bogoliubov|duhamel|Duhamel|mori|Mori"),
    ),
    FeatureSpec(
        19,
        "Dirac (1942), Pauli (1943), Krein (1950, 1964), Iokhvidov-Krein (1956)",
        "M5",
        "r2_m35",
        "lean/InfoGeometry/Krein/PontryaginSpace.lean",
        (r"KreinSpace|kreinInner|IsKreinIsometry|IsKreinSkewAdjoint|dirac|pauli",),
    ),
    FeatureSpec(
        20,
        "Pontryagin (1944)",
        "M5",
        "r2_m35",
        "lean/InfoGeometry/Krein/PontryaginSpace.lean",
        (r"PontryaginSpace|pontryagin|kappa|invariant",),
    ),
    FeatureSpec(
        21,
        "Tomita-Takesaki (1967/1970) & Kasparov (1980)",
        "M5",
        "r2_m35",
        "lean/InfoGeometry/KK/KreinSpectralTriplePrimary.lean",
        (r"tomita|Tomita|modular|Modular", r"kasparov|Kasparov|KasparovCycle|evenOdd"),
    ),
    FeatureSpec(
        22,
        "Connes (1995), Strohmaier, Paschke-Sitarz, v.d. Dungen-P-R (2001-2013)",
        "M5",
        "r2_m35",
        "lean/InfoGeometry/KK/KreinSpectralTriplePrimary.lean",
        (r"\bjCLM\b", r"\bgradeCLM\b|\bchi\b", r"\bJ_real\b|\bRealStructure\b|\bPhaseRealStructure\b"),
    ),
    FeatureSpec(
        23,
        "Cross-Pillar Bridge, Source-to-Declaration Traceability & Final Verification",
        "M6",
        "all",
        BRIDGE_FILE_REL,
        (r"GrassmannPrimarySources|LieKleinPfaffCartanPrimary", r"LipschitzWittRieszPrimary|KahlerHestenesJWABSPrimary", r"PeirceCartanKoszulDVPrimary|OnsagerCasimirKBMPrimary", r"PontryaginSpace|KreinSpectralTriplePrimary"),
    ),
)
