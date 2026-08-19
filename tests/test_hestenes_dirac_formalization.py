from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
MODULE = ROOT / "lean" / "InfoGeometry" / "Clifford" / "HestenesDirac.lean"
CR_MODULE = ROOT / "lean" / "InfoGeometry" / "Clifford" / "HestenesCauchyRiemann.lean"
SQ_FLOW_MODULE = ROOT / "lean" / "InfoGeometry" / "Clifford" / "SplitQuaternionNilpotentFlow.lean"
CLIFFORD_ALL = ROOT / "lean" / "InfoGeometry" / "Clifford" / "All.lean"


def test_hestenes_dirac_module_declares_real_bivector_phase_not_complex_i():
    text = MODULE.read_text()
    assert "structure RealSpacetimeAlgebra" in text
    assert "ellipticBivector_sq" in text
    assert "hyperbolicBivector_sq" in text
    assert "spinPlane_sq" in text
    assert "abstractScalarI" not in text
    assert "import Mathlib.Data.Complex" not in text
    assert "Complex." not in text


def test_hestenes_dirac_module_declares_spinor_current_and_spin_plane_bilinears():
    text = MODULE.read_text()
    assert "structure DiracHestenesSpinor" in text
    assert "def current" in text
    assert "def spinPlane" in text
    assert "def velocityFrame" in text
    assert "def spinAxis" in text
    assert "current_eq_density_smul_velocityFrame" in text
    assert "spinPlane_eq_density_smul_orientedSpinPlane" in text


def test_hestenes_dirac_module_declares_real_dirac_equation_and_conservation_packet():
    text = MODULE.read_text()
    assert "structure DiracHestenesEquation" in text
    assert "mass_clock_law" in text
    assert "structure DiracHestenesConservationPacket" in text
    assert "current_conserved" in text
    assert "spin_plane_transported" in text
    assert "electromagneticGaugeRotation" in text
    assert "pauliMagneticCoupling" in text


def test_hestenes_dirac_finite_tilt_shell_declares_current_density_readout():
    text = ROOT.joinpath("lean", "InfoGeometry", "Clifford", "FiniteTiltDiracShell.lean").read_text()
    assert "def finiteTiltCurrentDensity" in text
    assert "theorem finiteTiltCurrentDensity_eq_boundaryCurrent" in text
    assert "theorem finiteTiltBoundaryCurrent_sq_zero" in text
    assert "theorem finiteTiltCurrentDensity_sq_zero" in text
    assert "theorem finiteTiltDiracShell_eq_boundaryCurrent_add_mass" in text


def test_hestenes_dirac_finite_tilt_shell_bridge_declares_current_density_reexport():
    text = ROOT.joinpath("lean", "InfoGeometry", "Clifford", "FiniteTiltDiracShellBridge.lean").read_text()
    assert "theorem finiteTiltDiracShellBridge_properties" in text
    assert "finiteTiltCurrentDensity_eq_boundaryCurrent" in text


def test_hestenes_dirac_finite_tilt_shell_builds():
    result = subprocess.run(
        [
            "python3",
            "tools/infra/run_locked_lake_build.py",
            "--wait-for-build-lock",
            "InfoGeometry.Clifford.FiniteTiltDiracShell",
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=240,
    )
    assert result.returncode == 0, result.stdout


def test_hestenes_dirac_finite_tilt_shell_bridge_builds():
    result = subprocess.run(
        [
            "python3",
            "tools/infra/run_locked_lake_build.py",
            "--wait-for-build-lock",
            "InfoGeometry.Clifford.FiniteTiltDiracShellBridge",
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=1200,
    )
    assert result.returncode == 0, result.stdout


def test_hestenes_dirac_polar_owner_exposes_density_rotor_phase_without_complex_i():
    text = MODULE.read_text()
    assert "structure DiracHestenesPolarDecomposition" in text
    assert "densityRoot" in text
    assert "lorentzRotor" in text
    assert "ytAngle" in text
    assert "pseudoscalarPhase" in text
    assert "spinor_eq_density_rotor_phase" in text
    assert "toDiracHestenesSpinor" in text
    polar_block = text.split("structure DiracHestenesPolarDecomposition", 1)[1].split("namespace DiracHestenesPolarDecomposition", 1)[0]
    assert "Complex." not in polar_block
    assert "abstractScalarI" not in polar_block


def test_hestenes_dirac_polar_owner_derives_real_bilinear_readouts():
    text = MODULE.read_text()
    assert "current_of_polar" in text
    assert "spinPlane_of_polar" in text
    assert "yvonTakabayasiAngle_of_polar" in text
    assert "phasePlane_of_polar" in text
    assert "polar_current_eq_density_velocity" in text
    assert "polar_spinPlane_eq_density_spinPlane" in text


def test_hestenes_dirac_real_four_by_four_paffian_biquaternion_surface():
    text = MODULE.read_text()
    assert "structure RealFourByFourBiquaternionSlice" in text
    assert "complexStructureJ" in text
    assert "J_sq" in text
    assert "commutes_with_J" in text
    assert "symmetric" in text
    assert "minkowskiInterval" in text
    assert "pfaffianSJ" in text
    assert "det_realification_eq_interval_sq" in text
    assert "interval_eq_neg_pfaffianSJ" in text
    assert "null_cone_iff_pfaffian_zero" in text
    block = text.split("structure RealFourByFourBiquaternionSlice", 1)[1].split("structure MajoranaBdGFourByFour", 1)[0]
    assert "Complex." not in block
    assert "abstractScalarI" not in block


def test_hestenes_dirac_majorana_bdg_real_skew_pfaffian_surface():
    text = MODULE.read_text()
    assert "structure MajoranaBdGFourByFour" in text
    assert "skewSymmetric" in text
    assert "pfaffian" in text
    assert "det_eq_pfaffian_sq" in text
    assert "zero_mode_iff_pfaffian_zero" in text
    assert "structure RealPfaffianBridge" in text
    assert "biquaternionNull" in text
    assert "bdgZeroMode" in text
    assert "pfaffian_bridge" in text
    block = text.split("structure MajoranaBdGFourByFour", 1)[1]
    assert "Complex." not in block
    assert "abstractScalarI" not in block


def test_hestenes_dirac_concrete_realification_pfaffian_proof_layer():
    text = MODULE.read_text()
    assert "structure RealMatrix4" in text
    assert "structure MinkowskiCoordinates" in text
    assert "def concreteComplexStructureJ" in text
    assert "def concreteSpacetimeMatrix" in text
    assert "def concreteBiquaternionSlice" in text
    assert "theorem concreteComplexStructureJ_sq" in text
    assert "theorem concreteSpacetimeMatrix_commutes_with_J" in text
    assert "theorem concreteSpacetimeMatrix_symmetric" in text
    assert "theorem concrete_pfaffianSJ_eq_neg_interval" in text
    assert "theorem concrete_det_realification_eq_interval_sq" in text
    assert "theorem concrete_null_cone_iff_pfaffian_zero" in text
    block = text.split("structure RealMatrix4", 1)[1].split("structure MajoranaBdGCoordinates", 1)[0]
    assert "Complex." not in block
    assert "abstractScalarI" not in block


def test_hestenes_dirac_concrete_majorana_bdg_pfaffian_proof_layer():
    text = MODULE.read_text()
    assert "structure MajoranaBdGCoordinates" in text
    assert "def concreteMajoranaBdGMatrix" in text
    assert "def pfaffianSkew4" in text
    assert "def determinantSkew4" in text
    assert "def concreteMajoranaBdGFourByFour" in text
    assert "theorem concreteMajoranaBdG_skewSymmetric" in text
    assert "theorem concreteMajoranaBdG_det_eq_pfaffian_sq" in text
    assert "theorem concreteMajoranaBdG_zero_mode_iff_pfaffian_zero" in text
    assert "RealMatrix4.transpose (concreteMajoranaBdGMatrix" in text
    assert "= -concreteMajoranaBdGMatrix" in text or "= - concreteMajoranaBdGMatrix" in text
    assert "majoranaBdGTranspose" not in text
    block = text.split("structure MajoranaBdGCoordinates", 1)[1]
    assert "Complex." not in block
    assert "abstractScalarI" not in block



def test_hestenes_dirac_imported_by_clifford_all():
    text = CLIFFORD_ALL.read_text()
    assert "import InfoGeometry.Clifford.HestenesDirac" in text


def test_hestenes_cauchy_riemann_module_declares_complex_real_and_cr_equivalence():
    text = CR_MODULE.read_text()
    assert "namespace InfoGeometry.Clifford.HestenesCauchyRiemann" in text
    assert "structure ComplexReal" in text
    assert "def c_mul" in text
    assert "structure RealLinearMap" in text
    assert "def is_complex_linear" in text
    assert "def satisfy_cauchy_riemann" in text
    assert "theorem complex_linear_iff_cauchy_riemann" in text
    assert "axiom " not in text


def test_hestenes_cauchy_riemann_module_declares_real_hestenes_spinor_and_cr_bridge():
    text = CR_MODULE.read_text()
    assert "structure HestenesSpinor" in text
    assert "def hMul" in text
    assert "def reverse" in text
    assert "def h_norm" in text
    assert "def krein_inner" in text
    assert "def bivector_i" in text
    assert "theorem even_algebra_mul_assoc" in text
    assert "theorem spinor_mul_reverse" in text
    assert "theorem bivector_i_squared" in text
    assert "theorem krein_inner_symmetry" in text
    assert "def satisfy_hestenes_cr" in text
    assert "structure StandardCRComponents" in text
    assert "theorem hestenes_cr_equivalence" in text
    assert "axiom " not in text


def test_hestenes_cauchy_riemann_imported_by_clifford_all():
    text = CLIFFORD_ALL.read_text()
    assert "import InfoGeometry.Clifford.HestenesCauchyRiemann" in text


def test_hestenes_dirac_module_builds():
    result = subprocess.run(
        [
            "python3",
            "tools/infra/run_locked_lake_build.py",
            "--wait-for-build-lock",
            "InfoGeometry.Clifford.HestenesDirac",
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=240,
    )
    assert result.returncode == 0, result.stdout


def test_hestenes_cauchy_riemann_module_builds():
    result = subprocess.run(
        [
            "python3",
            "tools/infra/run_locked_lake_build.py",
            "--wait-for-build-lock",
            "InfoGeometry.Clifford.HestenesCauchyRiemann",
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=240,
    )
    assert result.returncode == 0, result.stdout


def test_split_quaternion_nilpotent_flow_declares_closed_owner_surface_without_axioms():
    text = SQ_FLOW_MODULE.read_text()
    assert "namespace InfoGeometry.Clifford.SplitQuaternionNilpotentFlow" in text
    assert "def sq_smul" in text
    assert "def sq_recursive_prod" in text
    assert "def recursive_sum" in text
    assert "def N_nil" in text
    assert "def sq_nilpotent_exp" in text
    assert "def sq_finite_prod_seq" in text
    assert "def sq_tendsto" in text
    assert "theorem N_nil_sq" in text
    assert "theorem sq_nilpotent_prod_induction_N" in text
    assert "theorem sq_finite_to_infinite_limit" in text
    assert "axiom " not in text
    assert "sorry" not in text


def test_split_quaternion_nilpotent_flow_imported_by_clifford_all():
    text = CLIFFORD_ALL.read_text()
    assert "import InfoGeometry.Clifford.SplitQuaternionNilpotentFlow" in text


def test_split_quaternion_nilpotent_flow_module_builds():
    result = subprocess.run(
        [
            "python3",
            "tools/infra/run_locked_lake_build.py",
            "--wait-for-build-lock",
            "InfoGeometry.Clifford.SplitQuaternionNilpotentFlow",
        ],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=240,
    )
    assert result.returncode == 0, result.stdout
