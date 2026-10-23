"""Independent certificate checks; Lean verification is a separate CI step."""
from dataclasses import asdict, replace
import itertools
import json
import unittest
from unittest.mock import patch

from tools.functional_route_fibers import analyze_route
from tools.route_certificate import (
    certificate_from_dict, certificate_from_geometry, certificate_from_route,
    emit_lean, validate_certificate,
)


class RouteCertificateTests(unittest.TestCase):
    def test_all_maps_through_four_vertices(self):
        count = 0
        for n in range(1, 5):
            for route in itertools.product(range(n), repeat=n):
                cert = certificate_from_route(route)
                validate_certificate(cert)
                count += 1
                # Independent iteration checks exact first entry for each token.
                for i in range(n):
                    current = i
                    for r in range(n + 1):
                        self.assertEqual(current in cert.recurrent, cert.depth[i] <= r)
                        current = route[current]
        self.assertEqual(count, 288)

    def test_mixed_cycles(self):
        for route in ([1, 2, 0, 1, 3, 5, 5], [1, 0, 3, 2, 1, 4, 3, 6]):
            cert = certificate_from_route(route)
            validate_certificate(cert)
            self.assertGreater(len(cert.recurrent), 1)

    def test_validator_does_not_invoke_analyzer(self):
        cert = certificate_from_route([0, 0, 1, 1])
        with patch('tools.route_certificate.analyze_route', side_effect=AssertionError):
            validate_certificate(cert)

    def test_mutations_are_rejected(self):
        cert = certificate_from_route([0, 0, 1, 1])
        mutations = [
            replace(cert, route=(0, 0, 1, 4)),
            replace(cert, recurrent=(0, 0)),
            replace(cert, cycle=(1,)),
            replace(cert, inverse_cycle=(-1,)),
            replace(cert, rho=(0, 0, 0, 1)),
            replace(cert, depth=(0, 1, 1, 2)),
            replace(cert, depth=(0, 0, 0, 0)),
            replace(cert, depth=(0, True, 2, 2)),
            replace(cert, bound=3),
            replace(cert, bound=True),
            replace(cert, route=()),
        ]
        for bad in mutations:
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                validate_certificate(bad)

    def test_geometry_inverse_tampering(self):
        g = analyze_route([0, 0, 1, 1])
        with self.assertRaises(ValueError):
            certificate_from_geometry(replace(g, inverse_route=(1, 0, 0, 0)))

    def test_cycle_orientation_tampering(self):
        cert = certificate_from_route([1, 2, 0, 1])
        with self.assertRaises(ValueError):
            validate_certificate(replace(cert, inverse_cycle=cert.cycle))

    def test_json_roundtrip_and_schema(self):
        cert = certificate_from_route([0, 0, 1, 1])
        payload = json.loads(json.dumps(asdict(cert)))
        self.assertEqual(certificate_from_dict(payload), cert)
        payload['trusted'] = True
        with self.assertRaises(ValueError):
            certificate_from_dict(payload)

    def test_export_is_data_and_native_proofs(self):
        cert = certificate_from_route([0, 0, 1, 1])
        source = emit_lean(cert, 'Generated.Branch')
        self.assertIn('constructor <;> decide', source)
        self.assertIn('minimum_witness_index', source)
        self.assertIn('def depth : Fin 4 → ℕ := ![0, 1, 2, 2]', source)
        self.assertNotIn('native_decide', source)
        self.assertNotIn('sorry', source)
        with self.assertRaises(ValueError):
            emit_lean(cert, 'Bad\nnamespace Injection')
        with self.assertRaises(ValueError):
            emit_lean(replace(cert, bound=99))


if __name__ == '__main__':
    unittest.main()
