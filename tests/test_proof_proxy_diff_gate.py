from tools.quality.proof_proxy_diff_gate import (
    aliases_to_proxy_types,
    documented_socket_structures,
)


def test_only_explicitly_documented_socket_structures_are_classified_as_sockets():
    source = '''
/-! A nearby module comment mentioning a socket does not classify declarations. -/
/-- A transport socket whose law is supplied as a field. -/
@[rep_depth operator]
structure ExampleTransport where
  transform : Nat → Nat
  law : ∀ n, transform n = n

/-- A concrete transport with a specified action. -/
structure ConcreteTransport where
  transform : Nat → Nat
'''
    assert documented_socket_structures(source) == {"ExampleTransport"}


def test_documented_socket_attribute_can_precede_the_structure():
    source = '''
/-- A readout socket for a model-specific relation. -/
@[rep_depth operator]
structure ReadoutSocket (A : Type) where
  value : A
'''
    assert documented_socket_structures(source) == {"ReadoutSocket"}


def test_only_aliases_to_named_proxy_types_inherit_proxy_classification():
    source = '''
abbrev OldCertificateSurface := Example.Certificate
abbrev MultilineCertificateSurface :=
  Example.Certificate
abbrev ConcreteReadout := Example.Readout
'''
    assert aliases_to_proxy_types(source) == {
        "OldCertificateSurface",
        "MultilineCertificateSurface",
    }
