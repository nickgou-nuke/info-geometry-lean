import unittest
import torch
from tools.route_diagnostics_torch import FunctionalRouteDiagnostics, peel_routes


class TorchDiagnosticsTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls): torch.set_num_threads(1)

    def test_truncated_readout_keeps_residual(self):
        P=torch.tensor([[.8,.2],[.3,.7]],dtype=torch.float64);V=torch.eye(2,dtype=P.dtype)
        out=FunctionalRouteDiagnostics(1)(P,V)
        self.assertAlmostEqual(out['captured_mass'].item(),.7)
        torch.testing.assert_close(out['reconstructed_output'],P@V)
        torch.testing.assert_close(out['retained_core_output'],.7*V)
        self.assertFalse(torch.allclose(out['retained_core_output']+out['retained_nilpotent_output'],P@V))

    def test_batched_causal_and_readout(self):
        gen=torch.Generator().manual_seed(10)
        P=torch.softmax(torch.rand((2,3,6,6),generator=gen,dtype=torch.float64).masked_fill(
            torch.triu(torch.ones((6,6),dtype=torch.bool),diagonal=1),-float('inf')),-1)
        V=torch.randn((2,3,6,4),generator=gen,dtype=P.dtype)
        for k in (0,1,4,25):
            out=FunctionalRouteDiagnostics(k)(P,V)
            torch.testing.assert_close(out['reconstructed_output'],P@V)
            torch.testing.assert_close(out['exact_causal_expected_core_fraction'],P.diagonal(dim1=-2,dim2=-1).sum(-1)/6)
        with self.assertRaises(ValueError): FunctionalRouteDiagnostics()(P,V[0])

    def test_graph_depth_is_not_shell_rank(self):
        f=torch.tensor([0,0,1,1]);P=torch.eye(4,dtype=torch.float64)[f]
        out=FunctionalRouteDiagnostics(1)(P)
        torch.testing.assert_close(out['conditional_entry_depth_histogram'],torch.tensor([.25,.5,0,0],dtype=P.dtype))
        torch.testing.assert_close(out['conditional_shell_rank_histogram'],torch.tensor([.5,.25,0,0],dtype=P.dtype))

    def test_validation(self):
        for P in (torch.ones(2,3,dtype=torch.float64),torch.zeros(2,2,dtype=torch.float64),
                  torch.tensor([[2.,-1.],[0.,1.]]),torch.tensor([[float('nan')]])):
            with self.assertRaises(ValueError): peel_routes(P)
        with self.assertRaises(ValueError):peel_routes(torch.eye(2),-1)

    def test_no_grad_and_no_mutation(self):
        P=torch.tensor([[.5,.5],[.5,.5]],requires_grad=True)
        before=P.detach().clone();V=torch.eye(2,requires_grad=True)
        out=FunctionalRouteDiagnostics(3)(P,V)
        self.assertFalse(out['reconstructed_output'].requires_grad)
        torch.testing.assert_close(P,before)


if __name__=='__main__':unittest.main()
