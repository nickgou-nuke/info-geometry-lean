"""Numerical regressions; no floating-point check is a Lean proof."""
import unittest
import torch
from tools.shape_sinkhorn_detector import (
    differentiable_sinkhorn_core_decomposition as decompose,
    BistochasticBipartiteLaplacianSolver as Solver,
    FiveFactorShapeSinkhornDetector as Model,
)

DTYPE = torch.float64

class ShapeSinkhornTests(unittest.TestCase):
    def setUp(self):
        torch.manual_seed(123)

    def core(self, k=3):
        return decompose(torch.randn(k, k, dtype=DTYPE), 120)[1]

    def test_factor_reconstruction_gauge_and_copula(self):
        s = torch.randn(2, 3, 3, dtype=DTYPE)
        a, B, b, reconstructed, info = decompose(s, 120)
        torch.testing.assert_close(reconstructed, s.exp(), rtol=1e-12, atol=1e-12)
        torch.testing.assert_close(a.log().sum(-1), b.log().sum(-1))
        phi = s-s.mean(-1, keepdim=True)-s.mean(-2, keepdim=True)+s.mean((-2,-1), keepdim=True)
        torch.testing.assert_close(info['phi_copula'], phi)
        self.assertTrue(info['sinkhorn_converged'].all())

    def test_finite_iteration_not_bistochastic(self):
        s = torch.tensor([[5., -1., -2.], [2., 0., -3.], [0., 2., 1.]], dtype=DTYPE)
        _, B, _, reconstructed, info = decompose(s, 1)
        self.assertFalse(info['sinkhorn_converged'].all())
        torch.testing.assert_close(reconstructed, s.exp())
        with self.assertRaisesRegex(ValueError, 'bistochastic'):
            Solver()(B, torch.ones(3,1,dtype=DTYPE), torch.ones(3,1,dtype=DTYPE))

    def test_two_solvers_agree_and_match_pseudoinverse(self):
        B = self.core(4)
        bs, bd = torch.randn(4,2,dtype=DTYPE), torch.randn(4,2,dtype=DTYPE)
        xs, xd, diag = Solver()(B, bs, bd)
        ys, yd, _ = Solver('full_2k')(B, bs, bd)
        torch.testing.assert_close(xs, ys, rtol=1e-10, atol=1e-10)
        torch.testing.assert_close(xd, yd, rtol=1e-10, atol=1e-10)
        _, L, _, _ = Solver.build_bipartite_matrices(B)
        rhs = torch.cat((bs,bd),-2); rhs = rhs-rhs.mean(-2,keepdim=True)
        torch.testing.assert_close(torch.cat((xs,xd),-2), torch.linalg.pinv(L) @ rhs,
                                   rtol=1e-9,atol=1e-9)
        self.assertLess(diag['poisson_residual'].item(), 1e-10)

    def test_parity_correction(self):
        B = self.core()
        bs = torch.full((3,1),3.,dtype=DTYPE)
        bd = torch.full((3,1),-1.,dtype=DTYPE)
        xs, xd, _ = Solver()(B,bs,bd)
        torch.testing.assert_close(xs,torch.ones_like(xs))
        torch.testing.assert_close(xd,-torch.ones_like(xd))

    def test_one_channel(self):
        B = torch.ones(1,1,dtype=DTYPE)
        xs,xd,_ = Solver()(B, torch.tensor([[7.]],dtype=DTYPE), torch.tensor([[3.]],dtype=DTYPE))
        torch.testing.assert_close(xs,torch.ones_like(xs))
        torch.testing.assert_close(xd,-torch.ones_like(xd))

    def test_disconnected_rejected(self):
        for method in ('gramian_schur','full_2k'):
            with self.subTest(method=method), self.assertRaisesRegex(ValueError,'Disconnected'):
                Solver(method)(torch.eye(3,dtype=DTYPE),torch.ones(3,1,dtype=DTYPE),torch.zeros(3,1,dtype=DTYPE))

    def test_near_disconnected_rejected(self):
        B = (1-1e-8)*torch.eye(3,dtype=DTYPE)+torch.full((3,3),1e-8/3,dtype=DTYPE)
        with self.assertRaisesRegex(ValueError,'unresolved'):
            Solver(gap_tolerance=1e-6)(B,torch.ones(3,1,dtype=DTYPE),torch.zeros(3,1,dtype=DTYPE))

    def test_batched_solve(self):
        B = decompose(torch.randn(2,3,3,dtype=DTYPE),120)[1]
        bs,bd = torch.randn(2,3,2,dtype=DTYPE),torch.randn(2,3,2,dtype=DTYPE)
        xs,xd,_ = Solver()(B,bs,bd)
        ys,yd,_ = Solver('full_2k')(B,bs,bd)
        torch.testing.assert_close(xs,ys); torch.testing.assert_close(xd,yd)

    def test_shared_core_batch(self):
        B=self.core(); bs=torch.randn(2,3,2,dtype=DTYPE); bd=torch.randn_like(bs)
        xs,xd,_=Solver()(B,bs,bd)
        self.assertEqual(xs.shape,(2,3,2)); self.assertEqual(xd.shape,(2,3,2))

    def test_model_marginals_and_backward(self):
        model=Model(4,5,3).double()
        out=model(torch.randn(4,2,dtype=DTYPE),torch.randn(5,2,dtype=DTYPE))
        torch.testing.assert_close(out['C_recon'].sum(-1),out['row_marginal'])
        torch.testing.assert_close(out['C_recon'].sum(-2),out['col_marginal'])
        loss,_=model.loss_function(torch.zeros(4,5,dtype=DTYPE))
        loss=loss+out['shape_response_out'].square().sum()
        loss.backward()
        for p in model.parameters():
            self.assertIsNotNone(p.grad); self.assertTrue(torch.isfinite(p.grad).all())

    def test_zero_observation_kl(self):
        model=Model(2,3,2).double()
        loss,_=model.loss_function(torch.zeros(2,3,dtype=DTYPE))
        torch.testing.assert_close(loss,model()['C_recon'].sum())

    def test_gradcheck_on_bistochastic_parameterization(self):
        theta=torch.tensor([0.3],dtype=DTYPE,requires_grad=True)
        bs=torch.tensor([[1.],[3.]],dtype=DTYPE,requires_grad=True)
        bd=torch.tensor([[2.],[-1.]],dtype=DTYPE,requires_grad=True)
        def run(t,x,y):
            p=t.sigmoid()[0]
            B=torch.stack((torch.stack((p,1-p)),torch.stack((1-p,p))))
            a,b,_=Solver()(B,x,y)
            return torch.cat((a,b),-2)
        self.assertTrue(torch.autograd.gradcheck(run,(theta,bs,bd),eps=1e-6,atol=1e-5))

    def test_sinkhorn_gradcheck(self):
        s=torch.tensor([[0.2,-0.3],[0.7,0.1]],dtype=DTYPE,requires_grad=True)
        self.assertTrue(torch.autograd.gradcheck(lambda z: decompose(z,30)[1],(s,),eps=1e-6,atol=1e-5))

    def test_invalid_inputs(self):
        for s in (torch.empty(0,0,dtype=DTYPE),torch.ones(2,3,dtype=DTYPE),
                  torch.full((2,2),float('nan'),dtype=DTYPE)):
            with self.assertRaises(ValueError): decompose(s)
        with self.assertRaises(ValueError): decompose(torch.ones(2,2,dtype=DTYPE),0)
        with self.assertRaises(TypeError): decompose(torch.ones(2,2,dtype=torch.int64))
        with self.assertRaises(ValueError): Model(2,3,2)(torch.ones(2,1))

    def test_overflow_and_underflow_rejected(self):
        for value in (2000.,-2000.):
            with self.assertRaises(FloatingPointError):
                decompose(torch.full((2,2),value,dtype=DTYPE))

if __name__=='__main__': unittest.main()
