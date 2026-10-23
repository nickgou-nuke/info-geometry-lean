"""Numerical regression coverage, not a Lean proof of Python or floating point."""
import unittest
import torch
from tools.causal_bipartite_sinkhorn import (
    masked_column_pool, merge_pools, five_factor_conditional,
    MultiHeadBipartiteSinkhornAttention as Full,
    BlockCausalMultiHeadBipartiteSinkhornAttention as Causal,
)


class CausalSinkhornTests(unittest.TestCase):
    def setUp(self):
        torch.manual_seed(19)
        torch.set_num_threads(1)

    def model(self, mode="strict_token_causal", **kw):
        return Causal(4, 2, 2, chunk_size=2, causal_mode=mode,
                      sinkhorn_iters=80, **kw).double().eval()

    def test_streaming_pool_equals_dense(self):
        logits = torch.randn(2, 2, 7, 3, dtype=torch.float64)
        x = torch.randn(2, 2, 7, 2, dtype=torch.float64)
        mask = torch.tensor([[True, False, True, True, False, True, True],
                             [False, False, True, True, True, False, True]])[:, None]
        state = None
        for start, end in ((0, 2), (2, 5), (5, 7)):
            state = merge_pools(state, masked_column_pool(logits[..., start:end, :],
                x[..., start:end, :], -x[..., start:end, :], mask[..., start:end]))
            dense = masked_column_pool(logits[..., :end, :], x[..., :end, :],
                                        -x[..., :end, :], mask[..., :end])
            torch.testing.assert_close(state.keys, dense.keys)
            torch.testing.assert_close(state.values, dense.values)
            torch.testing.assert_close(state.log_mass, dense.log_mass)

    def test_empty_pool_and_empty_merge(self):
        l = torch.randn(1, 2, 3, dtype=torch.float64, requires_grad=True)
        v = torch.randn(1, 2, 4, dtype=torch.float64, requires_grad=True)
        state = masked_column_pool(l, v, v, torch.zeros(1, 2, dtype=torch.bool))
        merged = merge_pools(state, state)
        self.assertTrue(torch.isneginf(merged.log_mass).all())
        self.assertEqual(merged.values.abs().max().item(), 0.)
        g = torch.autograd.grad(merged.values.sum(), (l, v))
        self.assertTrue(all(torch.isfinite(x).all() and x.abs().max() == 0 for x in g))

    def test_extreme_logits_and_mask(self):
        logits = torch.tensor([[[-1e10, 1000.], [1e10, 1e10], [-1e10-2, 999.]]], dtype=torch.float64)
        v = torch.tensor([[[1.], [1e9], [3.]]], dtype=torch.float64)
        p = masked_column_pool(logits, v, v, torch.tensor([[True, False, True]]))
        self.assertTrue(torch.isfinite(p.values).all())
        self.assertTrue((p.values < 3).all())
        self.assertTrue((p.values > 1).all())

    def test_five_factor_conditional_matches_dense(self):
        U = torch.rand(2, 5, 3, dtype=torch.float64); U = U/U.sum(-2, keepdim=True)
        V = torch.rand(2, 4, 3, dtype=torch.float64); V = V/V.sum(-2, keepdim=True)
        a, b = torch.rand(2, 3, dtype=torch.float64)+.2, torch.rand(2, 3, dtype=torch.float64)+.2
        B, x = torch.rand(2, 3, 3, dtype=torch.float64)+.1, torch.randn(2, 5, 2, dtype=torch.float64)
        c = (U*a.unsqueeze(-2))@B@(V*b.unsqueeze(-2)).transpose(-2,-1)
        expected = (c.transpose(-2,-1)@x)/c.sum(-2).unsqueeze(-1)
        torch.testing.assert_close(five_factor_conditional(U,V,a,B,b,x),expected)

    def test_strict_full_jacobian_upper_blocks_zero(self):
        m = self.model()
        x = torch.randn(1, 5, 4, dtype=torch.float64, requires_grad=True)
        jac = torch.autograd.functional.jacobian(lambda z: m(z)[0], x)
        for t in range(4):
            self.assertEqual(jac[0,t,:,0,t+1:,:].abs().max().item(), 0.)
        self.assertGreater(jac[0,3,:,0,:3,:].abs().max().item(), 0.)

    def test_block_jacobian_future_blocks_zero(self):
        m = self.model("block_causal")
        x = torch.randn(1, 5, 4, dtype=torch.float64, requires_grad=True)
        y,_ = m(x)
        g = torch.autograd.grad(y[:,2,:].square().sum(), x)[0]
        self.assertEqual(g[:,4:,:].abs().max().item(), 0.)
        self.assertGreater(g[:,3,:].abs().max().item(), 0.)

    def test_strict_future_perturbations(self):
        m = self.model(direct_mode="five_factor")
        x = torch.randn(1, 6, 4, dtype=torch.float64)
        y,_ = m(x)
        for t in range(5):
            changed=x.clone(); changed[:,t+1:,:] += torch.randn_like(changed[:,t+1:,:])*.3
            other,_=m(changed)
            torch.testing.assert_close(y[:,:t+1,:],other[:,:t+1,:],atol=0,rtol=0)

    def test_prefix_extension_strict(self):
        m=self.model(); x=torch.randn(1,7,4,dtype=torch.float64)
        y,_=m(x)
        for n in (1,3,4,6):
            z,_=m(x[:,:n,:]); torch.testing.assert_close(y[:,:n,:],z,atol=1e-13,rtol=1e-13)

    def test_padding_invariance_both_modes(self):
        for mode in ("block_causal","strict_token_causal"):
            m=self.model(mode); x=torch.randn(2,5,4,dtype=torch.float64)
            mask=torch.tensor([[False,True,False,False,True],[True,True,False,True,False]])
            changed=x.clone(); changed[mask]=torch.randn_like(changed[mask])*100
            a,_=m(x,key_padding_mask=mask); b,_=m(changed,key_padding_mask=mask)
            torch.testing.assert_close(a,b,atol=0,rtol=0)
            self.assertEqual(a[mask].abs().max().item(),0.)

    def test_all_padding_is_zero_with_finite_backward(self):
        for mode in ("block_causal","strict_token_causal"):
            m=self.model(mode); x=torch.randn(1,5,4,dtype=torch.float64,requires_grad=True)
            y,_=m(x,key_padding_mask=torch.ones(1,5,dtype=torch.bool))
            self.assertEqual(y.abs().max().item(),0.)
            g=torch.autograd.grad(y.sum(),x)[0]
            self.assertTrue(torch.isfinite(g).all()); self.assertEqual(g.abs().max().item(),0.)

    def test_cross_attention_shapes_and_masks(self):
        m=Full(4,2,2,sinkhorn_iters=80).double().eval()
        q,k=torch.randn(2,3,4,dtype=torch.float64),torch.randn(2,5,4,dtype=torch.float64)
        km=torch.zeros(2,5,dtype=torch.bool); km[:,1]=True
        qm=torch.zeros(2,3,dtype=torch.bool); qm[:,2]=True
        y,d=m(q,k,km,qm,True)
        self.assertEqual(y.shape,(2,3,4)); self.assertEqual(y[:,2,:].abs().max().item(),0.)
        self.assertLess(d['poisson_residual'].max().item(),1e-10)
        with self.assertRaises(ValueError): m(q,k,torch.ones(2,5,dtype=torch.bool))

    def test_gate_probability_initialization(self):
        m=self.model(poisson_mix_init=.2)
        torch.testing.assert_close(m.poisson_gate.sigmoid(),torch.full_like(m.poisson_gate,.2))

    def test_gradcheck_pool_merge(self):
        l=torch.randn(1,3,2,dtype=torch.float64,requires_grad=True)
        v=torch.randn(1,3,2,dtype=torch.float64,requires_grad=True)
        mask=torch.ones(1,3,dtype=torch.bool)
        def f(a,b):
            p=masked_column_pool(a[:,:1],b[:,:1],b[:,:1],mask[:,:1])
            q=masked_column_pool(a[:,1:],b[:,1:],b[:,1:],mask[:,1:])
            return merge_pools(p,q).values
        self.assertTrue(torch.autograd.gradcheck(f,(l,v)))

    def test_gradcheck_strict_layer(self):
        m=self.model(); x=torch.randn(1,3,4,dtype=torch.float64,requires_grad=True)*.1
        self.assertTrue(torch.autograd.gradcheck(lambda v: m(v)[0],(x,),fast_mode=True))

    def test_solver_methods_agree(self):
        a=self.model(); b=self.model(solver_method="full_2k"); b.load_state_dict(a.state_dict())
        x=torch.randn(1,5,4,dtype=torch.float64)
        ya,_=a(x); yb,_=b(x); torch.testing.assert_close(ya,yb,atol=1e-11,rtol=1e-11)

    def test_chunk_one_and_ragged(self):
        for n in (1,2,5):
            m=Causal(4,2,2,chunk_size=1,causal_mode="strict_token_causal",sinkhorn_iters=80).double()
            x=torch.randn(1,n,4,dtype=torch.float64)
            y,_=m(x); self.assertEqual(y.shape,x.shape); self.assertTrue(torch.isfinite(y).all())

    def test_invalid_arguments(self):
        for kw in ({'chunk_size':0},{'causal_mode':'future'}):
            with self.assertRaises(ValueError): Causal(4,2,2,**kw)
        for kw in ({'tau':0},{'poisson_mix_init':1},{'direct_mode':'bad'}):
            with self.assertRaises(ValueError): Full(4,2,2,**kw)
        with self.assertRaises(ValueError): self.model()(torch.zeros(1,0,4,dtype=torch.float64))

if __name__ == '__main__':
    unittest.main()
