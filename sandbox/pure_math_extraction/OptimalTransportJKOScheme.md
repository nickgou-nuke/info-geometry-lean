# Pure Mathematical Problem: The JKO Scheme and Wasserstein Gradient Flow

## Mathematical Context
In the theory of optimal transport (specifically the Jordan-Kinderlehrer-Otto or JKO scheme), the evolution of a probability density under a Fokker-Planck or diffusion equation can be framed as a gradient flow in the space of probability measures equipped with the $L^2$-Wasserstein metric $W_2$.

Given a free energy functional $\mathcal{F}(\rho)$, the JKO scheme defines discrete time steps $\tau > 0$ by minimizing the variational problem:
$$ \rho_{k+1} = \text{argmin}_{\rho} \left( \mathcal{F}(\rho) + \frac{1}{2\tau} W_2^2(\rho, \rho_k) \right) $$

As $\tau \to 0$, the discrete scheme converges to the continuous gradient flow equation (the continuity equation):
$$ \frac{\partial \rho}{\partial t} = \nabla \cdot (\rho \nabla (\delta \mathcal{F} / \delta \rho)) $$

This provides a rigorous thermodynamic interpretation of diffusion as steepest descent in the Wasserstein geometry.

## Explicit Premises and Givens
Let $\mathcal{M}$ be a manifold of states.
Let $Dens(\mathcal{M})$ be the space of probability densities over $\mathcal{M}$.
Let $W_2 : Dens(\mathcal{M}) \times Dens(\mathcal{M}) \to \mathbb{R}_{\ge 0}$ be the Wasserstein metric.
Let $\mathcal{F} : Dens(\mathcal{M}) \to \mathbb{R}$ be a Free Energy functional (e.g., internal energy minus entropy).
Let $JKO_\tau : Dens(\mathcal{M}) \to Dens(\mathcal{M})$ be the discrete step mapping defined by the variational argmin above.

## What is to be Proved
1. **Mobility Tensor Claim**: Prove that the variation $\delta \mathcal{F} / \delta \rho$ induces a velocity field $v = -\nabla (\delta \mathcal{F} / \delta \rho)$ through a positive semi-definite mobility tensor.
2. **Continuity Equation Claim**: Prove that the continuous limit of the $JKO$ step satisfies the continuity equation $\partial_t \rho + \nabla \cdot (\rho v) = 0$.
3. **Wasserstein Metric Law Claim**: Prove that $W_2^2$ is bounded strictly by the action integral of the continuity equation via the Benamou-Brenier formula.

## Discussion Protocol
Do not provide Lean 4 code. Discuss how this property is rigorously derived in optimal transport theory (e.g., using lower semi-continuity, coercivity, and the Benamou-Brenier fluid dynamics formulation). Discuss how to formalize the geometric meaning of the gradient flow without relying on explicit measure theory.
