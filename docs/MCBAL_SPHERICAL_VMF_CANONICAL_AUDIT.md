# Canonical spherical vMF frontier for the mcbal corridor

## Live repository correction

At the audited head, PR #168 is the spherical vMF development itself. The main
branch does not contain the previously described nine-file finite
product-marginal implementation, and PR #167 remains an alias-oriented corridor
audit. Consequently this branch does not claim that the finite-to-continuous
intertwiner has already been merged. It develops the continuous exponential
family independently on native Mathlib measure and derivative primitives.

## Canonical carrier and measure

For a finite-dimensional nontrivial real inner-product space `E`, the sample
space is the subtype

```lean
Metric.sphere (0 : E) 1
```

and the rotation-invariant finite measure is Mathlib's `Measure.toSphere`
applied to an additive Haar measure. The branch then uses
`FiniteMeasure.normalize` to obtain a probability measure. This normalization
is mathematically significant: the partition function satisfies `Z(0)=1`.

With natural parameter `theta : E`, the exact law is the Esscher tilt

```math
p_\theta(ds)
= \frac{\exp\langle\theta,s\rangle}
        {\int_{S^{d-1}}\exp\langle\theta,u\rangle\,\sigma(du)}\,\sigma(ds),
```

implemented by Mathlib's `Measure.tilted`.

## Correct normalized Bessel formula

Let `d = finrank R E`, `nu = d/2 - 1`, and `kappa = ||theta||`. For the
unnormalized surface-area measure one has

```math
\int_{S^{d-1}} e^{\langle\theta,s\rangle}\,dS(s)
= (2\pi)^{d/2}\,\frac{I_\nu(\kappa)}{\kappa^\nu}.
```

The branch, however, uses probability-normalized spherical Haar measure. Its
closed form must therefore be

```math
Z_d^{\mathrm{prob}}(\kappa)
= \Gamma(d/2)\left(\frac{2}{\kappa}\right)^\nu I_\nu(\kappa),
```

with the continuous extension `Z_d^{prob}(0)=1`. The unnormalized formula
cannot be attached to `vmfPartition` without changing the base-measure
contract.

The repository currently has a genuine integral definition of `I_0`, but no
general real-order modified Bessel `I_nu` owner with the recurrence and
positivity package needed for arbitrary dimension. For that reason the branch
keeps the canonical integral partition as theorem authority and does not insert
a synthetic Bessel certificate.

## Natural parameter calculus

The existing owner proves that every linear spherical observable is bounded,
all exponential moments are finite, and the cumulant-generating function is
analytic on all real parameters. It defines

```math
A(\theta)=\log Z(\theta),
\qquad
\varphi(\theta)=\int s\,p_\theta(ds).
```

The new field-derivative owner proves additive tilting

```math
(p_\theta)^{t\langle v,\cdot\rangle}=p_{\theta+tv},
```

and the exact line derivative at every `t`:

```math
\frac{d}{dt}A(\theta+tv)
=\langle v,\varphi(\theta+tv)\rangle.
```

It also proves

```math
\left.\frac{d}{dt}\langle v,\varphi(\theta+tv)\rangle\right|_{t=0}
=\operatorname{Cov}_{p_\theta}
  (\langle v,S\rangle,\langle v,S\rangle),
```

and packages the mixed covariance as a native `LinearMap.BilinForm`.

Directional cumulants are defined by actual iterated derivatives of `A`. The
first and second cumulants are respectively the projected response and the
variance. Crucially,

```math
\left.\frac{d^2}{dt^2}\langle v,\varphi(\theta+tv)\rangle\right|_{t=0}
=\kappa_3(\theta;v,v,v).
```

Thus covariance is the first derivative of the response, whereas the quadratic
Taylor coefficient of the response is a third cumulant.

## Field parameter `theta = beta h`

For

```math
A_\beta(h)=A(\beta h),
```

the exact chain-rule factors are

```math
D_h A_\beta(h)[v]
=\beta\langle v,\varphi_\beta(h)\rangle,
```

and

```math
D_h^2 A_\beta(h)[v,v]
=\beta^2\operatorname{Var}_{p_{\beta h}}\langle v,S\rangle.
```

Accordingly, for `beta != 0`,

```math
\langle v,\varphi_\beta(h)\rangle
=\beta^{-1}D_h A_\beta(h)[v].
```

Writing the mean response directly as `grad_h log Z` without the factor
`beta^{-1}` is incorrect when the external field, rather than the natural
parameter, is the differentiation variable.

## Controlled closure expansion

For a random effective field `H`, the exact defect is

```math
\Delta
=\mathbb E[\varphi(H)]-\varphi(\mathbb E H).
```

The existing continuous closure owner proves, for an actual derivative `D` and
actual bilinear second derivative `B`,

```math
\Delta
=\frac12\mathbb E\,B[\xi,\xi]
 +\mathbb E\,R_2(H),
\qquad
\xi=H-\mathbb EH,
```

and the rigorous remainder estimate

```math
\left\|\Delta-\frac12\mathbb E\,B[\xi,\xi]\right\|
\le \frac{C}{6}\mathbb E\|\xi\|^3
```

whenever the pointwise Taylor remainder is bounded by
`(C/6) * ||xi||^3`.

For the vMF response, `D varphi` is covariance and `D^2 varphi` is a third
cumulant tensor. Therefore the quadratic closure term contracts the third
cumulant with the field covariance. Calling that coefficient simply the
"covariance Hessian" confuses the Hessian of `A` with the Hessian of
`grad A`.

The small parameter in this estimate is the centered field fluctuation
`||H-EH||`; it is not automatically the concentration `kappa`. A genuine
vMF-specific uniform remainder theorem still requires a bound on the next
response derivative, equivalently a fourth-cumulant bound, on the convex field
region traversed by the random fluctuations.

## Plefka versus TAP

The theorem above is a controlled delta-method/Jensen-closure expansion. It is
not, by itself, the full Thouless--Anderson--Palmer correction. A TAP theorem
must start from an interpolation of the coupled joint law, differentiate the
free energy with respect to the Plefka coupling parameter, and derive the
Onsager reaction term from the second coupling derivative. This distinction is
retained in the code.

## New theorem owner

```text
lean/InfoGeometry/LLM/SphericalVMFFieldDerivatives.lean
```

Principal declarations:

```text
law_tilted_spinObservable
deriv_directionalPotential_eq_inner_response
deriv_projectedResponseLine_zero_eq_covarianceHessian
directionalCumulant
iteratedDeriv_two_projectedResponseLine_zero_eq_cumulant_three
vmfFieldDirectionalPotential
deriv_vmfFieldDirectionalPotential_eq_beta_mul_response
inner_vmfResponse_eq_inv_mul_deriv_fieldPotential
iteratedDeriv_two_vmfFieldDirectionalPotential_zero_eq_beta_sq_covariance
vmfFieldDirectionalCumulant
```

The public umbrella `InfoGeometry.LLM` imports the new owner.

## Verification gate

```text
scripts/check_spherical_vmf_native.sh
```

The script:

1. rejects `sorry`, `admit`, and custom primitive declarations in the theorem
   owners;
2. builds `InfoGeometry.LLM`;
3. executes `SphericalVMFNativeAudit.lean`;
4. rejects unexpected transitive axioms or `sorryAx`.

GitHub Actions currently terminates before provisioning a runner and reports no
executed steps. Therefore the presence of this gate must not be reported as a
successful kernel run until an environment with Lean 4.28.1 and the pinned
Mathlib commit actually executes it.

## Remaining theorem frontier

The next non-duplicative developments are:

1. prove invariance of the normalized `toSphere` law under orthogonal linear
   isometries and deduce radiality of `Z` and collinearity of the response;
2. develop or import a genuine general-order modified Bessel `I_nu` API and
   prove the normalized closed form and Bessel-ratio response;
3. upgrade directional identities to a full Frechet derivative/Riesz-gradient
   theorem where useful;
4. derive a vMF-specific uniform third-derivative response bound and discharge
   the generic remainder premise;
5. formalize the Plefka interpolation of the coupled synchronous model and
   derive the actual TAP/Onsager reaction term;
6. construct the still-missing finite-to-continuous approximation/convergence
   map rather than identifying the two carriers by terminology.
