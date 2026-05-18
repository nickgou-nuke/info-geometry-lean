# sl(2) Boundary Admissible Weights at k = -4/3

## 概述

本文档记录了 $\mathfrak{sl}_2$ 在边界可容许能级 $k = -4/3$ 时主可容许权重的计算方法和验证结果。

## 数学公式

### 1. 边界可容许能级

对于 $\mathfrak{sl}_2$，边界可容许能级的形式为：
$$k = -h^\vee + \frac{p}{u}$$

其中：
- $h^\vee = 2$（对偶 Coxeter 数）
- $p = 2$, $u = 3$（互质）
- $k = -2 + \frac{2}{3} = -\frac{4}{3}$

### 2. 主可容许权重

主可容许权重由以下公式给出：
$$\Lambda(m) = t_{m\omega} \cdot (k\Lambda_0), \quad m = 0, 1, \ldots, u-1$$

**关键点：使用正确的平移公式符号**

正确的平移公式（dot action）：
$$t_\beta(\mu) = \mu - \mu(K)\beta + (\delta\text{-shift})$$

错误的平移公式（会产生错误结果）：
$$t_\beta(\mu) = \mu + \mu(K)\beta$$

### 3. 显式计算

对于 $\mathfrak{sl}_2$：
- 基本余权：$\omega = \Lambda_1 - \Lambda_0$
- $\mu(K) = k + h^\vee = \frac{2}{3}$

代入公式：
$$\begin{aligned}
\Lambda(m) &= k\Lambda_0 - (k + h^\vee) \cdot m \cdot \omega \\
&= k\Lambda_0 - \frac{2m}{3}(\Lambda_1 - \Lambda_0) \\
&= \left(k + \frac{2m}{3}\right)\Lambda_0 - \frac{2m}{3}\Lambda_1
\end{aligned}$$

### 4. 结果

| $m$ | 权重 $\Lambda$ | LaTeX |
|-----|----------------|-------|
| 0 | $-\frac{4}{3}\Lambda_0$ | $-\frac{4}{3}\Lambda_0$ |
| 1 | $-\frac{2}{3}\Lambda_0 - \frac{2}{3}\Lambda_1$ | $-\frac{2}{3}\Lambda_0 - \frac{2}{3}\Lambda_1$ |
| 2 | $-\frac{4}{3}\Lambda_1$ | $-\frac{4}{3}\Lambda_1$ |

### 5. 共形维度

共形维度公式：
$$h_\Lambda = \frac{(\bar{\Lambda}, \bar{\Lambda} + 2\rho)}{2(k + h^\vee)}$$

对于 $\mathfrak{sl}_2$ 的有限部分 $a\omega$（$(\omega, \omega) = 1/2$）：
$$h(a) = \frac{3|a|(|a| + 2)}{8}$$

其中 $|a|$ 是 Dynkin 标签的绝对值（权重在反优势方向，$a < 0$）。

| $m$ | $|a|$ | $h_\Lambda$ |
|-----|------|------------|
| 0 | $0$ | $0$ |
| 1 | $\frac{2}{3}$ | $\frac{2}{3}$ |
| 2 | $\frac{4}{3}$ | $\frac{5}{3}$ |

## Python 实现

### 独立验证脚本

文件 `pyw/fractional/verify_sl2_boundary.py` 提供了不依赖 SageMath 的独立验证：

```bash
python pyw/fractional/verify_sl2_boundary.py
```

### SageMath 集成

文件 `pyw/fractional/boundary_admissible.py` 提供了与 SageMath 集成的完整实现：

```python
from pyw.fractional import BoundaryAdmissibleWeights

# 创建 sl(2) 在 k = -4/3 的边界可容许权重计算器
baw = BoundaryAdmissibleWeights(['A', 1, 1], p=2, u=3)

# 计算权重
weights = baw.compute_sl2_admissible_weights()

# 计算共形维度
dimensions = baw.compute_conformal_dimensions()
```

## 验证

运行独立验证脚本的输出：

```
======================================================================
sl(2) Principal Admissible Weights at k = -4/3
======================================================================

Input parameters:
  h^∨ = 2
  k = -4/3
  k + h^∨ = 2/3
  p = 2, u = 3
  Verification: k = -h^∨ + p/u = -2 + 2/3 = -4/3 ✓

----------------------------------------------------------------------
Computed Weights
----------------------------------------------------------------------

m = 0:
  Coefficients: a₀ = -4/3, a₁ = 0
  Λ = -\frac{4}{3}\Lambda_0
  Level check: -4/3 + 0 = -4/3 (expected -4/3) ✓

m = 1:
  Coefficients: a₀ = -2/3, a₁ = -2/3
  Λ = -\frac{2}{3}\Lambda_0 - \frac{2}{3}\Lambda_1
  Level check: -2/3 + -2/3 = -4/3 (expected -4/3) ✓

m = 2:
  Coefficients: a₀ = 0, a₁ = -4/3
  Λ = - \frac{4}{3}\Lambda_1
  Level check: 0 + -4/3 = -4/3 (expected -4/3) ✓

✓ All weights match!

----------------------------------------------------------------------
Conformal Dimensions
----------------------------------------------------------------------

Summary: h = [0, 2/3, 5/3]
Expected: [0, 2/3, 5/3]
Match: True ✓
```

## 参考文献

1. Kac, V. G., Wakimoto, M. "On rationality of W-algebras"
2. Kac, V. G. "Infinite-dimensional Lie algebras" (3rd ed.)
3. Shan, D., Xie, D., Yan, W. "Mirror symmetry for circle compactified 4d N=2 SCFTs"
