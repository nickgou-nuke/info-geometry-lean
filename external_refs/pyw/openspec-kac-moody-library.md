# OpenSpec 技术提案: Kac-Moody & W-Algebra 计算库

**项目名称**: `pyw`  
**版本**: 0.1.0 (提案)  
**日期**: 2025-01-31  
**调研方法**: CCG 多模型协作系统 (5 个并行 Ultrabrain agents)

---

## 📋 执行摘要

### 项目目标

开发一个 Python 库，用于快速完成以下计算：
- (co-)roots, affine (co-)roots, (co-)weights, affine (co-)weights
- Weyl, affine Weyl, extended Weyl group 操作
- 李代数的 embedding，表示的分解，Levi subalgebra 相关计算
- **特别支持 fractional level/weights 的计算**

### 核心发现

| 调研项 | 结论 |
|--------|------|
| **SymPy** | ❌ 不适用 - 仅支持有限维简单李代数 |
| **SageMath** | ✅ 推荐基础 - 完整的仿射李代数支持 |
| **Fractional Weights** | ⚠️ 需扩展 - 使用 `weight_space()` 而非 `weight_lattice()` |
| **W-algebra** | ❌ 需实现 - 无现成开源实现 |
| **GitHub 项目** | ⚠️ 有限 - 大多不活跃或功能不完整 |

### 推荐方案

**基于 SageMath 扩展** - 利用 SageMath 的成熟实现，扩展 fractional level 支持和 W-algebra 构造。

**预计工作量**: 2-3 个月

---

## 📚 需求分析

### 来源论文

1. **Kac, Wakimoto. "On rationality of W-algebras"**
2. **Shan, Xie, Yan. "Mirror symmetry for circle compactified 4d N=2 SCFTs"**

### 核心计算需求

#### 优先级 1: 基础根系统 (SageMath 已支持)

| 功能 | 描述 | SageMath 支持 |
|------|------|---------------|
| 有限维根系统 | $\Delta, \Delta_+, \Pi$ | ✅ 完整 |
| 仿射根系统 | $\widehat{\Delta}^{\mathrm{re}}, \widehat{\Delta}^{\mathrm{im}}$ | ✅ 完整 |
| 余根系统 | $\Delta^\vee, \widehat{\Delta}^\vee$ | ✅ 完整 |
| Weyl 向量 | $\rho, \widehat{\rho}$ | ✅ 完整 |
| Cartan 矩阵 | 有限和仿射类型 | ✅ 完整 |

#### 优先级 2: Weyl 群操作 (SageMath 已支持)

| 功能 | 描述 | SageMath 支持 |
|------|------|---------------|
| 有限 Weyl 群 | $W$ | ✅ 完整 |
| 仿射 Weyl 群 | $\widehat{W} = W \ltimes t_{Q^\vee}$ | ✅ 完整 |
| 扩展仿射 Weyl 群 | $\tilde{W} = W \ltimes t_{Q^*}$ | ✅ 完整 |
| Dot action | $w.\lambda = w(\lambda + \widehat{\rho}) - \widehat{\rho}$ | ⚠️ 需封装 |
| 平移算符 | $t_\alpha$ | ⚠️ 需封装 |

#### 优先级 3: Fractional Level 计算 (需扩展)

| 功能 | 描述 | SageMath 支持 |
|------|------|---------------|
| Fractional weights | $\frac{3}{4}\Lambda_0$ | ⚠️ 使用 `weight_space()` |
| Fractional level | $k = -h^\vee + \frac{p}{u}$ | ❌ 需实现 |
| 可容许权重判定 | 条件 (1.1a), (1.1b) | ❌ 需实现 |
| 主可容许权重 | $\widehat{P}_{u,y}^k$ | ❌ 需实现 |
| 非退化条件 | $(\lambda|\alpha) \notin \mathbb{Z}$ | ❌ 需实现 |

#### 优先级 4: 李代数 Embedding (需实现)

| 功能 | 描述 | SageMath 支持 |
|------|------|---------------|
| $sl_2$-triple | $(f, x, e)$ | ❌ 需实现 |
| Grading | $\mathfrak{g} = \bigoplus_{j} \mathfrak{g}_j$ | ❌ 需实现 |
| 中心化子 | $\mathfrak{g}^f$ | ❌ 需实现 |
| Levi 子代数 | $[\mathfrak{g}^h, \mathfrak{g}^h]$ | ❌ 需实现 |
| Nilpotent orbit | 分类和计算 | ❌ 需实现 |

#### 优先级 5: W-algebra 构造 (需实现)

| 功能 | 描述 | SageMath 支持 |
|------|------|---------------|
| 量子 DS 约化 | $H_f(-)$ | ❌ 需实现 |
| 中心荷 | $c(\mathfrak{g}, f, k)$ | ❌ 需实现 |
| 共形权重 | $h_\Lambda$ | ❌ 需实现 |
| 字符计算 | $\chi_{L(\lambda)}$ | ❌ 需实现 |

---

## 🔧 技术方案

### 架构设计

```
pyw/
├── core/                      # 核心层 (基于 SageMath)
│   ├── root_system.py         # 根系统封装
│   ├── weyl_group.py          # Weyl 群封装
│   └── weight_space.py        # 权空间封装 (支持 fractional)
│
├── fractional/                # Fractional Level 扩展
│   ├── level.py               # FractionalLevel 类
│   ├── admissible.py          # 可容许权重判定
│   ├── principal.py           # 主可容许权重构造
│   └── nondegenerate.py       # 非退化条件检查
│
├── embedding/                 # 李代数 Embedding
│   ├── sl2_triple.py          # sl2-triple 构造
│   ├── grading.py             # Grading 计算
│   ├── centralizer.py         # 中心化子
│   ├── levi.py                # Levi 子代数
│   └── nilpotent.py           # Nilpotent orbit
│
├── walgebra/                  # W-algebra 构造
│   ├── ds_reduction.py        # 量子 DS 约化
│   ├── central_charge.py      # 中心荷计算
│   ├── conformal_weight.py    # 共形权重
│   └── character.py           # 字符计算
│
├── algorithms/                # 论文中的具体算法
│   ├── kac_wakimoto.py        # Kac-Wakimoto 论文算法
│   └── mirror_symmetry.py     # Mirror symmetry 论文算法
│
└── utils/                     # 工具函数
    ├── latex.py               # LaTeX 渲染
    └── visualization.py       # 可视化
```

### 核心类设计

#### 1. FractionalLevel 类

```python
from sage.all import *
from fractions import Fraction

class FractionalLevel:
    """
    表示 fractional level k = -h^∨ + p/u
    
    参数:
        cartan_type: Cartan 类型，如 ['A', 2, 1]
        p: 分子 (正整数)
        u: 分母 (正整数)
    
    约束:
        - (p, u) = 1 (互质)
        - (u, ℓ) = 1 (ℓ 是 lacety)
        - p ≥ h^∨
    """
    
    def __init__(self, cartan_type, p, u):
        self.cartan_type = cartan_type
        self.p = p
        self.u = u
        self._validate()
        
    def _validate(self):
        """验证 fractional level 的约束条件"""
        from math import gcd
        
        # 获取 dual Coxeter number
        R = RootSystem(self.cartan_type)
        self.h_vee = R.cartan_type().dual_coxeter_number()
        
        # 获取 lacety
        self.lacety = self._get_lacety()
        
        # 检查约束
        if gcd(self.p, self.u) != 1:
            raise ValueError(f"p={self.p} 和 u={self.u} 必须互质")
        if gcd(self.u, self.lacety) != 1:
            raise ValueError(f"u={self.u} 和 lacety={self.lacety} 必须互质")
        if self.p < self.h_vee:
            raise ValueError(f"p={self.p} 必须 >= h^∨={self.h_vee}")
    
    def _get_lacety(self):
        """获取 lacety (ADE: 1, BCF: 2, G2: 3)"""
        ct = self.cartan_type[0]
        if ct in ['A', 'D', 'E']:
            return 1
        elif ct in ['B', 'C', 'F']:
            return 2
        elif ct == 'G':
            return 3
        else:
            raise ValueError(f"未知的 Cartan 类型: {ct}")
    
    @property
    def level(self):
        """返回 level k = -h^∨ + p/u"""
        return -self.h_vee + Fraction(self.p, self.u)
    
    @property
    def k_plus_h_vee(self):
        """返回 k + h^∨ = p/u"""
        return Fraction(self.p, self.u)
```

#### 2. AdmissibleWeight 类

```python
class AdmissibleWeight:
    """
    可容许权重判定
    
    条件 (1.1a): (λ + ρ̂ | α^∨) ∉ {0, -1, -2, ...} 对所有 α^∨ ∈ Δ̂_+^∨
    条件 (1.1b): Δ̂_λ^∨ 的 Q-张成包含 Δ̂^∨
    """
    
    def __init__(self, cartan_type, weight, level):
        self.cartan_type = cartan_type
        self.weight = weight
        self.level = level
        self._setup()
    
    def _setup(self):
        """初始化根系统和权空间"""
        R = RootSystem(self.cartan_type)
        self.W = R.weight_space(extended=True)
        self.rho_hat = self._compute_affine_weyl_vector()
        
    def is_admissible(self):
        """判定是否为可容许权重"""
        return self._check_condition_1a() and self._check_condition_1b()
    
    def _check_condition_1a(self):
        """检查条件 (1.1a)"""
        # 实现细节...
        pass
    
    def _check_condition_1b(self):
        """检查条件 (1.1b)"""
        # 实现细节...
        pass
```

#### 3. PrincipalAdmissibleWeight 类

```python
class PrincipalAdmissibleWeight:
    """
    主可容许权重构造
    
    集合: P̂_{u,y}^k = {y.(Λ + (k + h^∨ - p)D) | Λ ∈ P̂_+^{p-h^∨}}
    """
    
    def __init__(self, fractional_level, y):
        self.level = fractional_level
        self.y = y  # 扩展仿射 Weyl 群元素
        
    def construct_set(self):
        """构造主可容许权重集合"""
        # 实现细节...
        pass
    
    def is_nondegenerate(self, weight):
        """判定是否为非退化主可容许权重"""
        # 条件: (λ|α) ∉ Z 对所有 α ∈ Δ^∨
        pass
```

### Fractional Weights 的关键实现

```python
# 关键发现: 使用 weight_space() 而非 weight_lattice()

from sage.all import *

def create_fractional_weight(cartan_type, coefficients):
    """
    创建 fractional weight
    
    参数:
        cartan_type: 如 ['A', 2, 1]
        coefficients: 字典 {i: Fraction(p, q)} 或 {i: (p, q)}
    
    示例:
        create_fractional_weight(['A', 2, 1], {0: (3, 4), 1: (1, 2)})
        # 返回 3/4*Lambda[0] + 1/2*Lambda[1]
    """
    R = RootSystem(cartan_type)
    W = R.weight_space(extended=True)  # 关键: 使用 weight_space
    Lambda = W.fundamental_weights()
    
    result = W.zero()
    for i, coef in coefficients.items():
        if isinstance(coef, tuple):
            p, q = coef
            result += Integer(p) / Integer(q) * Lambda[i]
        else:
            result += coef * Lambda[i]
    
    return result

# 使用示例
w = create_fractional_weight(['A', 2, 1], {0: (3, 4), 1: (1, 2)})
print(w)  # 3/4*Lambda[0] + 1/2*Lambda[1]
```

---

## 📊 工具对比

### SymPy vs SageMath

| 功能 | SymPy | SageMath |
|------|-------|----------|
| 有限维简单李代数 | ✅ 完整 | ✅ 完整 |
| 根系统 | ✅ 基本 | ✅ 完整 |
| Cartan 矩阵 | ✅ 完整 | ✅ 完整 |
| Weyl 群 | ⚠️ 基本 | ✅ 完整 |
| **仿射李代数** | ❌ 无 | ✅ 完整 |
| **Kac-Moody 代数** | ❌ 无 | ✅ 完整 |
| **Fractional weights** | ❌ 无 | ⚠️ 需技巧 |
| **表示论** | ❌ 无 | ✅ 完整 |
| 文档质量 | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ |
| 社区支持 | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ |

**结论**: SageMath 是唯一可行的基础库

### GitHub 开源项目

| 项目 | Stars | 维护状态 | Fractional 支持 | 推荐度 |
|------|-------|----------|-----------------|--------|
| **sagemath/sage** | 1000+ | 活跃 | ⚠️ 需技巧 | ⭐⭐⭐⭐⭐ |
| tomaszcib/SymPy-LieAlgebras | 2 | 较少 | ❌ | ⭐⭐ |
| abackus/kacmoody | 2 | 不活跃 | ⚠️ 部分 | ⭐⭐⭐ |
| deehzee/affine-charform | 2 | 不活跃 | ⚠️ 理论 | ⭐⭐ |
| davidsd/lie | 54 | 较旧 | ⚠️ 取决于 LiE | ⭐⭐⭐⭐ |

---

## 🗓️ 实现路线图

### Phase 1: 基础验证 (2 周)

- [ ] 验证 SageMath 的 fractional weights 支持
- [ ] 测试可容许权重判定
- [ ] 实现简单的 fractional level 示例
- [ ] 创建项目结构和测试框架

**交付物**:
- 项目骨架
- 基础测试用例
- 验证报告

### Phase 2: 核心扩展 (4 周)

- [ ] 实现 `FractionalLevel` 类
- [ ] 实现 `AdmissibleWeight` 类
- [ ] 实现 `PrincipalAdmissibleWeight` 构造算法
- [ ] 实现非退化条件检查
- [ ] 实现 Dot action 和平移算符封装

**交付物**:
- `pyw.fractional` 模块
- 单元测试 (覆盖率 > 80%)
- API 文档

### Phase 3: Embedding 支持 (4 周)

- [ ] 实现 `SL2Triple` 类
- [ ] 实现 `Grading` 计算
- [ ] 实现 `Centralizer` 类
- [ ] 实现 `LeviSubalgebra` 构造
- [ ] 实现 `NilpotentOrbit` 分类

**交付物**:
- `pyw.embedding` 模块
- 集成测试
- 示例 Notebook

### Phase 4: W-algebra 支持 (4 周)

- [ ] 实现量子 Drinfeld-Sokolov 约化框架
- [ ] 实现中心荷计算
- [ ] 实现共形权重计算
- [ ] 实现字符计算基础

**交付物**:
- `pyw.walgebra` 模块
- 论文算法验证
- 性能基准测试

### Phase 5: 论文算法 (4 周)

- [ ] 实现 Kac-Wakimoto 论文中的算法
- [ ] 实现 Mirror symmetry 论文中的算法
- [ ] 添加高级示例和教程

**交付物**:
- `pyw.algorithms` 模块
- 完整教程
- 论文复现验证

### Phase 6: 文档和发布 (2 周)

- [ ] 编写用户文档
- [ ] 编写 API 文档
- [ ] 添加教程和示例
- [ ] 发布到 PyPI

**交付物**:
- 完整文档站点
- PyPI 包
- GitHub Release

**总工作量**: 约 20 周 (5 个月)

---

## 📦 依赖项

### 必需依赖

```toml
[project]
dependencies = [
    "sagemath >= 10.0",  # 核心数学库
]
```

### 可选依赖

```toml
[project.optional-dependencies]
dev = [
    "pytest >= 7.0",
    "pytest-cov >= 4.0",
    "black >= 23.0",
    "mypy >= 1.0",
]
docs = [
    "sphinx >= 6.0",
    "sphinx-rtd-theme >= 1.0",
]
jupyter = [
    "jupyter >= 1.0",
    "ipywidgets >= 8.0",
]
```

---

## 🔗 参考资源

### 论文

1. Kac, V. G., Wakimoto, M. "On rationality of W-algebras"
2. Shan, D., Xie, D., Yan, W. "Mirror symmetry for circle compactified 4d N=2 SCFTs"
3. Kac, V. G. "Infinite-dimensional Lie algebras" (3rd ed.)

### 文档

- [SageMath Affine Lie Algebras](https://doc.sagemath.org/html/en/thematic_tutorials/lie/affine.html)
- [SageMath Root Systems](https://doc.sagemath.org/html/en/reference/combinat/sage/combinat/root_system/root_system.html)
- [SageMath Integrable Representations](https://doc.sagemath.org/html/en/thematic_tutorials/lie/integrable.html)

### 代码参考

- SageMath 源码: `src/sage/algebras/lie_algebras/affine_lie_algebra.py`
- SageMath 源码: `src/sage/combinat/root_system/`
- GitHub: `abackus/kacmoody`

### 社区讨论

- [AskSage: rational weights of affine Lie algebra](https://ask.sagemath.org/question/67562/rational-weights-of-affine-lie-algebra/)

---

## ✅ 约束集总结

### 技术约束

1. **必须基于 SageMath** - 唯一支持仿射李代数的成熟库
2. **Fractional weights 使用 `weight_space()`** - 不能使用 `weight_lattice()`
3. **W-algebra 需要从头实现** - 无现成开源实现
4. **需要 Python 3.10+** - SageMath 10.x 要求

### 数学约束

1. **Fractional level**: $k = -h^\vee + \frac{p}{u}$，满足 $(p,u)=1$, $(u,\ell)=1$, $p \geq h^\vee$
2. **可容许权重**: 满足条件 (1.1a) 和 (1.1b)
3. **主可容许权重**: $y(\widehat{S}_{(u)}) \subset \widehat{\Delta}_+^\vee$

### 性能约束

1. **高秩李代数**: $u^r$ 指数增长，需要高效枚举算法
2. **仿射 Weyl 群**: 无限群，需要有限表示
3. **字符计算**: 可能需要数值近似

---

## 📝 下一步行动

### 立即行动 (本周)

1. ✅ 完成调研报告
2. ⏳ 创建项目仓库
3. ⏳ 设置开发环境
4. ⏳ 实现第一个原型 (FractionalLevel 类)

### 短期行动 (下周)

1. 实现 AdmissibleWeight 类
2. 编写测试用例
3. 验证论文中的示例

### 中期行动 (本月)

1. 完成 Phase 1 和 Phase 2
2. 发布 alpha 版本
3. 收集反馈

---

**状态**: ✅ 调研完成，提案已生成  
**下一步**: 等待用户确认后开始实现
