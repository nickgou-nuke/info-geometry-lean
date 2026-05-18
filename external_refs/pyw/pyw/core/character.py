from __future__ import annotations

from dataclasses import dataclass, field
from itertools import product
from typing import TYPE_CHECKING, Any, Dict, Iterable, Iterator, List, Optional, Tuple

from sage.all import Integer, QQ, binomial, matrix, vector
from sage.all import ZZ

if TYPE_CHECKING:
    from .affine_lie_algebra import AffineLieAlgebra
    from .affine_weight import AffineWeight


def _element_word_list(element: Any) -> list[int]:
    if hasattr(element, "reduced_word_list"):
        return list(element.reduced_word_list())
    return [int(i) for i in element.reduced_word()]


@dataclass(frozen=True)
class KLNumeratorTerm:
    representative: Any
    weight: "AffineWeight"
    coefficient: Any


@dataclass
class KazhdanLusztigData:
    algebra: Any
    lambda_hat: "AffineWeight"
    Lambda_hat: "AffineWeight"
    w_to_lambda: Any
    order: int
    translations: List[Any]
    W_affine_as_words: List[Any]
    stabilizer_candidates: List[Any]
    quotient_representatives: List[Any]

    @property
    def integral_case(self) -> bool:
        labels = self.Lambda_hat.dynkin_labels()
        return all(value in ZZ for value in labels.values())

    def apply(self, element: Any, weight: "AffineWeight") -> "AffineWeight":
        semidirect = self.algebra.affine_weyl_group()
        word = tuple(_element_word_list(element))
        return semidirect.from_word(word).action(weight)

    def quotient_weight(self, representative: Any) -> "AffineWeight":
        rho_hat = self.algebra.affine_rho()
        return self.apply(representative, self.Lambda_hat + rho_hat) - rho_hat

    def weyl_to_be_summed(self) -> List[Any]:
        from .bruhat import BruhatOrder

        if not self.W_affine_as_words:
            return []
        bruhat = BruhatOrder(self.W_affine_as_words[0].parent())
        lower = self.w_to_lambda
        result = []
        for w in self.quotient_representatives:
            if bruhat.le(lower, w):
                result.append(w)
        return sorted(result, key=lambda w: (int(w.length()), tuple(_element_word_list(w))))


@dataclass
class FormalCharacter:
    coefficients: Dict[int, Any] = field(default_factory=dict)
    max_grade: int = 10
    algebra: Optional["AffineLieAlgebra"] = None

    def __post_init__(self) -> None:
        self.coefficients = {
            grade: coeff
            for grade, coeff in self.coefficients.items()
            if coeff != 0 and grade <= self.max_grade
        }

    def __getitem__(self, grade: int) -> Any:
        return self.coefficients.get(grade, 0)

    def __setitem__(self, grade: int, value: Any) -> None:
        if value == 0:
            self.coefficients.pop(grade, None)
            return
        if grade <= self.max_grade:
            self.coefficients[grade] = value

    def __iter__(self) -> Iterator[Tuple[int, Any]]:
        for grade in sorted(self.coefficients):
            yield grade, self.coefficients[grade]

    def __len__(self) -> int:
        return len(self.coefficients)

    def __add__(self, other: "FormalCharacter") -> "FormalCharacter":
        if not isinstance(other, FormalCharacter):
            return NotImplemented

        max_grade = max(self.max_grade, other.max_grade)
        result: Dict[int, Any] = {}
        for grade in set(self.coefficients) | set(other.coefficients):
            if grade > max_grade:
                continue
            coeff = self[grade] + other[grade]
            if coeff != 0:
                result[grade] = coeff
        return FormalCharacter(result, max_grade=max_grade, algebra=self.algebra or other.algebra)

    def __sub__(self, other: "FormalCharacter") -> "FormalCharacter":
        if not isinstance(other, FormalCharacter):
            return NotImplemented

        max_grade = max(self.max_grade, other.max_grade)
        result: Dict[int, Any] = {}
        for grade in set(self.coefficients) | set(other.coefficients):
            if grade > max_grade:
                continue
            coeff = self[grade] - other[grade]
            if coeff != 0:
                result[grade] = coeff
        return FormalCharacter(result, max_grade=max_grade, algebra=self.algebra or other.algebra)

    def __mul__(self, other: Any) -> "FormalCharacter":
        if isinstance(other, FormalCharacter):
            max_grade = min(self.max_grade, other.max_grade)
            result: Dict[int, Any] = {}
            for grade_1, coeff_1 in self.coefficients.items():
                for grade_2, coeff_2 in other.coefficients.items():
                    grade = grade_1 + grade_2
                    if grade > max_grade:
                        continue
                    result[grade] = result.get(grade, 0) + coeff_1 * coeff_2
            return FormalCharacter(
                result, max_grade=max_grade, algebra=self.algebra or other.algebra
            )

        if isinstance(other, (int, Integer)) or hasattr(other, "__rmul__"):
            result = {
                grade: coeff * other
                for grade, coeff in self.coefficients.items()
                if coeff * other != 0
            }
            return FormalCharacter(result, max_grade=self.max_grade, algebra=self.algebra)

        return NotImplemented

    def __rmul__(self, scalar: Any) -> "FormalCharacter":
        return self.__mul__(scalar)

    def __neg__(self) -> "FormalCharacter":
        return self * (-1)

    @property
    def leading_grade(self) -> Optional[int]:
        if not self.coefficients:
            return None
        return min(self.coefficients)

    @property
    def leading_coefficient(self) -> Any:
        leading_grade = self.leading_grade
        if leading_grade is None:
            return 0
        return self.coefficients[leading_grade]

    def truncate(self, new_max: int) -> "FormalCharacter":
        return FormalCharacter(
            {grade: coeff for grade, coeff in self.coefficients.items() if grade <= new_max},
            max_grade=new_max,
            algebra=self.algebra,
        )

    def shift(self, delta: int) -> "FormalCharacter":
        shifted = {grade + delta: coeff for grade, coeff in self.coefficients.items()}
        return FormalCharacter(shifted, max_grade=self.max_grade + delta, algebra=self.algebra)

    def to_dict(self) -> Dict[int, Any]:
        return dict(self.coefficients)

    def to_list(self, up_to: Optional[int] = None) -> list[Any]:
        if up_to is None:
            up_to = self.max_grade
        return [self[grade] for grade in range(up_to + 1)]


class WeylKacDenominator:
    def __init__(self, algebra: "AffineLieAlgebra") -> None:
        self.algebra = algebra
        self._inverse_cache: Dict[int, FormalCharacter] = {}

    def inverse(self, max_grade: int = 10) -> FormalCharacter:
        cached = self._inverse_cache.get(max_grade)
        if cached is not None:
            return cached

        inverse = self._compute_inverse_product(max_grade)
        self._inverse_cache[max_grade] = inverse
        return inverse

    def _compute_inverse_product(self, max_grade: int) -> FormalCharacter:
        rank = int(getattr(self.algebra, "rank", 1) or 1)
        coeffs: Dict[int, Any] = {0: QQ(1)}

        for step in range(1, max_grade + 1):
            updated: Dict[int, Any] = {}
            for base_grade, base_coeff in coeffs.items():
                max_power = (max_grade - base_grade) // step
                for power in range(max_power + 1):
                    grade = base_grade + power * step
                    contribution = base_coeff * binomial(rank + power - 1, power)
                    updated[grade] = updated.get(grade, 0) + contribution
            coeffs = updated

        return FormalCharacter(coeffs, max_grade=max_grade, algebra=self.algebra)


class VermaCharacter:
    def __init__(self, algebra: "AffineLieAlgebra", weight: "AffineWeight") -> None:
        self.algebra = algebra
        self.weight = weight
        self._denominator = WeylKacDenominator(algebra)

    def character(self, max_grade: int = 10) -> FormalCharacter:
        weight_grade = int(getattr(self.weight, "grade", 0))
        inverse = self._denominator.inverse(max_grade + abs(weight_grade))
        return inverse.shift(-weight_grade).truncate(max_grade)


class KazhdanLusztigCharacter:
    def __init__(self, algebra: "AffineLieAlgebra") -> None:
        from .kazhdan_lusztig import KazhdanLusztigPolynomials

        self.algebra = algebra
        self.kl = KazhdanLusztigPolynomials(algebra.affine_weyl_group_sage())

    @staticmethod
    def _ceil_sqrt_qq(value: Any) -> int:
        target = QQ(value)
        if target <= 0:
            return 0

        lower = 0
        upper = 1
        while QQ(upper) * QQ(upper) < target:
            lower = upper
            upper *= 2

        while lower + 1 < upper:
            mid = (lower + upper) // 2
            if QQ(mid) * QQ(mid) >= target:
                upper = mid
            else:
                lower = mid

        return upper

    def _translations_by_n_shift(
        self,
        weight: "AffineWeight",
        *,
        order: int,
        max_neg_shift: Optional[Any] = None,
    ) -> List[Any]:
        semidirect = self.algebra.affine_weyl_group()
        idxs = [int(i) for i in semidirect._finite_coroot_space.index_set()]
        basis = semidirect._finite_coroot_space.simple_roots()

        if max_neg_shift is None:
            max_neg_shift_value = QQ(order) + QQ(weight.grade)
        else:
            max_neg_shift_value = QQ(max_neg_shift)
        if max_neg_shift_value < 0:
            return []

        if QQ(weight.level) == 0:
            raise ValueError("Translation enumeration by n-shift requires non-zero level")

        linear_coeffs = [QQ(weight.dynkin_labels().get(i, 0)) for i in idxs]
        gram = self._finite_coroot_gram_matrix(idxs)
        radius = self._translation_coefficient_radius(
            level=QQ(weight.level),
            linear_coeffs=linear_coeffs,
            gram=gram,
            max_neg_shift=max_neg_shift_value,
        )

        dimension = len(idxs)
        box_points = (2 * int(radius) + 1) ** int(dimension)
        # Large high-rank boxes become prohibitively expensive with direct
        # product enumeration. Switch to exact branch-and-bound pruning.
        if box_points > 2_000_000:
            return self._translations_by_n_shift_bnb(
                weight,
                order=order,
                max_neg_shift=max_neg_shift_value,
                return_stats=False,
            )

        ranges = [range(-radius, radius + 1) for _ in idxs]

        selected: dict[tuple[int, ...], Any] = {}
        for coeffs in product(*ranges):
            neg_shift = self._minus_Delta_n(
                level=QQ(weight.level),
                linear_coeffs=linear_coeffs,
                gram=gram,
                coeffs=coeffs,
            )
            if neg_shift < 0 or neg_shift > max_neg_shift_value:
                continue

            beta = semidirect._zero_beta
            for i, coeff in zip(idxs, coeffs):
                if coeff:
                    beta += int(coeff) * basis[i]
            selected[tuple(int(coeff) for coeff in coeffs)] = semidirect.translation(beta)

        return [selected[key] for key in sorted(selected.keys())]

    @staticmethod
    def _minus_Delta_n(
        *,
        level: Any,
        linear_coeffs: List[Any],
        gram: List[List[Any]],
        coeffs: tuple[int, ...],
    ) -> Any:
        m = [QQ(c) for c in coeffs]
        linear = sum(QQ(d) * mi for d, mi in zip(linear_coeffs, m))
        quadratic = QQ(0)
        for i, mi in enumerate(m):
            for j, mj in enumerate(m):
                quadratic += mi * QQ(gram[i][j]) * mj
        return linear + QQ(level) * quadratic / QQ(2)

    def _finite_coroot_gram_matrix(self, idxs: List[int]) -> List[List[Any]]:
        semidirect = self.algebra.affine_weyl_group()
        basis = semidirect._finite_coroot_space.simple_roots()
        ambient = {i: basis[i].to_ambient() for i in idxs}
        return [[QQ(ambient[i].inner_product(ambient[j])) for j in idxs] for i in idxs]

    def _translation_coefficient_radius(
        self,
        *,
        level: Any,
        linear_coeffs: List[Any],
        gram: List[List[Any]],
        max_neg_shift: Any,
    ) -> int:
        k = QQ(level)
        b = QQ(self._ceil_sqrt_qq(sum(QQ(d) * QQ(d) for d in linear_coeffs)))
        # Rigorous lower bound on lambda_min(gram):
        # lambda_min >= 1 / ||gram^{-1}||_2 >= 1 / ||gram^{-1}||_F.
        G = matrix(QQ, gram)
        G_inv = G.inverse()
        frob_sq = sum(QQ(v) * QQ(v) for v in G_inv.list())
        lam_lower = QQ(1) / QQ(self._ceil_sqrt_qq(frob_sq))

        if lam_lower <= 0:
            raise ValueError("Failed to obtain a positive coercive bound for translation enumeration")

        abs_k = abs(k)
        a = abs_k * lam_lower / QQ(2)
        if a <= 0:
            raise ValueError("Failed to derive a positive quadratic bound for translation enumeration")

        if k > 0:
            # If a r^2 - b r > max_neg_shift, then q(m) > max_neg_shift for ||m|| >= r.
            disc = b * b + QQ(4) * a * QQ(max_neg_shift)
            r_real = (b + QQ(self._ceil_sqrt_qq(disc))) / (QQ(2) * a)
            return max(0, int(r_real) + 1)

        # k < 0 case:
        # q(m) <= b r - a r^2, so q(m) < 0 for r > b/a.
        r_real = b / a
        return max(0, int(r_real) + 1)

    def _translations_by_n_shift_bnb(
        self,
        weight: "AffineWeight",
        *,
        order: int,
        max_neg_shift: Optional[Any] = None,
        return_stats: bool = False,
    ) -> Any:
        """备用枚举器：球约束 + 分支定界（不接入主流程）。"""
        semidirect = self.algebra.affine_weyl_group()
        idxs = [int(i) for i in semidirect._finite_coroot_space.index_set()]
        basis = semidirect._finite_coroot_space.simple_roots()

        if max_neg_shift is None:
            max_neg_shift_value = QQ(order) + QQ(weight.grade)
        else:
            max_neg_shift_value = QQ(max_neg_shift)
        if max_neg_shift_value < 0:
            return ({"translations": [], "stats": {}} if return_stats else [])

        level = QQ(weight.level)
        if level == 0:
            raise ValueError("Translation enumeration by n-shift requires non-zero level")

        linear_coeffs = [QQ(weight.dynkin_labels().get(i, 0)) for i in idxs]
        gram = self._finite_coroot_gram_matrix(idxs)
        radius = self._translation_coefficient_radius(
            level=level,
            linear_coeffs=linear_coeffs,
            gram=gram,
            max_neg_shift=max_neg_shift_value,
        )

        n = len(idxs)
        if n == 0:
            t0 = semidirect.translation(semidirect._zero_beta)
            return ({"translations": [t0], "stats": {"radius": 0}} if return_stats else [t0])

        # 椭球中心（连续极小点）用于分支顺序优化。
        center: list[QQ]
        try:
            G = matrix(QQ, gram)
            d_vec = vector(QQ, linear_coeffs)
            center_vec = -(G.solve_right(d_vec)) / level
            center = [QQ(center_vec[i]) for i in range(n)]
        except Exception:
            center = [QQ(0) for _ in range(n)]

        coeffs = [0 for _ in range(n)]
        selected: dict[tuple[int, ...], Any] = {}

        stats = {
            "radius": int(radius),
            "dimension": int(n),
            "box_points": int((2 * int(radius) + 1) ** int(n)),
            "visited_leaves": 0,
            "pruned_branches": 0,
            "accepted": 0,
        }

        def _partial_bounds(depth: int) -> tuple[Any, Any]:
            fixed = list(range(depth))
            rem = list(range(depth, n))

            const = QQ(0)
            for i in fixed:
                const += linear_coeffs[i] * QQ(coeffs[i])
            for i in fixed:
                for j in fixed:
                    const += level * QQ(gram[i][j]) * QQ(coeffs[i]) * QQ(coeffs[j]) / QQ(2)

            if not rem:
                return const, const

            b_rem: list[QQ] = []
            for i in rem:
                b_i = linear_coeffs[i]
                if fixed:
                    b_i += level * sum(QQ(gram[i][j]) * QQ(coeffs[j]) for j in fixed)
                b_rem.append(QQ(b_i))

            R = QQ(radius)
            lower = QQ(const)
            upper = QQ(const)

            for bi in b_rem:
                delta = abs(bi) * R
                lower -= delta
                upper += delta

            for a, i in enumerate(rem):
                qii = level * QQ(gram[i][i]) / QQ(2)
                term = qii * R * R
                if term >= 0:
                    upper += term
                else:
                    lower += term

                for b, j in enumerate(rem):
                    if b <= a:
                        continue
                    qij = level * QQ(gram[i][j])
                    band = abs(qij) * R * R
                    lower -= band
                    upper += band

            return lower, upper

        def _ordered_values(i: int) -> list[int]:
            vals = list(range(-radius, radius + 1))
            c = center[i]
            vals.sort(key=lambda x: (abs(QQ(x) - c), abs(x), x))
            return vals

        def _dfs(depth: int, prefix_norm_sq: int) -> None:
            if prefix_norm_sq > radius * radius:
                stats["pruned_branches"] += 1
                return

            low, high = _partial_bounds(depth)
            if high < 0 or low > max_neg_shift_value:
                stats["pruned_branches"] += 1
                return

            if depth == n:
                stats["visited_leaves"] += 1
                neg_shift = self._minus_Delta_n(
                    level=level,
                    linear_coeffs=linear_coeffs,
                    gram=gram,
                    coeffs=tuple(coeffs),
                )
                if QQ(0) <= neg_shift <= max_neg_shift_value:
                    beta = semidirect._zero_beta
                    for idx, c in zip(idxs, coeffs):
                        if c:
                            beta += int(c) * basis[idx]
                    key = tuple(int(c) for c in coeffs)
                    selected[key] = semidirect.translation(beta)
                    stats["accepted"] += 1
                return

            for value in _ordered_values(depth):
                coeffs[depth] = int(value)
                _dfs(depth + 1, prefix_norm_sq + int(value) * int(value))
            coeffs[depth] = 0

        _dfs(0, 0)
        out = [selected[key] for key in sorted(selected.keys())]
        if return_stats:
            return {"translations": out, "stats": stats}
        return out

    def _translation_neg_shift(self, weight: "AffineWeight", beta: Any) -> Any:
        translated = self.algebra.affine_weyl_group().translation(beta).action(weight)
        return weight.grade - translated.grade

    def _find_dominant_Lambda(
        self,
        lambda_hat: "AffineWeight",
        *,
        max_steps: int = 1000,
    ) -> Tuple["AffineWeight", Any]:
        rho_hat = self.algebra.affine_rho()
        weyl_group = self.kl.weyl_group
        current = lambda_hat + rho_hat
        current_w = weyl_group.one()
        visited: set[tuple[tuple[int, Any], ...]] = set()

        for _ in range(max_steps):
            labels = current.dynkin_labels()
            negative_nodes = [int(i) for i, value in labels.items() if value < 0]
            if not negative_nodes:
                return current - rho_hat, current_w

            state = tuple(sorted((int(i), labels[i]) for i in labels.keys())) + ((-1, current.grade),)
            if state in visited:
                break
            visited.add(state)

            node = min(negative_nodes)
            current = current.simple_reflection(node)
            current_w = weyl_group.simple_reflection(node) * current_w

        raise ValueError("Failed to find dominant Lambda via affine simple reflections")

    @staticmethod
    def _apply_element_to_weight(
        algebra: "AffineLieAlgebra", element: Any, weight: "AffineWeight"
    ) -> "AffineWeight":
        semidirect = algebra.affine_weyl_group()
        word = tuple(_element_word_list(element))
        return semidirect.from_word(word).action(weight)

    @classmethod
    def _collect_quotient_representatives(
        cls,
        algebra: "AffineLieAlgebra",
        Lambda_hat: "AffineWeight",
        *,
        candidates: Iterable[Any],
    ) -> List[Any]:
        rho_hat = algebra.affine_rho()
        by_weight: Dict[Tuple[Tuple[int, Any], ...], Any] = {}
        for w in candidates:
            image = cls._apply_element_to_weight(algebra, w, Lambda_hat + rho_hat) - rho_hat
            key = tuple(sorted(image.dynkin_labels().items())) + ((-1, image.grade),)
            current = by_weight.get(key)
            if current is None or int(w.length()) < int(current.length()):
                by_weight[key] = w
        return sorted(by_weight.values(), key=lambda w: (int(w.length()), tuple(_element_word_list(w))))

    def _build_W_affine_as_words_direct(
        self,
        normalized_translation_vectors: Iterable[Any],
    ) -> List[Any]:
        """Build KL Weyl elements directly from finite and translation words.

        For each translation vector ``beta`` and each finite Weyl element ``u``,
        construct the affine word as
        ``u.reduced_word() + translation_word_list(beta)`` and map it into
        ``self.kl.weyl_group`` via ``from_reduced_word``.
        """
        affine_weyl_group = self.algebra.affine_weyl_group()
        finite_elts_sorted = list(affine_weyl_group._finite_weyl_group)

        W_affine_as_words: Dict[Tuple[int, ...], Any] = {}
        for beta in normalized_translation_vectors:
            translation_word = tuple(int(i) for i in affine_weyl_group.translation_word_list(beta))
            for finite_element in finite_elts_sorted:
                finite_word = tuple(int(i) for i in finite_element.reduced_word())
                word = finite_word + translation_word
                W_affine_as_words[word] = self.kl.weyl_group.from_reduced_word(word)
        return list(W_affine_as_words.values())

    def _build_W_affine_as_words_via_semidirect(
        self,
        normalized_translations: Iterable[Any],
    ) -> List[Any]:
        """Legacy/reference builder through semidirect elements enumeration."""
        affine_weyl_group = self.algebra.affine_weyl_group()
        W_affine = affine_weyl_group.elements_as_semi_direct_product(
            translations=normalized_translations,
            factor_order="st",
        )
        W_affine_as_words: Dict[Tuple[int, ...], Any] = {}
        for element in W_affine:
            sage_element = element.reduced_word()
            word = tuple(int(i) for i in sage_element.reduced_word())
            if hasattr(sage_element, "parent") and sage_element.parent() == self.kl.weyl_group:
                W_affine_as_words[word] = sage_element
            else:
                W_affine_as_words[word] = self.kl.weyl_group.from_reduced_word(word)
        return list(W_affine_as_words.values())

    def prepare_data(
        self,
        lambda_hat: "AffineWeight",
        *,
        order: int,
        translations: Optional[Iterable[Any]] = None,
    ) -> KazhdanLusztigData:
        rho_hat = self.algebra.affine_rho()
        Lambda_hat, w_to_Lambda = self._find_dominant_Lambda(lambda_hat)
        w_to_lambda = w_to_Lambda.inverse()

        # Λ + ρ = w.λ should be deominant
        dominant_weight = Lambda_hat + rho_hat

        # ``translations`` accepts mixed explicit inputs (translation elements, coroot vectors,
        # or 0/None). Normalization happens in the affine Weyl group helper so the rest of the
        # pipeline always sees canonical coroot-space vectors.
        translation_inputs = list(translations) if translations is not None else None
        affine_weyl_group = self.algebra.affine_weyl_group()

        if translation_inputs is None:
            translation_order = order + max(
                0,
                int(QQ(dominant_weight.grade) - QQ(lambda_hat.grade)),
            )
            max_neg_shift = QQ(order) + QQ(dominant_weight.grade)
            translation_inputs = self._translations_by_n_shift(
                dominant_weight,
                order=translation_order,
                max_neg_shift=max_neg_shift,
            )

        normalized_translation_vectors = affine_weyl_group._translation_vectors_from_inputs(
            translations=translation_inputs,
        )

        if translations is None:
            # For auto-generated translation sets, prune vectors that cannot
            # contribute to grades <= order. Keep explicit user-provided
            # translation sets unchanged.
            pruned_translation_vectors: list[Any] = []
            for beta in normalized_translation_vectors:
                translated = affine_weyl_group.translation(beta).action(dominant_weight)
                resulting_grade = QQ(translated.grade) - QQ(rho_hat.grade)
                if resulting_grade >= -QQ(order):
                    pruned_translation_vectors.append(beta)
            normalized_translation_vectors = pruned_translation_vectors

        normalized_translations = [affine_weyl_group.translation(beta) for beta in normalized_translation_vectors]

        W_affine_as_words_sorted = self._build_W_affine_as_words_via_semidirect(
            normalized_translations,
        )
        # W_Λ^0
        stabilizer_candidates = self.kl.affine_stabilizer(
            Lambda_hat.to_sagemath(),
            rho_hat=rho_hat.to_sagemath(),
            candidates=W_affine_as_words_sorted,
            algebra=self.algebra,
        )
        # W_Λ/W_Λ^0
        quotient_representatives = self._collect_quotient_representatives(
            self.algebra,
            Lambda_hat,
            candidates=W_affine_as_words_sorted,
        )

        return KazhdanLusztigData(
            algebra=self.algebra,
            lambda_hat=lambda_hat,
            Lambda_hat=Lambda_hat,
            w_to_lambda=w_to_lambda,
            order=order,
            translations=normalized_translations,
            W_affine_as_words=W_affine_as_words_sorted,
            stabilizer_candidates=stabilizer_candidates,
            quotient_representatives=quotient_representatives,
        )

    def numerator_terms(
        self,
        lambda_hat: "AffineWeight",
        *,
        order: int,
        translations: Optional[Iterable[Any]] = None,
    ) -> list[Any]:
        context = self.prepare_data(
            lambda_hat,
            order=order,
            translations=translations,
        )
        terms: list[KLNumeratorTerm] = []
        lower = context.w_to_lambda
        for representative in context.weyl_to_be_summed():
            coefficient = self.kl.affine_bounded_parabolic_Q_tilde(
                lower,
                representative,
                candidates=context.W_affine_as_words,
                stabilizer_candidates=context.stabilizer_candidates,
                at_one=True,
            )
            if coefficient == 0:
                continue
            weight = context.quotient_weight(representative)
            terms.append(
                KLNumeratorTerm(
                    representative=representative,
                    weight=weight,
                    coefficient=coefficient,
                )
            )
        return terms

    def character(
        self,
        lambda_hat: "AffineWeight",
        *,
        order: int,
        translations: Optional[Iterable[Any]] = None,
    ) -> FormalCharacter:
        result = FormalCharacter({}, max_grade=order, algebra=self.algebra)
        for term in self.numerator_terms(
            lambda_hat,
            order=order,
            translations=translations,
        ):
            verma = VermaCharacter(self.algebra, term.weight)
            result = result + term.coefficient * verma.character(max_grade=order)
        return result.truncate(order)


def character_from_weight(
    algebra: "AffineLieAlgebra",
    weight: "AffineWeight",
    max_grade: int = 10,
) -> FormalCharacter:
    return VermaCharacter(algebra, weight).character(max_grade)
