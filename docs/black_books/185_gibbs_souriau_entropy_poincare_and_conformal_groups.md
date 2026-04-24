# 185. Gibbs-Souriau Entropy for Poincare and Conformal Groups

Rewrite artifact: [186_souriau_fisher_onsager_operatorial_formalization.tex](../rewritten_artifacts/latex/operatorial_lane/186_souriau_fisher_onsager_operatorial_formalization.tex)

Lean corridor: `SouriauTheoremTranslatorPacket` -> `SouriauCoadjointOrbitMetriplecticTheorem` -> `OperatorialHessianBridge` / `OnsagerReciprocity` / `SouriauKreinMetriplecticContext`.

Boundary note:

- this chapter is an intake/shadow chapter, not an owner theorem surface;
- the trunk correction is recorded in [187_noncommutative_ownerhood_and_the_shadow_status_of_scalars.md](187_noncommutative_ownerhood_and_the_shadow_status_of_scalars.md);
- the operatorial two-tier owner/shadow split is developed in [156_the_operatorial_free_energy_and_type_iii_surprisal.md](156_the_operatorial_free_energy_and_type_iii_surprisal.md).

Да. Най-полезно би било да се разгледа първо **Gibbs-Souriau ентропията за групата на Поанкаре**, защото там геометричната интерпретация е най-чиста:

\[
p_\beta(\xi)=\frac{1}{Z(\beta)} e^{-\langle J(\xi),\beta\rangle},
\qquad
Z(\beta)=\int_M e^{-\langle J(\xi),\beta\rangle}\,d\lambda(\xi)
\]

където:

- \(J:M\to\mathfrak g^*\) е моментното изображение;
- \(\beta\in\mathfrak g\) е геометричната температура;
- \(\langle J,\beta\rangle\) замества класическия Хамилтониан;
- \(Z(\beta)\) е обобщената статистическа сума;
- ентропията е

\[
S(\beta)=\log Z(\beta)-\langle Q(\beta),\beta\rangle
\]

със среден момент

\[
Q(\beta)=\frac{\partial \log Z}{\partial \beta}\in\mathfrak g^*.
\]

За групата на Поанкаре \(\mathfrak g\) съдържа транслации и Лоренцови генератори, така че \(\beta\) не е само обратна температура, а включва и движение/въртене на равновесното състояние. Това води до релативистка термодинамика, където равновесието е зададено от вектор в алгебрата на Ли.

За конформната група случаят е по-богат, но и по-деликатен: условието \(Z(\beta)<\infty\) вече силно зависи от това дали \(\beta\) лежи в подходящ положителен конус. Там връзката с weights, Weyl scaling и KKT ограниченията става естествена.

Ако целта е формализация в Lean, бих започнал с абстрактната схема:

\[
\mathfrak g,\quad \mathfrak g^*,\quad J,\quad \beta,\quad Z,\quad Q,\quad S
\]

и чак след това бих специализирал към Поанкаре или конформната алгебра.

Но след doctrinal correction-та на Chapter 187 това трябва да се чете внимателно:

- абстрактната схема е легитимна като scalar/coadjoint shadow;
- тя не бива да се обърква с owner surface на теорията;
- owner lane остава noncommutative, coordinate-free, dim-agnostic operator transport;
- групите на Поанкаре и Conformal служат тук като богати representation shadows, а не като задължителен ambient geometric origin на термодинамиката.

Затова този chapter трябва да се използва като corridor-finder към:

1. `SouriauCoadjointOrbitMetriplecticTheorem` за dimension-agnostic theorem interface;
2. `CertifiedModularReduction` / `OperatorialHessianBridge` / `OnsagerReciprocity` за operatorial owner lane;
3. `SouriauFenchelOnsagerBridge` само като finite/scalar translator surface.
