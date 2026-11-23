[![Lean Action CI](../../actions/workflows/lean_action_ci.yml/badge.svg)](../../actions/workflows/lean_action_ci.yml)

**Toolchain:** Lean `v4.37.0-rc1` | **Verified Theorems:** 26 | **Sorry count:** 0 | **License:** AGPL-3.0

# Combinatorial Complexity Phase Transitions of $\ell_1$ Metric Projection Null Layers

Формальная верификация в **Lean 4** и сертифицированные решатели для нулевых слоев $P_V^{-1}(0)$ многозначных метрических проекций в $\ell_1^m$.

* **Автор:** E. S. Markov | **Независимый исследователь**
* **Лицензия:** AGPLv3

---

## Структура репозитория

1. **`MarkovL1Complexity.lean`** *(Основная теория — 21 теорема, `0 sorry`)*
   * **Биполярная двойственность:** Характеристика векторов $u \in \{-1, 1\}^m$ в $P_V^{-1}(0)$ через ортогональность.
   * **NP-полнота:** Сведения из `Subset-Sum`, `Partition` и `3-SAT`.
   * **Полиномиальная разрешимость ($\Delta = 1$):** Блочная медианная декомпозиция и $O(m)$ дипольные селекторы.
   * **Фазовые переходы:** Расширение слоев, жесткость распространения знаков и экспоненциальные барьеры.

2. **`MarkovL1Solver.lean`** и **`MarkovL1WeightedSolver.lean`** *(Сертифицированные решатели в $\mathbb{Q}$)*
   * Вычислимые алгоритмы полиномиальной сложности для дипольных и блочных медианных проекций с формальными доказательствами корректности и тестами `#eval`.

---

## Сборка

```bash
lake exe cache get
lake build
```
