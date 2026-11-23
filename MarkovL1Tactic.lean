import MarkovL1Complexity
import MarkovL1Solver
import MarkovL1WeightedSolver

/-!
# Proof-by-Reflection Tactics for ℓ₁ Metric Projection Null Layers (`l1_zero_layer`)

* **Author:** E. S. Markov (ORCID: 0009-0005-2235-5464)
* **License:** GNU Affero General Public License v3.0 (AGPLv3)
* **Toolchain:** Lean `v4.37.0-rc1` / Mathlib

## Overview
Automated decision-procedure tactics turning the verified checkers from `MarkovL1Solver`
and `MarkovL1WeightedSolver` into one-line proof automation:
1. `l1_bipolar_cert`: Closes goals of the form
   `InL1ZeroLayer (MultiSpan (fun j i => (A j i : ℝ))) (embedQ u)` via computational reflection.
2. `l1_block_cert`: Closes goals of the form
   `InL1ZeroLayer (buildDisjointSubspace supp h_disj).mem (embedQ r)` for arbitrary disjoint
   block partitions (Δ = 1) via sign-balance reflection.
3. `l1_zero_layer`: Unified front-end tactic dispatching automatically between bipolar
   orthogonal systems and decoupled block projections.
-/

open Finset BigOperators

namespace MarkovL1Tactic

open MarkovL1Complexity
open MarkovL1Solver
open MarkovL1WeightedSolver

/-- Мост рефлексии для блочной сбалансированности: сводит аналитическое условие
    `InL1ZeroLayer (buildDisjointSubspace supp h_disj).mem (embedQ r)`
    к вычислимому булеву предикату `checkBlocksBalancedQ supp r = true` -/
theorem mem_disjoint_zero_layer_of_checkBlocksBalancedQ {m k : ℕ}
    (supp : Fin k → Fin m → Bool) (h_disj : checkDisjointSupports supp = true)
    (r : Fin m → ℚ) (h_bal : checkBlocksBalancedQ supp r = true) :
    InL1ZeroLayer (buildDisjointSubspace supp h_disj).mem (embedQ r) := by
  apply polynomial_zero_layer_of_block_balanced (buildDisjointSubspace supp h_disj) (embedQ r)
  intro b
  dsimp [buildDisjointSubspace]
  dsimp [checkBlocksBalancedQ] at h_bal
  rw [List.all_eq_true] at h_bal
  have hb := h_bal b (List.mem_finRange b)
  simp only [decide_eq_true_eq, Bool.and_eq_true] at hb
  obtain ⟨h_neg_len, h_pos_len⟩ := hb
  apply isBlockBalanced_of_balanced_counts
  · have h1 : ((List.finRange m).filter (fun i => supp b i && decide (r i < 0))).length ≤
              ((List.finRange m).filter (fun i => supp b i && decide (0 ≤ r i))).length := by
      simpa [List.filter_filter, Bool.and_comm] using h_neg_len
    rw [length_filter_finRange_eq_card, length_filter_finRange_eq_card] at h1
    convert h1 using 2 <;> (ext i; simp [embedQ])
  · have h2 : ((List.finRange m).filter (fun i => supp b i && decide (0 < r i))).length ≤
              ((List.finRange m).filter (fun i => supp b i && decide (r i ≤ 0))).length := by
      simpa [List.filter_filter, Bool.and_comm] using h_pos_len
    rw [length_filter_finRange_eq_card, length_filter_finRange_eq_card] at h2
    convert h2 using 2 <;> (ext i; simp [embedQ])

/-- Специализированная тактика для многомерных систем `MultiSpan`:
    автоматически доказывает принадлежность биполярного вектора нулевому слою -/
macro "l1_bipolar_cert" : tactic =>
  `(tactic| (apply checkBipolarZeroLayerQ_sound; native_decide))

/-- Специализированная тактика для развязанных блочных подпространств (`Δ = 1`):
    автоматически проверяет сбалансированность всех блоков через компилируемую рефлексию -/
macro "l1_block_cert" : tactic =>
  `(tactic| (apply mem_disjoint_zero_layer_of_checkBlocksBalancedQ; native_decide))

/-- Универсальная тактика `l1_zero_layer`: автоматически выбирает подходящий сертификат
    и закрывает цель целиком через `solve` -/
macro "l1_zero_layer" : tactic =>
  `(tactic| solve | l1_bipolar_cert | l1_block_cert)

-- =========================================================================
-- ДЕМОНСТРАЦИОННЫЕ ТЕОРЕМЫ (ДОКАЗЫВАЮТСЯ В ОДНУ СТРОЧКУ `by l1_zero_layer`)
-- =========================================================================

section DemoProofs

/-- Пример 1: 6-мерная многомерная система из 3 линейных ограничений.
    Принадлежность биполярного вектора u = (1, -1, 1, -1, 1, -1) нулевому слою
    доказывается полностью автоматически в одну строчку. -/
def demoMatrix6 : Fin 3 → Fin 6 → ℚ
  | ⟨0, _⟩, ⟨0, _⟩ => 1
  | ⟨0, _⟩, ⟨1, _⟩ => 1
  | ⟨0, _⟩, ⟨2, _⟩ => 0
  | ⟨0, _⟩, ⟨3, _⟩ => 0
  | ⟨0, _⟩, ⟨4, _⟩ => 2
  | ⟨0, _⟩, ⟨5, _⟩ => 2
  | ⟨1, _⟩, ⟨0, _⟩ => 3
  | ⟨1, _⟩, ⟨1, _⟩ => 1
  | ⟨1, _⟩, ⟨2, _⟩ => -2
  | ⟨1, _⟩, ⟨3, _⟩ => 0
  | ⟨1, _⟩, ⟨4, _⟩ => 0
  | ⟨1, _⟩, ⟨5, _⟩ => 0
  | ⟨2, _⟩, ⟨0, _⟩ => 1
  | ⟨2, _⟩, ⟨1, _⟩ => 1
  | ⟨2, _⟩, ⟨2, _⟩ => 1
  | ⟨2, _⟩, ⟨3, _⟩ => 1
  | ⟨2, _⟩, ⟨4, _⟩ => 1
  | ⟨2, _⟩, ⟨5, _⟩ => 1

def demoVec6 : Fin 6 → ℚ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => -1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => -1
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => -1

theorem demo_multidimensional_orth_auto :
    InL1ZeroLayer (MultiSpan (fun j i => (demoMatrix6 j i : ℝ))) (embedQ demoVec6) := by
  l1_zero_layer

/-- Пример 2: 8-мерное пространство с двумя разноразмерными блоками ({0,1,2} и {3,4,5,6,7}).
    Оптимальность найденного медианного остатка доказывается в одну строчку. -/
theorem demo_disjoint_blocks_auto :
    InL1ZeroLayer
      (buildDisjointSubspace generalBlockSupp (by decide)).mem
      (embedQ (fun i => generalInput i -
        ∑ b : Fin 2, if generalBlockSupp b i then computeBlockMedianQ (generalBlockSupp b) generalInput else 0)) := by
  l1_zero_layer

end DemoProofs

end MarkovL1Tactic

-- Проверка аксиом автоматически доказанных теорем:
#print axioms MarkovL1Tactic.demo_multidimensional_orth_auto
#print axioms MarkovL1Tactic.demo_disjoint_blocks_auto
