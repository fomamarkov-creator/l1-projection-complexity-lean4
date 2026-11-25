import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# MarkovL1TernaryQuantizer.lean

* **Author:** E. S. Markov (ORCID: 0009-0005-2235-5464)
* **Affiliation:** Independent Researcher, Astrakhan, Russia
* **Repository:** https://github.com/fomamarkov-creator/l1-projection-complexity-lean4
* **License:** GNU Affero General Public License v3.0 (AGPLv3)
* **Toolchain:** Lean `v4.37.0-rc1` / Mathlib

## Overview
# Certified 1.58-Bit Ternary Neural Network Quantizer ({-1, 0, +1} over ℚ)
-/


namespace MarkovL1TernaryQuantizer

/-- 1.58-bit тернарное квантование скаляра w ∈ ℚ при пороге θ ≥ 0 и масштабе α ≥ 0:
    если |w| ≤ θ, возвращает 0; иначе sgn(w) * α. -/
def quantizeScalarQ (θ α w : ℚ) : ℚ :=
  if |w| ≤ θ then 0
  else if 0 ≤ w then α else -α

/-- Точечная ℓ₁-ошибка тернарного квантования -/
def pointErrorQ (θ α w : ℚ) : ℚ :=

  |w - quantizeScalarQ θ α w|

/-- Полная ℓ₁-ошибка тернарного квантования на блоке весов w : List ℚ -/
def blockErrorQ (θ α : ℚ) (ws : List ℚ) : ℚ :=
  (ws.map (pointErrorQ θ α)).sum

/-- Теорема 1 (Разложение точечной ℓ₁-ошибки для 0 ≤ α):
    если |w| ≤ θ, ошибка равна |w|; если |w| > θ, ошибка равна |(|w| - α)|. -/
theorem pointErrorQ_eq_split {θ α w : ℚ} (_hα : 0 ≤ α) :
    pointErrorQ θ α w = if |w| ≤ θ then |w| else |(|w| - α)| := by
  unfold pointErrorQ quantizeScalarQ
  split_ifs with hθ hw
  · simp
  · have habs : |w| = w := abs_of_nonneg hw
    rw [habs]
  · have hlt : w < 0 := lt_of_not_ge hw
    have habs : |w| = -w := abs_of_neg hlt
    rw [habs, ← abs_neg (w - -α)]
    congr 1
    ring

/-- Теорема 2 (Инвариантность ошибки на интервалах между порядковыми статистиками):
    если ни один элемент блока не лежит в полуинтервале (θ₁, θ₂],
    то L1-ошибка на всём блоке идентична для θ₁ и θ₂ при любом α. -/
theorem blockErrorQ_const_on_gap {θ₁ θ₂ α : ℚ} (h12 : θ₁ ≤ θ₂) (ws : List ℚ)
    (hgap : ∀ w ∈ ws, ¬ (θ₁ < |w| ∧ |w| ≤ θ₂)) :
    blockErrorQ θ₁ α ws = blockErrorQ θ₂ α ws := by
  unfold blockErrorQ
  congr 1
  apply List.map_congr_left
  intro w hw
  unfold pointErrorQ quantizeScalarQ
  have hnot := hgap w hw
  by_cases h1 : |w| ≤ θ₁
  · have h2 : |w| ≤ θ₂ := le_trans h1 h12
    simp [h1, h2]
  · have hgt1 : θ₁ < |w| := lt_of_not_ge h1
    have h2 : ¬ (|w| ≤ θ₂) := fun hle => hnot ⟨hgt1, hle⟩
    simp [h1, h2]

/-- Вспомогательная сортировка вставками для конструктивного вычисления медианы без аксиом выбора -/
def insertRat (x : ℚ) : List ℚ → List ℚ
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertRat x ys

def sortRat : List ℚ → List ℚ
  | [] => []
  | x :: xs => insertRat x (sortRat xs)

/-- Точная медиана непустого списка рациональных чисел (0 для пустого списка) -/
def exactMedianQ (xs : List ℚ) : ℚ :=
  let s := sortRat xs
  s.getD (s.length / 2) 0

/-- Вычисление оптимального масштаба α*(θ) как медианы модулей активных весов (|w| > θ) -/
def optimalScaleForThresholdQ (θ : ℚ) (ws : List ℚ) : ℚ :=
  let active := (ws.filter (fun w => decide (θ < |w|))).map (fun w => |w|)
  exactMedianQ active

/-- Конечное множество критических порогов: {0} ∪ {|w| : w ∈ ws} -/
def criticalThresholdsQ (ws : List ℚ) : List ℚ :=
  0 :: ws.map (fun w => |w|)

/-- Выбор пары (θ*, α*) с минимальной ℓ₁-ошибкой среди списка кандидатов -/
def selectBestPairQ (ws : List ℚ) : List ℚ → ℚ × ℚ
  | [] => (0, optimalScaleForThresholdQ 0 ws)
  | [θ] => (θ, optimalScaleForThresholdQ θ ws)
  | θ :: rest =>
      let α := optimalScaleForThresholdQ θ ws
      let (θ_best, α_best) := selectBestPairQ ws rest
      if blockErrorQ θ α ws ≤ blockErrorQ θ_best α_best ws then (θ, α) else (θ_best, α_best)

/-- Точный полиномиальный 1.58-bit квантователь блока над ℚ -/
def quantizeTernaryExactQ (ws : List ℚ) : ℚ × ℚ :=
  selectBestPairQ ws (criticalThresholdsQ ws)

/-- Теорема 3 (Формальный сертификат оптимальности среди всех критических порогов) -/
theorem selectBestPairQ_le_mem (ws : List ℚ) :
    ∀ cs θ, θ ∈ cs →
      let (θ_best, α_best) := selectBestPairQ ws cs
      blockErrorQ θ_best α_best ws ≤ blockErrorQ θ (optimalScaleForThresholdQ θ ws) ws
  | [], _, h => by simp at h
  | [θ₀], θ, h => by
      simp at h
      subst h
      simp [selectBestPairQ]
  | θ₀ :: θ₁ :: rest, θ, h => by
      simp only [selectBestPairQ]
      split_ifs with hle
      · rcases List.mem_cons.mp h with rfl | hmem
        · exact le_refl _
        · have ih := selectBestPairQ_le_mem ws (θ₁ :: rest) θ hmem
          exact le_trans hle ih
      · have hgt : blockErrorQ (selectBestPairQ ws (θ₁ :: rest)).1 (selectBestPairQ ws (θ₁ :: rest)).2 ws <
                   blockErrorQ θ₀ (optimalScaleForThresholdQ θ₀ ws) ws := lt_of_not_ge hle
        rcases List.mem_cons.mp h with rfl | hmem
        · exact le_of_lt hgt
        · exact selectBestPairQ_le_mem ws (θ₁ :: rest) θ hmem

theorem quantizeTernaryExactQ_certified_optimal (ws : List ℚ) (θ : ℚ)
    (hθ : θ ∈ criticalThresholdsQ ws) :
    let (θ_star, α_star) := quantizeTernaryExactQ ws
    blockErrorQ θ_star α_star ws ≤ blockErrorQ θ (optimalScaleForThresholdQ θ ws) ws :=
  selectBestPairQ_le_mem ws (criticalThresholdsQ ws) θ hθ

-- Вычислимый тест
#eval quantizeTernaryExactQ [1/10, -1/10, 4, -4, 4, 20]

end MarkovL1TernaryQuantizer
