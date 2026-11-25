import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Next-Generation ℓ₁ Quantization: Orthogonal Hadamard Incoherence, Asymmetric Scales, and Residual Cascades

* **Author:** E. S. Markov (ORCID: 0009-0005-2235-5464)
* **Affiliation:** Independent Researcher, Astrakhan, Russia
* **Repository:** https://github.com/fomamarkov-creator/l1-projection-complexity-lean4
* **License:** GNU Affero General Public License v3.0 (AGPLv3)
* **Toolchain:** Lean `v4.37.0-rc1` / Mathlib

## Overview
Formalizes three exact-rational (`ℚ`) mathematical extensions beyond symmetric blockwise 1.58-bit quantization:
1. **Exact Rational Walsh–Hadamard Incoherence (`hadamard4Q`):** Orthogonal `4×4` rotation over `ℚ`
   (normalized by `1/2`, avoiding irrational `√2`) preserving inner products (`hadamard4Q_dot_invariant`)
   and dispersing heavy-tailed channel outliers prior to quantization.
2. **Asymmetric 1.58-Bit Alphabet (`{-α_neg, 0, +α_pos}`):** Decoupled positive/negative threshold
   and scale optimization (`optimalPosScaleQ`, `optimalNegScaleQ`) with exact branch decomposition
   (`asymBlockErrorQ_split`).
3. **Two-Stage Residual Ternary Cascade (`quantizeResidual2StageQ`):** Recursive `ℓ₁` residual
   quantization `w ≈ wHat₁ + wHat₂` with machine-checked exact residual error identity
   (`residual_cascade_error_eq`).
-/

namespace MarkovL1NextGenQuantizer

/-- Конструктивный модуль над ℚ без `Classical.choice` -/
def absQ (x : ℚ) : ℚ :=
  if 0 ≤ x then x else -x

lemma absQ_eq_abs (x : ℚ) : absQ x = |x| := by
  unfold absQ
  split_ifs with h
  · exact (abs_of_nonneg h).symm
  · exact (abs_of_neg (lt_of_not_ge h)).symm

/-- Суммарная ℓ₁-ошибка на блоке между исходными и квантованными весами -/
def blockL1ErrorQ (ws wHats : List ℚ) : ℚ :=
  (List.zipWith (fun w wh => absQ (w - wh)) ws wHats).sum

-- =========================================================================
-- 1. ОРТОГОНАЛЬНОЕ ПРЕОБРАЗОВАНИЕ УОЛША–АДАМАРА H₄ НАД ТОЧНЫМИ ДРОБЯМИ ℚ
-- =========================================================================

/-- Нормированное 4×4 преобразование Уолша–Адамара над ℚ.
    Коэффициент 1/2 делает преобразование строго рациональным (без √2),
    подавляя выбросы весов в "хрупких" слоях перед квантованием. -/
def hadamard4Q (v : ℚ × ℚ × ℚ × ℚ) : ℚ × ℚ × ℚ × ℚ :=
  let (x₀, x₁, x₂, x₃) := v
  ( (x₀ + x₁ + x₂ + x₃) / 2,
    (x₀ - x₁ + x₂ - x₃) / 2,
    (x₀ + x₁ - x₂ - x₃) / 2,
    (x₀ - x₁ - x₂ + x₃) / 2 )

/-- Евклидово скалярное произведение в ℝ⁴ / ℚ⁴ -/
def dot4Q (u v : ℚ × ℚ × ℚ × ℚ) : ℚ :=
  u.1 * v.1 + u.2.1 * v.2.1 + u.2.2.1 * v.2.2.1 + u.2.2.2 * v.2.2.2

/-- Теорема 1.1 (Инволютивность H₄): H₄(H₄(v)) = v без накопления ошибок округления -/
theorem hadamard4Q_involutive (v : ℚ × ℚ × ℚ × ℚ) :
    hadamard4Q (hadamard4Q v) = v := by
  rcases v with ⟨x₀, x₁, x₂, x₃⟩
  dsimp [hadamard4Q]
  ext <;> ring

/-- Теорема 1.2 (Сохранение скалярного произведения и линейного слоя):
    (H₄ w) · (H₄ x) = w · x. Вращение базиса весов и активаций не меняет выход слоя. -/
theorem hadamard4Q_dot_invariant (w x : ℚ × ℚ × ℚ × ℚ) :
    dot4Q (hadamard4Q w) (hadamard4Q x) = dot4Q w x := by
  rcases w with ⟨w₀, w₁, w₂, w₃⟩
  rcases x with ⟨x₀, x₁, x₂, x₃⟩
  dsimp [hadamard4Q, dot4Q]
  ring

-- =========================================================================
-- 2. АСИММЕТРИЧНЫЙ 1.58-БИТНЫЙ КВАНТОВАТЕЛЬ {-α_neg, 0, +α_pos}
-- =========================================================================

def insertRat (x : ℚ) : List ℚ → List ℚ
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertRat x ys

def sortRat : List ℚ → List ℚ
  | [] => []
  | x :: xs => insertRat x (sortRat xs)

def exactMedianQ (xs : List ℚ) : ℚ :=
  let s := sortRat xs
  s.getD (s.length / 2) 0

/-- Асимметричный скалярный оператор квантования с независимыми порогами (θ_neg, θ_pos)
    и раздельными масштабами (α_neg, α_pos) для отрицательной и положительной полуосей -/
def quantizeAsymScalarQ (θ_neg θ_pos α_neg α_pos w : ℚ) : ℚ :=
  if 0 ≤ w then
    if w ≤ θ_pos then 0 else α_pos
  else
    if -w ≤ θ_neg then 0 else -α_neg

/-- Оптимальный положительный масштаб: медиана активных положительных весов (w > θ_pos) -/
def optimalPosScaleQ (θ_pos : ℚ) (ws : List ℚ) : ℚ :=
  let posActive := ws.filter (fun w => decide (θ_pos < w))
  exactMedianQ posActive

/-- Оптимальный отрицательный масштаб: медиана модулей активных отрицательных весов (w < -θ_neg) -/
def optimalNegScaleQ (θ_neg : ℚ) (ws : List ℚ) : ℚ :=
  let negActive := (ws.filter (fun w => decide (w < -θ_neg))).map (fun w => -w)
  exactMedianQ negActive

/-- Полная ℓ₁-ошибка асимметричного тернарного квантования на блоке -/
def asymBlockErrorQ (θ_neg θ_pos α_neg α_pos : ℚ) (ws : List ℚ) : ℚ :=
  (ws.map (fun w => absQ (w - quantizeAsymScalarQ θ_neg θ_pos α_neg α_pos w))).sum

/-- Теорема 2.1 (Декомпозиция асимметричной ℓ₁-ошибки):
    оптимизация (θ_neg, α_neg) и (θ_pos, α_pos) полностью расщепляется на две
    независимые одномерные задачи по положительной и отрицательной ветвям весов. -/
theorem asymBlockErrorQ_split (θ_neg θ_pos α_neg α_pos : ℚ) (ws : List ℚ) :
    asymBlockErrorQ θ_neg θ_pos α_neg α_pos ws =
      ((ws.filter (fun w => decide (0 ≤ w))).map (fun w => absQ (w - if w ≤ θ_pos then 0 else α_pos))).sum +
      ((ws.filter (fun w => decide (w < 0))).map (fun w => absQ (w - if -w ≤ θ_neg then 0 else -α_neg))).sum := by
  induction ws with
  | nil => simp [asymBlockErrorQ]
  | cons w rest ih =>
      unfold asymBlockErrorQ at ih ⊢
      simp only [List.map_cons, List.sum_cons, ih]
      by_cases hw : 0 ≤ w
      · have hnot : ¬ (w < 0) := not_lt.mpr hw
        simp only [List.filter_cons, decide_eq_true hw, decide_eq_false hnot,
          Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]
        simp only [quantizeAsymScalarQ, hw, ↓reduceIte]
        ring
      · have hlt : w < 0 := lt_of_not_ge hw
        simp only [List.filter_cons, decide_eq_false hw, decide_eq_true hlt,
          Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]
        simp only [quantizeAsymScalarQ, hw, ↓reduceIte]
        ring
-- =========================================================================
-- 3. ДВУХСТУПЕНЧАТОЕ ОСТАТОЧНОЕ ℓ₁-КВАНТОВАНИЕ (W ≈ α₁ T₁ + α₂ T₂)
-- =========================================================================

/-- Базовый симметричный 1.58-bit квантователь одного каскада -/
def quantizeSymScalarQ (θ α w : ℚ) : ℚ :=
  if absQ w ≤ θ then 0 else if 0 ≤ w then α else -α

/-- Медианный масштаб активных элементов одного каскада -/
def symOptimalScaleQ (θ : ℚ) (ws : List ℚ) : ℚ :=
  let active := (ws.filter (fun w => decide (θ < absQ w))).map absQ
  exactMedianQ active

/-- Блочная ℓ₁-ошибка одного каскада -/
def symBlockErrorQ (θ α : ℚ) (ws : List ℚ) : ℚ :=
  (ws.map (fun w => absQ (w - quantizeSymScalarQ θ α w))).sum

/-- Точный поиск оптимальной пары (θ*, α*) по критическим порядковым статистикам -/
def selectBestSymQ (ws : List ℚ) : List ℚ → ℚ × ℚ
  | [] => (0, symOptimalScaleQ 0 ws)
  | [θ] => (θ, symOptimalScaleQ θ ws)
  | θ :: rest =>
      let α := symOptimalScaleQ θ ws
      let (θ_b, α_b) := selectBestSymQ ws rest
      if symBlockErrorQ θ α ws ≤ symBlockErrorQ θ_b α_b ws then (θ, α) else (θ_b, α_b)

/-- Выполнение одного полного каскада 1.58-bit квантования -/
def quantizeLayer1Q (ws : List ℚ) : ℚ × ℚ × List ℚ :=
  let cands := 0 :: ws.map absQ
  let (θ₁, α₁) := selectBestSymQ ws cands
  let wHat₁ := ws.map (quantizeSymScalarQ θ₁ α₁)
  (θ₁, α₁, wHat₁)

/-- Двухступенчатый остаточный квантователь (3.16 бита на вес без умножений):
    1) Находит оптимальный первый слой wHat₁ = α₁ * T₁;
    2) Вычисляет точный остаток r = w - wHat₁ и находит второй слой wHat₂ = α₂ * T₂;
    3) Возвращает сумму wHatTotal = wHat₁ + wHat₂, ошибку 1-го шага и ошибку 2-го шага. -/
def quantizeResidual2StageQ (ws : List ℚ) : List ℚ × ℚ × ℚ :=
  let (θ₁, α₁, wHat₁) := quantizeLayer1Q ws
  let err₁ := symBlockErrorQ θ₁ α₁ ws
  let residual := List.zipWith (fun w wh => w - wh) ws wHat₁
  let (_, _, wHat₂) := quantizeLayer1Q residual
  let wHatTotal := List.zipWith (· + ·) wHat₁ wHat₂
  let err₂ := blockL1ErrorQ ws wHatTotal
  (wHatTotal, err₁, err₂)

/-- Вспомогательная лемма: точечная ошибка суммы двух слоёв равна ошибке приближения остатка -/
lemma residual_point_error_eq (w wh₁ wh₂ : ℚ) :
    absQ (w - (wh₁ + wh₂)) = absQ ((w - wh₁) - wh₂) := by
  congr 1
  ring

/-- Теорема 3.1 (Точное тождество остаточного каскада):
    полная ℓ₁-ошибка двухступенчатого приближения w ≈ wHat₁ + wHat₂
    тождественно равна ℓ₁-ошибке квантования остатка r = w - wHat₁ вторым слоем wHat₂. -/
theorem residual_cascade_error_eq :
    ∀ (ws wHat₁ wHat₂ : List ℚ),
      blockL1ErrorQ ws (List.zipWith (· + ·) wHat₁ wHat₂) =
      blockL1ErrorQ (List.zipWith (fun w wh => w - wh) ws wHat₁) wHat₂
  | [], _, _ => by simp [blockL1ErrorQ]
  | _ :: _, [], _ => by simp [blockL1ErrorQ]
  | _ :: _, _ :: _, [] => by simp [blockL1ErrorQ]
  | w :: ws, wh₁ :: wh₁s, wh₂ :: wh₂s => by
      have ih := residual_cascade_error_eq ws wh₁s wh₂s
      unfold blockL1ErrorQ at ih ⊢
      simp only [List.zipWith_cons_cons, List.sum_cons, ih, residual_point_error_eq]

-- =========================================================================
-- ИСПОЛНЯЕМЫЕ ТЕСТЫ (#eval) И АУДИТ АКСИОМ (#print axioms)
-- =========================================================================

-- Тест 1: Подавление одиночного выброса (100, 0, 0, 0) преобразованием Адамара H₄
#eval
  let outlierVec : ℚ × ℚ × ℚ × ℚ := (100/1, 0/1, 0/1, 0/1)
  let rotated := hadamard4Q outlierVec
  let restored := hadamard4Q rotated
  s!"[Hadamard H4 Incoherence] outlier={outlierVec} -> rotated={rotated} -> restored={restored}"

-- Тест 2: Двухступенчатое остаточное квантование (снижение ошибки 18.2 -> 6.2)
#eval
  let ws : List ℚ := [1/10, -1/10, 4/1, -4/1, 10/1, 20/1]
  let (wHatTotal, err1, err2) := quantizeResidual2StageQ ws
  s!"[2-Stage Residual Cascade] stage1_err={err1} -> stage2_err={err2} (wHat={wHatTotal})"

end MarkovL1NextGenQuantizer

#print axioms MarkovL1NextGenQuantizer.hadamard4Q
#print axioms MarkovL1NextGenQuantizer.optimalPosScaleQ
#print axioms MarkovL1NextGenQuantizer.optimalNegScaleQ
#print axioms MarkovL1NextGenQuantizer.quantizeResidual2StageQ

#print axioms MarkovL1NextGenQuantizer.hadamard4Q_involutive
#print axioms MarkovL1NextGenQuantizer.hadamard4Q_dot_invariant
#print axioms MarkovL1NextGenQuantizer.asymBlockErrorQ_split
#print axioms MarkovL1NextGenQuantizer.residual_cascade_error_eq
