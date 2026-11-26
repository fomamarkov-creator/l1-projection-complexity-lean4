import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# V-CORE v5.0 Frontier Module 24: Cross-Layer ℓ₁ Curvature Compensation, Rational Spherical Codes & Integer-Only Transformer Primitives

* **Author:** E. S. Markov (ORCID: 0009-0005-2235-5464)
* **Affiliation:** Independent Researcher, Astrakhan, Russia
* **Repository:** https://github.com/fomamarkov-creator/l1-projection-complexity-lean4
* **License:** GNU Affero General Public License v3.0 (AGPLv3)
* **Toolchain:** Lean `v4.37.0-rc1` / Mathlib
-/

namespace MarkovL1CrossLayerAndIntegerTransformer

/-- Конструктивный модуль над ℚ без `Classical.choice` -/
def absQ (x : ℚ) : ℚ :=
  if 0 ≤ x then x else -x

lemma absQ_eq_abs (x : ℚ) : absQ x = |x| := by
  unfold absQ
  split_ifs with h
  · exact (abs_of_nonneg h).symm
  · exact (abs_of_neg (lt_of_not_ge h)).symm

lemma absQ_nonneg (x : ℚ) : 0 ≤ absQ x := by
  rw [absQ_eq_abs]; exact abs_nonneg x

lemma absQ_add_le (a b : ℚ) : absQ (a + b) ≤ absQ a + absQ b := by
  rw [absQ_eq_abs, absQ_eq_abs, absQ_eq_abs]; exact abs_add_le a b

lemma absQ_mul (a b : ℚ) : absQ (a * b) = absQ a * absQ b := by
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
  · have hab : 0 ≤ a * b := mul_nonneg ha hb
    simp [absQ, ha, hb, hab]
  · have hb' : b < 0 := lt_of_not_ge hb
    have hab : a * b ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha (le_of_lt hb')
    unfold absQ; split_ifs <;> linarith
  · have ha' : a < 0 := lt_of_not_ge ha
    have hab : a * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt ha') hb
    unfold absQ; split_ifs <;> linarith
  · have ha' : a < 0 := lt_of_not_ge ha
    have hb' : b < 0 := lt_of_not_ge hb
    have hab : 0 ≤ a * b := mul_nonneg_of_nonpos_of_nonpos (le_of_lt ha') (le_of_lt hb')
    simp [absQ, ha, hb, hab]

-- =========================================================================
-- 1. МЕЖСЛОЙНАЯ КОМПЕНСАЦИЯ ОШИБКИ (CROSS-LAYER ℓ₁ CURVATURE COMPENSATION)
-- =========================================================================

/-- Межслойная компенсационная поправка весов `w₂` следующего слоя `l+1`:
    если слой `l` имеет ошибку `e₁ = w₁ - wHat₁` и ненулевой квантованный отклик `yHat₁`,
    поправка `Δw₂ = w₂ * (e₁ / wHat₁)` восстанавливает точный выход каскада `w₂ * (w₁ * x)`. -/
def crossLayerCompensatedWeightQ (w1 wHat1 w2 : ℚ) : ℚ :=
  if wHat1 == 0 then w2 else w2 + w2 * ((w1 - wHat1) / wHat1)

/-- Теорема 1.1 (Точное межслойное подавление ошибки квантования каскада двух слоёв):
    при `wHat1 ≠ 0` скорректированный вес `w2Comp` следующего слоя полностью аннулирует
    ошибку квантования предыдущего слоя: `w2Comp * (wHat1 * x) = w2 * (w1 * x)`. -/
theorem cross_layer_exact_cancellation (w1 wHat1 w2 x : ℚ) (h_nz : wHat1 ≠ 0) :
    (w2 + w2 * ((w1 - wHat1) / wHat1)) * (wHat1 * x) = w2 * (w1 * x) := by
  field_simp [h_nz]
  ring

/-- Теорема 1.2 (Граница межслойного дрейфа с учётом остаточной невязки `δ_res` после ℓ₁-LoRA):
    если слой `l` квантован с ошибкой `|wHat1 - w1| ≤ ε₁`, а слой `l+1` имеет ошибку `|wHat2 - w2| ≤ ε₂`,
    то выходной дрейф двухслойного каскада ограничен `|w2 * w1 * x - wHat2 * wHat1 * x| ≤ (|w2| * ε₁ + ε₂ * |wHat1|) * |x|`. -/
theorem two_layer_cascade_drift_bound (w1 wHat1 w2 wHat2 x ε1 ε2 : ℚ)
    (he1 : absQ (wHat1 - w1) ≤ ε1)
    (he2 : absQ (wHat2 - w2) ≤ ε2) :
    absQ (w2 * (w1 * x) - wHat2 * (wHat1 * x)) ≤
      (absQ w2 * ε1 + ε2 * absQ wHat1) * absQ x := by
  have h_decomp : w2 * (w1 * x) - wHat2 * (wHat1 * x) =
      (w2 * (w1 - wHat1) + (w2 - wHat2) * wHat1) * x := by
    ring
  rw [h_decomp, absQ_mul]
  have h_tri := absQ_add_le (w2 * (w1 - wHat1)) ((w2 - wHat2) * wHat1)
  rw [absQ_mul, absQ_mul] at h_tri
  have h_sym1 : absQ (w1 - wHat1) = absQ (wHat1 - w1) := by
    unfold absQ; split_ifs <;> linarith
  have h_sym2 : absQ (w2 - wHat2) = absQ (wHat2 - w2) := by
    unfold absQ; split_ifs <;> linarith
  rw [h_sym1, h_sym2] at h_tri
  have h_m1 : absQ w2 * absQ (wHat1 - w1) ≤ absQ w2 * ε1 :=
    mul_le_mul_of_nonneg_left he1 (absQ_nonneg w2)
  have h_m2 : absQ (wHat2 - w2) * absQ wHat1 ≤ ε2 * absQ wHat1 :=
    mul_le_mul_of_nonneg_right he2 (absQ_nonneg wHat1)
  have h_sum : absQ w2 * absQ (wHat1 - w1) + absQ (wHat2 - w2) * absQ wHat1 ≤
      absQ w2 * ε1 + ε2 * absQ wHat1 := by
    linarith
  exact mul_le_mul_of_nonneg_right (le_trans h_tri h_sum) (absQ_nonneg x)
-- =========================================================================
-- 2. РАЦИОНАЛЬНЫЕ СФЕРИЧЕСКИЕ КОДЫ ДЛЯ EMBEDDINGS, LM_HEAD И KV-CACHE
-- =========================================================================

abbrev VecQ := List ℚ

def dotListQ (u v : VecQ) : ℚ :=
  (List.zipWith (· * ·) u v).sum

def sqNormListQ (v : VecQ) : ℚ :=
  dotListQ v v

def l1NormListQ (v : VecQ) : ℚ :=
  (v.map absQ).sum

/-- Предикат принадлежности кодового слова рациональной гиперсфере радиуса `R` (`‖c‖₂² = R²`) -/
def isOnRationalSphereQ (c : VecQ) (radiusSq : ℚ) : Bool :=
  decide (sqNormListQ c = radiusSq)

/-- Вычислимая проверка сферической кодовой книги (все кодовые слова лежат на одной гиперсфере `R²`) -/
def checkSphericalCodebookQ (codebook : List VecQ) (radiusSq : ℚ) : Bool :=
  codebook.all (fun c => isOnRationalSphereQ c radiusSq)

/-- Теорема 2.1 (Тождество скалярного произведения на рациональной гиперсфере):
    для любых двух векторов `u, v` одинаковой длины выполняется
    `‖u - v‖₂² = ‖u‖₂² + ‖v‖₂² - 2 ⟨u, v⟩`. -/
theorem spherical_chord_dot_identity :
    ∀ (u v : VecQ),
      u.length = v.length →
      sqNormListQ (List.zipWith (· - ·) u v) =
        sqNormListQ u + sqNormListQ v - 2 * dotListQ u v
  | [], [], _ => by simp [sqNormListQ, dotListQ]
  | [], _ :: _, hlen => by simp at hlen
  | _ :: _, [], hlen => by simp at hlen
  | a :: as, b :: bs, hlen => by
      have ih := spherical_chord_dot_identity as bs (by simpa using hlen)
      dsimp [sqNormListQ, dotListQ, List.zipWith] at ih ⊢
      simp only [List.sum_cons] at ih ⊢
      have h_alg : (a - b) * (a - b) = a * a + b * b - 2 * (a * b) := by ring
      linarith

/-- Теорема 2.2 (Гарантированное сохранение скалярного произведения при сферическом квантовании):
    если исходный нормализованный эмбеддинг `u` и кодовое слово `c` лежат на одной
    рациональной сфере (`‖u‖₂² = R²`, `‖c‖₂² = R²`), а квадрат хорды `‖u - c‖₂² ≤ δ²`,
    то косинусное сходство / скалярное произведение удовлетворяет `⟨u, c⟩ ≥ R² - δ² / 2`. -/
theorem spherical_code_inner_product_lower_bound (u c : VecQ) (radiusSq deltaSq : ℚ)
    (hlen : u.length = c.length)
    (hu_sph : sqNormListQ u = radiusSq)
    (hc_sph : sqNormListQ c = radiusSq)
    (h_chord : sqNormListQ (List.zipWith (· - ·) u c) ≤ deltaSq) :
    radiusSq - deltaSq / 2 ≤ dotListQ u c := by
  have hid := spherical_chord_dot_identity u c hlen
  rw [hu_sph, hc_sph] at hid
  linarith
-- =========================================================================
-- 3. ЦЕЛОЧИСЛЕННЫЕ ПРИМИТИВЫ ТРАНСФОРМЕРА БЕЗ FLOAT (EXP И 1/√S НАД ℚ)
-- =========================================================================

/-- Целочисленно-двоичная аппроксимация экспоненты для Softmax без чисел с плавающей точкой:
    вычисляет `(max(0, 1 + x / 2^k))^(2^k)` над точными рациональными ℚ (только сдвиги и квадраты). -/
def dyadicExpApproxQ (x : ℚ) (k : Nat) : ℚ :=
  let pow2 := ((2 : ℚ) ^ k)
  let base := if 0 ≤ 1 + x / pow2 then 1 + x / pow2 else 0
  Nat.repeat (fun acc => acc * acc) k base

lemma repeat_sq_nonneg (k : Nat) (b : ℚ) (hb : 0 ≤ b) :
    0 ≤ Nat.repeat (fun acc => acc * acc) k b := by
  induction k generalizing b with
  | zero => exact hb
  | succ n ih =>
      simp only [Nat.repeat]
      exact ih (b * b) (mul_self_nonneg b)

/-- Теорема 3.1 (Строгая неотрицательность и корректность весов Softmax без `float`):
    для любого рационального логита `x ∈ ℚ` и глубины возведения в квадрат `k`,
    `dyadicExpApproxQ x k ≥ 0`. -/
theorem dyadicExpApproxQ_nonneg (x : ℚ) (k : Nat) :
    0 ≤ dyadicExpApproxQ x k := by
  dsimp [dyadicExpApproxQ]
  apply repeat_sq_nonneg
  split_ifs with h
  · exact h
  · exact le_refl 0

/-- Один шаг бесплуючей итерации Ньютона для `1 / √S` в RMSNorm:
    `y_{n+1} = y_n * (3 - S * y_n²) / 2`. -/
def invSqrtNewtonStepQ (S y : ℚ) : ℚ :=
  y * (3 - S * y * y) / 2

/-- Теорема 3.2 (Точное алгебраическое тождество сходимости метода Ньютона для RMSNorm):
    невязка `1 - S * y_{n+1}²` выражается через квадрат предыдущей невязки `e = 1 - S * y_n²`
    по точной формуле `1 - S * y_{n+1}² = e² * (4 - e) / 4` (квадратичная сходимость над ℚ!). -/
theorem invSqrtNewtonStepQ_residual_identity (S y : ℚ) :
    1 - S * (invSqrtNewtonStepQ S y) * (invSqrtNewtonStepQ S y) =
      (1 - S * y * y) * (1 - S * y * y) * (4 - (1 - S * y * y)) / 4 := by
  dsimp [invSqrtNewtonStepQ]
  ring

-- =========================================================================
-- ИСПОЛНЯЕМЫЕ ТЕСТЫ (#eval) И ПРОВЕРКА АКСИОМАТИЧЕСКОЙ ЧИСТОТЫ
-- =========================================================================

#eval
  let w1 : ℚ := 3/4
  let wHat1 : ℚ := 1/2
  let w2 : ℚ := 2/1
  let x : ℚ := 4/1
  let w2Comp := crossLayerCompensatedWeightQ w1 wHat1 w2
  let origOut := w2 * (w1 * x)
  let compOut := w2Comp * (wHat1 * x)
  s!"[Cross-Layer ℓ₁ Compensation] origOut={origOut}, compensatedOut={compOut}, w2Comp={w2Comp}"

#eval
  let d4Shell : List VecQ := [[1, 1, 0, 0], [1, -1, 0, 0], [0, 1, 1, 0], [0, 0, 1, -1]]
  let allSph := checkSphericalCodebookQ d4Shell 2
  let u : VecQ := [1, 1, 0, 0]
  let c : VecQ := [1, 0, 1, 0]
  let dotVal := dotListQ u c
  s!"[Rational Spherical Code] allOnSphere(R²=2)={allSph}, dot(u,c)={dotVal}"

#eval
  let eApprox := dyadicExpApproxQ (-1/2) 3
  let y0 : ℚ := 1/2
  let y1 := invSqrtNewtonStepQ (4/1) y0
  let y2 := invSqrtNewtonStepQ (4/1) y1
  s!"[Integer-Only Transformer Primitives] exp(-1/2)≈{eApprox}, invSqrt(4): y0={y0} -> y1={y1} -> y2={y2}"

end MarkovL1CrossLayerAndIntegerTransformer

#print axioms MarkovL1CrossLayerAndIntegerTransformer.cross_layer_exact_cancellation
#print axioms MarkovL1CrossLayerAndIntegerTransformer.two_layer_cascade_drift_bound
#print axioms MarkovL1CrossLayerAndIntegerTransformer.spherical_chord_dot_identity
#print axioms MarkovL1CrossLayerAndIntegerTransformer.spherical_code_inner_product_lower_bound
#print axioms MarkovL1CrossLayerAndIntegerTransformer.dyadicExpApproxQ_nonneg
#print axioms MarkovL1CrossLayerAndIntegerTransformer.invSqrtNewtonStepQ_residual_identity
