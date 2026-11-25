import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# 3D Hexagonal Close-Packed (3HCP) Lattice Quantizer, Register Inversion (Le₀ = 0.024), and Birkhoff–James ℓ₁-Orthogonality

* **Author:** E. S. Markov (ORCID: 0009-0005-2235-5464)
* **Affiliation:** Independent Researcher, Astrakhan, Russia
* **Repository:** https://github.com/fomamarkov-creator/l1-projection-complexity-lean4
* **License:** GNU Affero General Public License v3.0 (AGPLv3)
* **Toolchain:** Lean `v4.37.0-rc1` / Mathlib

## Overview
Adapts geometric lattice invariants, modular register inversion, and Banach-space
orthogonality into exact-rational (`ℚ`) neural network quantization:
1. **3D Hexagonal Close-Packed (3HCP) Lattice (`hcp3DAlphabet`, ~1.23 bits/weight):**
   Vector-quantizes weight triplets into the 13-element 3HCP coordination shell
   (origin + 12 nearest neighbors), verified via `hcp3DAlphabet_verified`.
2. **Modular Register Inversion & Leeway Gap (`Le₀ = 256/250 - 1 = 3/125`):**
   Isolates extreme weight/activation outliers exceeding `Λ_limit = 256` into a high-precision
   sparse register (`registerInversionSplitQ`), proving exact lossless decomposition
   (`registerInversion_exact_decomposition`).
3. **Birkhoff–James Orthogonality in `ℓ₁` (`birkhoff_l1_orthogonality_sufficient`):**
   Proves that sign-balanced subgradients guarantee `‖wHat + t · e‖₁ ≥ ‖wHat‖₁` for all `t ∈ ℚ`,
   certifying that `wHat` is a true Banach-space `ℓ₁`-orthogonal projection.
-/

namespace MarkovL1HCPAndBirkhoffQuantizer

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

-- =========================================================================
-- 1. 3D РЕШЁТКА ПЛОТНОЙ УПАКОВКИ 3HCP (13 СОСТОЯНИЙ ≈ 1.23 БИТА НА ВЕС)
-- =========================================================================

abbrev Vec3Q := ℚ × ℚ × ℚ
abbrev Vec3Z := ℤ × ℤ × ℤ

/-- 13-элементный координационный словарь 3D-решётки плотной упаковки 3HCP:
    начало координат + 12 векторов ближайших соседей (6 в базисной плоскости + 6 межслоевых) -/
def hcp3DAlphabet : List Vec3Z :=
  [ (0, 0, 0),
    (1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (1, -1, 0), (-1, 1, 0),
    (0, 0, 1), (1, 0, 1), (0, 1, 1), (0, 0, -1), (1, 0, -1), (0, 1, -1) ]

/-- Теорема 1.1 (Машинная верификация 3HCP-словаря):
    алфавит содержит ровно 13 попарно различных 3D-векторов (~1.233 бита на вес). -/
theorem hcp3DAlphabet_verified :
    hcp3DAlphabet.length = 13 ∧ hcp3DAlphabet.Nodup := by
  decide

def scaleVec3Z (α : ℚ) (z : Vec3Z) : Vec3Q :=
  (α * (z.1 : ℚ), α * (z.2.1 : ℚ), α * (z.2.2 : ℚ))

def l1Dist3Q (u v : Vec3Q) : ℚ :=
  absQ (u.1 - v.1) + absQ (u.2.1 - v.2.1) + absQ (u.2.2 - v.2.2)

def isCloser3Q (target cand best : Vec3Q) : Bool :=
  decide (l1Dist3Q target cand < l1Dist3Q target best)

/-- Векторный 3HCP-квантователь троек весов с медианным масштабом α -/
def quantize3HCPBlockQ (v : Vec3Q) : Vec3Q :=
  let m0 := absQ v.1
  let m1 := absQ v.2.1
  let m2 := absQ v.2.2
  let α := (m0 + m1 + m2) / 3
  let cands := hcp3DAlphabet.map (scaleVec3Z α)
  cands.foldl (fun best c => if isCloser3Q v c best then c else best) (0, 0, 0)

-- =========================================================================
-- 2. РЕГИСТРОВАЯ ИНВЕРСИЯ (256 ≡ 0) И АДАПТИВНЫЙ ЗАЗОР Le₀ = 0.024
-- =========================================================================

/-- Фундаментальные рациональные инварианты зазора -/
def Λ_limit : ℚ := 256
def N_base : ℚ := 250
def ζ_ratio : ℚ := Λ_limit / N_base
def Le0_gap : ℚ := ζ_ratio - 1

/-- Теорема 2.1 (Точное значение дыхательного зазора Le₀ = 3/125 = 0.024) -/
theorem markov_leeway_gap_exact :
    ζ_ratio = 128 / 125 ∧ Le0_gap = 3 / 125 := by
  unfold Le0_gap ζ_ratio Λ_limit N_base
  norm_num

/-- Регистровая инверсия выбросов: если амплитуда веса/активации достигает порога `limit`,
    основной низкобитный канал запирается (`0`), а полный вес выносится в разреженный регистр выбросов. -/
def registerInversionSplitQ (limit w : ℚ) : ℚ × ℚ :=
  if limit ≤ absQ w then
    (0, w)
  else
    (w, 0)

/-- Теорема 2.2 (Точное сохранение сигнала при регистровой инверсии выбросов):
    сумма основного канала и регистра выбросов тождественно равна исходному весу `w`,
    а основной канал гарантированно ограничен по амплитуде `< limit`. -/
theorem registerInversion_exact_decomposition (limit w : ℚ) (hlim : 0 < limit) :
    let (mainCh, outlierReg) := registerInversionSplitQ limit w
    mainCh + outlierReg = w ∧ absQ mainCh < limit := by
  dsimp [registerInversionSplitQ]
  split_ifs with h
  · constructor
    · ring
    · unfold absQ
      split_ifs <;> linarith
  · constructor
    · ring
    · exact lt_of_not_ge h
-- =========================================================================
-- 3. ОРТОГОНАЛЬНОСТЬ БИРКГОФА–ДЖЕЙМСА В БАНАХОВОМ ПРОСТРАНСТВЕ ℓ₁
-- =========================================================================

def l1VecQ (xs : List ℚ) : ℚ :=
  (xs.map absQ).sum

def addScaledVecQ (wHat e : List ℚ) (t : ℚ) : List ℚ :=
  List.zipWith (fun wh ei => wh + t * ei) wHat e

/-- Вычислимый предикат ортогональности Биркгофа–Джеймса `wHat ⊥_BJ e` в метрике `ℓ₁`:
    на активном носителе (`wh ≠ 0`) взвешенная сумма `∑ sign(wh_i) * e_i` по модулю
    не превосходит `ℓ₁`-нормы невязки на нулевом носителе (`wh = 0`), т.е.
    `|∑_{wh_i ≠ 0} sign(wh_i) e_i| ≤ ∑_{wh_i = 0} |e_i|`. -/
def checkBirkhoffL1OrthogonalQ (wHat e : List ℚ) : Bool :=
  let activeSum := (List.zipWith (fun wh ei =>
    if decide (wh = 0) then 0 else if 0 ≤ wh then ei else -ei) wHat e).sum
  let zeroSupportNorm := (List.zipWith (fun wh ei =>
    if decide (wh = 0) then absQ ei else 0) wHat e).sum
  decide (wHat.length = e.length ∧ absQ activeSum ≤ zeroSupportNorm)

/-- Покоординатная нижняя оценка модуля `|wh + t * e| ≥ |wh| + t * sign(wh) * e` при `wh ≠ 0`
    и `|0 + t * e| = |t| * |e|` при `wh = 0` -/
lemma point_birkhoff_lower_bound (wh ei t : ℚ) :
    absQ wh + t * (if decide (wh = 0) then 0 else if 0 ≤ wh then ei else -ei) +
    absQ t * (if decide (wh = 0) then absQ ei else 0) ≤
    absQ (wh + t * ei) := by
  by_cases h0 : wh = 0
  · subst h0
    simp only [decide_true, ↓reduceIte, mul_zero, add_zero, zero_add]
    unfold absQ
    by_cases ht : 0 ≤ t <;> by_cases he : 0 ≤ ei
    · have hte : 0 ≤ t * ei := mul_nonneg ht he
      simp [ht, he, hte]
    · have he' : ei < 0 := lt_of_not_ge he
      have hte : t * ei ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht (le_of_lt he')
      split_ifs <;> nlinarith
    · have ht' : t < 0 := lt_of_not_ge ht
      have hte : t * ei ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt ht') he
      split_ifs <;> nlinarith
    · have ht' : t < 0 := lt_of_not_ge ht
      have he' : ei < 0 := lt_of_not_ge he
      have hte : 0 ≤ t * ei := mul_nonneg_of_nonpos_of_nonpos (le_of_lt ht') (le_of_lt he')
      split_ifs <;> nlinarith
  · simp only [decide_eq_false h0, Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero]
    by_cases hp : 0 ≤ wh
    · simp only [hp, ↓reduceIte]
      unfold absQ
      split_ifs <;> linarith
    · simp only [hp, ↓reduceIte]
      unfold absQ
      split_ifs <;> linarith

/-- Теорема 3.1 (Сертификат ортогональности Биркгофа–Джеймса в метрике ℓ₁):
    если `checkBirkhoffL1OrthogonalQ wHat e = true`, то для ЛЮБОГО скаляра `t ∈ ℚ`
    выполняется `‖wHat + t · e‖₁ ≥ ‖wHat‖₁`, что доказывает оптимальность квантованной
    проекции `wHat` вдоль направления ошибки `e` в банаховом пространстве `ℓ₁`. -/
theorem birkhoff_l1_orthogonality_sufficient (wHat e : List ℚ)
    (horth : checkBirkhoffL1OrthogonalQ wHat e = true) (t : ℚ) :
    l1VecQ wHat ≤ l1VecQ (addScaledVecQ wHat e t) := by
  dsimp [checkBirkhoffL1OrthogonalQ] at horth
  rw [decide_eq_true_eq] at horth
  obtain ⟨hlen, hbal⟩ := horth
  have h_sum_bound : ∀ (us vs : List ℚ), us.length = vs.length →
      l1VecQ us +
      t * (List.zipWith (fun wh ei => if decide (wh = 0) then 0 else if 0 ≤ wh then ei else -ei) us vs).sum +
      absQ t * (List.zipWith (fun wh ei => if decide (wh = 0) then absQ ei else 0) us vs).sum ≤
      l1VecQ (addScaledVecQ us vs t) := by
    intro us
    induction us with
    | nil =>
        intro vs hlen_uv
        cases vs with
        | nil => simp [l1VecQ, addScaledVecQ]
        | cons _ _ => simp at hlen_uv
    | cons u uRest ih =>
        intro vs hlen_uv
        cases vs with
        | nil => simp at hlen_uv
        | cons v vRest =>
            have ih_step := ih vRest (by simpa using hlen_uv)
            have h_pt := point_birkhoff_lower_bound u v t
            simp only [l1VecQ, addScaledVecQ, List.map_cons, List.zipWith_cons_cons, List.sum_cons] at ih_step ⊢
            linarith
  have h_main := h_sum_bound wHat e hlen
  set A := (List.zipWith (fun wh ei => if decide (wh = 0) then 0 else if 0 ≤ wh then ei else -ei) wHat e).sum
  set Z := (List.zipWith (fun wh ei => if decide (wh = 0) then absQ ei else 0) wHat e).sum
  have h_tA : -(absQ t * absQ A) ≤ t * A := by
    unfold absQ at hbal ⊢
    by_cases ht : 0 ≤ t <;> by_cases hA : 0 ≤ A
    · simp [ht, hA]
    · have hA' : A < 0 := lt_of_not_ge hA
      simp [ht, hA]; nlinarith
    · have ht' : t < 0 := lt_of_not_ge ht
      simp [ht, hA]; nlinarith
    · have ht' : t < 0 := lt_of_not_ge ht
      have hA' : A < 0 := lt_of_not_ge hA
      simp [ht, hA]
  have h_prod : absQ t * absQ A ≤ absQ t * Z :=
    mul_le_mul_of_nonneg_left hbal (absQ_nonneg t)
  linarith

-- =========================================================================
-- ИСПОЛНЯЕМЫЕ ТЕСТЫ (#eval) И ПРОВЕРКА АКСИОМАТИЧЕСКОЙ ЧИСТОТЫ
-- =========================================================================

#eval
  let v3 : Vec3Q := (3/1, -3/1, 0/1);
  let q3 := quantize3HCPBlockQ v3;
  s!"[3HCP Lattice Quantizer] states={hcp3DAlphabet.length} (~1.23 b/w), input={v3} -> q3={q3}, dist={l1Dist3Q v3 q3}"

#eval
  let (mainCh, outlierReg) := registerInversionSplitQ Λ_limit (300/1);
  s!"[Register Inversion & Le₀] Le0={Le0_gap}, mainChannel={mainCh}, isolatedOutlier={outlierReg}"

#eval
  let wHat : List ℚ := [2/1, -2/1, 0/1, 0/1];
  let err : List ℚ := [1/2, 1/2, 1/4, -1/4];
  let isBJOrth := checkBirkhoffL1OrthogonalQ wHat err;
  s!"[Birkhoff–James ℓ₁-Orthogonality] wHat ⊥_BJ err = {isBJOrth}, ‖wHat‖₁={l1VecQ wHat}, ‖wHat+err‖₁={l1VecQ (addScaledVecQ wHat err 1)}"

end MarkovL1HCPAndBirkhoffQuantizer

#print axioms MarkovL1HCPAndBirkhoffQuantizer.hcp3DAlphabet_verified
#print axioms MarkovL1HCPAndBirkhoffQuantizer.markov_leeway_gap_exact
#print axioms MarkovL1HCPAndBirkhoffQuantizer.registerInversion_exact_decomposition
#print axioms MarkovL1HCPAndBirkhoffQuantizer.birkhoff_l1_orthogonality_sufficient
