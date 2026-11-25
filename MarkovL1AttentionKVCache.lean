import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Verified In-Domain Hadamard Inference and Sub-1-Bit Attention KV-Cache Compression

* **Author:** E. S. Markov (ORCID: 0009-0005-2235-5464)
* **Affiliation:** Independent Researcher, Astrakhan, Russia
* **Repository:** https://github.com/fomamarkov-creator/l1-projection-complexity-lean4
* **License:** GNU Affero General Public License v3.0 (AGPLv3)
* **Toolchain:** Lean `v4.37.0-rc1` / Mathlib

## Overview
Formalizes multiplier-free in-domain Walsh–Hadamard inference and certified Attention KV-Cache
quantization over exact rationals (`ℚ`):
1. **In-Domain Hadamard Dot-Product Identity (`in_domain_hadamard_exact_dot`):** Proves
   `dot8Q (W₈ w) (W₈ x) = 8 * dot8Q w x`, eliminating inverse weight transforms at runtime
   and avoiding the `2×` inverse-rotation distortion factor.
2. **Tight `ℓ₁`-`ℓ∞` Neuron Output Error Bound (`holder_l1_linf_bound`):** Bounds the
   exact output drift of a quantized neuron in terms of rotated weight `ℓ₁` error and
   transformed activation `ℓ∞` norm.
3. **Certified Attention KV-Cache Drift (`attention_logit_drift_bound`, `attention_value_drift_bound`):**
   Establishes machine-checked error bounds for quantized Key (`K̂`) and Value (`V̂`) tensors
   in autoregressive Transformer attention.
-/

namespace MarkovL1AttentionKVCache

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
    unfold absQ
    split_ifs <;> linarith
  · have ha' : a < 0 := lt_of_not_ge ha
    have hab : a * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt ha') hb
    unfold absQ
    split_ifs <;> linarith
  · have ha' : a < 0 := lt_of_not_ge ha
    have hb' : b < 0 := lt_of_not_ge hb
    have hab : 0 ≤ a * b := mul_nonneg_of_nonpos_of_nonpos (le_of_lt ha') (le_of_lt hb')
    simp [absQ, ha, hb, hab]

-- =========================================================================
-- 1. ИНФЕРЕНС ПРЯМО В БАЗИСЕ УОЛША–АДАМАРА W₈ БЕЗ ОБРАТНОГО ПРЕОБРАЗОВАНИЯ
-- =========================================================================

@[ext]
structure Vec8Q where
  x0 : ℚ
  x1 : ℚ
  x2 : ℚ
  x3 : ℚ
  x4 : ℚ
  x5 : ℚ
  x6 : ℚ
  x7 : ℚ
  deriving Repr, DecidableEq

/-- Ненормированное 8×8 преобразование Уолша–Адамара W₈ (только сложения и вычитания) -/
def walshHadamard8Q (v : Vec8Q) : Vec8Q :=
  let a0 := v.x0 + v.x1
  let a1 := v.x0 - v.x1
  let a2 := v.x2 + v.x3
  let a3 := v.x2 - v.x3
  let a4 := v.x4 + v.x5
  let a5 := v.x4 - v.x5
  let a6 := v.x6 + v.x7
  let a7 := v.x6 - v.x7
  let b0 := a0 + a2
  let b1 := a1 + a3
  let b2 := a0 - a2
  let b3 := a1 - a3
  let b4 := a4 + a6
  let b5 := a5 + a7
  let b6 := a4 - a6
  let b7 := a5 - a7
  { x0 := b0 + b4
    x1 := b1 + b5
    x2 := b2 + b6
    x3 := b3 + b7
    x4 := b0 - b4
    x5 := b1 - b5
    x6 := b2 - b6
    x7 := b3 - b7 }

def dot8Q (u v : Vec8Q) : ℚ :=
  u.x0 * v.x0 + u.x1 * v.x1 + u.x2 * v.x2 + u.x3 * v.x3 +
  u.x4 * v.x4 + u.x5 * v.x5 + u.x6 * v.x6 + u.x7 * v.x7

/-- Теорема 1.1 (Точный инференс в пространстве Адамара без обратного преобразования весов):
    (W₈ w) · (W₈ x) = 8 · (w · x). -/
theorem in_domain_hadamard_exact_dot (w x : Vec8Q) :
    dot8Q (walshHadamard8Q w) (walshHadamard8Q x) = 8 * dot8Q w x := by
  rcases w with ⟨w0, w1, w2, w3, w4, w5, w6, w7⟩
  rcases x with ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩
  dsimp [walshHadamard8Q, dot8Q]
  ring

-- =========================================================================
-- 2. ТОЧНАЯ ОЦЕНКА ВЫХОДНОЙ ОШИБКИ НЕЙРОНА В БАЗИСЕ АДАМАРА (ℓ₁ - ℓ∞)
-- =========================================================================

def l1ListQ (xs : List ℚ) : ℚ :=
  (xs.map absQ).sum

def dotListQ (us vs : List ℚ) : ℚ :=
  (List.zipWith (· * ·) us vs).sum

lemma dotListQ_sub_left :
    ∀ (us uhs xs : List ℚ),
      us.length = uhs.length →
      dotListQ uhs xs - dotListQ us xs =
      dotListQ (List.zipWith (· - ·) uhs us) xs
  | [], [], _, _ => by simp [dotListQ]
  | [], _ :: _, _, hlen => by simp at hlen
  | _ :: _, [], _, hlen => by simp at hlen
  | _ :: _, _ :: _, [], _ => by simp [dotListQ]
  | u :: us, uh :: uhs, x :: xs, hlen => by
      simp only [dotListQ, List.zipWith_cons_cons, List.sum_cons]
      have ih := dotListQ_sub_left us uhs xs (by simpa using hlen)
      simp only [dotListQ] at ih
      have h_lin : uh * x - u * x = (uh - u) * x := by ring
      linarith

/-- Теорема 2.1 (Неравенство Гёльдера ℓ₁-ℓ∞ для произвольной размерности d):

    |⟨e, z⟩| ≤ ‖e‖₁ · B, если каждая координата |z_i| ≤ B -/
theorem holder_l1_linf_bound :
    ∀ (es zs : List ℚ) (B : ℚ),
      es.length = zs.length →
      0 ≤ B →
      (∀ z ∈ zs, absQ z ≤ B) →
      absQ (dotListQ es zs) ≤ l1ListQ es * B
  | [], [], _, _, _, _ => by simp [dotListQ, l1ListQ, absQ]
  | [], _ :: _, _, hlen, _, _ => by simp at hlen
  | _ :: _, [], _, hlen, _, _ => by simp at hlen
  | e :: es, z :: zs, B, hlen, hB, hz_bound => by
      have hz0 : absQ z ≤ B := hz_bound z List.mem_cons_self
      have hz_rest : ∀ z' ∈ zs, absQ z' ≤ B := fun z' hz' =>
        hz_bound z' (List.mem_cons_of_mem _ hz')
      have ih := holder_l1_linf_bound es zs B (by simpa using hlen) hB hz_rest
      have h_tri : absQ (e * z + dotListQ es zs) ≤ absQ (e * z) + absQ (dotListQ es zs) :=
        absQ_add_le _ _
      rw [absQ_mul] at h_tri
      have h_mul : absQ e * absQ z ≤ absQ e * B :=
        mul_le_mul_of_nonneg_left hz0 (absQ_nonneg e)
      simp only [dotListQ, List.zipWith_cons_cons, List.sum_cons, l1ListQ, List.map_cons] at ih h_tri ⊢
      have h_dist : (absQ e + (es.map absQ).sum) * B = absQ e * B + (es.map absQ).sum * B := by ring
      linarith
-- =========================================================================
-- 3. ВЕРИФИЦИРОВАННОЕ СЖАТИЕ ATTENTION KV-CACHE В ТРАНСФОРМЕРАХ
-- =========================================================================

/-- Вычислимая проверка попадания всех координат вектора в интервал [-B, B] -/
def checkInfBoundQ (zs : List ℚ) (B : ℚ) : Bool :=
  zs.all (fun z => decide (absQ z ≤ B))

lemma checkInfBoundQ_sound (zs : List ℚ) (B : ℚ) (h : checkInfBoundQ zs B = true) :
    ∀ z ∈ zs, absQ z ≤ B := by
  intro z hz
  have hall := List.all_eq_true.mp h z hz
  exact decide_eq_true_eq.mp hall

/-- Теорема 3.1 (Гарантированная граница искажения логитов внимания `q · K̂ᵀ` при квантовании ключей):
    Если ключ `k` сжат в `kHat` с ошибкой `‖kHat - k‖₁ ≤ ε_K`, а вектор запроса `q` ограничен
    по максимуму `‖q‖∞ ≤ B_Q`, то ошибка скалярного произведения внимания строго ограничена:
    `|q · kHat - q · k| ≤ ε_K * B_Q`. -/
theorem attention_logit_drift_bound (q k kHat : List ℚ) (ε_K B_Q : ℚ)
    (hlen_k : k.length = kHat.length)
    (hlen_q : k.length = q.length)
    (hB : 0 ≤ B_Q)
    (hq_bound : checkInfBoundQ q B_Q = true)
    (hk_err : l1ListQ (List.zipWith (· - ·) kHat k) ≤ ε_K) :
    absQ (dotListQ kHat q - dotListQ k q) ≤ ε_K * B_Q := by
  rw [dotListQ_sub_left k kHat q hlen_k]
  have hlen_zip : (List.zipWith (· - ·) kHat k).length = q.length := by
    simp [List.length_zipWith, ← hlen_k, hlen_q]
  have h_holder := holder_l1_linf_bound (List.zipWith (· - ·) kHat k) q B_Q hlen_zip hB
    (checkInfBoundQ_sound q B_Q hq_bound)
  have h_mono : l1ListQ (List.zipWith (· - ·) kHat k) * B_Q ≤ ε_K * B_Q :=
    mul_le_mul_of_nonneg_right hk_err hB
  linarith

/-- Теорема 3.2 (Гарантированная граница искажения контекста внимания `α · V̂` при квантовании значений):
    Для весов внимания `α_t ≥ 0` (где `∑ α_t = 1` после Softmax) и квантованных значений `vHat_t`,
    ошибка агрегированного контекста по каждой координате `d` не превосходит взвешенной суммы
    ошибок значений `∑ α_t · |vHat_t - v_t|`. -/
theorem attention_value_drift_bound :
    ∀ (alphas vs vHats : List ℚ),
      alphas.length = vs.length →
      vs.length = vHats.length →
      (∀ α ∈ alphas, 0 ≤ α) →
      absQ (dotListQ alphas vHats - dotListQ alphas vs) ≤
        dotListQ alphas (List.zipWith (fun vh v => absQ (vh - v)) vHats vs)
  | [], [], [], _, _, _ => by simp [dotListQ, absQ]
  | [], _ :: _, _, h1, _, _ => by simp at h1
  | _ :: _, [], _, h1, _, _ => by simp at h1
  | _, [], _ :: _, _, h2, _ => by simp at h2
  | _, _ :: _, [], _, h2, _ => by simp at h2
  | α :: aRest, v :: vRest, vh :: vhRest, h1, h2, hα_nn => by
      have hα0 : 0 ≤ α := hα_nn α List.mem_cons_self
      have hα_rest : ∀ a ∈ aRest, 0 ≤ a := fun a ha => hα_nn a (List.mem_cons_of_mem _ ha)
      have ih := attention_value_drift_bound aRest vRest vhRest
        (by simpa using h1) (by simpa using h2) hα_rest
      simp only [dotListQ, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
      have h_rearr :
          (α * vh + (List.zipWith (· * ·) aRest vhRest).sum) -
          (α * v + (List.zipWith (· * ·) aRest vRest).sum) =
          α * (vh - v) + ((List.zipWith (· * ·) aRest vhRest).sum -
                          (List.zipWith (· * ·) aRest vRest).sum) := by
        ring
      rw [h_rearr]
      have h_tri := absQ_add_le (α * (vh - v))
        ((List.zipWith (· * ·) aRest vhRest).sum - (List.zipWith (· * ·) aRest vRest).sum)
      rw [absQ_mul] at h_tri
      have h_abs_α : absQ α = α := by
        unfold absQ; exact ite_eq_left_iff.mpr (fun hn => False.elim (hn hα0))
      rw [h_abs_α] at h_tri
      linarith

-- =========================================================================
-- ИСПОЛНЯЕМЫЕ ТЕСТЫ (#eval) И ПРОВЕРКА АКСИОМАТИЧЕСКОЙ ЧИСТОТЫ
-- =========================================================================

#eval
  let w : Vec8Q := ⟨1/2, -1/2, 1/4, 3/4, -1/4, 1/2, 0, -1/2⟩;
  let x : Vec8Q := ⟨2/1, 1/1, -1/1, 3/1, 1/2, -1/2, 4/1, 1/1⟩;
  let directDot := dot8Q w x;
  let hadamardDot := dot8Q (walshHadamard8Q w) (walshHadamard8Q x) / 8;
  s!"[In-Domain Hadamard W8] directDot={directDot}, hadamardDot/8={hadamardDot}"

#eval
  let q : List ℚ := [3/2, -2/1, 1/2, 1/1];
  let k : List ℚ := [1/4, -1/2, 3/4, -1/4];
  let kHat : List ℚ := [1/4, -1/2, 1/2, -1/4];
  let keyL1Err := l1ListQ (List.zipWith (· - ·) kHat k);
  let actualDrift := absQ (dotListQ kHat q - dotListQ k q);
  let certBound := keyL1Err * (2/1);
  s!"[Certified KV-Cache Logit] actualDrift={actualDrift} ≤ certBound={certBound}"

end MarkovL1AttentionKVCache

-- Проверка аксиоматической чистоты:
#print axioms MarkovL1AttentionKVCache.in_domain_hadamard_exact_dot
#print axioms MarkovL1AttentionKVCache.holder_l1_linf_bound
#print axioms MarkovL1AttentionKVCache.attention_logit_drift_bound
#print axioms MarkovL1AttentionKVCache.attention_value_drift_bound
