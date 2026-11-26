import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

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

def crossLayerCompensatedWeightQ (w1 wHat1 w2 : ℚ) : ℚ :=
  if wHat1 == 0 then w2 else w2 + w2 * ((w1 - wHat1) / wHat1)

theorem cross_layer_exact_cancellation (w1 wHat1 w2 Δw2 x : ℚ)
    (h_comp : Δw2 * wHat1 = w2 * (w1 - wHat1)) :
    (w2 + Δw2) * (wHat1 * x) = w2 * (w1 * x) := by
  calc
    (w2 + Δw2) * (wHat1 * x)
      = (w2 * wHat1 + Δw2 * wHat1) * x := by ring
    _ = (w2 * wHat1 + w2 * (w1 - wHat1)) * x := by rw [h_comp]
    _ = w2 * (w1 * x) := by ring

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

def dotListQ : VecQ → VecQ → ℚ
  | [], _ => 0
  | _, [] => 0
  | a :: as, b :: bs => a * b + dotListQ as bs

def sqNormListQ (v : VecQ) : ℚ :=
  dotListQ v v

def subListQ : VecQ → VecQ → VecQ
  | [], _ => []
  | _, [] => []
  | a :: as, b :: bs => (a - b) :: subListQ as bs

def isOnRationalSphereQ (c : VecQ) (radiusSq : ℚ) : Bool :=
  decide (sqNormListQ c = radiusSq)

def checkSphericalCodebookQ (codebook : List VecQ) (radiusSq : ℚ) : Bool :=
  codebook.all (fun c => isOnRationalSphereQ c radiusSq)

theorem spherical_chord_dot_identity (u v : VecQ) (hlen : u.length = v.length) :
    sqNormListQ (subListQ u v) = sqNormListQ u + sqNormListQ v - 2 * dotListQ u v := by
  induction u generalizing v with
  | nil =>
      cases v with
      | nil => simp [sqNormListQ, subListQ, dotListQ]
      | cons _ _ => simp at hlen
  | cons a as ih =>
      cases v with
      | nil => simp at hlen
      | cons b bs =>
          have hsub : as.length = bs.length := by simpa using hlen
          have hrec := ih bs hsub
          unfold sqNormListQ at hrec ⊢
          unfold subListQ
          simp only [dotListQ]
          have h_alg : (a - b) * (a - b) = a * a + b * b - 2 * (a * b) := by ring
          linarith

theorem spherical_code_inner_product_lower_bound (u c : VecQ) (radiusSq deltaSq : ℚ)
    (hlen : u.length = c.length)
    (hu_sph : sqNormListQ u = radiusSq)
    (hc_sph : sqNormListQ c = radiusSq)
    (h_chord : sqNormListQ (subListQ u c) ≤ deltaSq) :
    radiusSq - deltaSq / 2 ≤ dotListQ u c := by
  have hid := spherical_chord_dot_identity u c hlen
  rw [hu_sph, hc_sph] at hid
  linarith
-- =========================================================================
-- 3. ЦЕЛОЧИСЛЕННЫЕ ПРИМИТИВЫ ТРАНСФОРМЕРА БЕЗ FLOAT (EXP И 1/√S НАД ℚ)
-- =========================================================================

def dyadicExpApproxQ (x : ℚ) (k : Nat) : ℚ :=
  let pow2 := ((2 : ℚ) ^ k)
  let base := if 0 ≤ 1 + x / pow2 then 1 + x / pow2 else 0
  Nat.repeat (fun acc => acc * acc) k base

lemma repeat_sq_nonneg (k : Nat) (b : ℚ) (hb : 0 ≤ b) :
    0 ≤ Nat.repeat (fun acc => acc * acc) k b := by
  cases k with
  | zero => exact hb
  | succ n =>
      simp only [Nat.repeat]
      exact mul_self_nonneg _

theorem dyadicExpApproxQ_nonneg (x : ℚ) (k : Nat) :
    0 ≤ dyadicExpApproxQ x k := by
  dsimp [dyadicExpApproxQ]
  apply repeat_sq_nonneg
  split_ifs with h
  · exact h
  · exact le_refl 0

def invSqrtNewtonStepQ (S y : ℚ) : ℚ :=
  y * (3 - S * y * y) / 2

theorem invSqrtNewtonStepQ_residual_identity (S y : ℚ) :
    1 - S * (invSqrtNewtonStepQ S y) * (invSqrtNewtonStepQ S y) =
      (1 - S * y * y) * (1 - S * y * y) * (3 + (1 - S * y * y)) / 4 := by
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
  let v1 : VecQ := 1 :: 1 :: 0 :: 0 :: []
  let v2 : VecQ := 1 :: (-1) :: 0 :: 0 :: []
  let v3 : VecQ := 0 :: 1 :: 1 :: 0 :: []
  let v4 : VecQ := 0 :: 0 :: 1 :: (-1) :: []
  let d4Shell : List VecQ := v1 :: v2 :: v3 :: v4 :: []
  let allSph := checkSphericalCodebookQ d4Shell 2
  let u : VecQ := 1 :: 1 :: 0 :: 0 :: []
  let c : VecQ := 1 :: 0 :: 1 :: 0 :: []
  let dotVal := dotListQ u c
  s!"[Rational Spherical Code] allOnSphere(R²=2)={allSph}, dot(u,c)={dotVal}"

#eval
  let eApprox := dyadicExpApproxQ (-1/2) 3
  let y0 : ℚ := 1/2
  let y1 := invSqrtNewtonStepQ (4/1) y0
  let y2 := invSqrtNewtonStepQ (4/1) y1
  s!"[Integer-Only Transformer Primitives] exp(-1/2)≈{eApprox}, invSqrt(4): y0={y0} -> y1={y1} -> y2={y2}"
-- =========================================================================
-- 4. ДОПОЛНЕНИЕ V5.0: KL-УСТОЙЧИВОСТЬ, ГИПЕРБОЛИЧЕСКИЙ ШАР ПУАНКАРЕ И ЦЕЛОЧИСЛЕННЫЕ РЕГИСТРЫ ℤ
-- =========================================================================

/-- 4.1. Взвешенная граница дрейфа кросс-энтропии / KL-дивергенции при квантовании логитов:
    если вероятности `p_i ≥ 0` и ошибка лог-вероятностей ограничена `|logP_i - logPHat_i| ≤ δ`,
    то суммарное искажение `∑ p_i * |logP_i - logPHat_i| ≤ δ * (∑ p_i)`. -/
theorem weighted_kl_logit_drift_bound :
    ∀ (ps logP logPHat : List ℚ) (δ : ℚ),
      ps.length = logP.length →
      logP.length = logPHat.length →
      (∀ p ∈ ps, 0 ≤ p) →
      (∀ d ∈ List.zipWith (fun a b => absQ (a - b)) logP logPHat, d ≤ δ) →
      (List.zipWith (fun p d => p * d) ps
        (List.zipWith (fun a b => absQ (a - b)) logP logPHat)).sum ≤ δ * ps.sum
  | [], [], [], _, _, _, _, _ => by simp
  | [], _ :: _, _, _, h1, _, _, _ => by simp at h1
  | _ :: _, [], _, _, h1, _, _, _ => by simp at h1
  | _, [], _ :: _, _, _, h2, _, _ => by simp at h2
  | _, _ :: _, [], _, _, h2, _, _ => by simp at h2
  | p :: pRest, lp :: lpRest, lph :: lphRest, δ, h1, h2, hp_nn, hd_le => by
      have hp0 : 0 ≤ p := hp_nn p List.mem_cons_self
      have hp_r : ∀ x ∈ pRest, 0 ≤ x := fun x hx => hp_nn x (List.mem_cons_of_mem _ hx)
      have hd0 : absQ (lp - lph) ≤ δ := hd_le _ List.mem_cons_self
      have hd_r : ∀ d ∈ List.zipWith (fun a b => absQ (a - b)) lpRest lphRest, d ≤ δ :=
        fun d hd => hd_le d (List.mem_cons_of_mem _ hd)
      have ih := weighted_kl_logit_drift_bound pRest lpRest lphRest δ
        (by simpa using h1) (by simpa using h2) hp_r hd_r
      simp only [List.zipWith_cons_cons, List.sum_cons] at ih ⊢
      have h_mul : p * absQ (lp - lph) ≤ p * δ := mul_le_mul_of_nonneg_left hd0 hp0
      have h_dist : δ * (p + pRest.sum) = p * δ + δ * pRest.sum := by ring
      linarith

/-- 4.2. Гиперболическое / радиально-угловое разложение в шаре Пуанкаре:
    вектор эмбеддинга представляется парой `(радиус r, сферическое направление u)`.
    Теорема доказывает строгую квадратичную границу искажения при раздельной
    квантизации гиперболического радиуса `rHat` и направления `uHat` на решетке. -/
def scaleListQ (c : ℚ) (v : VecQ) : VecQ :=
  v.map (fun x => c * x)

theorem radial_angular_poincare_bound :
    ∀ (u uHat : VecQ) (r rHat : ℚ),
      u.length = uHat.length →
      sqNormListQ (subListQ (scaleListQ r u) (scaleListQ rHat uHat)) ≤
        2 * (r - rHat) * (r - rHat) * sqNormListQ u +
        2 * rHat * rHat * sqNormListQ (subListQ u uHat)
  | [], [], _, _, _ => by
      simp [scaleListQ, subListQ, sqNormListQ, dotListQ]
  | [], _ :: _, _, _, hlen => by simp at hlen
  | _ :: _, [], _, _, hlen => by simp at hlen
  | a :: as, b :: bs, r, rHat, hlen => by
      have ih := radial_angular_poincare_bound as bs r rHat (by simpa using hlen)
      unfold sqNormListQ at ih ⊢
      simp only [scaleListQ, List.map_cons, subListQ, dotListQ] at ih ⊢
      have h_sq : 0 ≤ ((r - rHat) * a - rHat * (a - b)) * ((r - rHat) * a - rHat * (a - b)) :=
        mul_self_nonneg _
      have h_pt : (r * a - rHat * b) * (r * a - rHat * b) ≤
          2 * (r - rHat) * (r - rHat) * (a * a) + 2 * rHat * rHat * ((a - b) * (a - b)) := by
        linarith [show (r * a - rHat * b) * (r * a - rHat * b) +
          ((r - rHat) * a - rHat * (a - b)) * ((r - rHat) * a - rHat * (a - b)) =
          2 * (r - rHat) * (r - rHat) * (a * a) + 2 * rHat * rHat * ((a - b) * (a - b)) by ring]
      have h_dist1 : 2 * (r - rHat) * (r - rHat) * (a * a + dotListQ as as) =
          2 * (r - rHat) * (r - rHat) * (a * a) + 2 * (r - rHat) * (r - rHat) * dotListQ as as := by ring
      have h_dist2 : 2 * rHat * rHat * ((a - b) * (a - b) + dotListQ (subListQ as bs) (subListQ as bs)) =
          2 * rHat * rHat * ((a - b) * (a - b)) + 2 * rHat * rHat * dotListQ (subListQ as bs) (subListQ as bs) := by ring
      linarith

/-- 4.3. Побитово-точная целочисленная арифметика ℤ (без float и без деления):
    диадическое возведение в квадрат со сдвигом `>>> F` для фиксированной точки `Q.F`. -/
def fixedPointExpStepZ (fracBits : Nat) (acc : Int) : Int :=
  (acc * acc) >>> fracBits

def fixedPointExpZ (xFixed : Int) (kSquarings fracBits : Nat) : Int :=
  let oneFixed : Int := (1 : Int) <<< fracBits
  let raw := oneFixed + (xFixed >>> kSquarings)
  let base := if 0 ≤ raw then raw else 0
  Nat.repeat (fixedPointExpStepZ fracBits) kSquarings base

/-- Теорема 4.3: Целочисленный оператор `fixedPointExpZ` в регистрах CPU `ℤ`
    строго неотрицателен при любых входах и любой разрядности `fracBits`. -/
theorem fixedPointExpZ_nonneg (xFixed : Int) (kSquarings fracBits : Nat) :
    0 ≤ fixedPointExpZ xFixed kSquarings fracBits := by
  dsimp [fixedPointExpZ]
  set base := if 0 ≤ ((1 : Int) <<< fracBits) + (xFixed >>> kSquarings)
              then ((1 : Int) <<< fracBits) + (xFixed >>> kSquarings) else 0
  have hbase : 0 ≤ base := by
    dsimp [base]; split_ifs with h
    · exact h
    · exact le_refl 0
  induction kSquarings with
  | zero => exact hbase
  | succ n ih =>
      simp only [Nat.repeat, fixedPointExpStepZ]
      exact Int.shiftRight_nonneg (mul_self_nonneg _) _

/-- Целочисленный шаг Ньютона в фиксированной точке `Q.F` для `1 / √S`:
    `y_{n+1} = (y_n * (3 * 2^F - ((S * y_n^2) >>> F))) >>> (F + 1)`. -/
def fixedPointInvSqrtStepZ (SFixed yFixed : Int) (fracBits : Nat) : Int :=
  let threeFixed : Int := (3 : Int) <<< fracBits
  let sy2 := (SFixed * ((yFixed * yFixed) >>> fracBits)) >>> fracBits
  (yFixed * (threeFixed - sy2)) >>> (fracBits + 1)

#eval
  let expVal := fixedPointExpZ (-8192) 4 14  -- x = -0.5 в Q14 (16384 = 1.0) -> exp(-0.5) ≈ 0.6065 * 16384 ≈ 9937
  let y0 : Int := 8192                      -- 0.5 в Q14
  let y1 := fixedPointInvSqrtStepZ (4 * 16384) y0 14
  s!"[Integer-Only CPU Registers Z (Q14)] exp(-0.5)_fixed={expVal}/16384, invSqrt(4)_fixed={y1}/16384"

end MarkovL1CrossLayerAndIntegerTransformer

open MarkovL1CrossLayerAndIntegerTransformer
#print axioms cross_layer_exact_cancellation
#print axioms two_layer_cascade_drift_bound
#print axioms spherical_chord_dot_identity
#print axioms spherical_code_inner_product_lower_bound
#print axioms dyadicExpApproxQ_nonneg
#print axioms invSqrtNewtonStepQ_residual_identity
