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

end MarkovL1CrossLayerAndIntegerTransformer

open MarkovL1CrossLayerAndIntegerTransformer
#print axioms cross_layer_exact_cancellation
#print axioms two_layer_cascade_drift_bound
#print axioms spherical_chord_dot_identity
#print axioms spherical_code_inner_product_lower_bound
#print axioms dyadicExpApproxQ_nonneg
#print axioms invSqrtNewtonStepQ_residual_identity
