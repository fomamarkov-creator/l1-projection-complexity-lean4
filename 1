import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fast O(n²) Freivalds Inference Certificates and Master End-to-End V-CORE Pipeline Theorem

* **Author:** E. S. Markov (ORCID: 0009-0005-2235-5464)
* **Affiliation:** Independent Researcher, Astrakhan, Russia
* **Repository:** https://github.com/fomamarkov-creator/l1-projection-complexity-lean4
* **License:** GNU Affero General Public License v3.0 (AGPLv3)
* **Toolchain:** Lean `v4.37.0-rc1` / Mathlib

## Overview
Completes the 20-module verified V-CORE stack with fast inference integrity verification and
a unified master error bound combining lattice quantization with low-rank `ℓ₁`-LoRA:
1. **O(n²) Freivalds Matrix-Multiplication Certificate (`verifyMatMulFreivaldsQ`):**
   Verifies claimed quantized matrix products `C = A · B` in `O(n²)` operations via `A · (B · r) = C · r`,
   with proved associative algebraic soundness (`matMul_vec_assoc`).
2. **Master V-CORE Hybrid Pipeline Bound (`vcore_full_pipeline_master_bound`):**
   Unifies lattice quantization (`D₄` / `E₈` / `Λ₂₄`) and data-free `ℓ₁`-LoRA residual
   compensation into a single end-to-end neuron output guarantee.
-/

namespace MarkovL1ZeroKnowledgeInferenceCert

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
-- 1. БЫСТРАЯ O(n²) ВЕРИФИКАЦИЯ МАТРИЧНЫХ ВЫЧИСЛЕНИЙ (СЕРТИФИКАТ ФРЕЙВАЛДСА)
-- =========================================================================

abbrev VecQ := List ℚ
abbrev MatQ := List (List ℚ)

def dotQ (u v : VecQ) : ℚ :=
  (List.zipWith (· * ·) u v).sum

/-- Умножение матрицы на вектор за O(n²) операций -/
def matVecMulQ (M : MatQ) (v : VecQ) : VecQ :=
  M.map (fun row => dotQ row v)

/-- Вычислимый O(n²) верификатор Фрейвалдса: проверяет `A · (B · r) = C · r` -/
def verifyMatMulFreivaldsQ (A B C : MatQ) (r : VecQ) : Bool :=
  let br := matVecMulQ B r
  let abr := matVecMulQ A br
  let cr := matVecMulQ C r
  decide (abr = cr)

lemma dotQ_zeros_left :
    ∀ (n : Nat) (r : VecQ), dotQ (List.replicate n 0) r = 0
  | 0, _ => by simp [dotQ]
  | n + 1, [] => by simp [dotQ]
  | n + 1, x :: xs => by
      simp only [List.replicate, dotQ, List.zipWith_cons_cons, List.sum_cons, zero_mul, zero_add]
      exact dotQ_zeros_left n xs

lemma dotQ_scale_add :
    ∀ (c : ℚ) (row acc r : VecQ),
      row.length = acc.length →
      dotQ (List.zipWith (fun a b => c * a + b) row acc) r =
      c * dotQ row r + dotQ acc r
  | _, [], [], _, _ => by simp [dotQ]
  | _, [], _ :: _, _, hlen => by simp at hlen
  | _, _ :: _, [], _, hlen => by simp at hlen
  | _, _ :: _, _ :: _, [], _ => by simp [dotQ]
  | c, a :: aRest, b :: bRest, x :: xRest, hlen => by
      have ih := dotQ_scale_add c aRest bRest xRest (by simpa using hlen)
      simp only [dotQ, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
      have h_step : (c * a + b) * x = c * (a * x) + b * x := by ring
      linarith

def matMulRowQ (rowA : VecQ) (B : MatQ) (cols : Nat) : VecQ :=
  List.foldr (fun (ai, rowB) acc => List.zipWith (fun b c => ai * b + c) rowB acc)
    (List.replicate cols 0) (List.zip rowA B)

lemma matMulRowQ_length :
    ∀ (rowA : VecQ) (B : MatQ) (cols : Nat),
      (∀ row ∈ B, row.length = cols) →
      (matMulRowQ rowA B cols).length = cols
  | [], _, cols, _ => by simp [matMulRowQ]
  | _ :: _, [], cols, _ => by simp [matMulRowQ]
  | ai :: aRest, rowB :: bRest, cols, hB => by
      have hB0 : rowB.length = cols := hB rowB List.mem_cons_self
      have hB_rest : ∀ row ∈ bRest, row.length = cols := fun row hr =>
        hB row (List.mem_cons_of_mem _ hr)
      have ih := matMulRowQ_length aRest bRest cols hB_rest
      simp only [matMulRowQ, List.zip_cons_cons, List.foldr_cons, List.length_zipWith] at ih ⊢
      omega

/-- Теорема 1.1 (Ассоциативность матрично-векторного действия `(A · B) · r = A · (B · r)`):
    основа корректности алгоритма Фрейвалдса над точными рациональными числами `ℚ`. -/
theorem matMul_vec_assoc :
    ∀ (A B : MatQ) (r : VecQ),
      (∀ row ∈ B, row.length = r.length) →
      matVecMulQ (A.map (fun rowA => matMulRowQ rowA B r.length)) r =
      matVecMulQ A (matVecMulQ B r)
  | [], _, _, _ => by simp [matVecMulQ]
  | rowA :: restA, B, r, hB => by
      simp only [matVecMulQ, List.map_cons]
      congr 1
      · induction rowA generalizing B with
        | nil =>
            simp only [matMulRowQ, List.zip_nil_left, List.foldr_nil]
            exact dotQ_zeros_left r.length r
        | cons ai aRest ihA =>
            cases B with
            | nil =>
                simp only [matMulRowQ, List.zip_nil_right, List.foldr_nil]
                exact dotQ_zeros_left r.length r
            | cons rowB bRest =>
                have hB0 : rowB.length = r.length := hB rowB List.mem_cons_self
                have hB_rest : ∀ row ∈ bRest, row.length = r.length := fun row hr =>
                  hB row (List.mem_cons_of_mem _ hr)
                have hlen_acc : (matMulRowQ aRest bRest r.length).length = r.length :=
                  matMulRowQ_length aRest bRest r.length hB_rest
                have hlen_eq : rowB.length = (matMulRowQ aRest bRest r.length).length := by
                  omega
                have h_step : matMulRowQ (ai :: aRest) (rowB :: bRest) r.length =
                    List.zipWith (fun b c => ai * b + c) rowB (matMulRowQ aRest bRest r.length) := by
                  simp [matMulRowQ]
                rw [h_step, dotQ_scale_add ai rowB _ r hlen_eq, ihA bRest hB_rest]
                simp [dotQ]
      · exact matMul_vec_assoc restA B r hB
-- =========================================================================
-- 2. МАСТЕР-ТЕОРЕМА ПОЛНОГО ГИБРИДНОГО ПАЙПЛАЙНА V-CORE (LATTICE + ℓ₁-LORA)
-- =========================================================================

def l1VecQ (xs : VecQ) : ℚ :=
  (xs.map absQ).sum

def checkInfBoundQ (xs : VecQ) (B : ℚ) : Bool :=
  xs.all (fun x => decide (absQ x ≤ B))

/-- Полный сертифицированный вектор весов гибридного слоя V-CORE:
    `wHybrid = wLattice + wLoraCorrection` -/
def hybridWeightsQ (wLat wLora : VecQ) : VecQ :=
  List.zipWith (· + ·) wLat wLora

/-- Вычислимая проверка полного сертификата гибридного слоя V-CORE -/
def verifyHybridLayerCertQ (w wLat wLora x : VecQ) (ε_final B_X : ℚ) : Bool :=
  let wHyb := hybridWeightsQ wLat wLora
  let residual := List.zipWith (· - ·) wHyb w
  decide (w.length = wLat.length ∧ wLat.length = wLora.length ∧ w.length = x.length ∧
          0 ≤ B_X ∧ l1VecQ residual ≤ ε_final) &&
  checkInfBoundQ x B_X

/-- Теорема 2.1 (Мастер-теорема сквозной точности гибридного слоя V-CORE):
    если `verifyHybridLayerCertQ w wLat wLora x ε_final B_X = true`, то фактическое
    отклонение выхода нейрона `|(wLat + wLora) · x - w · x|` гарантированно
    не превосходит `ε_final * B_X`. -/
theorem vcore_full_pipeline_master_bound (w wLat wLora x : VecQ) (ε_final B_X : ℚ)
    (hcert : verifyHybridLayerCertQ w wLat wLora x ε_final B_X = true) :
    absQ (dotQ (hybridWeightsQ wLat wLora) x - dotQ w x) ≤ ε_final * B_X := by
  dsimp [verifyHybridLayerCertQ] at hcert
  rw [Bool.and_eq_true, decide_eq_true_eq] at hcert
  obtain ⟨⟨hlen1, hlen2, hlen3, hBX, herr_le⟩, hx_inf⟩ := hcert
  have hlen_hyb : (hybridWeightsQ wLat wLora).length = w.length := by
    simp [hybridWeightsQ, List.length_zipWith, hlen1, hlen2]
  have h_diff : ∀ (u v z : VecQ), u.length = v.length →
      dotQ u z - dotQ v z = dotQ (List.zipWith (· - ·) u v) z := by
    intro u
    induction u with
    | nil =>
        intro v z huv
        cases v with
        | nil => simp [dotQ]
        | cons _ _ => simp at huv
    | cons a aRest ih =>
        intro v z huv
        cases v with
        | nil => simp at huv
        | cons b bRest =>
            cases z with
            | nil => simp [dotQ]
            | cons c cRest =>
                simp only [dotQ, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
                have h_sub := ih bRest cRest (by simpa using huv)
                have h_alg : a * c - b * c = (a - b) * c := by ring
                linarith
  rw [h_diff (hybridWeightsQ wLat wLora) w x hlen_hyb]
  have h_holder : ∀ (es zs : VecQ),
      es.length = zs.length →
      (∀ z ∈ zs, absQ z ≤ B_X) →
      absQ (dotQ es zs) ≤ l1VecQ es * B_X := by
    intro es
    induction es with
    | nil =>
        intro zs _ _
        simp [dotQ, l1VecQ, absQ]
    | cons e eRest ih =>
        intro zs hlen_ez hz_b
        cases zs with
        | nil => simp at hlen_ez
        | cons z zRest =>
            have hz0 : absQ z ≤ B_X := hz_b z List.mem_cons_self
            have hz_r : ∀ z' ∈ zRest, absQ z' ≤ B_X := fun z' hz' =>
              hz_b z' (List.mem_cons_of_mem _ hz')
            have ih_step := ih zRest (by simpa using hlen_ez) hz_r
            have h_tri := absQ_add_le (e * z) (dotQ eRest zRest)
            rw [absQ_mul] at h_tri
            have h_mul : absQ e * absQ z ≤ absQ e * B_X :=
              mul_le_mul_of_nonneg_left hz0 (absQ_nonneg e)
            simp only [dotQ, List.zipWith_cons_cons, List.sum_cons, l1VecQ, List.map_cons] at ih_step h_tri ⊢
            have h_dist : (absQ e + (eRest.map absQ).sum) * B_X = absQ e * B_X + (eRest.map absQ).sum * B_X := by ring
            linarith
  have hlen_res : (List.zipWith (· - ·) (hybridWeightsQ wLat wLora) w).length = x.length := by
    simp [List.length_zipWith, hlen_hyb, hlen3]
  have hx_all : ∀ z ∈ x, absQ z ≤ B_X := by
    intro z hz
    have hall := List.all_eq_true.mp hx_inf z hz
    exact decide_eq_true_eq.mp hall
  have h_bound := h_holder _ x hlen_res hx_all
  have h_mono : l1VecQ (List.zipWith (· - ·) (hybridWeightsQ wLat wLora) w) * B_X ≤ ε_final * B_X :=
    mul_le_mul_of_nonneg_right herr_le hBX
  linarith

-- =========================================================================
-- ИСПОЛНЯЕМЫЕ ТЕСТЫ (#eval) И ПРОВЕРКА АКСИОМАТИЧЕСКОЙ ЧИСТОТЫ
-- =========================================================================

#eval
  let A : MatQ := [[1/1, 2/1], [3/1, 4/1]];
  let B : MatQ := [[2/1, 0/1], [1/1, 2/1]];
  let C_valid : MatQ := [[4/1, 4/1], [10/1, 8/1]];
  let C_corrupt : MatQ := [[4/1, 4/1], [10/1, 9/1]];
  let r : VecQ := [1/1, 3/1];
  let okValid := verifyMatMulFreivaldsQ A B C_valid r;
  let okCorrupt := verifyMatMulFreivaldsQ A B C_corrupt r;
  s!"[O(n²) Freivalds Cert] validMatMul={okValid}, corruptedMatMulRejected={!okCorrupt}"

#eval
  let w : VecQ := [1/2, -1/2, 3/4, -1/4];
  let wLat : VecQ := [1/2, -1/2, 1/2, -1/2];
  let wLora : VecQ := [0/1, 0/1, 1/4, 1/4];
  let x : VecQ := [2/1, -1/1, 3/2, -2/1];
  let certOK := verifyHybridLayerCertQ w wLat wLora x (1/10) (2/1);
  let actualErr := absQ (dotQ (hybridWeightsQ wLat wLora) x - dotQ w x);
  s!"[Master V-CORE Pipeline Cert] verified={certOK}, actualOutputDrift={actualErr} ≤ maxCertBound={(1/10 : ℚ) * 2}"

end MarkovL1ZeroKnowledgeInferenceCert

#print axioms MarkovL1ZeroKnowledgeInferenceCert.matMul_vec_assoc
#print axioms MarkovL1ZeroKnowledgeInferenceCert.vcore_full_pipeline_master_bound
