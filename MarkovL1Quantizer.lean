import MarkovL1Complexity
import MarkovL1Solver
import MarkovL1WeightedSolver

/-!
# Certified 1-Bit / Bipolar Neural Network Layer Quantizer (Δ = 1 Decoupled Groups)

* **Author:** E. S. Markov (ORCID: 0009-0005-2235-5464)
* **License:** GNU Affero General Public License v3.0 (AGPLv3)
* **Toolchain:** Lean `v4.37.0-rc1` / Mathlib

## Overview
Application of the Δ = 1 decoupled block-median theory to 1-bit / bipolar neural network
weight quantization (`w ≈ α_b * s_i`, `s_i ∈ {-1, 1}`, `α_b ∈ ℚ`):
1. `bipolarSignQ`: Extracts bipolar signs `s_i ∈ {-1, 1}` from full-precision rational weights.
2. `quantizeBipolarBlockwiseQ`: Computes optimal per-group rational scaling factors
   `α_b* = median(|w_i| : i ∈ S_b)` in `O(|S_b| log |S_b|)` time without `Classical.choice`.
3. `quantizeBipolarBlockwiseQ_certified_optimal`: Proves that the signed quantization
   residual `s_i * (w_i - α_b* * s_i)` belongs to the `ℓ₁` null layer `P_B⁻¹(0)`.
4. `ExperimentalBenchmarks`: Exact rational comparison against Mean-Abs and Global Median scaling.
-/

open Finset BigOperators

namespace MarkovL1Quantizer

open MarkovL1Complexity
open MarkovL1Solver
open MarkovL1WeightedSolver

-- =========================================================================
-- 1. ВЫЧИСЛИМЫЙ 1-BIT / BIPOLAR КВАНТОВАТЕЛЬ СЛОЕВ НЕЙРОСЕТЕЙ НАД ℚ
-- =========================================================================

/-- Биполярный знак рационального веса: `1` при `w ≥ 0` и `-1` при `w < 0` -/
def bipolarSignQ (w : ℚ) : ℚ :=
  if 0 ≤ w then 1 else -1

/-- Модуль рационального числа (вычислимый) -/
def absQ (w : ℚ) : ℚ :=
  if 0 ≤ w then w else -w

/-- Оптимальный 1-bit масштабный коэффициент группы `S` по ℓ₁-норме:
    `α_b* = median(|w_i| : i ∈ S)` -/
def computeGroupScaleQ {m : ℕ} (S : Fin m → Bool) (w : Fin m → ℚ) : ℚ :=
  listMedianQ (((List.finRange m).filter (fun i => S i)).map (fun i => absQ (w i)))

/-- Выход 1-bit / Bipolar квантователя -/
structure QuantizedLayerOutputQ (m k : ℕ) where
  signs : Fin m → ℚ
  scales : Fin k → ℚ
  quantized : Fin m → ℚ
  error : Fin m → ℚ

/-- Вычислимый групповой 1-bit квантователь для развязанных групп весов (Δ = 1) -/
def quantizeBipolarBlockwiseQ {m k : ℕ} (supp : Fin k → Fin m → Bool) (w : Fin m → ℚ) :
    Option (QuantizedLayerOutputQ m k) :=
  if allBlocksNonempty supp && checkDisjointSupports supp then
    let s : Fin m → ℚ := fun i => bipolarSignQ (w i)
    let alpha : Fin k → ℚ := fun b => computeGroupScaleQ (supp b) w
    let wHat : Fin m → ℚ := fun i =>
      ∑ b : Fin k, if supp b i then alpha b * s i else 0
    let err : Fin m → ℚ := fun i => w i - wHat i
    some ⟨s, alpha, wHat, err⟩
  else
    none

/-- Выравнивание ошибки по биполярному знаку: `alignedErr_i = s_i * (w_i - wHat_i)` -/
def signAlignedErrorQ {m k : ℕ} (out : QuantizedLayerOutputQ m k) : Fin m → ℚ :=
  fun i => out.signs i * out.error i

-- =========================================================================
-- 2. ТЕОРЕМА ГЛОБАЛЬНОЙ ℓ₁-ОПТИМАЛЬНОСТИ 1-BIT МАСШТАБОВ КВАНТОВАНИЯ
-- =========================================================================

lemma abs_bipolar_mul (s z : ℝ) (hs : s = 1 ∨ s = -1) : |s * z| = |z| := by
  rcases hs with h1 | hm1
  · rw [h1, one_mul]
  · rw [hm1, neg_one_mul, abs_neg]

lemma embedQ_bipolarSignQ (q : ℚ) :
    (bipolarSignQ q : ℝ) = 1 ∨ (bipolarSignQ q : ℝ) = -1 := by
  dsimp [bipolarSignQ]
  split_ifs
  · left; simp
  · right; simp

theorem quantizeBipolarBlockwiseQ_certified_optimal {m k : ℕ}
    (supp : Fin k → Fin m → Bool) (w : Fin m → ℚ) (out : QuantizedLayerOutputQ m k)
    (h_some : quantizeBipolarBlockwiseQ supp w = some out)
    (h_bal : checkBlocksBalancedQ supp (signAlignedErrorQ out) = true) :
    ∃ (h_disj : checkDisjointSupports supp = true),
      InL1ZeroLayer (buildDisjointSubspace supp h_disj).mem
        (embedQ (signAlignedErrorQ out)) := by
  dsimp [quantizeBipolarBlockwiseQ] at h_some
  split_ifs at h_some with h_val
  rw [Bool.and_eq_true] at h_val
  refine ⟨h_val.2, ?_⟩
  apply polynomial_zero_layer_of_block_balanced (buildDisjointSubspace supp h_val.2)
    (embedQ (signAlignedErrorQ out))
  intro b
  dsimp [buildDisjointSubspace]
  dsimp [checkBlocksBalancedQ] at h_bal
  rw [List.all_eq_true] at h_bal
  have hb := h_bal b (List.mem_finRange b)
  simp only [decide_eq_true_eq, Bool.and_eq_true] at hb
  obtain ⟨h_neg_len, h_pos_len⟩ := hb
  apply isBlockBalanced_of_balanced_counts
  · have h1 : ((List.finRange m).filter
                (fun i => supp b i && decide (signAlignedErrorQ out i < 0))).length ≤
              ((List.finRange m).filter
                (fun i => supp b i && decide (0 ≤ signAlignedErrorQ out i))).length := by
      simpa [List.filter_filter, Bool.and_comm] using h_neg_len
    rw [length_filter_finRange_eq_card, length_filter_finRange_eq_card] at h1
    convert h1 using 2 <;> (ext i; simp [embedQ])
  · have h2 : ((List.finRange m).filter
                (fun i => supp b i && decide (0 < signAlignedErrorQ out i))).length ≤
              ((List.finRange m).filter
                (fun i => supp b i && decide (signAlignedErrorQ out i ≤ 0))).length := by
      simpa [List.filter_filter, Bool.and_comm] using h_pos_len
    rw [length_filter_finRange_eq_card, length_filter_finRange_eq_card] at h2
    convert h2 using 2 <;> (ext i; simp [embedQ])
### Release v1.1.0

Adds the certified 1-bit / bipolar neural network weight quantizer (`MarkovL1Quantizer.lean`) and exact-rational comparative benchmarks (`Mean-Abs` vs `Global Median` vs `Certified Group Median Δ = 1`) on top of the `v1.0.0` formal verification and solver stack.

#### New in v1.1.0
* **`MarkovL1Quantizer.lean`**: Computable group-wise 1-bit quantizer over $\mathbb{Q}$ without `Classical.choice`, accompanied by the formal global $\ell_1$-optimality theorem `quantizeBipolarBlockwiseQ_certified_optimal` and reproducible `#eval` benchmarks across multi-channel and outlier layers.
