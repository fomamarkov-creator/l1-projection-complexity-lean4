import MarkovL1Complexity

/-!
# Executable Certified ℓ₁ Metric Projection Solver (Δ = 1 Regime & Certificate Checker)

* **Author:** E. S. Markov (ORCID: 0009-0005-2235-5464)
* **License:** GNU Affero General Public License v3.0 (AGPLv3)
* **Toolchain:** Lean `v4.37.0-rc1` / Mathlib

## Overview
Constructive, computable counterpart to `MarkovL1Complexity.lean` operating over exact
rationals `ℚ` (zero `Classical.choice` in executable routines):
1. `checkDisjointSupports`: Decidable O(k² m) detector verifying pairwise disjointness
   of block supports (Δ = 1), constructing a certified `DisjointBlockSubspace`.
2. `solveDipoleBlockProjection`: Exact O(m) computable solver computing optimal block
   coefficients `c_b = (x(idx1 b) + x(idx2 b)) / 2`, projection `v* ∈ B`, and residual
   `r* = x - v*`, paired with a formal soundness proof (`r* ∈ P_B⁻¹(0)`).
3. `checkBipolarZeroLayerQ`: Executable polynomial-time certificate verifier for
   bipolar vectors in multidimensional `MultiSpan` null layers over `ℚ`.
-/

open Finset BigOperators

namespace MarkovL1Solver

open MarkovL1Complexity

-- =========================================================================
-- 1. ВЫЧИСЛИМЫЙ ДЕТЕКТОР РЕЖИМА Δ = 1 (РАЗВЯЗКА НОСИТЕЛЕЙ БЛОКОВ)
-- =========================================================================

/-- Вычислимая проверка попарной непересекаемости носителей k блоков в ℝ^m (Δ = 1) -/
def checkDisjointSupports {m k : ℕ} (supp : Fin k → Fin m → Bool) : Bool :=
  (List.finRange k).all fun b₁ =>
    (List.finRange k).all fun b₂ =>
      (List.finRange m).all fun i =>
        !(supp b₁ i && supp b₂ i) || decide (b₁ = b₂)

/-- Формальная корректность детектора: если `checkDisjointSupports supp = true`,
    то матрица индикаторов задает корректное `DisjointBlockSubspace m k` -/
theorem checkDisjointSupports_sound {m k : ℕ} (supp : Fin k → Fin m → Bool)
    (h_ok : checkDisjointSupports supp = true) :
    ∀ (b₁ b₂ : Fin k) (i : Fin m), supp b₁ i = true → supp b₂ i = true → b₁ = b₂ := by
  intro b₁ b₂ i hb₁ hb₂
  dsimp [checkDisjointSupports] at h_ok
  rw [List.all_eq_true] at h_ok
  have h1 := h_ok b₁ (List.mem_finRange b₁)
  rw [List.all_eq_true] at h1
  have h2 := h1 b₂ (List.mem_finRange b₂)
  rw [List.all_eq_true] at h2
  have h3 := h2 i (List.mem_finRange i)
  rw [hb₁, hb₂] at h3
  simp only [Bool.and_self, Bool.not_true, Bool.false_or, decide_eq_true_eq] at h3
  exact h3

/-- Конструктор сертифицированного развязанного подпространства из вычислимой проверки -/
def buildDisjointSubspace {m k : ℕ} (supp : Fin k → Fin m → Bool)
    (h_ok : checkDisjointSupports supp = true) : DisjointBlockSubspace m k where
  supp := supp
  disjoint := checkDisjointSupports_sound supp h_ok

-- =========================================================================
-- 2. ИСПОЛНЯЕМЫЙ O(m)-СОЛВЕР ДЛЯ ДИПОЛЬНЫХ БЛОЧНЫХ ПРОЕКЦИЙ НАД ℚ
-- =========================================================================

/-- Структура дипольной конфигурации: для каждого блока b ∈ Fin k указана пара индексов
    (idx1 b, idx2 b) его носителя -/
structure DipoleConfig (m k : ℕ) where
  idx1 : Fin k → Fin m
  idx2 : Fin k → Fin m

/-- Индикаторная функция носителей дипольных блоков -/
def DipoleConfig.supp {m k : ℕ} (cfg : DipoleConfig m k) (b : Fin k) (i : Fin m) : Bool :=
  decide (i = cfg.idx1 b || i = cfg.idx2 b)

/-- Вычислимая проверка корректности дипольной конфигурации (различие индексов в парах
    и отсутствие перекрытий между блоками, Δ = 1) -/
def DipoleConfig.isValid {m k : ℕ} (cfg : DipoleConfig m k) : Bool :=
  (List.finRange k).all (fun b => decide (cfg.idx1 b ≠ cfg.idx2 b)) &&
  checkDisjointSupports cfg.supp

/-- Результат работы вычислимого солвера над точными рациональными числами ℚ -/
structure SolverOutputQ (m k : ℕ) where
  coeffs : Fin k → ℚ
  projection : Fin m → ℚ
  residual : Fin m → ℚ

/-- Вычислимый O(m)-солвер оптимальной ℓ₁-проекции для развязанных дипольных блоков:
    на каждом блоке b вычисляет медианный коэффициент c_b = (x(idx1 b) + x(idx2 b)) / 2,
    восстанавливает проекцию v* ∈ B и остаток r* = x - v* -/
def solveDipoleBlockProjection {m k : ℕ} (cfg : DipoleConfig m k) (x : Fin m → ℚ) :
    Option (SolverOutputQ m k) :=
  if cfg.isValid then
    let c : Fin k → ℚ := fun b => (x (cfg.idx1 b) + x (cfg.idx2 b)) / 2
    let v : Fin m → ℚ := fun i =>
      ∑ b : Fin k, if cfg.supp b i then c b else 0
    let r : Fin m → ℚ := fun i => x i - v i
    some ⟨c, v, r⟩
  else
    none

/-- Вложение рационального вектора ℚ^m в вещественное пространство ℝ^m -/
def embedQ {m : ℕ} (x : Fin m → ℚ) : Fin m → ℝ :=
  fun i => (x i : ℝ)
-- =========================================================================
-- 3. ТЕОРЕМЫ ФОРМАЛЬНОЙ КОРРЕКТНОСТИ СОЛВЕРА (SOUNDNESS)
-- =========================================================================

/-- Теорема 1 (Принадлежность проекции подпространству):
    Если солвер вернул выход `out`, то вектор `embedQ out.projection` гарантированно
    принадлежит подпространству `B.mem` -/
theorem solveDipoleBlockProjection_mem_subspace {m k : ℕ} (cfg : DipoleConfig m k)
    (x : Fin m → ℚ) (out : SolverOutputQ m k)
    (h_some : solveDipoleBlockProjection cfg x = some out) :
    ∃ (h_disj : checkDisjointSupports cfg.supp = true),
      (buildDisjointSubspace cfg.supp h_disj).mem (embedQ out.projection) := by
  dsimp [solveDipoleBlockProjection] at h_some
  split_ifs at h_some with h_val
  injection h_some with h_eq
  subst h_eq
  dsimp [DipoleConfig.isValid] at h_val
  rw [Bool.and_eq_true] at h_val
  refine ⟨h_val.2, fun b => (out.coeffs b : ℝ), ?_⟩
  ext i
  dsimp [embedQ, DisjointBlockSubspace.eval, buildDisjointSubspace, out]
  push_cast
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp

/-- Теорема 2 (Главная теорема корректности солвера):
    Если `solveDipoleBlockProjection cfg x = some out`, то вещественный вектор остатка
    `embedQ out.residual` строго принадлежит нулевому слою `P_B⁻¹(0)`!
    Следовательно, `out.projection` является глобально оптимальной ℓ₁-проекцией `x` на `B`. -/
theorem solveDipoleBlockProjection_residual_in_zero_layer {m k : ℕ}
    (cfg : DipoleConfig m k) (x : Fin m → ℚ) (out : SolverOutputQ m k)
    (h_some : solveDipoleBlockProjection cfg x = some out) :
    ∃ (h_disj : checkDisjointSupports cfg.supp = true),
      InL1ZeroLayer (buildDisjointSubspace cfg.supp h_disj).mem (embedQ out.residual) := by
  dsimp [solveDipoleBlockProjection] at h_some
  split_ifs at h_some with h_val
  injection h_some with h_eq
  dsimp [DipoleConfig.isValid] at h_val
  rw [Bool.and_eq_true] at h_val
  obtain ⟨h_dist_all, h_disj⟩ := h_val
  refine ⟨h_disj, ?_⟩
  let B := buildDisjointSubspace cfg.supp h_disj
  apply dipole_pairs_in_polynomial_zero_layer B (embedQ out.residual) cfg.idx1 cfg.idx2
  · intro b i
    dsimp [B, buildDisjointSubspace, DipoleConfig.supp]
    simp only [decide_eq_true_eq, Bool.or_eq_true]
  · intro b
    rw [List.all_eq_true] at h_dist_all
    have hb := h_dist_all b (List.mem_finRange b)
    simpa using hb
  · intro b
    have h_res_def : out.residual = fun i =>
        x i - ∑ b' : Fin k, if cfg.supp b' i then (x (cfg.idx1 b') + x (cfg.idx2 b')) / 2 else 0 := by
      rw [← h_eq]
    have h_eval_idx1 : (∑ b' : Fin k, if cfg.supp b' (cfg.idx1 b) then
        (x (cfg.idx1 b') + x (cfg.idx2 b')) / 2 else 0) =
        (x (cfg.idx1 b) + x (cfg.idx2 b)) / 2 := by
      rw [Finset.sum_eq_single b]
      · have hs1 : cfg.supp b (cfg.idx1 b) = true := by
          dsimp [DipoleConfig.supp]; simp
        rw [hs1]; rfl
      · intro b' _ hb'_ne
        have hs_false : cfg.supp b' (cfg.idx1 b) = false := by
          cases h_v : cfg.supp b' (cfg.idx1 b)
          · rfl
          · have hs1 : cfg.supp b (cfg.idx1 b) = true := by dsimp [DipoleConfig.supp]; simp
            exact False.elim (hb'_ne (checkDisjointSupports_sound cfg.supp h_disj b' b _ h_v hs1))
        rw [hs_false]; rfl
      · intro h_nm; exact False.elim (h_nm (Finset.mem_univ b))
    have h_eval_idx2 : (∑ b' : Fin k, if cfg.supp b' (cfg.idx2 b) then
        (x (cfg.idx1 b') + x (cfg.idx2 b')) / 2 else 0) =
        (x (cfg.idx1 b) + x (cfg.idx2 b)) / 2 := by
      rw [Finset.sum_eq_single b]
      · have hs2 : cfg.supp b (cfg.idx2 b) = true := by
          dsimp [DipoleConfig.supp]; simp
        rw [hs2]; rfl
      · intro b' _ hb'_ne
        have hs_false : cfg.supp b' (cfg.idx2 b) = false := by
          cases h_v : cfg.supp b' (cfg.idx2 b)
          · rfl
          · have hs2 : cfg.supp b (cfg.idx2 b) = true := by dsimp [DipoleConfig.supp]; simp
            exact False.elim (hb'_ne (checkDisjointSupports_sound cfg.supp h_disj b' b _ h_v hs2))
        rw [hs_false]; rfl
      · intro h_nm; exact False.elim (h_nm (Finset.mem_univ b))
    dsimp [embedQ]
    rw [h_res_def]
    dsimp only
    rw [h_eval_idx1, h_eval_idx2]
    push_cast
    linarith

-- =========================================================================
-- 4. ВЫЧИСЛИМЫЙ ВЕРИФИКАТОР СЕРТИФИКАТОВ ДЛЯ МНОГОМЕРНЫХ СИСТЕМ MultiSpan
-- =========================================================================

/-- Полиномиальный верификатор принадлежности биполярного вектора u ∈ {-1, 1}^m
    нулевому слою многомерного подпространства MultiSpan A над ℚ -/
def checkBipolarZeroLayerQ {m r : ℕ} (A : Fin r → Fin m → ℚ) (u : Fin m → ℚ) : Bool :=
  (List.finRange m).all (fun i => decide (u i = 1 || u i = -1)) &&
  (List.finRange r).all (fun j => decide ((∑ i : Fin m, A j i * u i) = 0))

/-- Теорема 3 (Корректность вычислимого верификатора):
    Если `checkBipolarZeroLayerQ A u = true`, то `embedQ u` гарантированно принадлежит
    нулевому слою `P_{MultiSpan A}⁻¹(0)` в ℝ^m -/
theorem checkBipolarZeroLayerQ_sound {m r : ℕ} (A : Fin r → Fin m → ℚ) (u : Fin m → ℚ)
    (h_cert : checkBipolarZeroLayerQ A u = true) :
    InL1ZeroLayer (MultiSpan (fun j i => (A j i : ℝ))) (embedQ u) := by
  dsimp [checkBipolarZeroLayerQ] at h_cert
  rw [Bool.and_eq_true] at h_cert
  obtain ⟨h_bip_all, h_orth_all⟩ := h_cert
  apply (bipolar_multi_orth_iff_mem_zero_layer (fun j i => (A j i : ℝ)) (embedQ u) ?_).mpr
  · intro j
    rw [List.all_eq_true] at h_orth_all
    have hj := h_orth_all j (List.mem_finRange j)
    rw [decide_eq_true_eq] at hj
    have h_cast : (((∑ i : Fin m, A j i * u i : ℚ) : ℝ)) = 0 := by
      rw [hj, Rat.cast_zero]
    dsimp [embedQ]
    push_cast at h_cast
    exact h_cast
  · intro i
    rw [List.all_eq_true] at h_bip_all
    have hi := h_bip_all i (List.mem_finRange i)
    simp only [decide_eq_true_eq, Bool.or_eq_true] at hi
    dsimp [embedQ]
    rcases hi with h1 | hm1
    · left; rw [h1, Rat.cast_one]
    · right; rw [hm1, Rat.cast_neg, Rat.cast_one]

-- =========================================================================
-- 5. ИСПОЛНЯЕМЫЕ ТЕСТЫ (#eval) — ЗАПУСКАЮТСЯ ПРИ СБОРКЕ ПРОЕКТА
-- =========================================================================

section ExecutableTests

/-- Пример 1: Пространство ℝ⁴, 2 непересекающихся дипольных блока: {0, 1} и {2, 3} (Δ = 1) -/
def exampleDipoleCfg : DipoleConfig 4 2 where
  idx1 b := if b.val == 0 then 0 else 2
  idx2 b := if b.val == 0 then 1 else 3

/-- Входной вектор x = (10, 4, -6, 2) ∈ ℚ⁴ -/
def exampleInput : Fin 4 → ℚ
  | ⟨0, _⟩ => 10
  | ⟨1, _⟩ => 4
  | ⟨2, _⟩ => -6
  | ⟨3, _⟩ => 2

/-- Ожидаемый результат:
    c = (7, -2), проекция v* = (7, 7, -2, -2), сбалансированный остаток r* = (3, -3, -4, 4) ∈ P_B⁻¹(0) -/
#eval
  match solveDipoleBlockProjection exampleDipoleCfg exampleInput with
  | some out =>
      s!"[Delta=1 Solver OK] coeffs = ({out.coeffs 0}, {out.coeffs 1}), " ++
      s!"projection = ({out.projection 0}, {out.projection 1}, {out.projection 2}, {out.projection 3}), " ++
      s!"residual = ({out.residual 0}, {out.residual 1}, {out.residual 2}, {out.residual 3})"
  | none => "Overlap detected (Delta >= 2)"

/-- Пример 2: Вырожденный случай с перекрытием носителей {0, 1} и {1, 2} (Δ = 2) -> солвер корректно отклоняет -/
def overlappingCfg : DipoleConfig 4 2 where
  idx1 b := if b.val == 0 then 0 else 1
  idx2 b := if b.val == 0 then 1 else 2

#eval
  match solveDipoleBlockProjection overlappingCfg exampleInput with
  | some _ => "Unexpected success"
  | none => "[Delta=2 Detector OK] Overlap detected: safely rejected non-decoupled instance"

/-- Пример 3: Проверка биполярного сертификата u = (1, -1, 1, -1) для матрицы из 2 ограничений -/
def exampleMatrix : Fin 2 → Fin 4 → ℚ
  | ⟨0, _⟩, ⟨0, _⟩ => 1
  | ⟨0, _⟩, ⟨1, _⟩ => 1
  | ⟨0, _⟩, ⟨2, _⟩ => 1
  | ⟨0, _⟩, ⟨3, _⟩ => 1
  | ⟨1, _⟩, ⟨0, _⟩ => 1
  | ⟨1, _⟩, ⟨1, _⟩ => 2
  | ⟨1, _⟩, ⟨2, _⟩ => -1
  | ⟨1, _⟩, ⟨3, _⟩ => -2

def exampleCert : Fin 4 → ℚ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => -1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => -1

#eval s!"[MultiSpan Cert Verifier] valid = {checkBipolarZeroLayerQ exampleMatrix exampleCert}"

end ExecutableTests

end MarkovL1Solver

-- Проверка отсутствия аксиомы выбора Classical.choice в вычислимых функциях:
#print axioms MarkovL1Solver.checkDisjointSupports
#print axioms MarkovL1Solver.solveDipoleBlockProjection
#print axioms MarkovL1Solver.checkBipolarZeroLayerQ

-- Проверка аксиоматической чистоты теорем корректности:
#print axioms MarkovL1Solver.solveDipoleBlockProjection_mem_subspace
#print axioms MarkovL1Solver.solveDipoleBlockProjection_residual_in_zero_layer
#print axioms MarkovL1Solver.checkBipolarZeroLayerQ_sound
