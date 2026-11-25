import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Certified Mixture-of-Experts (MoE) Top-K Routing Stability and Optimal Mixed-Precision Bit-Allocation

* **Author:** E. S. Markov (ORCID: 0009-0005-2235-5464)
* **Affiliation:** Independent Researcher, Astrakhan, Russia
* **Repository:** https://github.com/fomamarkov-creator/l1-projection-complexity-lean4
* **License:** GNU Affero General Public License v3.0 (AGPLv3)
* **Toolchain:** Lean `v4.37.0-rc1` / Mathlib

## Overview
Addresses two critical architectural challenges for large-scale sparse and mixed-precision LLMs:
1. **MoE Top-K Routing Invariance (`moe_pair_order_invariant`, `verifyMoERoutingSafety`):**
   Proves that if the routing logit margin between a selected expert `i` and a non-selected
   expert `j` satisfies `g_i - g_j > δ_i + δ_j` (where `δ_k = ε_k · ‖x‖∞`), then quantized
   routing `ĝ` preserves the exact expert selection (`ĝ_i > ĝ_j`).
2. **Optimal Mixed-Precision Bit-Allocation Solver (`solveMixedPrecisionDPQ`):** Exact rational
   dynamic programming solver assigning quantization modes (`E₈ 0.99b`, `D₄ 1.16b`, `1.58b`, `3.16b`)
   across layers to minimize total certified distortion under a strict memory budget `B_max`,
   backed by `solveMixedPrecisionDPQ_budget_sound`.
-/

namespace MarkovL1MoERoutingAndDynamicBits

/-- Конструктивный модуль над ℚ без `Classical.choice` -/
def absQ (x : ℚ) : ℚ :=
  if 0 ≤ x then x else -x

lemma absQ_le_iff {x b : ℚ} : absQ x ≤ b ↔ -b ≤ x ∧ x ≤ b := by
  unfold absQ
  split_ifs with h
  · constructor
    · intro hxb; exact ⟨by linarith, hxb⟩
    · intro ⟨_, hxb⟩; exact hxb
  · have hlt : x < 0 := lt_of_not_ge h
    constructor
    · intro hxb; exact ⟨by linarith, by linarith⟩
    · intro ⟨hnb, _⟩; linarith

-- =========================================================================
-- 1. ТЕОРЕМА УСТОЙЧИВОСТИ TOP-K МАРШРУТИЗАЦИИ MIXTURE-OF-EXPERTS (MoE)
-- =========================================================================

/-- Теорема 1.1 (Сохранение относительного порядка двух экспертов при квантовании гейта):
    Если исходные логиты маршрутизатора удовлетворяют `g_i - g_j > δ_i + δ_j`,
    а ошибки квантования ограничены `|ĝ_i - g_i| ≤ δ_i` и `|ĝ_j - g_j| ≤ δ_j`,
    то квантованный маршрутизатор строго сохраняет выбор эксперта `i` над `j` (`ĝ_i > ĝ_j`). -/
theorem moe_pair_order_invariant (g_i g_j gHat_i gHat_j δ_i δ_j : ℚ)
    (hi : absQ (gHat_i - g_i) ≤ δ_i)
    (hj : absQ (gHat_j - g_j) ≤ δ_j)
    (hmargin : δ_i + δ_j < g_i - g_j) :
    gHat_j < gHat_i := by
  rw [absQ_le_iff] at hi hj
  linarith

/-- Вычислимая проверка безопасности Top-K маршрутизации для выбранного множества
    индексов `selected` против всех отброшенных экспертов `rejected`:
    каждый элемент представлен парой `(исходный_логит, граница_ошибки_δ)`. -/
def verifyMoERoutingSafety (selected rejected : List (ℚ × ℚ)) : Bool :=
  selected.all fun (g_i, δ_i) =>
    rejected.all fun (g_j, δ_j) =>
      decide (δ_i + δ_j < g_i - g_j)

/-- Теорема 1.2 (Звучность сертификата безопасности MoE маршрутизатора):
    если `verifyMoERoutingSafety selected rejected = true`, то для ЛЮБОЙ пары
    `(i ∈ selected, j ∈ rejected)` при любых допустимых ошибках квантования
    выбранный эксперт `i` гарантированно получает больший квантованный логит, чем `j`. -/
theorem verifyMoERoutingSafety_sound (selected rejected : List (ℚ × ℚ))
    (hsafe : verifyMoERoutingSafety selected rejected = true) :
    ∀ p_i ∈ selected, ∀ p_j ∈ rejected,
      ∀ (gHat_i gHat_j : ℚ),
        absQ (gHat_i - p_i.1) ≤ p_i.2 →
        absQ (gHat_j - p_j.1) ≤ p_j.2 →
        gHat_j < gHat_i := by
  intro p_i hp_i p_j hp_j gHat_i gHat_j hi hj
  dsimp [verifyMoERoutingSafety] at hsafe
  have h1 := List.all_eq_true.mp hsafe p_i hp_i
  have h2 := List.all_eq_true.mp h1 p_j hp_j
  have hmargin : p_i.2 + p_j.2 < p_i.1 - p_j.1 := decide_eq_true_eq.mp h2
  exact moe_pair_order_invariant p_i.1 p_j.1 gHat_i gHat_j p_i.2 p_j.2 hi hj hmargin
-- =========================================================================
-- 2. ОПТИМАЛЬНОЕ РАСПРЕДЕЛЕНИЕ БИТНОСТИ ПО СЛОЯМ ПРИ БЮДЖЕТЕ ПАМЯТИ B_max
-- =========================================================================

/-- Вариант квантования одного слоя:
    `modeId` — код режима (0 = E₈ 0.99b, 1 = D₄ 1.16b, 2 = 1.58b, 3 = 3.16b),
    `memCost` — целочисленный размер в единицах памяти (в мегабайтах),
    `weightedDistortion` — сертифицированная взвешенная ошибка `S_l · ε_{l,m}`. -/
structure LayerOption where
  modeId : Nat
  memCost : Nat
  weightedDistortion : ℚ
  deriving Repr, DecidableEq

/-- Суммарный расход памяти для выбранного списка режимов по слоям -/
def totalMemoryCost (plan : List LayerOption) : Nat :=
  (plan.map LayerOption.memCost).sum

/-- Суммарная взвешенная ошибка для выбранного плана квантования -/
def totalPlanDistortion (plan : List LayerOption) : ℚ :=
  (plan.map LayerOption.weightedDistortion).sum

/-- Точный комбинаторный решатель (Branch-and-Bound / DP по бюджету памяти):
    находит план квантования с минимальной суммарной ошибкой при ограничении
    `totalMemoryCost plan ≤ budget`. -/
def solveMixedPrecisionDPQ (budget : Nat) : List (List LayerOption) → Option (List LayerOption)
  | [] => some []
  | opts :: rest =>
      let candidates := opts.filterMap fun opt =>
        if opt.memCost ≤ budget then
          match solveMixedPrecisionDPQ (budget - opt.memCost) rest with
          | none => none
          | some subPlan => some (opt :: subPlan)
        else
          none
      candidates.foldl (fun best cand =>
        match best with
        | none => some cand
        | some b =>
            if totalPlanDistortion cand < totalPlanDistortion b then some cand else some b) none

/-- Теорема 2.1 (Гарантия соблюдения бюджета памяти):
    если `solveMixedPrecisionDPQ budget layers = some plan`, то суммарный размер
    квантованной модели строго не превосходит заданный лимит `budget`. -/
theorem solveMixedPrecisionDPQ_budget_sound :
    ∀ (budget : Nat) (layers : List (List LayerOption)) (plan : List LayerOption),
      solveMixedPrecisionDPQ budget layers = some plan →
      totalMemoryCost plan ≤ budget
  | budget, [], plan, h => by
      dsimp [solveMixedPrecisionDPQ] at h
      injection h with h_eq
      subst h_eq
      simp [totalMemoryCost]
  | budget, opts :: rest, plan, h => by
      dsimp [solveMixedPrecisionDPQ] at h
      have h_fold : ∀ (cands : List (List LayerOption)) (acc : Option (List LayerOption)),
          (∀ p, acc = some p → totalMemoryCost p ≤ budget) →
          (∀ c ∈ cands, totalMemoryCost c ≤ budget) →
          ∀ res, (cands.foldl (fun best cand =>
            match best with
            | none => some cand
            | some b =>
                if totalPlanDistortion cand < totalPlanDistortion b then some cand else some b) acc) = some res →
          totalMemoryCost res ≤ budget := by
        intro cands
        induction cands with
        | nil =>
            intro acc hacc _ res hres
            exact hacc res hres
        | cons c tail ih =>
            intro acc hacc hcands res hres
            dsimp [List.foldl] at hres
            apply ih _ _ (fun c' hc' => hcands c' (List.mem_cons_of_mem _ hc')) res hres
            intro p hp
            cases acc with
            | none =>
                injection hp with hp_eq
                subst hp_eq
                exact hcands c List.mem_cons_self
            | some b =>
                dsimp only at hp
                split_ifs at hp
                · injection hp with hp_eq
                  subst hp_eq
                  exact hcands c List.mem_cons_self
                · exact hacc p hp
      apply h_fold _ none (fun _ hp => by contradiction) _ plan h
      intro c hc
      rcases List.mem_filterMap.mp hc with ⟨opt, _, hopt⟩
      split_ifs at hopt with hcost
      cases hsub : solveMixedPrecisionDPQ (budget - opt.memCost) rest with
      | none => rw [hsub] at hopt; contradiction
      | some subPlan =>
          rw [hsub] at hopt
          injection hopt with hc_eq
          subst hc_eq
          have ih := solveMixedPrecisionDPQ_budget_sound (budget - opt.memCost) rest subPlan hsub
          simp only [totalMemoryCost, List.map_cons, List.sum_cons] at ih ⊢
          omega

-- =========================================================================
-- ИСПОЛНЯЕМЫЕ ТЕСТЫ (#eval) И ПРОВЕРКА АКСИОМАТИЧЕСКОЙ ЧИСТОТЫ
-- =========================================================================

#eval
  let selected : List (ℚ × ℚ) := [(5/2, 1/10), (2/1, 1/10)];
  let rejected : List (ℚ × ℚ) := [(3/2, 1/10), (1/2, 1/10)];
  let isSafe := verifyMoERoutingSafety selected rejected;
  s!"[MoE Top-2 Routing Safety] invariantUnderQuantization={isSafe}"

#eval
  let layer0 : List LayerOption := [⟨0, 100, 12/1⟩, ⟨1, 120, 6/1⟩, ⟨2, 160, 2/1⟩];
  let layer1 : List LayerOption := [⟨0, 100, 3/1⟩,  ⟨1, 120, 2/1⟩, ⟨2, 160, 1/1⟩];
  let layer2 : List LayerOption := [⟨0, 100, 10/1⟩, ⟨1, 120, 5/1⟩, ⟨2, 160, 2/1⟩];
  let bestPlan := solveMixedPrecisionDPQ 400 [layer0, layer1, layer2];
  let modes := bestPlan.map (fun p => p.map LayerOption.modeId);
  let totalMem := bestPlan.map totalMemoryCost;
  let totalErr := bestPlan.map totalPlanDistortion;
  s!"[Mixed-Precision Optimal Allocation] modes={modes}, mem={totalMem}/400 MB, minWeightedErr={totalErr}"

end MarkovL1MoERoutingAndDynamicBits

-- Проверка аксиоматической чистоты:
#print axioms MarkovL1MoERoutingAndDynamicBits.moe_pair_order_invariant
#print axioms MarkovL1MoERoutingAndDynamicBits.verifyMoERoutingSafety_sound
#print axioms MarkovL1MoERoutingAndDynamicBits.solveMixedPrecisionDPQ_budget_sound
