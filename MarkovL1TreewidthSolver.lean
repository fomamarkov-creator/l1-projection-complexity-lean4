import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith

/-!
# MarkovL1TreewidthSolver.lean

* **Author:** E. S. Markov (ORCID: 0009-0005-2235-5464)
* **Affiliation:** Independent Researcher, Astrakhan, Russia
* **Repository:** https://github.com/fomamarkov-creator/l1-projection-complexity-lean4
* **License:** GNU Affero General Public License v3.0 (AGPLv3)
* **Toolchain:** Lean `v4.37.0-rc1` / Mathlib

## Overview
# Fixed-Parameter Tractable (FPT) Dynamic Programming Solver for Δ = 2 Chain Overlaps
-/


namespace MarkovL1TreewidthSolver

/-- Ленточный граф перекрытий Δ = 2 (цепочка соседних взаимодействий w_i + w_{i+1},
    ширина дерева treewidth = 1). -/
def chainOverlapErrorQ (ws : List ℚ) (cs : List ℚ) : ℚ :=
  match ws, cs with

  | [w], c :: _ => |w - c|
  | w₁ :: w₂ :: wRest, c₁ :: c₂ :: cRest =>

      |w₁ - c₁| + |w₂ - (c₁ + c₂)| + chainOverlapErrorQ (w₂ :: wRest) (c₂ :: cRest)
  | _, _ => 0

/-- Шаг динамического программирования по дереву декомпозиции (Treewidth = 1):
    для каждого допустимого состояния c_curr ∈ grid выбирает оптимальное
    предыдущее состояние c_prev ∈ grid, минимизирующее суммарную ℓ₁-ошибку. -/
def dpStepQ (grid : List ℚ) (w_prev w_curr : ℚ) (prevDP : List (ℚ × ℚ)) : List (ℚ × ℚ) :=
  grid.map fun c_curr =>
    let best := prevDP.foldl (fun (bestCost, bestPrev) (prevCost, c_prev) =>
      let edgeCost := prevCost + |w_prev - c_prev| + |w_curr - (c_prev + c_curr)|
      if edgeCost ≤ bestCost then (edgeCost, c_prev) else (bestCost, bestPrev)
    ) (1000000000, 0)
    (best.1, c_curr)

/-- Полиномиальный FPT-решатель O(m * |grid|²) для Δ = 2 ленточных перекрытий над ℚ -/
def solveChainOverlapFPT (grid : List ℚ) : List ℚ → ℚ
  | [] => 0
  | [w] =>
      grid.foldl (fun best c => min best |w - c|) 1000000000
  | w₁ :: w₂ :: rest =>
      let initDP := grid.map fun c => ((0 : ℚ), c)
      let rec loop (wp wc : ℚ) (rem : List ℚ) (dp : List (ℚ × ℚ)) : List (ℚ × ℚ) :=
        let nextDP := dpStepQ grid wp wc dp
        match rem with
        | [] => nextDP
        | wNext :: wTail => loop wc wNext wTail nextDP
      let finalDP := loop w₁ w₂ rest initDP
      finalDP.foldl (fun best (cost, _) => min best cost) 1000000000

/-- Теорема 1: FPT-решатель на пустом входе возвращает точную нулевую ошибку -/
theorem solveChainOverlapFPT_nil (grid : List ℚ) :
    solveChainOverlapFPT grid [] = 0 := rfl

/-- Теорема 2: Монотонность шага редукции минимума в FPT-алгоритме -/
theorem foldl_min_le_init (xs : List ℚ) (init : ℚ) :
    xs.foldl min init ≤ init := by
  induction xs generalizing init with
  | nil => exact le_refl init
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact le_trans (ih (min init x)) (min_le_left init x)

end MarkovL1TreewidthSolver
