import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith

namespace MarkovL1GeneralTreewidthFPT

/-- Конструктивный модуль над ℚ -/
def absQ (x : ℚ) : ℚ :=
  if 0 ≤ x then x else -x

/-- Целевая функция ℓ₁-ошибки для графа перекрытий степени Δ = 3 (древесная ширина k = 2),
    моделирующая совместное квантование троек связанных проекций (например, W_Q, W_K, W_V):
    на каждом окне длины 3 учитывается локальная ошибка |w_i - c_i| и тройная связь

    |w_{i+2} - (c_i + c_{i+1} + c_{i+2})|. -/
def tripleOverlapErrorQ (ws : List ℚ) (cs : List ℚ) : ℚ :=
  match ws, cs with

  | [w], c :: _ => absQ (w - c)
  | [w₁, w₂], c₁ :: c₂ :: _ => absQ (w₁ - c₁) + absQ (w₂ - c₂)
  | w₁ :: w₂ :: w₃ :: wRest, c₁ :: c₂ :: c₃ :: cRest =>

      absQ (w₁ - c₁) + absQ (w₃ - (c₁ + c₂ + c₃)) +
      tripleOverlapErrorQ (w₂ :: w₃ :: wRest) (c₂ :: c₃ :: cRest)
  | _, _ => 0

/-- Декартово произведение сетки `grid × grid` для мешков древесной ширины k = 2 -/
def gridPairs (grid : List ℚ) : List (ℚ × ℚ) :=
  grid.flatMap fun c₁ => grid.map fun c₂ => (c₁, c₂)

/-- Шаг динамического программирования по декомпозиции дерева ширины k = 2:
    состояния — пары `(c_{i-1}, c_i) ∈ grid²`, переход за `O(|grid|³)` -/
def dpStepTreewidth2Q (grid : List ℚ) (w_prev2 w_curr : ℚ)
    (prevDP : List ((ℚ × ℚ) × ℚ)) : List ((ℚ × ℚ) × ℚ) :=
  (gridPairs grid).map fun (c_mid, c_curr) =>
    let bestCost := prevDP.foldl (fun acc ((c_prev2, c_prev1), prevCost) =>
      if c_prev1 == c_mid then
        let stepCost := prevCost + absQ (w_prev2 - c_prev2) +
                        absQ (w_curr - (c_prev2 + c_mid + c_curr))
        if stepCost ≤ acc then stepCost else acc
      else acc
    ) 1000000000
    ((c_mid, c_curr), bestCost)
/-- Точный FPT-решатель за время `O(m * |grid|³)` для перекрытий степени Δ = 3 (treewidth k = 2) -/
def solveTripleOverlapFPT (grid : List ℚ) : List ℚ → ℚ
  | [] => 0
  | [w] =>
      grid.foldl (fun best c => min best (absQ (w - c))) 1000000000
  | [w₁, w₂] =>
      (gridPairs grid).foldl (fun best (c₁, c₂) =>
        min best (absQ (w₁ - c₁) + absQ (w₂ - c₂))) 1000000000
  | w₁ :: w₂ :: w₃ :: rest =>
      let initDP := (gridPairs grid).map fun pair => (pair, (0 : ℚ))
      let rec loop (wp2 wp1 wc : ℚ) (rem : List ℚ)
          (dp : List ((ℚ × ℚ) × ℚ)) : List ((ℚ × ℚ) × ℚ) :=
        let nextDP := dpStepTreewidth2Q grid wp2 wc dp
        match rem with
        | [] =>
            nextDP.map fun ((c_last2, c_last1), cost) =>
              ((c_last2, c_last1), cost + absQ (wp1 - c_last2) + absQ (wc - c_last1))
        | wNext :: wTail =>
            loop wp1 wc wNext wTail nextDP
      let finalDP := loop w₁ w₂ w₃ rest initDP
      finalDP.foldl (fun best (_, cost) => min best cost) 1000000000

/-- Теорема 1: Пустой вход дает нулевую ℓ₁-ошибку -/
theorem solveTripleOverlapFPT_nil (grid : List ℚ) :
    solveTripleOverlapFPT grid [] = 0 := rfl

/-- Теорема 2: Невозрастание стоимости при редукции по мешку treewidth = 2 -/
theorem foldl_min_pair_le_init (xs : List ((ℚ × ℚ) × ℚ)) (init : ℚ) :
    xs.foldl (fun best (_, cost) => min best cost) init ≤ init := by
  induction xs generalizing init with
  | nil => exact le_refl init
  | cons x xs ih =>
      simp only [List.foldl_cons]
      exact le_trans (ih (min init x.2)) (min_le_left init x.2)

-- Исполняемые тесты (#eval) для совместного квантования троек (W_Q, W_K, W_V)
#eval
  let grid : List ℚ := [-2/1, 0/1, 2/1, 4/1]
  let ws : List ℚ := [2/1, 0/1, 6/1, 4/1]
  let fptCost := solveTripleOverlapFPT grid ws
  let directErr := tripleOverlapErrorQ ws [2/1, 0/1, 4/1, 4/1]
  s!"[Treewidth k=2 (Δ=3) FPT] grid={grid}, ws={ws} -> FPT_min={fptCost}, directErr={directErr}"

end MarkovL1GeneralTreewidthFPT

-- Проверка аксиоматической чистоты:
#print axioms MarkovL1GeneralTreewidthFPT.solveTripleOverlapFPT
#print axioms MarkovL1GeneralTreewidthFPT.foldl_min_pair_le_init
