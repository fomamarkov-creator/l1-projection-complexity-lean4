import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open Finset BigOperators

namespace MarkovL1TriangularActivation

/-- Конструктивный модуль над ℚ -/
def absQ (x : ℚ) : ℚ :=
  if 0 ≤ x then x else -x

/-- 1.58-bit тернарный квантователь скаляра -/
def quantizeScalarQ (θ α w : ℚ) : ℚ :=
  if absQ w ≤ θ then 0
  else if 0 ≤ w then α else -α

/-- Скорректированный вес на шаге `j` с учетом переноса ошибок квантования
    предыдущих каналов `i < j` через верхнетреугольный фактор корреляции `R`:
    `wTilde_j = w_j + ∑_{i < j} (w_i - wHat_i) * (R_{i,j} / R_{j,j})` -/
def adjustedWeightQ {g : ℕ} (R : Fin g → Fin g → ℚ) (w wHat : Fin g → ℚ) (j : Fin g) : ℚ :=
  w j + (∑ i ∈ Finset.univ.filter (fun i : Fin g => i.val < j.val),
    (w i - wHat i) * R i j) / R j j

/-- Главная теорема (Точная треугольная компенсация корреляций для произвольного блока `g`):
    если диагональные элементы верхнетреугольной матрицы `R` ненулевые (`R j j ≠ 0`),
    то выходная ℓ₁-ошибка на j-м канале `|∑_{i ≤ j} (w_i - wHat_i) * R_{i,j}|`
    ТОЖДЕСТВЕННО равна `|R_{j,j}| * |wTilde_j - wHat_j|` (0 sorrys). -/
theorem triangular_channel_exact_reduction {g : ℕ}
    (R : Fin g → Fin g → ℚ) (w wHat : Fin g → ℚ) (j : Fin g) (hRjj : R j j ≠ 0) :

    |∑ i ∈ Finset.univ.filter (fun i : Fin g => i.val ≤ j.val), (w i - wHat i) * R i j| =
      |R j j| * |adjustedWeightQ R w wHat j - wHat j| := by
  have h_split : (Finset.univ.filter (fun i : Fin g => i.val ≤ j.val)) =
      insert j (Finset.univ.filter (fun i : Fin g => i.val < j.val)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    omega
  have h_not_mem : j ∉ Finset.univ.filter (fun i : Fin g => i.val < j.val) := by
    simp
  rw [h_split, Finset.sum_insert h_not_mem]
  dsimp [adjustedWeightQ]
  have h_alg : (w j - wHat j) * R j j +
      ∑ i ∈ Finset.univ.filter (fun i : Fin g => i.val < j.val), (w i - wHat i) * R i j =
      R j j * (w j + (∑ i ∈ Finset.univ.filter (fun i : Fin g => i.val < j.val),
        (w i - wHat i) * R i j) / R j j - wHat j) := by
    field_simp
    ring
  rw [h_alg]
  set A := R j j
  set B := w j + (∑ i ∈ Finset.univ.filter (fun i : Fin g => i.val < j.val),
    (w i - wHat i) * R i j) / R j j - wHat j
  by_cases hA : 0 ≤ A <;> by_cases hB : 0 ≤ B
  · rw [abs_of_nonneg hA, abs_of_nonneg hB, abs_of_nonneg (mul_nonneg hA hB)]
  · have hB' : B < 0 := lt_of_not_ge hB
    rw [abs_of_nonneg hA, abs_of_neg hB', abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hA (le_of_lt hB'))]
    ring
  · have hA' : A < 0 := lt_of_not_ge hA
    rw [abs_of_neg hA', abs_of_nonneg hB, abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (le_of_lt hA') hB)]
    ring
  · have hA' : A < 0 := lt_of_not_ge hA
    have hB' : B < 0 := lt_of_not_ge hB
    rw [abs_of_neg hA', abs_of_neg hB', abs_of_pos (mul_pos_of_neg_of_neg hA' hB')]
    ring
/-- Конструктивный последовательный квантователь блока `w : List ℚ` с компенсацией
    верхнетреугольной матрицы корреляций `R` (столбцы `R` передаются как списки) -/
def quantizeBlockTriangularQ (θ α : ℚ) (w : List ℚ) (R_cols : List (List ℚ)) : List ℚ :=
  let rec go (idx : ℕ) (wRem : List ℚ) (colsRem : List (List ℚ))
      (errsAcc : List ℚ) (wHatAcc : List ℚ) : List ℚ :=
    match wRem, colsRem with
    | [], _ => wHatAcc.reverse
    | wj :: wTail, colJ :: colTail =>
        let offDiagSum := (List.zip errsAcc colJ).foldl (fun acc (ei, rij) => acc + ei * rij) 0
        let rjj := colJ.getD idx 1
        let wTilde := if rjj == 0 then wj else wj + offDiagSum / rjj
        let whj := quantizeScalarQ θ α wTilde
        let ej := wj - whj
        go (idx + 1) wTail colTail (errsAcc ++ [ej]) (whj :: wHatAcc)
    | _, [] => wHatAcc.reverse
  go 0 w R_cols [] []

/-- Вычисление полной треугольной выходной ошибки `∑_j |∑_{i ≤ j} (w_i - wHat_i) * R_{i,j}|` над ℚ -/
def triangularBlockErrorQ (w wHat : List ℚ) (R_cols : List (List ℚ)) : ℚ :=
  let errs := (List.zip w wHat).map fun (wi, whi) => wi - whi
  let rec sumCols (cols : List (List ℚ)) (acc : ℚ) : ℚ :=
    match cols with
    | [] => acc
    | colJ :: rest =>
        let colDot := (List.zip errs colJ).foldl (fun s (ei, rij) => s + ei * rij) 0
        sumCols rest (acc + absQ colDot)
  sumCols R_cols 0

-- Исполняемый тест (#eval) на 3 коррелированных каналах:
#eval
  let w : List ℚ := [6/1, 5/1, 1/1]
  let R_cols : List (List ℚ) := [
    [10/1, 0/1, 0/1],
    [8/1,  2/1, 0/1],
    [6/1,  4/1, 2/1]
  ]
  let wHatNaive : List ℚ := [4/1, 4/1, 0/1]
  let errNaive := triangularBlockErrorQ w wHatNaive R_cols
  let wHatComp := quantizeBlockTriangularQ (2/1) (4/1) w R_cols
  let errComp := triangularBlockErrorQ w wHatComp R_cols
  s!"[3-Ch Triangular Activation Feedback] naive_err={errNaive} vs triangular_err={errComp} (wHat={wHatComp})"

end MarkovL1TriangularActivation

-- Проверка аксиоматической чистоты:
#print axioms MarkovL1TriangularActivation.triangular_channel_exact_reduction
#print axioms MarkovL1TriangularActivation.quantizeBlockTriangularQ
