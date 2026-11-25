import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Grid-Free Continuous Dynamic Programming and Dual Certificates for Δ = 2 Chain Overlaps

* **Author:** E. S. Markov (ORCID: 0009-0005-2235-5464)
* **Affiliation:** Independent Researcher, Astrakhan, Russia
* **Repository:** https://github.com/fomamarkov-creator/l1-projection-complexity-lean4
* **License:** GNU Affero General Public License v3.0 (AGPLv3)
* **Toolchain:** Lean `v4.37.0-rc1` / Mathlib

## Overview
Eliminates discrete grid quantization (`G ⊂ ℚ`) for Δ = 2 chain overlaps by solving the
continuous Bellman recurrence over all of `ℚ^m` via convex piecewise-linear (`PWLConvexQ`)
slope-clipping (`infConvAbs`) and backward trajectory reconstruction (`solveContinuousChainDP`).
Includes a constructive, `Classical.choice`-free Lagrangian dual certificate verifier
(`checkChainOptimalCertQ`) and a complete formal soundness proof (`checkChainOptimalCertQ_sound`)
certifying global optimality across continuous `ℚ^m`.
-/

namespace MarkovL1ContinuousChainDP

/-- Конструктивный модуль над ℚ без `Classical.choice` -/
def absQ (x : ℚ) : ℚ :=
  if 0 ≤ x then x else -x

lemma absQ_eq_abs (x : ℚ) : absQ x = |x| := by
  unfold absQ
  split_ifs with h
  · exact (abs_of_nonneg h).symm
  · exact (abs_of_neg (lt_of_not_ge h)).symm

/-- Точка излома кусочно-линейной функции -/
structure BreakpointQ where
  x : ℚ
  dSlope : ℚ
  deriving Repr, DecidableEq

/-- Выпуклая кусочно-линейная функция над ℚ -/
structure PWLConvexQ where
  valAtZero : ℚ
  leftSlope : ℚ
  breaks : List BreakpointQ
  deriving Repr

/-- Часть значения PWL-функции без константы сдвига -/
def PWLConvexQ.rawEval (f : PWLConvexQ) (z : ℚ) : ℚ :=
  f.leftSlope * z +
  f.breaks.foldl (fun acc bp => if bp.x < z then acc + bp.dSlope * (z - bp.x) else acc) 0

/-- Точное вычисление значения `f(z)` в любой рациональной точке `z : ℚ` -/
def PWLConvexQ.eval (f : PWLConvexQ) (z : ℚ) : ℚ :=
  f.valAtZero + (f.rawEval z - f.rawEval 0)

/-- Конструктивная вставка точки излома (через `decide`, без `Classical.choice`) -/
def insertBreakpointQ (bp : BreakpointQ) : List BreakpointQ → List BreakpointQ
  | [] => [bp]
  | h :: t =>
      if bp.x < h.x then bp :: h :: t
      else if decide (bp.x = h.x) then
        let merged := h.dSlope + bp.dSlope
        if decide (merged = 0) then t else { x := h.x, dSlope := merged } :: t
      else h :: insertBreakpointQ bp t

/-- Поиск точки минимума выпуклой PWL-функции -/
def PWLConvexQ.argMin (f : PWLConvexQ) : ℚ :=
  let rec scan (currSlope : ℚ) : List BreakpointQ → ℚ
    | [] => 0
    | bp :: rest =>
        if 0 ≤ currSlope then bp.x
        else
          let nextSlope := currSlope + bp.dSlope
          if 0 ≤ nextSlope then bp.x else scan nextSlope rest
  scan f.leftSlope f.breaks

/-- Шаг 1 Беллмана: `g(x) = f(x) + |x - w|` -/
def PWLConvexQ.addAbsShift (f : PWLConvexQ) (w : ℚ) : PWLConvexQ :=
  let newBreaks := insertBreakpointQ { x := w, dSlope := 2 } f.breaks
  let newLeft := f.leftSlope - 1
  { valAtZero := f.valAtZero + absQ w
    leftSlope := newLeft
    breaks := newBreaks }

/-- Обрезка наклона на отрезок `[-1, 1]` -/
def clipSlopeQ (s : ℚ) : ℚ :=
  if s < -1 then -1 else if 1 < s then 1 else s

/-- Шаг 2 Беллмана: инфимальная конволюция `H(y) = min_{x ∈ ℚ} (f(x) + |y - x|)` -/
def PWLConvexQ.infConvAbs (f : PWLConvexQ) : PWLConvexQ :=
  let xStar := f.argMin
  let minVal := f.eval xStar
  let rec rebuild (currRaw : ℚ) : List BreakpointQ → List BreakpointQ
    | [] => []
    | bp :: rest =>
        let nextRaw := currRaw + bp.dSlope
        let dClip := clipSlopeQ nextRaw - clipSlopeQ currRaw
        if decide (dClip = 0) then rebuild nextRaw rest
        else { x := bp.x, dSlope := dClip } :: rebuild nextRaw rest
  let clippedBreaks := rebuild f.leftSlope f.breaks
  let unshifted : PWLConvexQ := {
    valAtZero := 0
    leftSlope := clipSlopeQ f.leftSlope
    breaks := clippedBreaks
  }
  let valAtXStar := unshifted.eval xStar
  { unshifted with valAtZero := minVal - valAtXStar }

/-- Шаг 3 Беллмана: отражение и сдвиг `DP_next(z) = H(w - z)` -/
def PWLConvexQ.reflectShift (H : PWLConvexQ) (w : ℚ) : PWLConvexQ :=
  let totalSlope := H.breaks.foldl (fun acc bp => acc + bp.dSlope) H.leftSlope
  let revBreaks := H.breaks.reverse.map fun bp => { x := w - bp.x, dSlope := bp.dSlope }
  let val0 := H.eval w
  { valAtZero := val0
    leftSlope := -totalSlope
    breaks := revBreaks }

/-- Целевая функция ошибки цепочки перекрытий Δ = 2 (совпадает с `MarkovL1TreewidthSolver`) -/
def chainOverlapErrorQ (ws : List ℚ) (cs : List ℚ) : ℚ :=
  match ws, cs with
  | [w], c :: _ => absQ (w - c)
  | w₁ :: w₂ :: wRest, c₁ :: c₂ :: cRest =>
      absQ (w₁ - c₁) + absQ (w₂ - (c₁ + c₂)) + chainOverlapErrorQ (w₂ :: wRest) (c₂ :: cRest)
  | _, _ => 0

/-- Полный прямой и обратный проход непрерывного ДП (с учетом последнего узла `|w_m - c_m|`) -/
def solveContinuousChainDP (ws : List ℚ) : List ℚ × ℚ :=
  let zeroF : PWLConvexQ := { valAtZero := 0, leftSlope := 0, breaks := [] }
  match ws with
  | [] => ([], 0)
  | [w] =>
      let f := zeroF.addAbsShift w
      let cStar := f.argMin
      ([cStar], f.eval cStar)
  | w₁ :: w₂ :: rest =>
      let rec forward (wp wc : ℚ) (rem : List ℚ) (dp : PWLConvexQ)
          (history : List (PWLConvexQ × ℚ)) : List (PWLConvexQ × ℚ) × PWLConvexQ :=
        let fWithNode := dp.addAbsShift wp
        let hConv := fWithNode.infConvAbs
        let nextDP := hConv.reflectShift wc
        let history' := (fWithNode, wc) :: history
        match rem with
        | [] => (history', nextDP.addAbsShift wc)
        | wNext :: wTail => forward wc wNext wTail nextDP history'
      let (history, finalDP) := forward w₁ w₂ rest zeroF []
      let cLast := finalDP.argMin
      let minCost := finalDP.eval cLast
      let rec backward (cNext : ℚ) (csAcc : List ℚ) : List (PWLConvexQ × ℚ) → List ℚ
        | [] => cNext :: csAcc
        | (fNode, wNext) :: tail =>
            let target := wNext - cNext
            let fTotal := fNode.addAbsShift target
            let cPrev := fTotal.argMin
            backward cPrev (cNext :: csAcc) tail
      (backward cLast [] history, minCost)

/-- Вычислимая проверка баланса двойственных множителей Лагранжа вдоль цепочки -/
def checkChainBalanceQ (qPrev : ℚ) : List ℚ → List ℚ → Bool
  | [], [] => decide (qPrev = 0)
  | [pLast], [] => decide (qPrev + pLast = 0)
  | p₀ :: pRest, q₀ :: qRest =>
      decide (qPrev + p₀ + q₀ = 0) && checkChainBalanceQ q₀ pRest qRest
  | _, _ => false

/-- Вычислимое значение двойственного функционала Лагранжа -/
def evalChainDualQ : List ℚ → List ℚ → List ℚ → ℚ
  | [w], p₀ :: _, _ => p₀ * w
  | w₁ :: w₂ :: wRest, p₀ :: pRest, q₀ :: qRest =>
      p₀ * w₁ + q₀ * w₂ + evalChainDualQ (w₂ :: wRest) pRest qRest
  | _, _, _ => 0

/-- Вычислимая проверка двойственного сертификата `(p, q)` и точки `c*`:
    если `checkChainOptimalCertQ ws cs p q = true`, то `cs` — доказанный глобальный оптимум! -/
def checkChainOptimalCertQ (ws cs p q : List ℚ) : Bool :=
  let boundsP := p.all fun u => decide (-1 ≤ u && u ≤ 1)
  let boundsQ := q.all fun u => decide (-1 ≤ u && u ≤ 1)
  boundsP && boundsQ && decide (p.length = ws.length) && checkChainBalanceQ 0 p q &&
  decide (evalChainDualQ ws p q = chainOverlapErrorQ ws cs)
-- =========================================================================
-- ТЕОРЕМЫ ДВОЙСТВЕННОСТИ ЛАГРАНЖА И ФОРМАЛЬНАЯ КОРРЕКТНОСТЬ СЕРТИФИКАТА
-- =========================================================================

lemma dual_mul_le_abs {u z : ℚ} (hu_lo : -1 ≤ u) (hu_hi : u ≤ 1) :
    u * z ≤ |z| := by
  by_cases hz : 0 ≤ z
  · rw [abs_of_nonneg hz]; nlinarith
  · have hlt : z < 0 := lt_of_not_ge hz
    rw [abs_of_neg hlt]; nlinarith

theorem step_dual_le_primal {w₁ w₂ c₁ c₂ p q : ℚ}
    (hp1 : -1 ≤ p) (hp2 : p ≤ 1) (hq1 : -1 ≤ q) (hq2 : q ≤ 1) :
    p * (w₁ - c₁) + q * (w₂ - (c₁ + c₂)) ≤ |w₁ - c₁| + |w₂ - (c₁ + c₂)| :=
  add_le_add (dual_mul_le_abs hp1 hp2) (dual_mul_le_abs hq1 hq2)

/-- Индуктивная лемма слабой двойственности вдоль цепочки с граничным множителем `qPrev` -/
theorem weak_duality_aux :
    ∀ (ws cs' p q : List ℚ) (qPrev : ℚ),
      ws.length = cs'.length →
      p.length = ws.length →
      p.all (fun u => decide (-1 ≤ u && u ≤ 1)) = true →
      q.all (fun u => decide (-1 ≤ u && u ≤ 1)) = true →
      checkChainBalanceQ qPrev p q = true →
      evalChainDualQ ws p q + qPrev * (cs'.headD 0) ≤ chainOverlapErrorQ ws cs'
  | [], cs', _, _, _, hlen_c, _, _, _, _ => by
      cases cs' with
      | nil => simp [evalChainDualQ, chainOverlapErrorQ]
      | cons _ _ => simp at hlen_c
  | [w], cs', p, q, qPrev, hlen_c, hlen_p, hp_all, _, hbal => by
      rcases cs' with _ | ⟨c, _ | _⟩ <;> simp at hlen_c
      rcases p with _ | ⟨p₀, _ | _⟩ <;> simp at hlen_p
      have hp_b := List.all_eq_true.mp hp_all p₀ List.mem_cons_self
      simp only [decide_eq_true_eq, Bool.and_eq_true] at hp_b
      have h_qp0 : qPrev + p₀ = 0 := by
        cases q with
        | nil =>
            dsimp [checkChainBalanceQ] at hbal
            exact decide_eq_true_eq.mp hbal
        | cons q₀ qRest =>
            dsimp [checkChainBalanceQ] at hbal
            rw [Bool.and_eq_true, decide_eq_true_eq] at hbal
            cases qRest with
            | nil =>
                dsimp [checkChainBalanceQ] at hbal
                have hq0 : q₀ = 0 := decide_eq_true_eq.mp hbal.2
                linarith [hbal.1]
            | cons _ _ =>
                dsimp [checkChainBalanceQ] at hbal
                simp at hbal
      have h_le := dual_mul_le_abs hp_b.1 hp_b.2 (z := w - c)
      dsimp [evalChainDualQ, chainOverlapErrorQ, List.headD]
      rw [absQ_eq_abs]
      have h_qprev : qPrev = -p₀ := by linarith
      rw [h_qprev]
      have h_alg : p₀ * w + -p₀ * c = p₀ * (w - c) := by ring
      linarith
  | w₁ :: w₂ :: wRest, cs', p, q, qPrev, hlen_c, hlen_p, hp_all, hq_all, hbal => by
      rcases cs' with _ | ⟨c₁, _ | ⟨c₂, cRest⟩⟩ <;> simp at hlen_c
      rcases p with _ | ⟨p₀, _ | ⟨p₁, pRest⟩⟩ <;> simp at hlen_p
      rcases q with _ | ⟨q₀, qRest⟩
      · dsimp [checkChainBalanceQ] at hbal
        simp at hbal
      · dsimp [checkChainBalanceQ] at hbal
        rw [Bool.and_eq_true, decide_eq_true_eq] at hbal
        obtain ⟨h_node_bal, h_rest_bal⟩ := hbal
        have hp₀_b := List.all_eq_true.mp hp_all p₀ List.mem_cons_self
        simp only [decide_eq_true_eq, Bool.and_eq_true] at hp₀_b
        have hq₀_b := List.all_eq_true.mp hq_all q₀ List.mem_cons_self
        simp only [decide_eq_true_eq, Bool.and_eq_true] at hq₀_b
        have hp_rest_all : (p₁ :: pRest).all (fun u => decide (-1 ≤ u && u ≤ 1)) = true :=
          List.all_eq_true.mpr fun u hu =>
            List.all_eq_true.mp hp_all u (List.mem_cons_of_mem _ hu)
        have hq_rest_all : qRest.all (fun u => decide (-1 ≤ u && u ≤ 1)) = true :=
          List.all_eq_true.mpr fun u hu =>
            List.all_eq_true.mp hq_all u (List.mem_cons_of_mem _ hu)
        have ih := weak_duality_aux (w₂ :: wRest) (c₂ :: cRest) (p₁ :: pRest) qRest q₀
          (by simp [hlen_c]) (by simp [hlen_p]) hp_rest_all hq_rest_all h_rest_bal
        have h_step := step_dual_le_primal (w₁ := w₁) (w₂ := w₂) (c₁ := c₁) (c₂ := c₂)
          hp₀_b.1 hp₀_b.2 hq₀_b.1 hq₀_b.2
        dsimp [evalChainDualQ, chainOverlapErrorQ, List.headD] at ih ⊢
        rw [absQ_eq_abs, absQ_eq_abs]
        have h_qprev : qPrev = -(p₀ + q₀) := by linarith
        rw [h_qprev]
        have h_alg :
            (p₀ * w₁ + q₀ * w₂ + evalChainDualQ (w₂ :: wRest) (p₁ :: pRest) qRest) + -(p₀ + q₀) * c₁ =
            (p₀ * (w₁ - c₁) + q₀ * (w₂ - (c₁ + c₂))) +
            (evalChainDualQ (w₂ :: wRest) (p₁ :: pRest) qRest + q₀ * c₂) := by
          ring
        linarith

/-- Главная теорема сертификации непрерывного ДП над всем `ℚ^m`:
    если `checkChainOptimalCertQ ws cs p q = true`, то вектор `cs` является
    доказанным глобальным минимумом задачи цепочки перекрытий среди всех `c' ∈ ℚ^m` -/
theorem checkChainOptimalCertQ_sound (ws cs p q : List ℚ)
    (h_cert : checkChainOptimalCertQ ws cs p q = true) :
    ∀ c' : List ℚ, c'.length = ws.length →
      chainOverlapErrorQ ws cs ≤ chainOverlapErrorQ ws c' := by
  intro c' hc'_len
  dsimp [checkChainOptimalCertQ] at h_cert
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h_cert
  obtain ⟨⟨⟨⟨hp_all, hq_all⟩, hp_len⟩, hbal⟩, hdual_eq⟩ := h_cert
  have h_weak := weak_duality_aux ws c' p q 0 hc'_len.symm hp_len hp_all hq_all hbal
  rw [hdual_eq] at h_weak
  linarith

-- Исполняемые тесты (#eval) и самопроверка совпадения прямой стоимости с `chainOverlapErrorQ`
#eval
  let ws : List ℚ := [4/1, 8/1, 4/1]
  let (cs, cost) := solveContinuousChainDP ws
  let exactErr := chainOverlapErrorQ ws cs
  let certOK := checkChainOptimalCertQ ws cs [0/1, 1/1, 1/1] [0/1, -1/1]
  s!"ws={ws} -> c*={cs}, DP_cost={cost}, exactErr={exactErr}, dualCertified={certOK}"

#eval
  let ws : List ℚ := [3/4, 5/2, 7/4]
  let (cs, cost) := solveContinuousChainDP ws
  let exactErr := chainOverlapErrorQ ws cs
  s!"ws={ws} -> c*={cs}, DP_cost={cost}, exactErr={exactErr}"

end MarkovL1ContinuousChainDP

-- Проверка аксиоматической чистоты:
#print axioms MarkovL1ContinuousChainDP.solveContinuousChainDP
#print axioms MarkovL1ContinuousChainDP.checkChainOptimalCertQ
#print axioms MarkovL1ContinuousChainDP.checkChainOptimalCertQ_sound
