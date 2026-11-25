import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# V-CORE Super-Quantizer: Hadamard-D₄ Lattice, Asymmetric Scales, and Adaptive Certified Cascades

* **Author:** E. S. Markov (ORCID: 0009-0005-2235-5464)
* **Affiliation:** Independent Researcher, Astrakhan, Russia
* **Repository:** https://github.com/fomamarkov-creator/l1-projection-complexity-lean4
* **License:** GNU Affero General Public License v3.0 (AGPLv3)
* **Toolchain:** Lean `v4.37.0-rc1` / Mathlib

## Overview
Unifies all next-generation exact-rational (`ℚ`) quantization mechanisms into a single
self-certifying adaptive super-quantizer (`superQuantize4Q`):
1. **Hadamard `H₄` Incoherence & `ℓ₁` Distortion Bound (`hadamard4Q_l1_bound`):** Proves that
   inverse Hadamard rotation amplifies `ℓ₁` quantization error by at most a factor of `2`.
2. **4D Root Lattice `D₄` (`quantizeD4BlockQ`, ~1.16 bits/weight):** Vector-quantizes 4-tuples
   into the 25-element `D₄` root shell (`{0} ∪ Φ(D₄)`, 24 roots + origin), verified via
   `d4Alphabet_all_valid`.
3. **Adaptive Multi-Mode Escalation (`1.16b D₄ → 1.58b Asym → 3.16b Residual`):** Automatically
   selects the lowest-bit representation meeting a target distortion budget `ε`, backed by
   the end-to-end certified error bound `superQuantize4Q_certified_bound`.
-/

namespace MarkovL1SuperQuantizer

/-- Конструктивный модуль над ℚ без `Classical.choice` -/
def absQ (x : ℚ) : ℚ :=
  if 0 ≤ x then x else -x

abbrev Vec4Q := ℚ × ℚ × ℚ × ℚ

def l1Norm4Q (v : Vec4Q) : ℚ :=
  absQ v.1 + absQ v.2.1 + absQ v.2.2.1 + absQ v.2.2.2

def l1Dist4Q (u v : Vec4Q) : ℚ :=
  l1Norm4Q (u.1 - v.1, u.2.1 - v.2.1, u.2.2.1 - v.2.2.1, u.2.2.2 - v.2.2.2)

-- =========================================================================
-- 1. ОРТОГОНАЛЬНОЕ ПРЕОБРАЗОВАНИЕ АДАМАРА H₄ И ТЕОРЕМА ГРАНИЦЫ ℓ₁-ОШИБКИ
-- =========================================================================

def hadamard4Q (v : Vec4Q) : Vec4Q :=
  let (x₀, x₁, x₂, x₃) := v
  ( (x₀ + x₁ + x₂ + x₃) / 2,
    (x₀ - x₁ + x₂ - x₃) / 2,
    (x₀ + x₁ - x₂ - x₃) / 2,
    (x₀ - x₁ - x₂ + x₃) / 2 )

theorem hadamard4Q_involutive (v : Vec4Q) :
    hadamard4Q (hadamard4Q v) = v := by
  rcases v with ⟨x₀, x₁, x₂, x₃⟩
  dsimp [hadamard4Q]
  ext <;> ring

lemma hadamard4Q_sub (u v : Vec4Q) :
    (u.1 - v.1, u.2.1 - v.2.1, u.2.2.1 - v.2.2.1, u.2.2.2 - v.2.2.2) =
    hadamard4Q ( (hadamard4Q u).1 - (hadamard4Q v).1,
                 (hadamard4Q u).2.1 - (hadamard4Q v).2.1,
                 (hadamard4Q u).2.2.1 - (hadamard4Q v).2.2.1,
                 (hadamard4Q u).2.2.2 - (hadamard4Q v).2.2.2 ) := by
  rcases u with ⟨u₀, u₁, u₂, u₃⟩
  rcases v with ⟨v₀, v₁, v₂, v₃⟩
  dsimp [hadamard4Q]
  ext <;> ring

/-- Теорема 1.1 (Верхняя граница искажения при обратном вращении H₄):
    ‖H₄(e)‖₁ ≤ 2 · ‖e‖₁ -/
theorem hadamard4Q_l1_bound (e : Vec4Q) :
    l1Norm4Q (hadamard4Q e) ≤ 2 * l1Norm4Q e := by
  rcases e with ⟨e₀, e₁, e₂, e₃⟩
  dsimp [l1Norm4Q, hadamard4Q]
  have h1 : absQ ((e₀ + e₁ + e₂ + e₃) / 2) ≤ (absQ e₀ + absQ e₁ + absQ e₂ + absQ e₃) / 2 := by
    unfold absQ; split_ifs <;> linarith
  have h2 : absQ ((e₀ - e₁ + e₂ - e₃) / 2) ≤ (absQ e₀ + absQ e₁ + absQ e₂ + absQ e₃) / 2 := by
    unfold absQ; split_ifs <;> linarith
  have h3 : absQ ((e₀ + e₁ - e₂ - e₃) / 2) ≤ (absQ e₀ + absQ e₁ + absQ e₂ + absQ e₃) / 2 := by
    unfold absQ; split_ifs <;> linarith
  have h4 : absQ ((e₀ - e₁ - e₂ + e₃) / 2) ≤ (absQ e₀ + absQ e₁ + absQ e₂ + absQ e₃) / 2 := by
    unfold absQ; split_ifs <;> linarith
  linarith

-- =========================================================================
-- 2. ВЕКТОРНОЕ РЕШЁТЧАТОЕ КВАНТОВАНИЕ D₄ (~1.16 БИТА НА ВЕС, 25 СОСТОЯНИЙ)
-- =========================================================================

abbrev Vec4Z := ℤ × ℤ × ℤ × ℤ

/-- Предикат принадлежности корневой оболочке решётки D₄ (ноль + 24 корня D₄):
    координаты в {-1, 0, 1}, чётная сумма и квадрат евклидовой нормы ≤ 2 -/
def isD4RootShell (z : Vec4Z) : Bool :=
  let (z₀, z₁, z₂, z₃) := z
  decide (-1 ≤ z₀ ∧ z₀ ≤ 1 ∧ -1 ≤ z₁ ∧ z₁ ≤ 1 ∧
          -1 ≤ z₂ ∧ z₂ ≤ 1 ∧ -1 ≤ z₃ ∧ z₃ ≤ 1 ∧
          (z₀ + z₁ + z₂ + z₃) % 2 = 0 ∧
          z₀ * z₀ + z₁ * z₁ + z₂ * z₂ + z₃ * z₃ ≤ 2)

/-- Полный 25-элементный алфавит корневой оболочки D₄ (24 корня + начало координат) -/
def d4Alphabet : List Vec4Z :=
  [ (0, 0, 0, 0),
    (1, 1, 0, 0), (1, -1, 0, 0), (-1, 1, 0, 0), (-1, -1, 0, 0),
    (1, 0, 1, 0), (1, 0, -1, 0), (-1, 0, 1, 0), (-1, 0, -1, 0),
    (1, 0, 0, 1), (1, 0, 0, -1), (-1, 0, 0, 1), (-1, 0, 0, -1),
    (0, 1, 1, 0), (0, 1, -1, 0), (0, -1, 1, 0), (0, -1, -1, 0),
    (0, 1, 0, 1), (0, 1, 0, -1), (0, -1, 0, 1), (0, -1, 0, -1),
    (0, 0, 1, 1), (0, 0, 1, -1), (0, 0, -1, 1), (0, 0, -1, -1) ]

/-- Теорема 2.1 (Машинная верификация корневого алфавита D₄):
    словарь содержит ровно 25 попарно различных векторов из корневой оболочки D₄ -/
theorem d4Alphabet_all_valid :
    d4Alphabet.length = 25 ∧ d4Alphabet.Nodup ∧ d4Alphabet.all isD4RootShell = true := by
  decide

def scaleVec4Z (α : ℚ) (z : Vec4Z) : Vec4Q :=
  (α * (z.1 : ℚ), α * (z.2.1 : ℚ), α * (z.2.2.1 : ℚ), α * (z.2.2.2 : ℚ))

def insertRat (x : ℚ) (xs : List ℚ) : List ℚ :=
  match xs with
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertRat x ys

def sortRat (xs : List ℚ) : List ℚ :=
  match xs with
  | [] => []
  | x :: xs => insertRat x (sortRat xs)

def exactMedianQ (xs : List ℚ) : ℚ :=
  let s := sortRat xs
  s.getD (s.length / 2) 0

def isCloser4Q (target cand best : Vec4Q) : Bool :=
  decide (l1Dist4Q target cand < l1Dist4Q target best)

/-- Решётчатый D₄-квантователь четвёрки весов над ℚ (~1.16 бита/вес) -/
def quantizeD4BlockQ (v : Vec4Q) : Vec4Q :=
  let mags := [absQ v.1, absQ v.2.1, absQ v.2.2.1, absQ v.2.2.2].filter (fun m => decide (0 < m))
  let α := exactMedianQ mags
  let cands := d4Alphabet.map (scaleVec4Z α)
  cands.foldl (fun best c => if isCloser4Q v c best then c else best) (0, 0, 0, 0)
-- =========================================================================
-- 3. АСИММЕТРИЧНЫЙ 1.58b И 2-СТУПЕНЧАТЫЙ ОСТАТОЧНЫЙ КАСКАД НА ЧЕТВЁРКАХ
-- =========================================================================

def toList4 (v : Vec4Q) : List ℚ :=
  [v.1, v.2.1, v.2.2.1, v.2.2.2]

/-- Асимметричный 1.58-битный квантователь {-α_neg, 0, +α_pos} с медианными масштабами -/
def quantizeAsym4Q (v : Vec4Q) : Vec4Q :=
  let xs := toList4 v
  let posMags := xs.filter (fun x => decide (0 < x))
  let negMags := (xs.filter (fun x => decide (x < 0))).map (fun x => -x)
  let α_pos := exactMedianQ posMags
  let α_neg := exactMedianQ negMags
  let qScalar (x : ℚ) : ℚ :=
    if 0 < x then (if x ≤ α_pos / 2 then 0 else α_pos)
    else if x < 0 then (if -x ≤ α_neg / 2 then 0 else -α_neg)
    else 0
  (qScalar v.1, qScalar v.2.1, qScalar v.2.2.1, qScalar v.2.2.2)

/-- Двухступенчатый остаточный ℓ₁-каскад на четвёрке (3.16 бита без умножений) -/
def quantizeResidual4Q (v : Vec4Q) : Vec4Q :=
  let wHat₁ := quantizeAsym4Q v
  let res : Vec4Q := (v.1 - wHat₁.1, v.2.1 - wHat₁.2.1, v.2.2.1 - wHat₁.2.2.1, v.2.2.2 - wHat₁.2.2.2)
  let wHat₂ := quantizeAsym4Q res
  (wHat₁.1 + wHat₂.1, wHat₁.2.1 + wHat₂.2.1, wHat₁.2.2.1 + wHat₂.2.2.1, wHat₁.2.2.2 + wHat₂.2.2.2)

-- =========================================================================
-- 4. ЕДИНЫЙ АДАПТИВНЫЙ СУПЕРКВАНТОВАТЕЛЬ (HADAMARD + ADAPTIVE BIT-CASCADE)
-- =========================================================================

inductive QuantMode where
  | D4Lattice_1_16bit
  | AsymTernary_1_58bit
  | ResidualCascade_3_16bit
  deriving Repr, DecidableEq

structure SuperQuantOutput where
  mode : QuantMode
  rotatedQuant : Vec4Q
  restoredWeights : Vec4Q
  rotatedErr : ℚ
  certifiedMaxOutputErr : ℚ
  deriving Repr

/-- Главный алгоритм V-CORE Super-Quantizer -/
def superQuantize4Q (ε : ℚ) (w : Vec4Q) : SuperQuantOutput :=
  let wRot := hadamard4Q w
  let qD4 := quantizeD4BlockQ wRot
  let errD4 := l1Dist4Q wRot qD4
  if errD4 ≤ ε then
    { mode := QuantMode.D4Lattice_1_16bit
      rotatedQuant := qD4
      restoredWeights := hadamard4Q qD4
      rotatedErr := errD4
      certifiedMaxOutputErr := 2 * errD4 }
  else
    let qAsym := quantizeAsym4Q wRot
    let errAsym := l1Dist4Q wRot qAsym
    if errAsym ≤ ε then
      { mode := QuantMode.AsymTernary_1_58bit
        rotatedQuant := qAsym
        restoredWeights := hadamard4Q qAsym
        rotatedErr := errAsym
        certifiedMaxOutputErr := 2 * errAsym }
    else
      let qRes := quantizeResidual4Q wRot
      let errRes := l1Dist4Q wRot qRes
      { mode := QuantMode.ResidualCascade_3_16bit
        rotatedQuant := qRes
        restoredWeights := hadamard4Q qRes
        rotatedErr := errRes
        certifiedMaxOutputErr := 2 * errRes }

/-- Главная теорема сквозной корректности Суперквантователя -/
theorem superQuantize4Q_certified_bound (ε : ℚ) (w : Vec4Q) :
    let out := superQuantize4Q ε w
    l1Dist4Q w out.restoredWeights ≤ out.certifiedMaxOutputErr := by
  dsimp [superQuantize4Q]
  split_ifs with h1 h2
  · dsimp [l1Dist4Q]
    rw [hadamard4Q_sub]
    simp only [hadamard4Q_involutive]
    exact hadamard4Q_l1_bound _
  · dsimp [l1Dist4Q]
    rw [hadamard4Q_sub]
    simp only [hadamard4Q_involutive]
    exact hadamard4Q_l1_bound _
  · dsimp [l1Dist4Q]
    rw [hadamard4Q_sub]
    simp only [hadamard4Q_involutive]
    exact hadamard4Q_l1_bound _

-- =========================================================================
-- ИСПОЛНЯЕМЫЕ ТЕСТЫ (#eval) И ПРОВЕРКА АКСИОМАТИЧЕСКОЙ ЧИСТОТЫ
-- =========================================================================

#eval
  let out1 := superQuantize4Q (1/10) (100/1, 0/1, 0/1, 0/1);
  s!"[Scenario 1: Extreme Outlier] mode={repr out1.mode}, rotErr={out1.rotatedErr}, restored={out1.restoredWeights}"

#eval
  let w2 : Vec4Q := (10/1, -2/1, 3/1, -1/1);
  let out2 := superQuantize4Q (2/1) w2;
  let actualErr := l1Dist4Q w2 out2.restoredWeights;
  s!"[Scenario 2: Hard Block] mode={repr out2.mode}, actualErr={actualErr} ≤ certBound={out2.certifiedMaxOutputErr}"

end MarkovL1SuperQuantizer

#print axioms MarkovL1SuperQuantizer.d4Alphabet_all_valid
#print axioms MarkovL1SuperQuantizer.hadamard4Q_l1_bound
#print axioms MarkovL1SuperQuantizer.superQuantize4Q_certified_bound
