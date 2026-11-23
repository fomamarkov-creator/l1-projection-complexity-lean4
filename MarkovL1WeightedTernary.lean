import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace MarkovL1WeightedTernary

/-- Взвешенная пара (вес нейросети w, важность канала γ ≥ 0) в точных дробях ℚ -/
structure WeightedEntryQ where
  w : ℚ
  γ : ℚ

/-- 1.58-bit тернарный оператор квантования -/
def quantizeScalarQ (θ α w : ℚ) : ℚ :=
  if |w| ≤ θ then 0
  else if 0 ≤ w then α else -α

/-- Точечная взвешенная ℓ₁-ошибка γ * |w - Q(w)| -/
def weightedPointErrorQ (θ α : ℚ) (e : WeightedEntryQ) : ℚ :=
  e.γ * |e.w - quantizeScalarQ θ α e.w|

/-- Полная взвешенная ℓ₁-ошибка на блоке с учётом важности активаций -/
def weightedBlockErrorQ (θ α : ℚ) (es : List WeightedEntryQ) : ℚ :=
  (es.map (weightedPointErrorQ θ α)).sum

/-- Теорема 1: Инвариантность взвешенной ℓ₁-ошибки на интервалах между порядковыми статистиками -/
theorem weightedBlockErrorQ_const_on_gap {θ₁ θ₂ α : ℚ} (h12 : θ₁ ≤ θ₂) (es : List WeightedEntryQ)
    (hgap : ∀ e ∈ es, ¬ (θ₁ < |e.w| ∧ |e.w| ≤ θ₂)) :
    weightedBlockErrorQ θ₁ α es = weightedBlockErrorQ θ₂ α es := by
  unfold weightedBlockErrorQ
  congr 1
  apply List.map_congr_left
  intro e he
  unfold weightedPointErrorQ quantizeScalarQ
  have hnot := hgap e he
  by_cases h1 : |e.w| ≤ θ₁
  · have h2 : |e.w| ≤ θ₂ := le_trans h1 h12
    simp [h1, h2]
  · have hgt1 : θ₁ < |e.w| := lt_of_not_ge h1
    have h2 : ¬ (|e.w| ≤ θ₂) := fun hle => hnot ⟨hgt1, hle⟩
    simp [h1, h2]

/-- Сортировка пар (|w|, γ) по неубыванию |w| для конструктивной взвешенной медианы -/
def insertPairQ (p : ℚ × ℚ) : List (ℚ × ℚ) → List (ℚ × ℚ)
  | [] => [p]
  | q :: qs => if p.1 ≤ q.1 then p :: q :: qs else q :: insertPairQ p qs

def sortPairsQ : List (ℚ × ℚ) → List (ℚ × ℚ)
  | [] => []
  | p :: ps => insertPairQ p (sortPairsQ ps)

def sumWeightsQ : List (ℚ × ℚ) → ℚ
  | [] => 0
  | p :: ps => p.2 + sumWeightsQ ps

def findWeightedMedAux (half : ℚ) (acc : ℚ) : List (ℚ × ℚ) → ℚ
  | [] => 0
  | [p] => p.1
  | p :: ps =>
      let acc' := acc + p.2
      if half ≤ acc' then p.1 else findWeightedMedAux half acc' ps

/-- Точная конструктивная взвешенная медиана над ℚ -/
def exactWeightedMedianQ (pairs : List (ℚ × ℚ)) : ℚ :=
  let s := sortPairsQ pairs
  let total := sumWeightsQ s
  findWeightedMedAux (total / 2) 0 s

/-- Оптимальный взвешенный масштаб α_γ*(θ) для активных элементов (|w| > θ) -/
def optimalWeightedScaleQ (θ : ℚ) (es : List WeightedEntryQ) : ℚ :=
  let active := (es.filter (fun e => decide (θ < |e.w|))).map (fun e => (|e.w|, e.γ))
  exactWeightedMedianQ active

/-- Конечный список критических порогов {0} ∪ {|w_i|} -/
def criticalThresholdsWeightedQ (es : List WeightedEntryQ) : List ℚ :=
  0 :: es.map (fun e => |e.w|)

def selectBestWeightedPairQ (es : List WeightedEntryQ) : List ℚ → ℚ × ℚ
  | [] => (0, optimalWeightedScaleQ 0 es)
  | [θ] => (θ, optimalWeightedScaleQ θ es)
  | θ :: rest =>
      let α := optimalWeightedScaleQ θ es
      let (θ_b, α_b) := selectBestWeightedPairQ es rest
      if weightedBlockErrorQ θ α es ≤ weightedBlockErrorQ θ_b α_b es then (θ, α) else (θ_b, α_b)

/-- Точный активационно-взвешенный 1.58-bit квантователь над ℚ -/
def quantizeWeightedTernaryExactQ (es : List WeightedEntryQ) : ℚ × ℚ :=
  selectBestWeightedPairQ es (criticalThresholdsWeightedQ es)

/-- Теорема 2: Формальный сертификат оптимальности активационно-взвешенного квантователя -/
theorem selectBestWeightedPairQ_le_mem (es : List WeightedEntryQ) :
    ∀ cs θ, θ ∈ cs →
      let (θ_b, α_b) := selectBestWeightedPairQ es cs
      weightedBlockErrorQ θ_b α_b es ≤ weightedBlockErrorQ θ (optimalWeightedScaleQ θ es) es
  | [], _, h => by simp at h
  | [θ₀], θ, h => by
      simp at h
      subst h
      simp [selectBestWeightedPairQ]
  | θ₀ :: θ₁ :: rest, θ, h => by
      simp only [selectBestWeightedPairQ]
      split_ifs with hle
      · rcases List.mem_cons.mp h with rfl | hmem
        · exact le_refl _
        · exact le_trans hle (selectBestWeightedPairQ_le_mem es (θ₁ :: rest) θ hmem)
      · have hgt : weightedBlockErrorQ (selectBestWeightedPairQ es (θ₁ :: rest)).1 (selectBestWeightedPairQ es (θ₁ :: rest)).2 es <
                   weightedBlockErrorQ θ₀ (optimalWeightedScaleQ θ₀ es) es := lt_of_not_ge hle
        rcases List.mem_cons.mp h with rfl | hmem
        · exact le_of_lt hgt
        · exact selectBestWeightedPairQ_le_mem es (θ₁ :: rest) θ hmem

theorem quantizeWeightedTernaryExactQ_certified (es : List WeightedEntryQ) (θ : ℚ)
    (hθ : θ ∈ criticalThresholdsWeightedQ es) :
    let (θ_star, α_star) := quantizeWeightedTernaryExactQ es
    weightedBlockErrorQ θ_star α_star es ≤ weightedBlockErrorQ θ (optimalWeightedScaleQ θ es) es :=
  selectBestWeightedPairQ_le_mem es (criticalThresholdsWeightedQ es) θ hθ

end MarkovL1WeightedTernary
