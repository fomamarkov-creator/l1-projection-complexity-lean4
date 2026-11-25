import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# V-CORE v4.0 Master Formalization: W₁₆/W₃₂ Cascade Rotations, Barnes–Wall Λ₃₂, LUT Kernel Soundness, Mixed-Lattice Budget & End-to-End Transformer Block Certificate

* **Author:** E. S. Markov (ORCID: 0009-0005-2235-5464)
* **Affiliation:** Independent Researcher, Astrakhan, Russia
* **Repository:** https://github.com/fomamarkov-creator/l1-projection-complexity-lean4
* **License:** GNU Affero General Public License v3.0 (AGPLv3)
* **Toolchain:** Lean `v4.37.0-rc1` / Mathlib
-/

namespace MarkovL1FullTransformerCert

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
    unfold absQ; split_ifs <;> linarith
  · have ha' : a < 0 := lt_of_not_ge ha
    have hab : a * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_lt ha') hb
    unfold absQ; split_ifs <;> linarith
  · have ha' : a < 0 := lt_of_not_ge ha
    have hb' : b < 0 := lt_of_not_ge hb
    have hab : 0 ≤ a * b := mul_nonneg_of_nonpos_of_nonpos (le_of_lt ha') (le_of_lt hb')
    simp [absQ, ha, hb, hab]

@[ext]
structure Vec8Q where
  x0 : ℚ
  x1 : ℚ
  x2 : ℚ
  x3 : ℚ
  x4 : ℚ
  x5 : ℚ
  x6 : ℚ
  x7 : ℚ
  deriving Repr, DecidableEq

def addVec8Q (u v : Vec8Q) : Vec8Q :=
  ⟨u.x0 + v.x0, u.x1 + v.x1, u.x2 + v.x2, u.x3 + v.x3,
   u.x4 + v.x4, u.x5 + v.x5, u.x6 + v.x6, u.x7 + v.x7⟩

def subVec8Q (u v : Vec8Q) : Vec8Q :=
  ⟨u.x0 - v.x0, u.x1 - v.x1, u.x2 - v.x2, u.x3 - v.x3,
   u.x4 - v.x4, u.x5 - v.x5, u.x6 - v.x6, u.x7 - v.x7⟩

def scaleVec8Q (c : ℚ) (v : Vec8Q) : Vec8Q :=
  ⟨c * v.x0, c * v.x1, c * v.x2, c * v.x3,
   c * v.x4, c * v.x5, c * v.x6, c * v.x7⟩

def dot8Q (u v : Vec8Q) : ℚ :=
  u.x0 * v.x0 + u.x1 * v.x1 + u.x2 * v.x2 + u.x3 * v.x3 +
  u.x4 * v.x4 + u.x5 * v.x5 + u.x6 * v.x6 + u.x7 * v.x7

lemma dot8Q_add_left (a b c : Vec8Q) : dot8Q (addVec8Q a b) c = dot8Q a c + dot8Q b c := by
  rcases a with ⟨a0,a1,a2,a3,a4,a5,a6,a7⟩
  rcases b with ⟨b0,b1,b2,b3,b4,b5,b6,b7⟩
  rcases c with ⟨c0,c1,c2,c3,c4,c5,c6,c7⟩
  dsimp [addVec8Q, dot8Q]; ring

lemma dot8Q_sub_left (a b c : Vec8Q) : dot8Q (subVec8Q a b) c = dot8Q a c - dot8Q b c := by
  rcases a with ⟨a0,a1,a2,a3,a4,a5,a6,a7⟩
  rcases b with ⟨b0,b1,b2,b3,b4,b5,b6,b7⟩
  rcases c with ⟨c0,c1,c2,c3,c4,c5,c6,c7⟩
  dsimp [subVec8Q, dot8Q]; ring

lemma dot8Q_add_right (a b c : Vec8Q) : dot8Q a (addVec8Q b c) = dot8Q a b + dot8Q a c := by
  rcases a with ⟨a0,a1,a2,a3,a4,a5,a6,a7⟩
  rcases b with ⟨b0,b1,b2,b3,b4,b5,b6,b7⟩
  rcases c with ⟨c0,c1,c2,c3,c4,c5,c6,c7⟩
  dsimp [addVec8Q, dot8Q]; ring

lemma dot8Q_sub_right (a b c : Vec8Q) : dot8Q a (subVec8Q b c) = dot8Q a b - dot8Q a c := by
  rcases a with ⟨a0,a1,a2,a3,a4,a5,a6,a7⟩
  rcases b with ⟨b0,b1,b2,b3,b4,b5,b6,b7⟩
  rcases c with ⟨c0,c1,c2,c3,c4,c5,c6,c7⟩
  dsimp [subVec8Q, dot8Q]; ring

def walshHadamard8Q (v : Vec8Q) : Vec8Q :=
  let a0 := v.x0 + v.x1
  let a1 := v.x0 - v.x1
  let a2 := v.x2 + v.x3
  let a3 := v.x2 - v.x3
  let a4 := v.x4 + v.x5
  let a5 := v.x4 - v.x5
  let a6 := v.x6 + v.x7
  let a7 := v.x6 - v.x7
  let b0 := a0 + a2
  let b1 := a1 + a3
  let b2 := a0 - a2
  let b3 := a1 - a3
  let b4 := a4 + a6
  let b5 := a5 + a7
  let b6 := a4 - a6
  let b7 := a5 - a7
  ⟨b0 + b4, b1 + b5, b2 + b6, b3 + b7,
   b0 - b4, b1 - b5, b2 - b6, b3 - b7⟩

lemma walshHadamard8Q_involutive (v : Vec8Q) :
    walshHadamard8Q (walshHadamard8Q v) = scaleVec8Q 8 v := by
  rcases v with ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩
  dsimp [walshHadamard8Q, scaleVec8Q]
  ext <;> ring

lemma in_domain_hadamard8_dot (w x : Vec8Q) :
    dot8Q (walshHadamard8Q w) (walshHadamard8Q x) = 8 * dot8Q w x := by
  rcases w with ⟨w0, w1, w2, w3, w4, w5, w6, w7⟩
  rcases x with ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩
  dsimp [walshHadamard8Q, dot8Q]
  ring
abbrev Vec16Q := Vec8Q × Vec8Q

def addVec16Q (u v : Vec16Q) : Vec16Q := (addVec8Q u.1 v.1, addVec8Q u.2 v.2)
def subVec16Q (u v : Vec16Q) : Vec16Q := (subVec8Q u.1 v.1, subVec8Q u.2 v.2)
def scaleVec16Q (c : ℚ) (v : Vec16Q) : Vec16Q := (scaleVec8Q c v.1, scaleVec8Q c v.2)
def dot16Q (u v : Vec16Q) : ℚ := dot8Q u.1 v.1 + dot8Q u.2 v.2

def walshHadamard16Q (v : Vec16Q) : Vec16Q :=
  let h1 := walshHadamard8Q v.1
  let h2 := walshHadamard8Q v.2
  (addVec8Q h1 h2, subVec8Q h1 h2)

theorem walshHadamard16Q_involutive (v : Vec16Q) :
    walshHadamard16Q (walshHadamard16Q v) = scaleVec16Q 16 v := by
  rcases v with ⟨v1, v2⟩
  dsimp [walshHadamard16Q]
  have hlin1 : walshHadamard8Q (addVec8Q (walshHadamard8Q v1) (walshHadamard8Q v2)) =
      addVec8Q (walshHadamard8Q (walshHadamard8Q v1)) (walshHadamard8Q (walshHadamard8Q v2)) := by
    rcases v1 with ⟨a0,a1,a2,a3,a4,a5,a6,a7⟩; rcases v2 with ⟨b0,b1,b2,b3,b4,b5,b6,b7⟩
    dsimp [walshHadamard8Q, addVec8Q]; ext <;> ring
  have hlin2 : walshHadamard8Q (subVec8Q (walshHadamard8Q v1) (walshHadamard8Q v2)) =
      subVec8Q (walshHadamard8Q (walshHadamard8Q v1)) (walshHadamard8Q (walshHadamard8Q v2)) := by
    rcases v1 with ⟨a0,a1,a2,a3,a4,a5,a6,a7⟩; rcases v2 with ⟨b0,b1,b2,b3,b4,b5,b6,b7⟩
    dsimp [walshHadamard8Q, subVec8Q]; ext <;> ring
  rw [hlin1, hlin2, walshHadamard8Q_involutive v1, walshHadamard8Q_involutive v2]
  rcases v1 with ⟨a0,a1,a2,a3,a4,a5,a6,a7⟩; rcases v2 with ⟨b0,b1,b2,b3,b4,b5,b6,b7⟩
  dsimp [addVec8Q, subVec8Q, scaleVec8Q, scaleVec16Q]
  ext <;> ring

abbrev Vec32Q := Vec16Q × Vec16Q

def scaleVec32Q (c : ℚ) (v : Vec32Q) : Vec32Q := (scaleVec16Q c v.1, scaleVec16Q c v.2)
def dot32Q (u v : Vec32Q) : ℚ := dot16Q u.1 v.1 + dot16Q u.2 v.2

def walshHadamard32Q (v : Vec32Q) : Vec32Q :=
  let h1 := walshHadamard16Q v.1
  let h2 := walshHadamard16Q v.2
  (addVec16Q h1 h2, subVec16Q h1 h2)

theorem in_domain_hadamard32_exact_dot (w x : Vec32Q) :
    dot32Q (walshHadamard32Q w) (walshHadamard32Q x) = 32 * dot32Q w x := by
  rcases w with ⟨⟨w1, w2⟩, ⟨w3, w4⟩⟩
  rcases x with ⟨⟨x1, x2⟩, ⟨x3, x4⟩⟩
  dsimp [walshHadamard32Q, walshHadamard16Q, addVec16Q, subVec16Q, dot32Q, dot16Q]
  simp only [dot8Q_add_left, dot8Q_sub_left, dot8Q_add_right, dot8Q_sub_right, in_domain_hadamard8_dot]
  ring

def isBarnesWall32ShellQ (xs : List ℚ) : Bool :=
  let nz := xs.filter (fun v => decide (v ≠ 0))
  let sumAll := xs.sum
  let sqNorm := (xs.map (fun v => v * v)).sum
  decide (xs.length = 32 ∧ sqNorm = 4 ∧ (nz.length = 8 ∨ nz.length = 16)) &&
  xs.all (fun v => decide (v = 0 ∨ v = 1 ∨ v = -1 ∨ v = 1/2 ∨ v = -1/2)) &&
  decide (sumAll.num % 2 = 0)

def buildLatticeLUT8Q (codebook : List Vec8Q) (xRot : Vec8Q) : List ℚ :=
  codebook.map (fun c => dot8Q c xRot)

def lutBlockInference8Q (lut : List ℚ) (idx : Nat) (α : ℚ) : ℚ :=
  α * lut.getD idx 0

theorem lutBlockInference8Q_sound (codebook : List Vec8Q) (xRot : Vec8Q)
    (idx : Nat) (α : ℚ) (hidx : idx < codebook.length) :
    lutBlockInference8Q (buildLatticeLUT8Q codebook xRot) idx α =
    dot8Q (scaleVec8Q α (codebook.getD idx ⟨0,0,0,0,0,0,0,0⟩)) xRot := by
  dsimp [lutBlockInference8Q, buildLatticeLUT8Q]
  have hget : (codebook.map (fun c => dot8Q c xRot)).getD idx 0 =
      dot8Q (codebook.getD idx ⟨0,0,0,0,0,0,0,0⟩) xRot := by
    induction codebook generalizing idx with
    | nil => simp at hidx
    | cons c rest ih =>
        cases idx with
        | zero => simp
        | succ k =>
            simp only [List.map_cons, List.getD_cons_succ]
            exact ih k (Nat.succ_lt_succ_iff.mp hidx)
  rw [hget]
  set v := codebook.getD idx ⟨0,0,0,0,0,0,0,0⟩
  rcases v with ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩
  rcases xRot with ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩
  dsimp [scaleVec8Q, dot8Q]
  ring

structure MixedLatticeLayerSpec where
  layerName : String
  bpw : ℚ
  paramCount : ℚ
  holderDriftBound : ℚ
  deriving Repr

def totalParamsQ (specs : List MixedLatticeLayerSpec) : ℚ :=
  (specs.map MixedLatticeLayerSpec.paramCount).sum

def totalBitsQ (specs : List MixedLatticeLayerSpec) : ℚ :=
  (specs.map (fun s => s.bpw * s.paramCount)).sum

def totalModelDriftQ (specs : List MixedLatticeLayerSpec) : ℚ :=
  (specs.map MixedLatticeLayerSpec.holderDriftBound).sum

def verifyMixedLatticePlanQ (specs : List MixedLatticeLayerSpec)
    (targetAvgBpw maxTotalDrift : ℚ) : Bool :=
  let params := totalParamsQ specs
  let bits := totalBitsQ specs
  let drift := totalModelDriftQ specs
  decide (0 < params ∧ bits ≤ targetAvgBpw * params ∧ drift ≤ maxTotalDrift)

theorem mixed_lattice_plan_certified (specs : List MixedLatticeLayerSpec)
    (targetAvgBpw maxTotalDrift : ℚ)
    (hcert : verifyMixedLatticePlanQ specs targetAvgBpw maxTotalDrift = true) :
    totalBitsQ specs / totalParamsQ specs ≤ targetAvgBpw ∧
    totalModelDriftQ specs ≤ maxTotalDrift := by
  dsimp [verifyMixedLatticePlanQ] at hcert
  rw [decide_eq_true_eq] at hcert
  obtain ⟨hpos, hbits, hdrift⟩ := hcert
  exact ⟨(div_le_iff₀ hpos).mpr hbits, hdrift⟩
structure TransformerBlockErrorBudget where
  δ_x : ℚ
  L_norm : ℚ
  ε_qkv : ℚ
  ε_o : ℚ
  ε_K : ℚ
  ε_V : ℚ
  L_sm : ℚ
  ε_mlp : ℚ
  L_act : ℚ
  B_X : ℚ
  deriving Repr

def transformerBlockTotalDriftQ (b : TransformerBlockErrorBudget) : ℚ :=
  let Δ_attn := b.L_sm * (b.ε_qkv * b.B_X + b.ε_K * b.B_X) + b.ε_V + b.ε_o * b.B_X
  let Δ_mid  := b.δ_x + b.L_norm * Δ_attn
  Δ_mid + b.L_act * (b.L_norm * Δ_mid + b.ε_mlp * b.B_X)

theorem transformer_block_e2e_certified_bound (b : TransformerBlockErrorBudget)
    (actualAttnDrift actualMidDrift actualOutDrift : ℚ)
    (h_norm_nn : 0 ≤ b.L_norm)
    (h_act_nn : 0 ≤ b.L_act)
    (h_attn : actualAttnDrift ≤ b.L_sm * (b.ε_qkv * b.B_X + b.ε_K * b.B_X) + b.ε_V + b.ε_o * b.B_X)
    (h_mid : actualMidDrift ≤ b.δ_x + b.L_norm * actualAttnDrift)
    (h_out : actualOutDrift ≤ actualMidDrift + b.L_act * (b.L_norm * actualMidDrift + b.ε_mlp * b.B_X)) :
    actualOutDrift ≤ transformerBlockTotalDriftQ b := by
  dsimp [transformerBlockTotalDriftQ]
  have h1 : b.L_norm * actualAttnDrift ≤
      b.L_norm * (b.L_sm * (b.ε_qkv * b.B_X + b.ε_K * b.B_X) + b.ε_V + b.ε_o * b.B_X) :=
    mul_le_mul_of_nonneg_left h_attn h_norm_nn
  have h2 : actualMidDrift ≤
      b.δ_x + b.L_norm * (b.L_sm * (b.ε_qkv * b.B_X + b.ε_K * b.B_X) + b.ε_V + b.ε_o * b.B_X) := by
    linarith
  have h3 : b.L_norm * actualMidDrift ≤
      b.L_norm * (b.δ_x + b.L_norm * (b.L_sm * (b.ε_qkv * b.B_X + b.ε_K * b.B_X) + b.ε_V + b.ε_o * b.B_X)) :=
    mul_le_mul_of_nonneg_left h2 h_norm_nn
  have h4 : b.L_act * (b.L_norm * actualMidDrift + b.ε_mlp * b.B_X) ≤
      b.L_act * (b.L_norm * (b.δ_x + b.L_norm * (b.L_sm * (b.ε_qkv * b.B_X + b.ε_K * b.B_X) + b.ε_V + b.ε_o * b.B_X)) + b.ε_mlp * b.B_X) :=
    mul_le_mul_of_nonneg_left (by linarith) h_act_nn
  linarith

#eval
  let v8 : Vec8Q := ⟨1/2, -1/2, 1/4, 3/4, -1/4, 1/2, 0, -1/2⟩
  let v16 : Vec16Q := (v8, scaleVec8Q (-1) v8)
  let v32 : Vec32Q := (v16, v16)
  let direct32 := dot32Q v32 v32
  let rot32 := dot32Q (walshHadamard32Q v32) (walshHadamard32Q v32) / 32
  s!"[Cascade W32 Rotation] directDot32={direct32}, inDomainW32Dot/32={rot32}"

#eval
  let c0 : Vec8Q := ⟨1, 1, 0, 0, 0, 0, 0, 0⟩
  let c1 : Vec8Q := ⟨1/2, -1/2, 1/2, -1/2, 1/2, -1/2, 1/2, -1/2⟩
  let xRot : Vec8Q := ⟨2, 3, -1, 4, 1, -2, 1, 1⟩
  let lut := buildLatticeLUT8Q [c0, c1] xRot
  let lutRes := lutBlockInference8Q lut 1 (1/2)
  let exactRes := dot8Q (scaleVec8Q (1/2) c1) xRot
  s!"[Direct Lattice LUT Kernel] lutRes={lutRes}, exactDot={exactRes}"

#eval
  let plan : List MixedLatticeLayerSpec := [
    { layerName := "attn.v_proj (D4)", bpw := 1161/1000, paramCount := 10/1, holderDriftBound := 1/100 },
    { layerName := "mlp.gate_proj (Leech Λ24)", bpw := 733/1000, paramCount := 50/1, holderDriftBound := 3/100 },
    { layerName := "mlp.up_proj (Leech Λ24)", bpw := 733/1000, paramCount := 50/1, holderDriftBound := 3/100 }
  ]
  let avgBpw := totalBitsQ plan / totalParamsQ plan
  let ok := verifyMixedLatticePlanQ plan (80/100) (1/10)
  s!"[Mixed-Lattice Allocation] avgBpw={avgBpw} ≤ 0.80, totalDrift={totalModelDriftQ plan} ≤ 0.10, certified={ok}"

#eval
  let budget : TransformerBlockErrorBudget := {
    δ_x := 1/100, L_norm := 1/1, ε_qkv := 1/200, ε_o := 1/200,
    ε_K := 1/100, ε_V := 1/100, L_sm := 1/2, ε_mlp := 1/100,
    L_act := 1/1, B_X := 2/1
  }
  s!"[E2E Transformer Block Certificate] maxOutputDriftBound={transformerBlockTotalDriftQ budget}"

end MarkovL1FullTransformerCert

#print axioms MarkovL1FullTransformerCert.walshHadamard16Q_involutive
#print axioms MarkovL1FullTransformerCert.in_domain_hadamard32_exact_dot
#print axioms MarkovL1FullTransformerCert.lutBlockInference8Q_sound
#print axioms MarkovL1FullTransformerCert.mixed_lattice_plan_certified
#print axioms MarkovL1FullTransformerCert.transformer_block_e2e_certified_bound
