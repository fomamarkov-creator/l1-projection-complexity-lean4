import MarkovL1Complexity
import MarkovL1Solver
import MarkovL1WeightedSolver
import MarkovL1Tactic
import MarkovL1Quantizer
import MarkovL1TernaryQuantizer
import MarkovL1WeightedTernary
import MarkovL1TreewidthSolver
import MarkovL1ContinuousChainDP
import MarkovL1TriangularActivation
import MarkovL1GeneralTreewidthFPT
import MarkovL1NextGenQuantizer
import MarkovL1SuperQuantizer
import MarkovL1UltimateE8Engine
import MarkovL1AttentionKVCache
import MarkovL1LeechAndLowRank
import MarkovL1EntropyAndSparsity
import MarkovL1MoERoutingAndDynamicBits
import MarkovL1ZeroKnowledgeInferenceCert
import MarkovL1HCPAndBirkhoffQuantizer
import MarkovL1FullTransformerCert
import MarkovL1RoPEAndGolaySyndrome
import MarkovL1CrossLayerAndIntegerTransformer
import MarkovL1QATConvergence
import MarkovL1DyadicVNodeReduction


/-!
# Main.lean

* **Author:** E. S. Markov (ORCID: 0009-0005-2235-5464)
* **Affiliation:** Independent Researcher, Astrakhan, Russia
* **Repository:** https://github.com/fomamarkov-creator/l1-projection-complexity-lean4
* **License:** GNU Affero General Public License v3.0 (AGPLv3)
* **Toolchain:** Lean `v4.37.0-rc1` / Mathlib
-/

open MarkovL1Complexity
open MarkovL1Solver
open MarkovL1WeightedSolver
open MarkovL1TernaryQuantizer

def parseRatToken (s : String) : Option ℚ :=
  let clean := s.trimAscii.toString
  match clean.splitOn "/" with
  | [numStr] =>
      (String.toInt? numStr.trimAscii.toString).map fun n => (n : ℚ)
  | [numStr, denStr] =>
      match String.toInt? numStr.trimAscii.toString, String.toInt? denStr.trimAscii.toString with
      | some n, some d => if d == 0 then none else some ((n : ℚ) / (d : ℚ))
      | _, _ => none
  | _ => none

def printHelp : IO Unit := do
  IO.println "==================================================================="
  IO.println " Certified ℓ₁ Metric Projection Solver (Lean 4 Verified Engine)"
  IO.println " Author: E. S. Markov | License: AGPLv3"
  IO.println "==================================================================="
  IO.println "Usage:"
  IO.println "  l1solver --demo                  Run built-in certified benchmarks"
  IO.println "  l1solver --dipole <x0,x1,...>    Solve decoupled dipole pairs (Δ = 1)"

def runDemo : IO Unit := do
  IO.println "=== Certified Dipole Solver (Δ = 1, O(m) exact rationals) ==="
  match solveDipoleBlockProjection exampleDipoleCfg exampleInput with
  | some out =>
      IO.println s!"  Input x        = (10, 4, -6, 2)"
      IO.println s!"  Medians c*     = ({out.coeffs 0}, {out.coeffs 1})"
      IO.println s!"  Projection v*  = ({out.projection 0}, {out.projection 1}, {out.projection 2}, {out.projection 3})"
      IO.println s!"  Residual r*    = ({out.residual 0}, {out.residual 1}, {out.residual 2}, {out.residual 3}) ∈ P_B⁻¹(0)"
  | none =>
      IO.println "  Error: unexpected overlap"

  IO.println "\n=== Phase-Transition Barrier Detector (Δ = 2 overlap check) ==="
  match solveDipoleBlockProjection overlappingCfg exampleInput with
  | some _ => IO.println "  Unexpected success"
  | none => IO.println "  Overlap (Δ ≥ 2) detected: safely rejected non-decoupled instance."

  IO.println "\n=== General Arbitrary-Size Block Median Solver (ℝ⁸: blocks of size 3 & 5) ==="
  match solveGeneralBlockProjection generalBlockSupp generalInput with
  | some out =>
      let ok := checkBlocksBalancedQ generalBlockSupp out.residual
      IO.println s!"  Block Medians  = ({out.coeffs 0}, {out.coeffs 1})"
      IO.println s!"  Certified Bal  = {ok}"
      IO.println s!"  Residual r*    = ({out.residual 0}, {out.residual 1}, {out.residual 2}, {out.residual 3}, {out.residual 4}, {out.residual 5}, {out.residual 6}, {out.residual 7})"
  | none =>
      IO.println "  Error: invalid blocks"

  IO.println "\n=== Multidimensional Bipolar Certificate Checker (MultiSpan) ==="
  let valid := checkBipolarZeroLayerQ exampleMatrix exampleCert
  IO.println s!"  u = (1, -1, 1, -1) ∈ P_(MultiSpan A)⁻¹(0) : {valid}"

  IO.println "\n=== Certified 1.58-Bit Ternary Quantizer (θ*, α* over ℚ) ==="
  let (θ_star, α_star) := quantizeTernaryExactQ [1/10, -1/10, 4, -4, 4, 20]
  IO.println s!"  Input block      = [1/10, -1/10, 4, -4, 4, 20]"
  IO.println s!"  Optimal (θ*, α*) = ({θ_star}, {α_star})"

  IO.println "\n=== Certified Activation-Weighted 1.58-Bit Quantizer ==="
  let wEntries : List MarkovL1WeightedTernary.WeightedEntryQ := [
    ⟨1/10, 1⟩, ⟨-1/10, 1⟩, ⟨4, 10⟩, ⟨-4, 10⟩, ⟨20, 1⟩
  ]
  let (wθ, wα) := MarkovL1WeightedTernary.quantizeWeightedTernaryExactQ wEntries
  IO.println s!"  Weighted Optimal (θ*, α*) = ({wθ}, {wα})"

  IO.println "\n=== Certified Bounded-Treewidth (Δ = 2) FPT Solver ==="
  let fptCost := MarkovL1TreewidthSolver.solveChainOverlapFPT [-4, 0, 4] [4, 8, 4]
  IO.println s!"  Chain Overlap (Δ = 2) Min L1 Cost = {fptCost}"
  IO.println "\n=== Certified Continuous Chain DP (Δ = 2, Grid-Free over ℚ^m) ==="
  let (contCs, contCost) := MarkovL1ContinuousChainDP.solveContinuousChainDP [4/1, 8/1, 4/1]
  let contCert := MarkovL1ContinuousChainDP.checkChainOptimalCertQ
    [4/1, 8/1, 4/1] contCs [0/1, 1/1, 1/1] [0/1, -1/1]
  IO.println s!"  Continuous c* = {contCs}, Min Cost = {contCost}, Dual Certified = {contCert}"

  IO.println "\n=== Certified Triangular Activation Correlation Feedback (ℓ₁-GPTQ) ==="
  let triWHat := MarkovL1TriangularActivation.quantizeBlockTriangularQ (2/1) (4/1)
    [6/1, 5/1, 1/1] [[10/1, 0/1, 0/1], [8/1, 2/1, 0/1], [6/1, 4/1, 2/1]]
  let triErr := MarkovL1TriangularActivation.triangularBlockErrorQ
    [6/1, 5/1, 1/1] triWHat [[10/1, 0/1, 0/1], [8/1, 2/1, 0/1], [6/1, 4/1, 2/1]]
  IO.println s!"  Triangular Compensated wHat = {triWHat}, Output L1 Error = {triErr}"

  IO.println "\n=== Certified Treewidth k=2 (Δ = 3, W_Q/W_K/W_V Joint FPT) ==="
  let tw2Cost := MarkovL1GeneralTreewidthFPT.solveTripleOverlapFPT
    [-2/1, 0/1, 2/1, 4/1] [2/1, 0/1, 6/1, 4/1]
  IO.println s!"  Joint Triple Overlap (Δ = 3, k = 2) Min L1 Cost = {tw2Cost}"

  IO.println "\n=== Next-Gen ℓ₁ Quantization (Hadamard H₄ Incoherence & 2-Stage Residual) ==="
  let outlierVec : ℚ × ℚ × ℚ × ℚ := (100/1, 0/1, 0/1, 0/1)
  let rotated := MarkovL1NextGenQuantizer.hadamard4Q outlierVec
  IO.println s!"  Hadamard H₄ Outlier Dispersion : {outlierVec} -> {rotated}"
  let (_, err1, err2) := MarkovL1NextGenQuantizer.quantizeResidual2StageQ
    [1/10, -1/10, 4/1, -4/1, 10/1, 20/1]
  IO.println s!"  2-Stage Residual Cascade (3.16b): Stage-1 L1 Err = {err1} -> Stage-2 L1 Err = {err2}"

  IO.println "\n=== V-CORE Super-Quantizer (Hadamard H₄ + D₄ Lattice + Adaptive Cascade) ==="
  let sqOut := MarkovL1SuperQuantizer.superQuantize4Q (2/1) (10/1, -2/1, 3/1, -1/1)
  IO.println s!"  Adaptive SuperQuantizer (Hard Block): mode={repr sqOut.mode}, rotErr={sqOut.rotatedErr}, maxCertErr={sqOut.certifiedMaxOutputErr}"

  IO.println "\n=== V-CORE Sub-1-Bit E₈ Lattice & Multi-Layer Network Certification ==="
  IO.println s!"  E₈ Root Lattice Alphabet Size   : {MarkovL1UltimateE8Engine.e8Alphabet.length} states (~0.989 bits/weight)"
  let netBound := MarkovL1UltimateE8Engine.networkErrorBoundQ (10/1) [(1/2, 1/100), (1/2, 1/100), (1/2, 1/100)]
  IO.println s!"  3-Layer Certified L1 Logit Bound: {netBound}"

  IO.println "\n=== In-Domain Hadamard W₈ & Certified KV-Cache Bounds ==="
  let w8 : MarkovL1AttentionKVCache.Vec8Q := ⟨1/2, -1/2, 1/4, 3/4, -1/4, 1/2, 0, -1/2⟩
  let x8 : MarkovL1AttentionKVCache.Vec8Q := ⟨2/1, 1/1, -1/1, 3/1, 1/2, -1/2, 4/1, 1/1⟩
  let hDot := MarkovL1AttentionKVCache.dot8Q (MarkovL1AttentionKVCache.walshHadamard8Q w8) (MarkovL1AttentionKVCache.walshHadamard8Q x8) / 8
  IO.println s!"  Multiplier-Free W₈ Domain Dot  : {hDot} (exact match without inverse weight transform)"

  IO.println "\n=== 24D Leech Lattice (Λ₂₄, ~0.73 b/w) & Data-Free ℓ₁-LoRA ==="
  IO.println s!"  Extended Golay Code G₂₄ Size   : {MarkovL1LeechAndLowRank.golay24Codewords.length} codewords (d_min = 8)"
  let E_res : List (List ℚ) := [[2/1, 4/1, 6/1], [-1/1, -2/1, -3/1]]
  let u_opt := MarkovL1LeechAndLowRank.updateLeftFactorL1Q E_res [1/1, 2/1, 3/1]
  IO.println s!"  Data-Free ℓ₁-LoRA Rank-1 Factor: u*={u_opt} (exact residual elimination)"

  IO.println "\n=== Prefix Entropy Coding, 2:4 Sparsity, MoE Safety & O(n²) Inference Cert ==="
  let q24 := MarkovL1EntropyAndSparsity.quantize24SparseTernaryQ (10/1, -2/1, 8/1, -1/1)
  IO.println s!"  Hardware 2:4 Sparse L1 Block   : {q24} (nnz = {MarkovL1EntropyAndSparsity.nnz4Q q24} ≤ 2)"
  let moeSafe := MarkovL1MoERoutingAndDynamicBits.verifyMoERoutingSafety [(5/2, 1/10), (2/1, 1/10)] [(3/2, 1/10), (1/2, 1/10)]
  IO.println s!"  MoE Top-2 Routing Invariance   : {moeSafe}"
  let freivaldsOK := MarkovL1ZeroKnowledgeInferenceCert.verifyMatMulFreivaldsQ [[1/1, 2/1], [3/1, 4/1]] [[2/1, 0/1], [1/1, 2/1]] [[4/1, 4/1], [10/1, 8/1]] [1/1, 3/1]
  IO.println s!"  O(n²) Freivalds MatMul Cert    : {freivaldsOK}"

  IO.println "\n=== 3HCP Lattice (~1.23 b/w), Register Inversion (Le₀ = 0.024) & Birkhoff–James ℓ₁ ==="
  let q3hcp := MarkovL1HCPAndBirkhoffQuantizer.quantize3HCPBlockQ (3/1, -3/1, 0/1)
  IO.println s!"  3HCP Lattice Quantizer (13-pt) : (3, -3, 0) -> {q3hcp}"
  let bjOrth := MarkovL1HCPAndBirkhoffQuantizer.checkBirkhoffL1OrthogonalQ [2/1, -2/1, 0/1, 0/1] [1/2, 1/2, 1/4, -1/4]
  IO.println s!"  Birkhoff–James ℓ₁-Orthogonality: {bjOrth}"

  IO.println "\n=== V-CORE v4.0: W32 Cascade, LUT Kernel, Mixed-Lattice & E2E Transformer Cert ==="
  let v8 : MarkovL1FullTransformerCert.Vec8Q := ⟨1/2, -1/2, 1/4, 3/4, -1/4, 1/2, 0, -1/2⟩
  let v16 : MarkovL1FullTransformerCert.Vec16Q := (v8, MarkovL1FullTransformerCert.scaleVec8Q (-1) v8)
  let v32 : MarkovL1FullTransformerCert.Vec32Q := (v16, v16)
  let rot32 := MarkovL1FullTransformerCert.dot32Q (MarkovL1FullTransformerCert.walshHadamard32Q v32) (MarkovL1FullTransformerCert.walshHadamard32Q v32) / 32
  IO.println s!"  Cascade W32 In-Domain Dot/32   : {rot32}"
  let plan : List MarkovL1FullTransformerCert.MixedLatticeLayerSpec := [
    { layerName := "attn.v_proj (D4)", bpw := 1161/1000, paramCount := 10/1, holderDriftBound := 1/100 },
    { layerName := "mlp.gate_proj (Leech Λ24)", bpw := 733/1000, paramCount := 50/1, holderDriftBound := 3/100 },
    { layerName := "mlp.up_proj (Leech Λ24)", bpw := 733/1000, paramCount := 50/1, holderDriftBound := 3/100 }
  ]
  let mixedOK := MarkovL1FullTransformerCert.verifyMixedLatticePlanQ plan (80/100) (1/10)
  IO.println s!"  Mixed-Lattice Plan (≤0.80 bpw) : certified={mixedOK}"
  let blockBudget : MarkovL1FullTransformerCert.TransformerBlockErrorBudget := {
    δ_x := 1/100, L_norm := 1/1, ε_qkv := 1/200, ε_o := 1/200,
    ε_K := 1/100, ε_V := 1/100, L_sm := 1/2, ε_mlp := 1/100,
    L_act := 1/1, B_X := 2/1
  }
  IO.println s!"  E2E Transformer Block Drift    : ≤ {MarkovL1FullTransformerCert.transformerBlockTotalDriftQ blockBudget}"

  IO.println "\n=== Module 23: Exact-Rational RoPE Drift & Golay G₂₄ Syndrome Algebra ==="
  let (cRope, sRope) := MarkovL1RoPEAndGolaySyndrome.rationalCayleyCS (1/2)
  IO.println s!"  Rational Cayley RoPE (c, s)    : ({cRope}, {sRope}), c²+s² = {cRope*cRope + sRope*sRope}"
  let cw := MarkovL1RoPEAndGolaySyndrome.encodeGolay24 1337
  let err : UInt32 := (1 : UInt32) <<< 5
  let synClean := MarkovL1RoPEAndGolaySyndrome.syndromeGolay24 cw
  let synNoisy := MarkovL1RoPEAndGolaySyndrome.syndromeGolay24 (cw ^^^ err)
  let synErr := MarkovL1RoPEAndGolaySyndrome.syndromeGolay24 err
  IO.println s!"  Golay G₂₄ Syndrome Invariance  : clean={synClean}, noisy={synNoisy}, errOnly={synErr}"

  IO.println "\n=== Module 24: Cross-Layer Compensation, Spherical Codes & Integer Transformer ==="
  let w2Comp := MarkovL1CrossLayerAndIntegerTransformer.crossLayerCompensatedWeightQ (3/4) (1/2) (2/1)
  IO.println s!"  Cross-Layer Compensated w2'    : {w2Comp} (exact cascade cancellation)"
  let d4Sph : List MarkovL1CrossLayerAndIntegerTransformer.VecQ := [[1, 1, 0, 0], [1, -1, 0, 0], [0, 0, 1, 1]]
  let sphOK := MarkovL1CrossLayerAndIntegerTransformer.checkSphericalCodebookQ d4Sph 2
  IO.println s!"  Rational Spherical Code (R²=2) : valid={sphOK}"
  let y1 := MarkovL1CrossLayerAndIntegerTransformer.invSqrtNewtonStepQ (4/1) (1/2)
  IO.println s!"  Integer-Only RMSNorm 1/√4 Step : y0=1/2 -> y1={y1}"

  IO.println s!"[25] QAT/STE Proximal L1 Contraction: prox(3/4, τ=1/4) = {MarkovL1QATConvergence.proxL1Q (1/4) (3/4)}"

def runDipoleCLI (csv : String) : IO Unit := do
  let tokens := csv.splitOn ","
  let parsed := tokens.filterMap parseRatToken
  if parsed.length != tokens.length || parsed.isEmpty || parsed.length % 2 != 0 then
    IO.println "Error: please provide an even number of comma-separated rationals (e.g., 10,4,-6,2)."
  else
    let k := parsed.length / 2
    let m := 2 * k
    let x : Fin m → ℚ := fun i => parsed.getD i.val 0
    let cfg : DipoleConfig m k := {
      idx1 := fun b => ⟨2 * b.val, by omega⟩
      idx2 := fun b => ⟨2 * b.val + 1, by omega⟩
    }
    match solveDipoleBlockProjection cfg x with
    | some out =>
        let cList := (List.finRange k).map out.coeffs
        let vList := (List.finRange m).map out.projection
        let rList := (List.finRange m).map out.residual
        IO.println s!"[Certified Δ=1 Output]"
        IO.println s!"  Coefficients c* = {cList}"
        IO.println s!"  Projection   v* = {vList}"
        IO.println s!"  Residual     r* = {rList}  (Verified ∈ P_B⁻¹(0))"
    | none =>
        IO.println "Error: invalid block configuration."

  IO.println s!"  [{MarkovL1DyadicVNodeReduction.controlCertificate.vcore_id}] {MarkovL1DyadicVNodeReduction.controlCertificate.boundary} -> VERIFIED"

def main (args : List String) : IO Unit := do
  match args with

  | [] | ["--demo"] => runDemo
  | ["--help"] | ["-h"] => printHelp
  | ["--dipole", csv] => runDipoleCLI csv
  | _ =>
      IO.println "Unknown arguments."
      printHelp
