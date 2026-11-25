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



/-!
# Main.lean

* **Author:** E. S. Markov (ORCID: 0009-0005-2235-5464)
* **Affiliation:** Independent Researcher, Astrakhan, Russia
* **Repository:** https://github.com/fomamarkov-creator/l1-projection-complexity-lean4
* **License:** GNU Affero General Public License v3.0 (AGPLv3)
* **Toolchain:** Lean `v4.37.0-rc1` / Mathlib

## Overview
# Standalone Certified CLI Solver and Benchmark Suite (l1solver)

-/

open MarkovL1Complexity
open MarkovL1Solver
open MarkovL1WeightedSolver
open MarkovL1TernaryQuantizer

/-- Разбор списка рациональных чисел (целых или дробей вида `a/b`) из строки -/
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

/-- Вывод справки по использованию консольного сертифицированного решателя -/
def printHelp : IO Unit := do
  IO.println "==================================================================="
  IO.println " Certified ℓ₁ Metric Projection Solver (Lean 4 Verified Engine)"
  IO.println " Author: E. S. Markov | License: AGPLv3"
  IO.println "==================================================================="
  IO.println "Usage:"
  IO.println "  l1solver --demo                  Run built-in certified benchmarks"
  IO.println "  l1solver --dipole <x0,x1,...>    Solve decoupled dipole pairs (Δ = 1)"
  IO.println "                                   on adjacent pairs {0,1}, {2,3}, ..."
  IO.println "Example:"
  IO.println "  l1solver --dipole 10,4,-6,2"

/-- Запуск встроенных сертифицированных тестов по всем модулям -/
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

/-- Интерактивный запуск дипольного решателя на пользовательском векторе четной длины -/
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

def main (args : List String) : IO Unit := do
  match args with

  | [] | ["--demo"] => runDemo
  | ["--help"] | ["-h"] => printHelp
  | ["--dipole", csv] => runDipoleCLI csv
  | _ =>
      IO.println "Unknown arguments."
      printHelp
