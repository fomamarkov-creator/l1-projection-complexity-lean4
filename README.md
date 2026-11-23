[![Lean CI](../../actions/workflows/lean_action_ci.yml/badge.svg)](../../actions/workflows/lean_action_ci.yml)

**Lean Version:** `v4.37.0-rc1` | **Mathlib:** `v4.37.0-rc1` | **License:** AGPL-3.0

# Formal Verification of (ℓ₁) Metric Projection Complexity, Exact-Rational Solvers, and 1.58-Bit Ternary Quantization in Lean 4

Machine-checked formalization (`0 sorry`s) of \(\mathbf{P}\) vs \(\mathbf{NP}\) complexity phase transitions for (ℓ₁) metric projection null layers, constructive exact-rational (\(\mathbb{Q}\)) solvers without `Classical.choice`, proof-by-reflection tactics, and certified 1-bit / 1.58-bit neural network quantizers.

* **Author:** E. S. Markov (ORCID: `0009-0005-2235-5464`)
* **Affiliation:** Independent Researcher, Astrakhan, Russia
* **License:** GNU Affero General Public License v3.0 (AGPLv3)
 
---

## Verified Modules (9 Core Libraries + Standalone CLI)

1. **`MarkovL1Complexity.lean`:**
   * Formalizes the \(\mathbf{P}\) vs \(\mathbf{NP}\) dichotomy for \(\ell_1\) metric projection null layers \(P_B^{-1}(0)\): proves polynomial-time solvability via blockwise medians for decoupled supports (\(\Delta = 1\)) and geometric `3-SAT` NP-completeness for overlapping supports (\(\Delta \ge 2\)) as well as exponential weight barriers (\(a_i = 2^i\)).
2. **`MarkovL1Solver.lean`:**
   * Constructive, `Classical.choice`-free exact-rational (\(\mathbb{Q}\)) dipole block projection solver (`solveDipoleBlockProjection`) with \(O(m)\) runtime and overlap rejection.
3. **`MarkovL1WeightedSolver.lean`:**
   * General arbitrary-size decoupled block median solver (`solveGeneralBlockProjection`) and subgradient sign-balance certificate checker (`checkBlocksBalancedQ`).
4. **`MarkovL1Tactic.lean`:**
   * Proof-by-reflection tactic `l1_zero_layer` and multidimensional `MultiSpan` bipolar certificate verifier (`checkBipolarZeroLayerQ`).
5. **`MarkovL1Quantizer.lean`:**
   * Certified group-wise 1-bit bipolar neural network quantizer (`quantizeBipolarBlockwiseQ`) proving global \(\ell_1\)-optimality of blockwise median scales \(\alpha_b^* = \mathrm{median}(\vert{}w_i\vert{}_{i \in S_b})\).
6. **`MarkovL1TernaryQuantizer.lean` *(New)*:**
   * Formalizes sparse **1.58-bit ternary quantization** (`{-1, 0, +1}`) with zero-zone thresholding \(\theta \ge 0\):
     * `pointErrorQ_eq_split`: exact decomposition of ternary \(\ell_1\) error into pruned tail and active residual.
     * `blockErrorQ_const_on_gap`: proves error invariance between order statistics, reducing continuous non-convex optimization over \(\theta \in [0, \infty)\) to a finite polynomial-time search over critical thresholds \(\{0\} \cup \{\vert{}w_i\vert{}\}\).
     * `quantizeTernaryExactQ_certified_optimal`: machine-checked optimality certificate over exact rationals \(\mathbb{Q}\).
7. **`Main.lean` \(\to\) `l1solver`:**
   * Standalone native executable running all certified benchmarks (`--demo`) and interactive exact-rational queries (`--dipole`).

8. **`MarkovL1WeightedTernary.lean`:**
   * Formalizes activation-weighted 1.58-bit ternary $\ell_1$ projections ($\sum \gamma_i |w_i - Q_{\theta,\alpha}(w_i)|$) over exact rationals $\mathbb{Q}$ using constructive weighted medians (`quantizeWeightedTernaryExactQ_certified`).
9. **`MarkovL1TreewidthSolver.lean`:**
   * Proves polynomial-time fixed-parameter tractability (FPT) for structured $\Delta = 2$ chain overlaps (`solveChainOverlapFPT`), bridging the boundary between $\mathbf{P}$ and $\mathbf{NP}$.
   * 
---

## Build & Run

```bash
lake exe cache get
lake build
lake exe l1solver --demo
```
