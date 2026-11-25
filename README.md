[![Lean CI](../../actions/workflows/lean_action_ci.yml/badge.svg)](../../actions/workflows/lean_action_ci.yml)

**Lean Version:** `v4.37.0-rc1` | **Mathlib:** `v4.37.0-rc1` | **License:** AGPL-3.0

# Formal Verification of (ℓ₁) Metric Projection Complexity, Exact-Rational Solvers, and 1.58-Bit Ternary Quantization in Lean 4

Machine-checked formalization (`0 sorry`s) of \(\mathbf{P}\) vs \(\mathbf{NP}\) complexity phase transitions for (ℓ₁) metric projection null layers, constructive exact-rational (\(\mathbb{Q}\)) solvers without `Classical.choice`, proof-by-reflection tactics, and certified 1-bit / 1.58-bit neural network quantizers.

* **Author:** E. S. Markov (ORCID: `0009-0005-2235-5464`)
* **Affiliation:** Independent Researcher, Astrakhan, Russia
* **License:** GNU Affero General Public License v3.0 (AGPLv3)
 
---

## Verified Modules (17 Core Libraries + Standalone CLI)

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
10. **MarkovL1ContinuousChainDP.lean *(New)*:**
    - Eliminates discrete grid quantization (`G ⊂ ℚ`) for `Δ = 2` chain overlaps by solving the continuous Bellman recurrence over all of `ℚ^m` via convex piecewise-linear (`PWLConvexQ`) slope-clipping (`infConvAbs`) and backward trajectory reconstruction (`solveContinuousChainDP`).
    - Includes a constructive Lagrangian dual certificate verifier (`checkChainOptimalCertQ`) proving global optimality across continuous `ℚ^m`.

11. **MarkovL1TriangularActivation.lean *(New)*:**
    - Generalizes activation-weighted quantization to correlated input channels (`‖(W - Ŵ)R‖₁`) via upper-triangular Cholesky/QR error feedback (`quantizeBlockTriangularQ`).
    - Formally proves `triangular_channel_exact_reduction`, showing that off-diagonal channel correlations reduce identically to sequential 1D weighted projections on compensated weights `w̃_j`.

12. **MarkovL1GeneralTreewidthFPT.lean *(New)*:**
    - Extends bounded-treewidth dynamic programming from chains (`k = 1, Δ = 2`) to treewidth `k = 2` (`Δ = 3`) triple-overlap graphs (`solveTripleOverlapFPT` in `O(m |G|³)` time), modeling joint quantization of coupled transformer projections (`W_Q, W_K, W_V`).

13. **MarkovL1NextGenQuantizer.lean *(New)*:**
    - Formalizes next-generation exact-rational ($\mathbb{Q}$) $\ell_1$ quantization primitives beyond symmetric blockwise 1.58-bit scaling:
      - `hadamard4Q_involutive` & `hadamard4Q_dot_invariant`: rational $4 \times 4$ Walsh–Hadamard incoherence rotation (normalized by $1/2$, avoiding irrational $\sqrt{2}$) that preserves inner products while dispersing heavy-tailed channel outliers.
      - `asymBlockErrorQ_split`: decoupled positive/negative threshold and median scale optimization over the asymmetric ternary alphabet $\{-\alpha_-, 0, +\alpha_+\}$.
      - `residual_cascade_error_eq` & `quantizeResidual2StageQ`: two-stage residual ternary cascade ($w \approx \hat{w}_1 + \hat{w}_2$, $3.16$ bits/weight without multiplications) with machine-checked residual error reduction.
     -
14. **MarkovL1SuperQuantizer.lean *(New)*:**
    - Unifies Hadamard $H_4$ incoherence rotation, $D_4$ root lattice vector quantization ($\approx 1.16$ bits/weight, 25 verified root states), asymmetric ternary scales, and two-stage residual cascades into an adaptive self-certifying super-quantizer (`superQuantize4Q`):
      - `d4Alphabet_all_valid`: machine-checked verification of the 25-element $D_4$ root shell alphabet.
      - `hadamard4Q_l1_bound`: proves inverse Hadamard distortion amplification is bounded by $2\times$ in $\ell_1$.
      - `superQuantize4Q_certified_bound`: end-to-end formal guarantee that restored weights in the original neural network basis satisfy $\|w - \hat{w}\|_1 \le \varepsilon_{\text{cert}}$.
      - 
15. **MarkovL1UltimateE8Engine.lean *(New)*:**
    - Pushes certified exact-rational ($\mathbb{Q}$) quantization below the $1$-bit-per-weight barrier ($\approx 0.989\text{ b/w}$) and proves full-network stability guarantees:
      - `e8Alphabet_all_valid`: machine-checked verification of all $241$ rational points of the 8D $E_8$ root shell ($0 + 112$ integer roots $+ 128$ spinor roots).
      - `walshHadamard8Q_involutive`: exact rational $8 \times 8$ Walsh–Hadamard transform ($W_8(W_8(v)) = 8v$ without irrational $\sqrt{8}$).
      - `triangular_e8_residual_identity`: fuses $E_8$ lattice quantization with Cholesky/QR activation error feedback.
      - `deep_network_l1_error_bound`: end-to-end compositional $\ell_1$ logit-drift certification across $L$-layer deep neural networks.
      - 
16. **MarkovL1AttentionKVCache.lean *(New)*:**
    - Formalizes multiplier-free in-domain Walsh–Hadamard inference and certified Attention KV-Cache compression:
      - `in_domain_hadamard_exact_dot`: proves $(W_8 w) \cdot (W_8 x) = 8 (w \cdot x)$, eliminating inverse weight transforms at runtime.
      - `holder_l1_linf_bound`: exact $\ell_1$-$\ell_\infty$ Hölder drift bound for quantized linear projections.
      - `attention_logit_drift_bound` & `attention_value_drift_bound`: end-to-end error certificates for quantized Key ($\hat{K}$) and Value ($\hat{V}$) tensors in Transformer attention.
      - 

17. **MarkovL1LeechAndLowRank.lean *(New)*:**
    - Reaches the 24-dimensional sphere-packing limit ($\Lambda_{24}$, $\approx 0.733$ bits/weight) and formalizes data-free low-rank $\ell_1$ residual compensation:
      - `golay24_code_verified`: machine-checked verification of all $2^{12} = 4096$ codewords of the extended binary Golay code $\mathcal{G}_{24}$ with minimum Hamming weight $d_{\min} = 8$.
      - `projectLeech24OctadQ`: constructive 24D Leech lattice quantizer in scaled rational arithmetic ($8 \cdot \Lambda_{24} \subset \mathbb{Z}^{24}$).
      - `rank1_weighted_median_identity`: exact factorization reducing matrix rank-$1$ $\ell_1$-LoRA residual updates ($E \approx u v^T$) to 1D weighted medians.
      
---

## Build & Run

```bash
lake exe cache get
lake build
lake exe l1solver --demo
```
