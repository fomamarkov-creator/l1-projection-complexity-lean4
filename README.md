[![Lean Action CI](../../actions/workflows/lean_action_ci.yml/badge.svg)](../../actions/workflows/lean_action_ci.yml)

**Toolchain:** Lean `v4.37.0-rc1` | **Verified Theorems:** 27 | **Sorry count:** 0 | **License:** AGPL-3.0

# Combinatorial Complexity Phase Transitions of $\ell_1$ Metric Projection Null Layers

Machine-checked formal verification, certified rational solvers, proof-by-reflection tactics, and a native CLI executable in **Lean 4** characterizing the computational complexity dichotomy of null layers $P_V^{-1}(0)$ of multivalued metric projections in finite-dimensional $\ell_1^m$ spaces.

* **Author:** E. S. Markov (ORCID: `0009-0005-2235-5464`)
* **Affiliation:** Independent Researcher, Astrakhan, Russia
* **License:** GNU Affero General Public License v3.0 (AGPLv3)

---

## Repository Architecture

1. **`MarkovL1Complexity.lean`** *(Core Mathematical Theory — 21 verified theorems, `0 sorry`s)*
   * **Bipolar Orthogonality Duality:** Exact characterization of bipolar vectors $u \in \{-1, 1\}^m$ in $P_V^{-1}(0)$ via Euclidean orthogonality.
   * **Universal NP-Completeness:** Polynomial-time many-one reductions from `Subset-Sum`, `Partition`, and general `3-SAT`.
   * **Polynomial-Time Tractability ($\Delta = 1$):** Blockwise median decomposition and $O(m)$ dipole-pair selectors for disjoint supports.
   * **Phase-Transition Barriers:** Strict layer expansion, sign-propagation rigidity at $\Delta = 2$, and the exponential superincreasing barrier $a_i = 2^i$.

2. **`MarkovL1Solver.lean`** *(Certified Dipole Solver & Multidimensional Verifier over $\mathbb{Q}$)*
   * Constructive $O(m)$ solver for decoupled dipole blocks and polynomial-time certificate checker for `MultiSpan` systems with formal soundness proofs.

3. **`MarkovL1WeightedSolver.lean`** *(Certified General Block-Median Solver over $\mathbb{Q}$)*
   * Exact $O(|B_b| \log |B_b|)$ merge-sort median solver for disjoint blocks of arbitrary sizes with formal subgradient balance proofs.

4. **`MarkovL1Tactic.lean`** *(Proof-by-Reflection Automation)*
   * Custom Lean 4 tactics (`l1_zero_layer`, `l1_bipolar_cert`, `l1_block_cert`) discharging multidimensional and blockwise $\ell_1$ null-layer goals in one line.

5. **`Main.lean` (`l1solver`)** *(Standalone Native CLI Executable)*
   * Compiled command-line tool executing certified $\ell_1$ projections over exact rationals $\mathbb{Q}$.

---

## Local Build & Running the CLI Solver

```bash
lake exe cache get
lake build

# Run built-in certified benchmarks
lake exe l1solver --demo

# Solve a custom decoupled dipole instance over exact rationals
lake exe l1solver --dipole 10,4,-6,2
```
