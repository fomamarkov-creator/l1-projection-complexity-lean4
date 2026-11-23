[![Lean Action CI](../../actions/workflows/lean_action_ci.yml/badge.svg)](../../actions/workflows/lean_action_ci.yml)

**Toolchain:** Lean `v4.37.0-rc1` | **Verified Theorems:** 21 + 3 Soundness Proofs | **Sorry count:** 0 | **License:** AGPL-3.0

# Combinatorial Complexity Phase Transitions of $\ell_1$ Metric Projection Null Layers

Machine-checked formal verification and executable certified solver in **Lean 4** characterizing the computational complexity dichotomy of null layers $P_V^{-1}(0)$ of multivalued metric projections in finite-dimensional $\ell_1^m$ spaces.

* **Author:** E. S. Markov (ORCID: `0009-0005-2235-5464`)
* **Affiliation:** Independent Researcher, Astrakhan, Russia
* **License:** GNU Affero General Public License v3.0 (AGPLv3)

---

## Repository Structure

1. **`MarkovL1Complexity.lean`** *(Core Theory — 21 verified theorems, `0 sorry`s)*
   * **Bipolar Orthogonality Duality:** Exact characterization of bipolar vectors in $P_V^{-1}(0)$ via Euclidean orthogonality.
   * **Universal NP-Completeness:** Polynomial-time reductions from `Subset-Sum`, `Partition`, and general `3-SAT`.
   * **Polynomial-Time Tractability ($\Delta = 1$):** Blockwise median decomposition and $O(m)$ dipole-pair selectors for disjoint supports.
   * **Phase-Transition Barriers:** Layer expansion, sign-propagation rigidity at $\Delta = 2$, and the superincreasing barrier $a_i = 2^i$.

2. **`MarkovL1Solver.lean`** *(Executable Certified Solver & Verifier over $\mathbb{Q}$)*
   * Computable detectors, $O(m)$ block solvers with formal soundness proofs, certificate verifiers, and executable `#eval` test cases.

---

## Local Build & Verification

```bash
lake exe cache get
lake build
```
