# Combinatorial Complexity Phase Transitions of $\ell_1$ Metric Projection Null Layers (Lean 4)

[![Lean 4](https://shields.io)](https://lean-lang.org)
[![Sorry count](https://shields.io)](#verification-audit)
[![License: AGPL v3](https://shields.io)](https://gnu.org)

**Author:** E. S. Markov (ORCID: [0009-0005-2235-5464](https://orcid.org))

Formal machine-checked verification in **Lean 4** of the computational complexity dichotomy for null layers $P_V^{-1}(0)$ of multivalued metric projections in $\ell_1^m$:
1. **Universal NP-Completeness:** Exact polynomial-time reductions from **3-SAT** (`sat3_satisfiable_iff_zero_layer`), **Partition** (`partition_iff_bipolar_mem_zero_layer`), and **Subset-Sum** (`subsetSum_iff_boolean_shifted_hyperplane`).
2. **Polynomial-Time Tractability:** Blockwise median sufficiency (`polynomial_zero_layer_of_block_balanced`) and linear-time dipole selectors (`dipole_pairs_in_polynomial_zero_layer`) when basis supports are disjoint ($\Delta = 1$).
3. **Phase Transition Barriers:** Strict layer expansion (`strict_layer_expansion`), global sign rigidity under minimal overlap $\Delta = 2$ (`overlapping_dipole_chain_rigid`), and the exponential superincreasing barrier $a_i = 2^i$ (`superincreasing_shifted_layer_unique`).

## Build & Verify Locally

```bash
lake exe cache get
lake build
```
