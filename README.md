# Relational Jerk Dynamics (RJD)

**A Minimalist Pre-Geometric Framework Driven by Fundamental Non-Locality and Discrete Third-Order Dynamics.**

## Overview
**Relational Jerk Dynamics (RJD)** explores how spacetime, elementary particles, spin-$1/2$ topology, and cosmological expansion can emerge from two foundational postulates without presupposing a background manifold or free coupling parameters:

1. **Fundamental Non-Locality:** All nodes are immediately coupled via pairwise state differences without mediating spatial distance.
2. **Discrete Jerk Imperative ($\vec{J} \neq \vec{0}$):** Third-order discrete state transitions drive evolution, while unit-vector normalization excludes static equilibria ($0/0$ singularity ban) and prevents Ostrogradski instabilities.

## Repository Contents
* `RJD/`: Machine-verified formal proofs written in **Lean 4** covering singularity avoidance, $2:1$ antitakt shell resonance, the $N \le 12$ particle saturation cutoff, $720^\circ$ double-ring spin-$1/2$ topology, and variance-driven cosmic expansion.
* `simulations/`: Vectorized **Python (`NumPy`)** scripts reproducing the $\gamma_3 = 2/3$ spherical projection limit, Platonic eigenvalues ($\sqrt{3}, \sqrt{6}$), and coordinate-free graph Laplacians.
* `paper/`: Complete **XeLaTeX / pdfLaTeX** treatise containing full mathematical proofs, TikZ/PGFPlots diagrams, comparative benchmarks, and an extensive glossary.

## Quickstart

### 1. Verify Lean 4 Proofs
Ensure [elan](https://github.com) is installed, then run:
```bash
lake update
lake build
```

### 2. Run Python Simulations
```bash
pip install numpy
python simulations/rjd_network_sim.py
```

## Provenance & Governance
This repository is governed by the **Re-Inversion Public License (RIPL v1.0)** and aligns with the anti-ZFC and third-order jerk invariants established by Johannes Geisen (`@OverThePlaces` / `@frintroper` in `ToneProjekt` and `LeanIsCorrupted`).
