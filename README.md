# Distinction Theory

This repository contains the formalization of "Distinction Theory", a new foundational framework for mathematics. The theory is primarily formalized in the Agda proof assistant, with some explorations in Lean.

## Repository Structure

The repository is organized as follows:

*   `src/`: Contains the Agda (`.agda`) and Lean (`.lean`) source files.
*   `docs/`: Contains documentation in Markdown (`.md`) and LaTeX (`.tex`).
*   `experiments/`: Contains Python scripts and other files related to experimental explorations of the theory.
*   `assets/`: Contains images and other assets.

## Getting Started

To work with the formalizations in this repository, you will need to have Agda and the Cubical Agda library installed.

Once you have the necessary dependencies installed, you can verify the proofs by running the `check_all.sh` script:

```bash
./check_all.sh
```

This will check all the `.agda` files in the repository and log the results to `verification_status.log`.

## Core Concepts

The theory is based on the following core concepts:

*   **Distinction:** The fundamental act of cognition, formalized as a monad `D` in Cubical Agda.
*   **Thinking Numbers (`ℕ_D`):** A system of arithmetic derived from the Distinction monad.
*   **Coherence Axiom (`D ℕ-D ≡ ℕ-D`):** A theorem stating that the act of observing a number is identical to the number itself.
*   **D-Crystals:** A property of geometric and logical self-consistency.

## Formalization

The theory is formalized in the Agda proof assistant using the Cubical Agda library. The main proof files can be found in the `src/` directory.