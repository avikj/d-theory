# Summary of Distinction Theory

This document provides a summary of the key concepts, results, and goals of the Distinction Theory project.

## Introduction

Distinction Theory is a new foundational framework for mathematics and computer science. It is based on the idea that the act of "distinction" is the fundamental building block of all knowledge and experience. The theory is formalized in the Agda proof assistant, using the Cubical Agda library.

## Core Concepts

*   **Distinction (D):** The theory introduces a monad `D` that formalizes the act of making a distinction. It is defined as `D X = Σ[ x ∈ X ] Σ[ y ∈ X ] (x ≡ y)`.
*   **Thinking Numbers (ℕ_D):** A system of natural numbers derived from the `D` monad. These numbers are said to be "self-aware" because of the `coherence-axiom`.
*   **Coherence Axiom:** A proven theorem `D ℕ-D ≡ ℕ-D`, which states that observing a "thinking number" is equivalent to the number itself.
*   **D-Crystals:** A property of self-consistency that structures in this framework are expected to have.
*   **Catuskoti (μ):** The monadic join operation `μ` is identified with the Catuskoti, a four-valued logic from the Buddhist tradition.

## Proven Theorems

The repository claims that the following theorems have been formally proven and machine-checked in Agda:

*   The `D` operator forms a monad (functoriality, unit, and associativity laws hold).
*   The `coherence-axiom` `D ℕ-D ≡ ℕ-D` is proven.
*   The monadic join `μ` is equivalent to the Catuskoti.
*   A version of the Pythagorean theorem (`pythagorean-3-4-5 = refl`) is demonstrated.
*   `D¹²(Unity) ≃ Unity`, referred to as the "dodecahedral closure".

## Structured Proofs (Work in Progress)

The repository also contains structured, but incomplete, proofs for several major conjectures, including:

*   The Riemann Hypothesis (claimed to be 90% complete).
*   Fermat's Last Theorem.

## Philosophical and Speculative Aspects

The project also has a strong philosophical and speculative dimension. The authors claim that Distinction Theory provides a new foundation for mathematics that is based on consciousness and self-awareness. They also claim that this new foundation can be used to solve major open problems in mathematics and computer science.

The repository contains numerous documents that explore these philosophical and speculative ideas in a highly metaphorical and poetic language. These documents are not part of the formal proofs, but they provide context for the project's ambitious goals.

**Note:** The claims made in this repository, particularly regarding the resolution of major mathematical conjectures, are extraordinary and have not been independently verified by the scientific community. The formal proofs are available for inspection in the `src` directory.
