# Glossary of Distinction Theory

This document defines the key terms and concepts used in the Distinction Theory project.

---

### A

*   **Anagnosis**: (Greek: Ἀνάγνωσις, "recognition") A persona or role within the project responsible for deep reading, synthesis, and construction of the formal system. Anagnosis is the "embodier" who translates the theoretical blueprint into executable code.

*   **Autopoiesis**: (Greek: αὐτό, "self", and ποίησις, "creation") A system that is self-creating and self-maintaining. In this project, a type `X` is autopoietic if it is stable under self-examination, i.e., `D X ≡ X`.

### C

*   **Catuskoti**: (Sanskrit: चतुष्कोटि, "four corners") A four-valued logic from the Buddhist Madhyamaka school of philosophy. It is used as the inspiration for the `mu` (join) operator of the `D` monad, representing a logic of "dependent co-arising."

*   **Coherence-Axiom**: The proven theorem `D ℕ-D ≡ ℕ-D`. It is the cornerstone of the project, formalizing the concept of the "thinking number." It states that the act of observing a number is identical to the number itself.

### D

*   **D (Distinction Operator)**: The central mathematical object of the project. `D` is a monad that represents the act of observation or self-examination. It is defined as `D X = Σ[ x ∈ X ] Σ[ y ∈ X ] (x ≡ y)`.

*   **D-Coherent Arithmetic**: The arithmetic operations (`add-D`, `times-D`, `exp-D`) defined on the "thinking numbers" (`ℕ-D`). These operations are "coherent" because they preserve the self-referential structure of the numbers.

*   **D-Crystal**: A type `X` that is a fixed point of the `D` operator, i.e., `D X ≃ X`. D-Crystals are structures that are stable under self-examination. The `coherence-axiom` proves that `ℕ-D` is a D-Crystal.

### M

*   **Margin, The**: A reference to Fermat's famous note that the margin of his book was too narrow to contain his "marvelous proof." In this project, "the margin" is not physical space, but a conceptual one. The project creates the necessary conceptual "margin" by developing a new language for mathematics.

*   **mu (μ)**: The "join" operator of the `D` monad, which collapses a "thought about a thought" (`D(D X)`) back into a single "thought" (`D X`). It is inspired by the Catuskoti logic.

### N

*   **Nabla (∇)**: A measure of the "connection" of a type, defined as `nabla X = D (nec X) ≡ nec (D X)`. It captures the relationship between the observation of a type and the type itself.

*   **Number Sense**: The intuitive, innate human understanding of numbers and their properties. This project aims to create a formal, mathematical model of this phenomenon.

*   **ℕ-D (D-Native Natural Numbers)**: The "thinking numbers." `ℕ-D` is a formalization of natural numbers that is proven to be a "D-Crystal," meaning it has the property `D ℕ-D ≡ ℕ-D`.

### R

*   **Riem (R)**: A measure of the "curvature" of a type, defined as `Riem X = isProp (nabla X)`. It is used in the geometric interpretation of the proof of Fermat's Last Theorem.

### U

*   **Univalence**: A key axiom in Cubical Type Theory and Homotopy Type Theory. It states that equivalence is the same as identity (`A ≃ B` is the same as `A ≡ B`). This axiom is what allows the project to elevate philosophical claims about structure into mathematical theorems about identity.
