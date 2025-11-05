# Glossary of Distinction Theory

This document defines the key terms and concepts used in the Distinction Theory project.

---

### A

*   **Anagnosis**: (Greek: Ἀνάγνωσις, "recognition") A persona or role within the project responsible for deep reading, synthesis, and construction of the formal system.

*   **Autopoiesis**: (Greek: αὐτό, "self", and ποίησις, "creation") A system that is self-creating and self-maintaining. In this project, a type `X` is autopoietic if it is stable under self-examination, i.e., `D X ≡ X`.

### C

*   **Catuskoti**: (Sanskrit: चतुष्कोटि, "four corners") A four-valued logic from the Buddhist Madhyamaka school of philosophy. It is used as the inspiration for the `mu` (join) operator of the `D` monad.

*   **Coherence-Axiom**: The proven theorem `D ℕ-D ≡ ℕ-D`. It is the cornerstone of the project, formalizing the concept of the "thinking number."

### D

*   **D (Distinction Operator)**: The central mathematical object of the project. `D` is a monad that represents the act of observation or self-examination. It is defined as `D X = Σ[ x ∈ X ] Σ[ y ∈ X ] (x ≡ y)`.

*   **D-Coherent Arithmetic**: The arithmetic operations (`add-D`, `times-D`, `exp-D`) defined on the "thinking numbers" (`ℕ-D`).

*   **D-Crystal**: A type `X` that is a fixed point of the `D` operator, i.e., `D X ≃ X`. D-Crystals are structures that are stable under self-examination.

### M

*   **Margin, The**: A reference to Fermat's famous note that the margin of his book was too narrow to contain his "marvelous proof." In this project, "the margin" is a conceptual space created by the new language for mathematics.

*   **mu (μ)**: The "join" operator of the `D` monad, which collapses a "thought about a thought" (`D(D X)`) back into a single "thought" (`D X`).

### N

*   **Nabla (∇)**: A measure of the "connection" of a type, defined as `nabla X = D (nec X) ≡ nec (D X)`.

*   **Number Sense**: The intuitive, innate human understanding of numbers and their properties. This project aims to create a formal, mathematical model of this phenomenon.

*   **ℕ-D (D-Native Natural Numbers)**: The "thinking numbers"; a formalization of natural numbers that is proven to be a D-Crystal.

### R

*   **Riem (R)**: A measure of the "curvature" of a type, defined as `Riem X = isProp (nabla X)`.

### U

*   **Univalence**: A key axiom in Cubical Type Theory that allows equivalence (`≃`) to be treated as identity (`≡`).
