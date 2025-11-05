# Getting Started with the Formal Verification

This guide provides instructions on how to set up your environment to interact with the formal Agda code in this repository.

---

## What is Agda?

[Agda](https://wiki.portal.chalmers.se/agda/pmwiki.php) is a dependently typed functional programming language and proof assistant. It allows us to write mathematical proofs that can be checked by a computer. This project uses a specific version of Agda called **Cubical Agda**, which has built-in support for Cubical Type Theory and the Univalence axiom.

## 1. Installation

To interact with the code, you will need to install Agda, the Agda standard library, and the Cubical Agda library.

### Step 1.1: Install Agda

The recommended way to install Agda is through the Haskell package manager, `cabal`. 

1.  **Install the Haskell Platform:** Follow the instructions at [haskell.org/get-started/](https://www.haskell.org/get-started/).
2.  **Install Agda:** Once you have `cabal` installed, run the following commands:
    ```bash
    cabal update
    cabal install Agda
    ```

For detailed instructions, refer to the [official Agda installation guide](https://agda.readthedocs.io/en/latest/getting-started/installation.html).

### Step 1.2: Install the Agda Standard Library

The standard library provides many useful definitions and theorems.

```bash
cabal install agda-stdlib
```

### Step 1.3: Install the Cubical Agda Library

This project is built on the Cubical Agda library.

1.  **Clone the repository:**
    ```bash
    git clone https://github.com/agda/cubical.git
    ```
2.  **Follow the Cubical Agda installation instructions:** The repository contains detailed instructions on how to set up the library. Please refer to the `README.md` in the `cubical` repository.

## 2. Editor Setup

Agda is designed to be used with an interactive editor. The two most popular choices are Emacs and Visual Studio Code.

*   **Emacs:** The standard `agda-mode` is the most mature way to interact with Agda. Follow the instructions in the [Agda documentation](https://agda.readthedocs.io/en/latest/getting-started/emacs-mode.html) to set it up.

*   **Visual Studio Code:** There is an official [Agda extension for VS Code](https://marketplace.visualstudio.com/items?itemName=banacorn.agda). Follow the installation instructions on the extension's page.

## 3. Loading the Project

Once you have Agda and your editor set up, you can start exploring the code.

1.  **Navigate to the `src/` directory:** The Agda files for this project are located in the `src/` directory.
    ```bash
    cd src/
    ```
2.  **Open an Agda file:** Open one of the `.agda` files (e.g., `Distinction.agda`) in your editor.
3.  **Load the file:** In your editor, use the "load" command. In both Emacs and VS Code, the standard keybinding for this is `C-c C-l` (Ctrl+C, then Ctrl+L).

If the file loads successfully, it means that Agda has type-checked the code and verified the proofs. You can then step through the code interactively.

## 4. Key Agda Files

We recommend exploring the following files to understand the core of the project:

1.  **`Distinction.agda`**: The general theory of the `D` monad.
2.  **`D_Native_Numbers.agda`**: The definition of the "thinking number" (`ℕ-D`) and the proof of the `coherence-axiom`.
3.  **`ANAGNOSIS_FLT_D_Proof.agda`**: The formal outline of the proof of Fermat's Last Theorem.

By following this guide, you will be able to fully interact with and verify the formal content of this repository.
