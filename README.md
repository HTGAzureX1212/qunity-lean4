# Mechanized Formalization of Qunity Semantics and Type System in Lean 4

Qunity is a unified quantum programming language introduced by
Finn Voichick, Liyi Li, Robert Rand, and Michael Hicks. This project aims
to formalize the language's **syntax, type system, and denotational
semantics**, with particular attention to faithfully reproducing the
definitions and proofs presented in the paper.

## Primary References

This formalization is based on the following two versions of the Qunity
language specification.

### POPL'23

Finn Voichick, Liyi Li, Robert Rand, and Michael Hicks.
*Qunity: A Unified Language for Quantum and Classical Computing.*
Proceedings of the ACM on Programming Languages, Volume 7, POPL, 2023.

[ACM Digital Library](https://doi.org/10.1145/3571225)

### Extended Version

Finn Voichick, Liyi Li, Robert Rand, and Michael Hicks.
*Qunity: A Unified Language for Quantum and Classical Computing
(Extended Version).*
arXiv:2204.12384.

[arXiv](https://arxiv.org/abs/2204.12384) · [PDF](https://arxiv.org/pdf/2204.12384)

## Goals

The primary goal of this project is a **faithful mechanized formalization of Qunity**.

The formalization is being developed incrementally, following the structure
of the paper:

- Qunity's data and program types
- Expression and program syntax
- Derived syntax and notation
- Typing contexts and typing judgments
- Structural properties of the type system
- Denotational semantics
- Mathematical foundations of the quantum semantics
- Soundness and related metatheoretic results

The published POPL'23 paper serves as the primary published reference,
while the extended version provides the additional definitions, details,
and proofs needed for the mechanization.

## Development

The project is currently moving into the formalization of Qunity's typing
judgments.

## Project Structure

The source tree is organized to separate the language from its mathematical
semantics.

```text
Qunity/
├── Language/
│   ├── Types.lean
│   ├── Syntax.lean
│   └── SyntaxSugar.lean
│
├── Math/
│   └── Reals.lean
│
└── Typing/
    └── Context.lean
```

The exact structure is expected to evolve as the formalization develops.

## Building

```bash
git clone https://github.com/HTGAzureX1212/qunity-lean4.git
cd qunity-lean4
lake build
```
