# Formalizing Cartesian Fibrations in Lean 4

A formalization of cartesian fibrations in ∞-category theory, targeting **Proposition 5.2.4** from Emily Riehl and Dominic Verity's *Elements of ∞-Category Theory*.

## Project Overview

**Goal**: Formalize the theorem that the composition of cartesian fibrations is a cartesian fibration.

**Mathematical Context**: This is a fundamental closure property in the theory of fibered ∞-categories, analogous to the classical pasting lemma for pullbacks in ordinary category theory.

**Strategic Purpose**: Pre-application research project demonstrating:
- Deep understanding of higher category theory
- Proficiency with Lean 4 and proof assistant methodology
- Engagement with Professor Emily Riehl's research program
- Collaborative open-source contribution approach

## Project Structure

```
cat-lemma/
├── CartesianFibrations/
│   ├── CartesianArrows.lean          # Section 5.1: Cartesian arrows
│   ├── CartesianFibrations.lean      # Section 5.2: Cartesian fibrations
│   └── CartesianComposition.lean     # Proposition 5.2.4: Main theorem
├── infinity-cosmos/                   # Submodule: ∞-cosmos infrastructure
├── claudedocs/
│   └── PROJECT_ANALYSIS.md           # Comprehensive project analysis
├── prospectus.md                      # Background and motivation
├── chosen_lemma.md                    # Target theorem rationale
├── CartesianFibrations.lean          # Main import file
├── lakefile.toml                      # Lake build configuration
├── lean-toolchain                     # Lean version specification
└── README.md                          # This file
```

## Current Status

### ✅ Completed

- [x] Comprehensive project analysis and planning
- [x] Infrastructure research (∞-cosmos project)
- [x] Project structure and build configuration
- [x] File stubs with documentation and proof strategies

### 🚧 In Progress

- [ ] Formalize `IsCartesianArrow` definition
- [ ] Formalize `IsCartesianFibration` definition
- [ ] Prove auxiliary lemmas for composition
- [ ] Complete proof of Proposition 5.2.4

### 📋 Planned

- [ ] Fill all `sorry` placeholders
- [ ] Add comprehensive examples
- [ ] Write detailed proof documentation
- [ ] Coordinate with ∞-cosmos team for potential PR

## Key Technical Challenges

### 1. Cartesian vs. Isofibration Distinction

**Critical Discovery**: The ∞-cosmos project currently formalizes **isofibrations**, not **cartesian fibrations**. These are related but distinct concepts:

- **Isofibrations**: Maps with right lifting property against certain inclusions
- **Cartesian fibrations**: Maps admitting cartesian lifts (universal property)

**Implication**: This project fills a genuine gap in the existing formalization infrastructure.

### 2. Homotopy-Coherent Universal Properties

Cartesian arrows in ∞-categories satisfy homotopy-coherent universal properties, not strict ones. The formalization must account for:

- Contractible spaces of lifts (not unique lifts)
- Homotopy pullback squares (not strict pullbacks)
- Coherent composition of universal properties

### 3. Model-Independent Framework

Following the ∞-cosmos approach, the formalization should be:

- Independent of specific models (quasi-categories, complete Segal spaces, etc.)
- Based on axiomatic properties of the ∞-cosmos
- Compatible with the existing `InfinityCosmos` type class

## Mathematical References

### Primary Source

**Riehl & Verity**, *Elements of ∞-Category Theory* (2022)
- Chapter 5.1: Cartesian arrows
- Chapter 5.2: Cartesian fibrations
- Proposition 5.2.4: Composition of cartesian fibrations

### Background Material

- **Riehl**, *Categorical Homotopy Theory* (2014)
- **Riehl**, *Category Theory in Context* (2016)
- **Lurie**, *Higher Topos Theory* (2009), §2 on cartesian fibrations

### Formalization References

- **Riehl et al.**, "Formalizing the ∞-categorical Yoneda lemma" (2024)
- **∞-Cosmos Project**: https://github.com/emilyriehl/infinity-cosmos
- **Mathlib4**: https://github.com/leanprover-community/mathlib4

## Getting Started

### Prerequisites

- **Lean 4**: Version v4.24.0 (specified in `lean-toolchain`)
- **Lake**: Lean's build tool (comes with Lean 4)
- **VS Code** + Lean 4 extension (recommended)

### Installation

1. **Install Lean 4** (if not already installed):
   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   ```

2. **Clone this repository**:
   ```bash
   git clone <repository-url>
   cd cat-lemma
   ```

3. **Initialize submodules**:
   ```bash
   git submodule update --init --recursive
   ```

4. **Build the project**:
   ```bash
   lake exe cache get  # Download Mathlib cache
   lake build           # Build project
   ```

### Development Workflow

1. **Open in VS Code**:
   ```bash
   code .
   ```

2. **Start with file stubs**: Each file in `CartesianFibrations/` has:
   - Mathematical documentation
   - Type signatures with `sorry` placeholders
   - Proof strategy comments

3. **Incremental development**:
   - Replace `sorry` with actual proofs
   - Run `lake build` frequently to check compilation
   - Use Lean's interactive proof mode (Ctrl+Shift+Enter)

4. **Test your changes**:
   ```bash
   lake build
   ```

## Proof Strategy Overview

### Proposition 5.2.4: Composition of Cartesian Fibrations

**Statement**: If `p : E → B` and `q : B → C` are cartesian fibrations, then `qp : E → C` is a cartesian fibration.

**Proof Outline**:

1. **Setup**:
   - Given cartesian fibrations `p : E ↠_c B` and `q : B ↠_c C`
   - Take object `e : E` and morphism `f : X → (qp)(e)` in `C`

2. **First lift (through q)**:
   - Since `q` is cartesian, lift `f` to cartesian `f₁ : X → b` in `B`
   - This uses that `q` admits cartesian lifts

3. **Second lift (through p)**:
   - Since `p` is cartesian, lift `f₁` to cartesian `f₂ : X → e'` in `E`
   - This uses that `p` admits cartesian lifts

4. **Composite is cartesian**:
   - The composite `f₂` is a lift of `f` through `qp`
   - Verify cartesian property using universal property composition

5. **Key lemma**: `comp_cartesian_over_comp`
   - Shows that composing cartesian arrows over different maps
   - Yields a cartesian arrow over the composite map
   - This is the main technical ingredient

## Contribution Guidelines

### Coordination with ∞-Cosmos Team

Before significant development work:

1. **Join Zulip**: https://leanprover.zulipchat.com/#narrow/channel/458659-infinity-cosmos
2. **Check for duplicates**: Search issues/PRs for "cartesian fibration"
3. **Announce intent**: Post plan to avoid duplicate effort
4. **Request feedback**: Ask about approach and priorities

### Code Style

Follow ∞-cosmos conventions:

- **Naming**: `lowerCamelCase` for definitions, `snake_case_with_underscores` for theorems
- **Documentation**: Use `/-! ... -/` for module docs, `/-- ... -/` for definition docs
- **Imports**: Group by Mathlib → InfinityCosmos → Local
- **Proofs**: Use tactic mode for readability, term mode for simple proofs

### Git Workflow

1. Work on feature branch: `git checkout -b feature/cartesian-fibrations`
2. Commit frequently with descriptive messages
3. Keep commits atomic and focused
4. Write commit messages explaining *why*, not just *what*

## Learning Resources

### Lean 4 Documentation

- **Theorem Proving in Lean 4**: https://leanprover.github.io/theorem_proving_in_lean4/
- **Mathematics in Lean**: https://leanprover-community.github.io/mathematics_in_lean/
- **Mathlib Docs**: https://leanprover-community.github.io/mathlib4_docs/

### Category Theory in Lean

- **Mathlib Category Theory**: `Mathlib.CategoryTheory.*`
- **∞-Cosmos Docs**: https://emilyriehl.github.io/infinity-cosmos/docs
- **Enriched Categories**: `Mathlib.CategoryTheory.Enriched.*`

### Community Support

- **Lean Zulip**: https://leanprover.zulipchat.com/
- **∞-Cosmos Channel**: https://leanprover.zulipchat.com/#narrow/channel/458659-infinity-cosmos
- **Mathlib PRs**: Browse for formalization examples

## Project Timeline (Indicative)

### Phase 1: Foundations (Weeks 1-2)
- [ ] Formalize cartesian arrow definition
- [ ] Prove basic properties (identity, isomorphisms)
- [ ] Establish relationship to existing concepts

### Phase 2: Fibrations (Weeks 3-4)
- [ ] Formalize cartesian fibration definition
- [ ] Prove basic closure properties
- [ ] Construct standard examples

### Phase 3: Main Theorem (Weeks 5-6)
- [ ] Formalize Proposition 5.2.4
- [ ] Prove auxiliary lemmas
- [ ] Complete main proof (may use `sorry` for minor gaps)

### Phase 4: Polish (Weeks 7-8)
- [ ] Fill any remaining `sorry` placeholders
- [ ] Comprehensive documentation
- [ ] Examples and tests
- [ ] Prepare for potential PR or portfolio presentation

## Success Metrics

### Minimum Viable Project
- ✅ Definitions compile and type-check
- ✅ Theorem statement is formalized
- ✅ Proof structure is outlined
- ✅ Well-documented with clear `sorry` markers

### Ideal Outcome
- ✅ Complete, `sorry`-free proof
- ✅ All auxiliary lemmas proven
- ✅ Integration tests and examples
- ✅ Accepted PR to ∞-cosmos or Mathlib
- ✅ Companion explanation document

### Portfolio Value (Even if Incomplete)
- Demonstrates engagement with research frontier
- Shows technical proficiency with Lean 4
- Reveals deep understanding of ∞-category theory
- Exhibits professional collaboration mindset

## Related Work

- **∞-Cosmos Project**: Axiomatic ∞-category theory in Lean
- **1Lab**: Cubical formalization of ∞-categories in Agda
- **HoTT-Agda**: Synthetic homotopy theory and higher categories
- **UniMath**: Univalent foundations approach in Coq

## License

This project is released under the **Apache 2.0 License**, consistent with Mathlib and the ∞-cosmos project.

## Contact

For questions about this specific formalization effort, please:

1. Open an issue in this repository
2. Post in the ∞-cosmos Zulip channel
3. Reach out via the Lean community channels

## Acknowledgments

This project builds on:

- The **∞-Cosmos Project** by Emily Riehl, Mario Carneiro, and Dominic Verity
- **Mathlib4** by the Lean community
- **Elements of ∞-Category Theory** by Emily Riehl and Dominic Verity

---

**Project Status**: 🚧 Active Development | **Last Updated**: October 21, 2025
# CartesianFibrationLemma
