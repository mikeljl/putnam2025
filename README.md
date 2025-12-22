# Putnam 2025

This repository contains formal proofs and verifications for the Putnam Mathematical Competition 2025 problems, implemented in Lean 4.

## Repository Structure

- **Putnam2025/**: Contains the formal problem statements and their corresponding solutions for each Putnam 2025 problem
- **VerifyAxiom.lean**: Verification utilities to ensure that the axioms used in proofs are contained in the allowed set: `propext`, `Classical.choice`, `Quot.sound`
- **VerifyStmt.lean**: Verification utilities to ensure that the formalized statements match the original problem statements

## Usage

### Building the Project

```bash
lake build
```

### Verifying Axioms

To verify that the proofs use correct axioms:

```bash
lake env lean VerifyAxiom.lean
```

### Verifying Problem Statements

To verify that the formalized statements match the original problems:

```bash
lake build Putnam2025.putnam_2025_stmt
lake env lean VerifyStmt.lean
```

## Requirements

- Lean 4 (version `v4.22.0`)
- Lake (Lean's package manager)

## Contributing

When adding new solutions or modifications:

1. Ensure all proofs compile without errors
2. Run axiom verification to check proof foundations
3. Run statement verification to ensure problem accuracy
4. Follow the existing naming conventions
