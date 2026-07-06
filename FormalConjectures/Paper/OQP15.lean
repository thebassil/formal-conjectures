/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.Util.ProblemImports

/-!
# Open Quantum Problem #15: Separability from Spectrum

## STATE A — SCAFFOLD ONLY
These are the Mathlib-compatible building blocks. The theorem statements
connecting them into the actual OQP #15 conjecture are NOT here.

See `oqp15/claude` for my attempt at connecting them.
Branch off this to write your own: `git checkout -b oqp15/bassil oqp15/scaffold`

*References:*
- [Normal decomposition of the density matrix of a bipartite mixed state]
  (https://arxiv.org/abs/quant-ph/0011110)
  by *Frank Verstraete, Koenraad Audenaert, Bart De Moor*, Phys. Rev. A 64, 012316 (2001)
- [Largest separable balls around the maximally mixed bipartite quantum state]
  (https://arxiv.org/abs/quant-ph/0204159)
  by *Leonid Gurvits, Howard Barnum*, Phys. Rev. A 66, 062311 (2002)
- [Complete characterization of the facial structure of the set of PPT states]
  (https://arxiv.org/abs/quant-ph/0502170)
  by *Martin Hildebrand*, Phys. Rev. A 76, 052325 (2007)
- [Absolute separability and the possible spectra of entanglement witnesses]
  (https://arxiv.org/abs/1309.2006)
  by *Nathaniel Johnston*, Phys. Rev. A 88, 062330 (2013)

## Mathlib objects available
- `Matrix (Fin n) (Fin n) ℂ` — complex matrices
- `Matrix.PosSemidef` — positive semidefinite predicate
- `Matrix.IsHermitian` — Hermitian predicate
- `Matrix.IsHermitian.eigenvalues` — real eigenvalues of Hermitian matrix
- `Matrix.trace` — trace of a matrix
- `Matrix.kronecker` — Kronecker product (returns `Fin N × Fin M` indices)
- `finProdFinEquiv` — equiv between `Fin N × Fin M` and `Fin (N * M)`
- `Matrix.reindex` — reindex a matrix along an equiv
- `unitaryGroup (Fin n) ℂ` — the unitary group
- `Real.sqrt` — square root on reals
-/

namespace OQP15

open Matrix Finset BigOperators ComplexOrder

variable {N M : ℕ}

-- ═══════════════════════════════════════════════════════════
-- LAYER 1: Density matrix
-- ═══════════════════════════════════════════════════════════

/--
A matrix is a density matrix if it is positive semidefinite with trace equal to 1.
-/
def IsDensityMatrix (ρ : Matrix (Fin (N * M)) (Fin (N * M)) ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

-- ═══════════════════════════════════════════════════════════
-- LAYER 2: Separability (convex combination of product states)
-- ═══════════════════════════════════════════════════════════

/--
A density matrix on $\mathbb{C}^N \otimes \mathbb{C}^M$ is **separable** if it can be written
as a convex combination of product states $\rho_A^{(i)} \otimes \rho_B^{(i)}$.

Note: `kronecker` returns `Fin N × Fin M` indices, so we use `Matrix.reindex finProdFinEquiv`
to convert to `Fin (N * M)`.
-/
def IsSeparable (N M : ℕ) (ρ : Matrix (Fin (N * M)) (Fin (N * M)) ℂ) : Prop :=
  ∃ (k : ℕ) (p : Fin k → ℝ) (ρA : Fin k → Matrix (Fin N) (Fin N) ℂ)
    (ρB : Fin k → Matrix (Fin M) (Fin M) ℂ),
    (∀ i, 0 ≤ p i) ∧
    (∑ i, p i = 1) ∧
    (∀ i, (ρA i).PosSemidef) ∧
    (∀ i, (ρB i).PosSemidef) ∧
    (∀ i, (ρA i).trace = 1) ∧
    (∀ i, (ρB i).trace = 1) ∧
    ρ = Matrix.reindex finProdFinEquiv finProdFinEquiv
      (∑ i, (p i : ℂ) • (ρA i).kronecker (ρB i))

-- ═══════════════════════════════════════════════════════════
-- LAYER 3: Absolute separability (separable under all unitaries)
-- ═══════════════════════════════════════════════════════════

/--
A density matrix is **absolutely separable** if $U \rho U^\dagger$ is separable for every
unitary $U$.
-/
def IsAbsolutelySeparable (N M : ℕ) (ρ : Matrix (Fin (N * M)) (Fin (N * M)) ℂ) : Prop :=
  ∀ U : unitaryGroup (Fin (N * M)) ℂ,
    IsSeparable N M ((U : Matrix _ _ ℂ) * ρ * (↑U)ᴴ)

-- ═══════════════════════════════════════════════════════════
-- LAYER 4: Partial transpose and absolute PPT
-- ═══════════════════════════════════════════════════════════

/--
Partial transpose with respect to the second subsystem.
For a matrix indexed by $(i_A, i_B) \times (j_A, j_B)$, transposes only the $B$ indices.
-/
noncomputable def partialTranspose (N M : ℕ)
    (ρ : Matrix (Fin (N * M)) (Fin (N * M)) ℂ) :
    Matrix (Fin (N * M)) (Fin (N * M)) ℂ :=
  let ρ' := Matrix.reindex finProdFinEquiv.symm finProdFinEquiv.symm ρ
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Matrix.of fun (i : Fin N × Fin M) (j : Fin N × Fin M) =>
      ρ' (i.1, j.2) (j.1, i.2))

/--
A state is absolutely PPT if its partial transpose is positive semidefinite under all
unitary rotations.
-/
def IsAbsolutelyPPT (N M : ℕ) (ρ : Matrix (Fin (N * M)) (Fin (N * M)) ℂ) : Prop :=
  ∀ U : unitaryGroup (Fin (N * M)) ℂ,
    (partialTranspose N M ((U : Matrix _ _ ℂ) * ρ * (↑U)ᴴ)).PosSemidef

-- ═══════════════════════════════════════════════════════════
-- LAYER 5: Spectrum-based absolute separability
-- ═══════════════════════════════════════════════════════════

/--
A spectrum characterizes absolute separability if every density matrix with that
spectrum is absolutely separable.
-/
def SpectrumIsAbsSep (N M : ℕ) (spec : Fin (N * M) → ℝ) : Prop :=
  (∀ i, 0 ≤ spec i) ∧
  (∑ i, spec i = 1) ∧
  ∀ ρ : Matrix (Fin (N * M)) (Fin (N * M)) ℂ,
    IsDensityMatrix ρ →
    (hH : ρ.IsHermitian) →
    (∀ i, hH.eigenvalues i = spec i) →
    IsAbsolutelySeparable N M ρ

-- ═══════════════════════════════════════════════════════════
-- LAYER 6: Known criteria (building blocks for theorem statements)
-- ═══════════════════════════════════════════════════════════

/--
The Verstraete criterion for 2×2: $\lambda_1 - \lambda_3 \leq 2\sqrt{\lambda_2 \lambda_4}$.
-/
def VerstraeteCriterion (spec : Fin 4 → ℝ) : Prop :=
  spec ⟨0, by omega⟩ - spec ⟨2, by omega⟩ ≤
    2 * Real.sqrt (spec ⟨1, by omega⟩ * spec ⟨3, by omega⟩)

-- ═══════════════════════════════════════════════════════════
-- TODO: Connect these into theorem statements for OQP #15
-- See oqp15/claude for one attempt, or branch off to make your own.
-- ═══════════════════════════════════════════════════════════

end OQP15
