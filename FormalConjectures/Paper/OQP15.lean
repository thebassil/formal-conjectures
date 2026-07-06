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

*References:*
- [Separability of mixed quantum states: linear contractions and permutation criteria]
  (https://arxiv.org/abs/quant-ph/0604168) by *Karol Życzkowski et al.*
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

Fix a bipartite Hilbert space $\mathbb{C}^N \otimes \mathbb{C}^M$. A density operator $\rho$
(positive semidefinite, trace 1) is **absolutely separable** if for every unitary $U$, the
state $U \rho U^\dagger$ is separable. Since unitary conjugation preserves eigenvalues, absolute
separability depends only on the spectrum.

**The problem:** Characterize the spectra $\lambda$ for which every density operator with that
spectrum is separable. Solved for $2 \times 2$ (Verstraete et al. 2001) and $2 \times d$
(Johnston 2013), open for $3 \times 3$ and above.
-/

namespace OQP15

open Matrix Finset BigOperators ComplexOrder

variable {N M : ℕ}

/--
A matrix is a density matrix if it is positive semidefinite with trace equal to 1.
-/
def IsDensityMatrix (ρ : Matrix (Fin (N * M)) (Fin (N * M)) ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace = 1

/--
A density matrix on $\mathbb{C}^N \otimes \mathbb{C}^M$ is **separable** if it can be written
as a convex combination of product states $\rho_A^{(i)} \otimes \rho_B^{(i)}$.

We work over the index type `Fin N × Fin M` to naturally express the tensor product structure,
using `Matrix.reindex finProdFinEquiv finProdFinEquiv` to convert to `Fin (N * M)` indexing.
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

/--
A density matrix is **absolutely separable** if $U \rho U^\dagger$ is separable for every
unitary $U$.
-/
def IsAbsolutelySeparable (N M : ℕ) (ρ : Matrix (Fin (N * M)) (Fin (N * M)) ℂ) : Prop :=
  ∀ U : unitaryGroup (Fin (N * M)) ℂ,
    IsSeparable N M ((U : Matrix _ _ ℂ) * ρ * (↑U)ᴴ)

/--
Partial transpose with respect to the second subsystem.
For a matrix indexed by $(i_A, i_B) \times (j_A, j_B)$, transposes only the $B$ indices.
We work over the product index type for clarity.
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

/-!
## Main open problem
-/

/--
**OQP #15 (general form):** There exists a decidable characterization of which spectra give
absolutely separable states in $\mathbb{C}^N \otimes \mathbb{C}^M$ for all $N, M \geq 2$.

Formally: there is a predicate on spectra, depending only on eigenvalues and dimensions,
that is equivalent to absolute separability.
-/
@[category research open, AMS 15 81]
theorem separability_from_spectrum (N M : ℕ) (hN : 2 ≤ N) (hM : 2 ≤ M) :
    ∃ (P : (Fin (N * M) → ℝ) → Prop),
      ∀ spec : Fin (N * M) → ℝ,
        (∀ i, 0 ≤ spec i) → (∑ i, spec i = 1) →
          (P spec ↔ SpectrumIsAbsSep N M spec) := by
  sorry

/-!
## Solved cases
-/

/--
**2×2 case (Verstraete, Audenaert, De Moor 2001):** A state on $\mathbb{C}^2 \otimes
\mathbb{C}^2$ is absolutely separable iff its eigenvalues $\lambda_1 \geq \lambda_2 \geq
\lambda_3 \geq \lambda_4$ satisfy $\lambda_1 - \lambda_3 \leq 2\sqrt{\lambda_2 \lambda_4}$.
-/
def VerstraeteCriterion (spec : Fin 4 → ℝ) : Prop :=
  spec ⟨0, by omega⟩ - spec ⟨2, by omega⟩ ≤
    2 * Real.sqrt (spec ⟨1, by omega⟩ * spec ⟨3, by omega⟩)

@[category research solved, AMS 15 81]
theorem separability_from_spectrum.variants.two_by_two
    (spec : Fin 4 → ℝ)
    (h_sorted : ∀ i j : Fin 4, i ≤ j → spec j ≤ spec i)
    (h_nonneg : ∀ i, 0 ≤ spec i)
    (h_sum : ∑ i, spec i = 1) :
    SpectrumIsAbsSep 2 2 spec ↔ VerstraeteCriterion spec := by
  sorry

/--
**2×d case (Johnston 2013):** For $\mathbb{C}^2 \otimes \mathbb{C}^M$, absolute separability
is equivalent to absolute PPT (positive partial transpose for all unitaries).
-/
@[category research solved, AMS 15 81]
theorem separability_from_spectrum.variants.two_by_d
    (M : ℕ) (hM : 2 ≤ M)
    (ρ : Matrix (Fin (2 * M)) (Fin (2 * M)) ℂ)
    (hρ : IsDensityMatrix ρ) :
    IsAbsolutelySeparable 2 M ρ ↔ IsAbsolutelyPPT 2 M ρ := by
  sorry

/-!
## Sufficient conditions
-/

/--
**Gurvits–Barnum ball (2002):** If $\mathrm{Tr}(\rho^2) \leq \frac{1}{NM - 1}$, then $\rho$
is absolutely separable.
-/
@[category research solved, AMS 15 81]
theorem gurvits_barnum_ball (N M : ℕ) (hN : 1 ≤ N) (hM : 1 ≤ M)
    (ρ : Matrix (Fin (N * M)) (Fin (N * M)) ℂ)
    (hρ : IsDensityMatrix ρ)
    (h_purity : Matrix.trace (ρ * ρ) ≤ (1 : ℂ) / (N * M - 1 : ℂ)) :
    IsAbsolutelySeparable N M ρ := by
  sorry

/-!
## The key open question
-/

/--
**Open:** Does absolute PPT imply absolute separability for $N, M \geq 3$?
If true, Hildebrand's 2007 classification of absolute PPT spectra would solve OQP #15.
-/
@[category research open, AMS 15 81]
theorem abs_ppt_implies_abs_sep (N M : ℕ) (hN : 3 ≤ N) (hM : 3 ≤ M)
    (ρ : Matrix (Fin (N * M)) (Fin (N * M)) ℂ)
    (hρ : IsDensityMatrix ρ)
    (h_appt : IsAbsolutelyPPT N M ρ) :
    IsAbsolutelySeparable N M ρ := by
  sorry

end OQP15
