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
module

public import FormalConjecturesUtil

/-!
# Open Quantum Problem 1: All the Bell inequalities

Find complete facet descriptions of the local polytopes for Bell scenarios with
$N$ parties, $M$ measurement choices per party, and $K$ outcomes per measurement.
All three parameters are positive. The one-outcome case is included; its local
polytope is a point and its facet description can be empty.

A local behavior is obtained by marginalizing one joint probability distribution
over the outcomes of all $NM$ observables. The same joint distribution is used
for every setting. Facets are relative to the affine span of the deterministic
behaviors, not to the larger space of all probability arrays.

The unknown answer is a family of finite sets of facet-inequality representatives.
Representatives with the same saturated deterministic vertices are not repeated.
This specifies a classification task, not the already-known existence of some
finite half-space description. No efficiency or symmetry-classification claim
is imposed, and only the full-probability version of the problem is formalized.

## References

* IQOQI Vienna, Open Quantum Problem 1:
  https://oqp.iqoqi.oeaw.ac.at/all-the-bell-inequalities
* Formal Conjectures issue 3401:
  https://github.com/google-deepmind/formal-conjectures/issues/3401
* A. Peres, *All the Bell inequalities*, Foundations of Physics 29, 589-614 (1999),
  https://arxiv.org/abs/quant-ph/9807017
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace OpenQuantumProblem1

/-- One measurement choice for each party. -/
abbrev Setting (N M : ℕ) := Fin N → Fin M

/-- One observed outcome for each party. -/
abbrev Outcome (N K : ℕ) := Fin N → Fin K

/-- One outcome for every party and every possible measurement. -/
abbrev Assignment (N M K : ℕ) := Fin N → Fin M → Fin K

/-- A real probability array; positivity and normalization are not assumed by the type. -/
abbrev Behaviour (N M K : ℕ) := Setting N M → Outcome N K → ℝ

variable {N M K : ℕ}

open scoped Classical in
/-- The deterministic behavior associated with a complete outcome assignment. -/
def deterministicBehaviour (s : Assignment N M K) : Behaviour N M K :=
  fun x a => if a = (fun i => s i (x i)) then 1 else 0

/-- A probability distribution over all counterfactual outcome assignments. -/
def IsJointDistribution (q : Assignment N M K → ℝ) : Prop :=
  (∀ s, 0 ≤ q s) ∧ ∑ s, q s = 1

/-- The probabilities observed by selecting one measurement at each party. -/
def jointMarginal (q : Assignment N M K → ℝ) : Behaviour N M K :=
  fun x a => ∑ s, q s * deterministicBehaviour s x a

/-- A single joint distribution realizes the entire probability array. -/
def IsLocal (p : Behaviour N M K) : Prop :=
  ∃ q : Assignment N M K → ℝ, IsJointDistribution q ∧ p = jointMarginal q

open scoped Classical in
/-- A joint distribution concentrated on one deterministic assignment. -/
def pointMass (s : Assignment N M K) : Assignment N M K → ℝ :=
  fun t => if t = s then 1 else 0

/-- A deterministic behavior has nonnegative entries. -/
@[category API, AMS 52 60 81]
lemma deterministicBehaviour_nonneg (s : Assignment N M K)
    (x : Setting N M) (a : Outcome N K) : 0 ≤ deterministicBehaviour s x a := by
  classical
  unfold deterministicBehaviour
  split <;> norm_num

/-- A deterministic behavior has total outcome probability one at each setting. -/
@[category API, AMS 52 60 81]
lemma deterministicBehaviour_sum (s : Assignment N M K) (x : Setting N M) :
    ∑ a, deterministicBehaviour s x a = 1 := by
  classical
  simp [deterministicBehaviour]

/-- A point mass is a joint probability distribution. -/
@[category API, AMS 52 60 81]
lemma pointMass_isJointDistribution (s : Assignment N M K) :
    IsJointDistribution (pointMass s) := by
  classical
  constructor
  · intro t
    by_cases h : t = s <;> simp [pointMass, h]
  · simp [pointMass]

/-- Marginalizing a point mass recovers its deterministic behavior. -/
@[category API, AMS 52 60 81]
lemma jointMarginal_pointMass (s : Assignment N M K) :
    jointMarginal (pointMass s) = deterministicBehaviour s := by
  classical
  funext x a
  simp [jointMarginal, pointMass]

/-- Every deterministic behavior is local. -/
@[category test, AMS 52 60 81]
lemma deterministicBehaviour_isLocal (s : Assignment N M K) :
    IsLocal (deterministicBehaviour s) := by
  exact ⟨pointMass s, pointMass_isJointDistribution s, (jointMarginal_pointMass s).symm⟩

/-- Every local behavior has nonnegative probabilities. -/
@[category API, AMS 52 60 81]
lemma isLocal_nonneg {p : Behaviour N M K} (hp : IsLocal p)
    (x : Setting N M) (a : Outcome N K) : 0 ≤ p x a := by
  rcases hp with ⟨q, hq, rfl⟩
  exact Finset.sum_nonneg fun s _ =>
    mul_nonneg (hq.1 s) (deterministicBehaviour_nonneg s x a)

/-- Every local behavior is normalized separately at each measurement setting. -/
@[category API, AMS 52 60 81]
lemma isLocal_sum {p : Behaviour N M K} (hp : IsLocal p) (x : Setting N M) :
    ∑ a, p x a = 1 := by
  rcases hp with ⟨q, hq, rfl⟩
  calc
    ∑ a, jointMarginal q x a = ∑ s, q s * ∑ a, deterministicBehaviour s x a := by
      simp only [jointMarginal]
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ = 1 := by simpa only [deterministicBehaviour_sum, mul_one] using hq.2

/-- The zero array cannot be a local behavior when a setting is available. -/
@[category test, AMS 52 60 81]
lemma zero_not_isLocal (x : Setting N M) : ¬ IsLocal (0 : Behaviour N M K) := by
  intro h
  have hsum := isLocal_sum h x
  simp at hsum

/-- The vertices used to specify the local affine space. -/
def deterministicVertices (N M K : ℕ) : Set (Behaviour N M K) :=
  Set.range (deterministicBehaviour (N := N) (M := M) (K := K))

/-- The affine space containing the local polytope. -/
def localAffineSpace (N M K : ℕ) : AffineSubspace ℝ (Behaviour N M K) :=
  affineSpan ℝ (deterministicVertices N M K)

/-- The dimension of the direction of an affine span. Empty sets are handled separately. -/
def affineDimension (S : Set (Behaviour N M K)) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ S).direction

/-- The inequality $\sum_{x,a} c_{x,a}p(a\mid x) \le b$. -/
structure BellInequality (N M K : ℕ) where
  coeff : Behaviour N M K
  bound : ℝ

namespace BellInequality

/-- Evaluate the left-hand side of a Bell inequality. -/
def value (I : BellInequality N M K) (p : Behaviour N M K) : ℝ :=
  ∑ x, ∑ a, I.coeff x a * p x a

/-- Validity on deterministic vertices; equivalently, validity on every local behavior. -/
def IsValid (I : BellInequality N M K) : Prop :=
  ∀ s : Assignment N M K, I.value (deterministicBehaviour s) ≤ I.bound

/-- The deterministic vertices on the bounding hyperplane. -/
def tightVertices (I : BellInequality N M K) : Set (Behaviour N M K) :=
  {p | p ∈ deterministicVertices N M K ∧ I.value p = I.bound}

/-- A valid inequality cuts out a nonempty face of relative codimension one. -/
def IsFacet (I : BellInequality N M K) : Prop :=
  I.IsValid ∧ I.tightVertices.Nonempty ∧
    affineDimension I.tightVertices + 1 = affineDimension (deterministicVertices N M K)

/-- Bell functionals commute with averaging over joint assignments. -/
@[category API, AMS 52 60 81]
lemma value_jointMarginal (I : BellInequality N M K) (q : Assignment N M K → ℝ) :
    I.value (jointMarginal q) = ∑ s, q s * I.value (deterministicBehaviour s) := by
  unfold value jointMarginal
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ x, ∑ s, ∑ a, I.coeff x a * (q s * deterministicBehaviour s x a) := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = ∑ s, ∑ x, ∑ a, I.coeff x a * (q s * deterministicBehaviour s x a) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro a _
      ring

/-- Testing an inequality on deterministic assignments is necessary and sufficient. -/
@[category API, AMS 52 60 81]
lemma isValid_iff_local (I : BellInequality N M K) :
    I.IsValid ↔ ∀ p : Behaviour N M K, IsLocal p → I.value p ≤ I.bound := by
  constructor
  · intro h p hp
    rcases hp with ⟨q, hq, rfl⟩
    rw [value_jointMarginal]
    calc
      ∑ s, q s * I.value (deterministicBehaviour s) ≤ ∑ s, q s * I.bound :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h s) (hq.1 s)
      _ = I.bound := by rw [← Finset.sum_mul, hq.2, one_mul]
  · intro h s
    exact h _ (deterministicBehaviour_isLocal s)

end BellInequality

/-- A complete family of facet representatives, with no duplicate supporting faces. -/
def IsCompleteFacetDescription (F : Finset (BellInequality N M K)) : Prop :=
  (∀ I ∈ F, I.IsFacet) ∧
  (∀ I ∈ F, ∀ J ∈ F, I.tightVertices = J.tightVertices → I = J) ∧
  ∀ p : Behaviour N M K,
    IsLocal p ↔ p ∈ localAffineSpace N M K ∧ ∀ I ∈ F, I.value p ≤ I.bound

/-- Determine a complete family of facet inequalities for every positive Bell scenario
$(N,M,K)$. The answer is a family of finite sets, not merely a yes-or-no existence claim. -/
@[category research open, AMS 52 68 81]
theorem allBellInequalities :
    let F : (N M K : ℕ) → Finset (BellInequality N M K) := answer(sorry)
    ∀ N M K : ℕ, 1 ≤ N → 1 ≤ M → 1 ≤ K → IsCompleteFacetDescription (F N M K) := by
  sorry

end OpenQuantumProblem1
