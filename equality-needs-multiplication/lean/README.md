# Sameness Requires a Product — Lean formalization

This directory contains the Lean 4 formalization for the note
**“Sameness Requires a Product: An Elementary Obstruction to Additive Matching.”**

The manuscript artifacts are included in `../paper/`:

```text
../paper/sameness_requires_a_product_combined_v5a.tex
../paper/sameness_requires_a_product_combined_v5a.pdf
```

The formalization proves the paper’s three core claims:

1. **Theorem 1 — additive obstruction.**
   A score of the form `a q + b k`, thresholded by a single scalar, cannot
   exactly classify equality on two symbols.

2. **Theorem 2 — symmetric regularized additive training is chance.**
   For the finite equality task, the class-balanced logistic risk with positive
   coordinatewise `ℓ²` regularization has a unique symmetric additive optimum.
   That optimum assigns the same score to every query-key pair, so every
   thresholded classifier derived from it has balanced accuracy exactly `1 / 2`.

3. **Theorem 3 — a product/bilinear matcher suffices.**
   A bilinear identity matcher `⟪φ q, φ k⟫` classifies equality correctly when
   the feature vectors are unit vectors and off-diagonal inner products are
   below the threshold.

The important practical point is that the files are not four independent proof
attempts. They form a proof ladder. Read them in the order below.

---

## Quick start

From this `equality-needs-multiplication/lean` directory:

```bash
lake build Sameness
```

Useful focused targets:

```bash
lake build Sameness.BalancedAccuracy
lake build Sameness.LogisticRisk
```

The package was verified against Lean/Mathlib versions listed in `RESULTS.md`.

---

## File layout

For public readability, the Lean module layout is:

```text
Sameness.lean                    # umbrella import file only
Sameness/
  Basic.lean                     # Theorems 1 and 3; compact abstract Theorem 2 scaffold
  Theorem2.lean                  # strict-convexity symmetry theorem
  BalancedAccuracy.lean          # finite equality-task balanced accuracy
  LogisticRisk.lean              # concrete logistic risks and final class-balanced theorem
RESULTS.md                       # build/proof audit log, not the reader entry point
README.md                        # this guide
```

The root `Sameness.lean` is an umbrella module:

```lean
import Sameness.Basic
import Sameness.Theorem2
import Sameness.BalancedAccuracy
import Sameness.LogisticRisk
```

This is the cleanest Lean style: one conceptual layer per module, plus one
root file that imports the public API.

---

## Reader’s map

### 1. `Sameness/Basic.lean`

This is the entry point for the elementary mathematical content.

Main declarations:

```lean
no_additive_matcher
no_additive_matcher_int
identity_matches
coherence_lt_one
unique_invariant_minimizer_constant
constant_score_balancedAccuracy
exactly_chance_under_symmetry
```

What it proves:

- `no_additive_matcher` is the additive/XNOR obstruction.
- `identity_matches` is the bilinear sufficiency theorem.
- `coherence_lt_one` proves that distinct unit vectors have pairwise inner
  product strictly below `1`.
- `unique_invariant_minimizer_constant` proves the abstract symmetry core of
  Theorem 2: a unique minimizer of a permutation-invariant additive risk is
  fixed by all symbol swaps, hence has constant query and key coordinates.

This file intentionally keeps the optimization layer abstract.

---

### 2. `Sameness/Theorem2.lean`

This file strengthens the abstract Theorem 2 scaffold.

Main declarations:

```lean
SamenessTheorem2.Coord
SamenessTheorem2.Params
SamenessTheorem2.score
SamenessTheorem2.relabel
SamenessTheorem2.strictConvex_minimizer_unique
SamenessTheorem2.strictConvex_invariant_minimizer_constant
SamenessTheorem2.strictConvex_exactly_chance_under_symmetry
```

What it adds:

- additive parameters are represented as a real function space:

  ```lean
  abbrev Params (S : Type*) := Coord S → ℝ
  ```

- this gives Mathlib’s vector-space structure for free;
- strict convexity supplies uniqueness via `StrictConvexOn.eq_of_isMinOn`;
- permutation invariance then forces the minimizer to be constant on all
  query-key pairs.

This file proves the abstract optimization/symmetry theorem, but still does not
commit to a specific loss.

---

### 3. `Sameness/BalancedAccuracy.lean`

This file formalizes the actual finite equality-task metric.

Main declarations:

```lean
SamenessTheorem2.offDiagonalPairs
SamenessTheorem2.equalityTruePositiveRate
SamenessTheorem2.equalityTrueNegativeRate
SamenessTheorem2.equalityBalancedAccuracy
SamenessTheorem2.equalityBalancedAccuracy_of_constant_score
SamenessTheorem2.strictConvex_exactly_chance_under_symmetry_equalityBalancedAccuracy
```

What it adds:

- positive examples are diagonal pairs `(s, s)`;
- negative examples are off-diagonal pairs `(q, k)` with `q ≠ k`;
- balanced accuracy is `(TPR + TNR) / 2`;
- a constant score has balanced accuracy exactly `1 / 2` for every threshold,
  provided the alphabet is finite and nontrivial.

This file is the bridge from “the score is constant” to “the classifier is
exactly chance on the equality task.”

---

### 4. `Sameness/LogisticRisk.lean`

This is the concrete-risk layer. It is longer because it proves convexity,
strict convexity, continuity, invariance, bounded sublevel sets, minimizer
existence, and the final class-balanced theorem.

Main definitions:

```lean
SamenessTheorem2.softplus
SamenessTheorem2.pairLogisticLoss
SamenessTheorem2.empiricalLogisticRisk
SamenessTheorem2.l2Regularizer
SamenessTheorem2.regularizedLogisticRisk
SamenessTheorem2.diagonalLogisticRisk
SamenessTheorem2.offDiagonalLogisticRisk
SamenessTheorem2.classBalancedRegularizedLogisticRisk
```

Main theorem families:

```lean
SamenessTheorem2.convexOn_softplus
SamenessTheorem2.regularizedLogisticRisk_strictConvex
SamenessTheorem2.classBalancedRegularizedLogisticRisk_strictConvex
SamenessTheorem2.classBalancedRegularizedLogisticRisk_invariant
SamenessTheorem2.classBalancedRegularizedLogisticRisk_exists_isMinOn
SamenessTheorem2.classBalancedRegularizedLogisticRisk_exists_unique_isMinOn
```

Final paper-aligned theorem:

```lean
SamenessTheorem2.classBalanced_regularized_logistic_unique_minimizer_chance_all_thresholds
```

Informally, this says:

> For a finite nontrivial alphabet and positive regularization `λ`, the
> class-balanced regularized logistic risk has a unique global minimizer. That
> minimizer has constant additive score on all query-key pairs, and for every
> threshold its finite equality-task balanced accuracy is exactly `1 / 2`.

There is also a convenience theorem for the common `λ / 2` regularizer
normalization:

```lean
SamenessTheorem2.classBalanced_regularized_logistic_equalityBalancedAccuracy_exists_of_pos_reg_half
```

---

## Theorem map

| Paper claim | Lean declaration | File |
|---|---|---|
| No additive threshold matcher can exactly classify equality on two symbols | `no_additive_matcher` | `Sameness/Basic.lean` |
| Integer-specialized additive obstruction | `no_additive_matcher_int` | `Sameness/Basic.lean` |
| Bilinear identity matcher works under a coherence margin | `identity_matches` | `Sameness/Basic.lean` |
| Distinct unit vectors have pairwise inner product `< 1` | `coherence_lt_one` | `Sameness/Basic.lean` |
| Unique invariant additive minimizer has constant score | `unique_invariant_minimizer_constant` | `Sameness/Basic.lean` |
| Strict convexity supplies minimizer uniqueness | `SamenessTheorem2.strictConvex_minimizer_unique` | `Sameness/Theorem2.lean` |
| Strict convexity + invariance implies constant additive optimum | `SamenessTheorem2.strictConvex_invariant_minimizer_constant` | `Sameness/Theorem2.lean` |
| Constant score has equality-task balanced accuracy `1 / 2` | `SamenessTheorem2.equalityBalancedAccuracy_of_constant_score` | `Sameness/BalancedAccuracy.lean` |
| Class-balanced logistic risk is strictly convex for `0 < λ` | `SamenessTheorem2.classBalancedRegularizedLogisticRisk_strictConvex` | `Sameness/LogisticRisk.lean` |
| Class-balanced logistic risk is invariant under relabeling | `SamenessTheorem2.classBalancedRegularizedLogisticRisk_invariant` | `Sameness/LogisticRisk.lean` |
| Class-balanced logistic risk has a global minimizer | `SamenessTheorem2.classBalancedRegularizedLogisticRisk_exists_isMinOn` | `Sameness/LogisticRisk.lean` |
| Class-balanced logistic risk has a unique global minimizer | `SamenessTheorem2.classBalancedRegularizedLogisticRisk_exists_unique_isMinOn` | `Sameness/LogisticRisk.lean` |
| Final paper-aligned chance theorem, all thresholds, unique minimizer | `SamenessTheorem2.classBalanced_regularized_logistic_unique_minimizer_chance_all_thresholds` | `Sameness/LogisticRisk.lean` |

---

## Why the proof is layered

Theorem 2 is split because each layer removes one assumption from the previous
layer:

```text
Basic.lean
  assumes uniqueness + invariance
  proves constant additive score

Theorem2.lean
  assumes strict convexity + invariance + global minimality
  derives uniqueness
  proves constant additive score

BalancedAccuracy.lean
  defines the real finite equality-task metric
  proves constant score => balanced accuracy 1 / 2

LogisticRisk.lean
  defines the concrete class-balanced logistic objective
  proves convexity, strict convexity, invariance, continuity, existence,
  uniqueness, and the final chance theorem
```

So the file structure is not accidental duplication. It is a sequence of
increasingly concrete theorem statements.

---

## What to cite in the paper

For a compact Lean footnote, cite the final theorem:

```lean
SamenessTheorem2.classBalanced_regularized_logistic_unique_minimizer_chance_all_thresholds
```

and mention that the elementary obstruction and product sufficiency are:

```lean
no_additive_matcher
identity_matches
```

A concise paper footnote could be:

> A Lean 4 formalization proves the additive obstruction theorem, the bilinear
> sufficiency theorem, and the class-balanced regularized logistic-risk theorem:
> for finite nontrivial alphabets and positive `ℓ²` regularization, the unique
> additive minimizer has constant score and therefore balanced accuracy `1 / 2`
> for every threshold.

---

## Maintenance notes

- Keep `RESULTS.md` as a verification/audit log, not as the main reader guide.
- Prefer theorem names that encode the mathematical content over chronology.
- Avoid presenting `constantScoreBalancedAccuracy` as the main balanced-accuracy
  theorem; it is a scalar compatibility helper. The dataset-level theorem is
  `equalityBalancedAccuracy_of_constant_score`.
- Keep the all-pairs empirical logistic risk declarations if useful, but cite the
  `classBalanced*` declarations for the paper because they match the paper’s
  class-balanced formula.
- If the public package grows, add a `docs/TheoremMap.md` rather than merging all
  Lean files into one large file.

---

## Refactor recommendation

Do **not** compress all proofs into one `Sameness.lean` file. That would make
`LogisticRisk.lean` dominate the artifact and hide the elementary Theorems 1 and
3.

The best standard layout is:

```text
Sameness.lean                 # only imports public modules
Sameness/Basic.lean           # short, readable, elementary theorem statements
Sameness/Theorem2.lean        # abstract strict-convexity theorem
Sameness/BalancedAccuracy.lean
Sameness/LogisticRisk.lean
README.md
RESULTS.md
```

This gives readers two paths:

- **paper readers** read `README.md`, then `Sameness/Basic.lean`, then the final
  theorem statement in `Sameness/LogisticRisk.lean`;
- **Lean reviewers** follow the dependency chain through all four modules.
