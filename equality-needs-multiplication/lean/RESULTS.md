# RESULTS

## Build environment

- Lean toolchain: `leanprover/lean4:v4.30.0`
- Lake: `Lake version 5.0.0-src+d024af0 (Lean version 4.30.0)`
- Mathlib input revision: `v4.30.0`
- Mathlib resolved commit: `c5ea00351c28e24afc9f0f84379aa41082b1188f`
- Repository base commit at verification time:
  `2ff117e96785e7538126bbd181afa581f63d3ec8` with the handoff updates in the
  working tree

## Verified Lean targets

`lake build` succeeds after registering `Sameness` as a Lake library target in
the root project. The following handoff theorems compile with no `sorry`:

- `no_additive_matcher`
- `no_additive_matcher_int`
- `identity_matches`
- `coherence_lt_one`
- `unique_invariant_minimizer_constant`
- `constant_score_balancedAccuracy`
- `exactly_chance_under_symmetry`
- `SamenessTheorem2.strictConvex_minimizer_unique`
- `SamenessTheorem2.strictConvex_invariant_minimizer_constant`
- `SamenessTheorem2.strictConvex_exactly_chance_under_symmetry`
- `SamenessTheorem2.equalityBalancedAccuracy_of_constant_score`
- `SamenessTheorem2.strictConvex_exactly_chance_under_symmetry_equalityBalancedAccuracy`
- `SamenessTheorem2.convexOn_softplus`
- `SamenessTheorem2.empiricalLogisticRisk_convex`
- `SamenessTheorem2.regularizedLogisticRisk_convex`
- `SamenessTheorem2.l2Regularizer_strictConvex`
- `SamenessTheorem2.regularizedLogisticRisk_strictConvex`
- `SamenessTheorem2.regularizedLogisticRisk_continuous`
- `SamenessTheorem2.regularizedLogisticRisk_sublevel_isBounded`
- `SamenessTheorem2.regularizedLogisticRisk_exists_isMinOn`
- `SamenessTheorem2.classBalancedRegularizedLogisticRisk_convex`
- `SamenessTheorem2.classBalancedRegularizedLogisticRisk_strictConvex`
- `SamenessTheorem2.classBalancedRegularizedLogisticRisk_continuous`
- `SamenessTheorem2.classBalancedRegularizedLogisticRisk_sublevel_isBounded`
- `SamenessTheorem2.classBalancedRegularizedLogisticRisk_exists_isMinOn`
- `SamenessTheorem2.classBalancedRegularizedLogisticRisk_exists_unique_isMinOn`
- `SamenessTheorem2.empiricalLogisticRisk_invariant`
- `SamenessTheorem2.regularizedLogisticRisk_invariant`
- `SamenessTheorem2.classBalancedRegularizedLogisticRisk_invariant`
- `SamenessTheorem2.concrete_regularized_logistic_exactly_chance`
- `SamenessTheorem2.concrete_regularized_logistic_exactly_chance_of_pos_reg`
- `SamenessTheorem2.concrete_regularized_logistic_exactly_chance_exists_of_pos_reg`
- `SamenessTheorem2.concrete_regularized_logistic_equalityBalancedAccuracy`
- `SamenessTheorem2.concrete_regularized_logistic_equalityBalancedAccuracy_of_pos_reg`
- `SamenessTheorem2.concrete_regularized_logistic_equalityBalancedAccuracy_exists_of_pos_reg`
- `SamenessTheorem2.classBalanced_regularized_logistic_equalityBalancedAccuracy_of_pos_reg`
- `SamenessTheorem2.classBalanced_regularized_logistic_equalityBalancedAccuracy_exists_of_pos_reg`
- `SamenessTheorem2.classBalanced_regularized_logistic_equalityBalancedAccuracy_exists_all_thresholds`
- `SamenessTheorem2.classBalanced_regularized_logistic_unique_minimizer_chance_all_thresholds`
- `SamenessTheorem2.classBalanced_regularized_logistic_equalityBalancedAccuracy_exists_of_pos_reg_half`

## Statement and proof changes

- Replaced the deprecated bundled assumption `[LinearOrderedField α]` in
  `no_additive_matcher` with the current Mathlib-compatible unbundled
  assumptions `[Field α] [LinearOrder α] [IsStrictOrderedRing α]`. This is the
  same ordered-field requirement in Mathlib v4.30.0.
- Switched real inner-product expressions from `⟪_, _⟫_ℝ` to the scoped plain
  real notation `⟪_, _⟫`, matching the opened `RealInnerProductSpace` notation.
- Finished `coherence_lt_one` by rewriting the equality case in the forward
  direction and normalizing the resulting real arithmetic.  Its docstring now
  states the proved pairwise `< 1` fact and does not claim an infinite-set
  uniform coherence bound.
- Added `AdditiveParams`, `AdditiveParams.permute`, and `AdditiveParams.score`
  to formalize one-hot additive matcher parameters for Theorem 2.
- Added `unique_invariant_minimizer_constant`: a unique minimizer of a
  permutation-invariant additive risk has constant `a` and `b` coordinates, so
  its score is constant on all query-key pairs.
- Added `constantScoreBalancedAccuracy` and
  `constant_score_balancedAccuracy`: thresholding any constant score has
  balanced accuracy exactly `1/2`.
- Added `exactly_chance_under_symmetry`, combining the symmetry result and the
  chance balanced-accuracy result.
- Added `Sameness/Theorem2.lean` with a stronger Theorem 2 formalization.  This
  file represents additive one-hot parameters as a real function space and uses
  `StrictConvexOn.eq_of_isMinOn` to derive minimizer uniqueness from strict
  convexity, removing the explicit `hunique` hypothesis used in the compact
  handoff theorem.
- Added `Sameness/BalancedAccuracy.lean` with the finite equality-task metric:
  positives are diagonal pairs `(s,s)`, negatives are off-diagonal pairs
  `(q,k)` with `q ≠ k`, and balanced accuracy is
  `(TPR + TNR) / 2`.  For a finite nontrivial alphabet, a constant score has
  balanced accuracy exactly `1/2` for every threshold.
- Added `Sameness/LogisticRisk.lean` with a concrete empirical logistic risk:
  `softplus x = log (1 + exp x)`, pair losses
  `softplus (-score)`/`softplus score`, a finite all-pairs empirical risk, and
  an optional coordinatewise `ℓ²` regularizer.  The module proves scalar
  softplus convexity from its second derivative, finite empirical logistic-risk
  convexity, regularized-risk convexity for `0 ≤ λ`, empirical-risk invariance
  under simultaneous relabeling, and regularized-risk invariance from the
  coordinate permutation proof for the regularizer.  It also proves strict
  convexity of the coordinatewise `ℓ²` regularizer, strict convexity of the
  concrete regularized logistic risk for `0 < λ`, continuity of the concrete
  risk, boundedness of the base sublevel set for `0 < λ`, existence of a global
  minimizer by Mathlib's finite-dimensional extreme-value theorem, a scalar
  compatibility chance theorem, and a fully concrete finite-dataset
  balanced-accuracy theorem with minimizer existence discharged.
- Added the class-balanced diagonal/off-diagonal logistic risk in
  `Sameness/LogisticRisk.lean`, with weights
  `(2 * Fintype.card S)⁻¹` and
  `(2 * (offDiagonalPairs S).card)⁻¹`.  The module proves its convexity,
  strict convexity for `0 < λ`, continuity, permutation invariance, bounded
  base sublevel set, minimizer existence, and the finite equality-task
  balanced-accuracy theorem with minimizer existence discharged.
- Added named class-balanced polish theorems:
  `classBalancedRegularizedLogisticRisk_exists_unique_isMinOn` for unique
  global minimizer existence, and
  `classBalanced_regularized_logistic_equalityBalancedAccuracy_exists_all_thresholds`
  plus
  `classBalanced_regularized_logistic_unique_minimizer_chance_all_thresholds`
  to state that the same minimizer has chance balanced accuracy for every
  threshold, and
  `classBalanced_regularized_logistic_equalityBalancedAccuracy_exists_of_pos_reg_half`
  for the common `λ / 2` regularizer normalization.
- Split the old theorem-heavy root module into `Sameness/Basic.lean` and made
  `Sameness.lean` an umbrella import file for `Sameness.Basic`,
  `Sameness.Theorem2`, `Sameness.BalancedAccuracy`, and
  `Sameness.LogisticRisk`.
- Registered `Sameness` as the Lake library target for the standalone
  `equality-needs-multiplication/lean` project and included it in
  `defaultTargets`, so `lake build` checks the handoff file.

## Theorem 2 status

The symmetry and balanced-accuracy core of Theorem 2 is proved in three levels:

- `Sameness.lean` has the compact handoff theorem, parameterized by an explicit
  uniqueness hypothesis.
- `Sameness/Theorem2.lean` proves the stronger scalar-compatibility version
  from strict convexity:
  if a one-hot additive risk is strictly convex on the full parameter space,
  invariant under simultaneous symbol permutations, and `p` is a global
  minimizer, then `p` has constant additive score on all query-key pairs and
  the scalar constant-score chance helper returns exactly `1/2`.
- `Sameness/BalancedAccuracy.lean` proves the reviewed dataset-level version:
  on a finite nontrivial equality task, a constant score has
  `equalityBalancedAccuracy = 1/2`, where the metric is computed over the
  diagonal positives and off-diagonal negatives.

The concrete logistic-risk formulas are now expanded in
`Sameness/LogisticRisk.lean`.  The original all-pairs empirical risk remains
verified, and the file now also defines the class-balanced diagonal/off-
diagonal risk:

- `diagonalLogisticRisk`
- `offDiagonalLogisticRisk`
- `classBalancedRegularizedLogisticRisk`

For the class-balanced risk, the module proves convexity and permutation
invariance from the definitions, proves strict convexity for positive `ℓ²`
regularization, proves continuity and boundedness of the base sublevel set, and
uses `Continuous.exists_forall_le_of_isBounded` to prove
`classBalancedRegularizedLogisticRisk_exists_isMinOn`: for every finite `S` and
every `0 < λ`, the class-balanced regularized logistic risk has a global
minimizer.  The named theorem
`classBalancedRegularizedLogisticRisk_exists_unique_isMinOn` strengthens this
to unique global minimizer existence.

The final dataset-level theorem is
`classBalanced_regularized_logistic_equalityBalancedAccuracy_exists_of_pos_reg`:
if `0 < λ` and `S` is finite and nontrivial, then there exists a global
minimizer of the class-balanced regularized logistic risk, its additive score
is constant on all query-key pairs, and the finite equality-task balanced
accuracy is exactly `1/2` for every threshold.  The wrapper
`classBalanced_regularized_logistic_equalityBalancedAccuracy_exists_all_thresholds`
packages this as one minimizer that works for all thresholds, and
`classBalanced_regularized_logistic_unique_minimizer_chance_all_thresholds`
strengthens it to the unique minimizer with the same all-threshold conclusion.
The wrapper
`classBalanced_regularized_logistic_equalityBalancedAccuracy_exists_of_pos_reg_half`
states the same result for `classBalancedRegularizedLogisticRisk S (λ / 2)`.
No `sorry` is used.

## Final verification output

Standalone target:

```text
lake build Sameness
Build completed successfully (8480 jobs).
```

Full project:

```text
lake build
Build completed successfully (8532 jobs).
```

Proof-gap audit:

```text
rg -n "^\\s*(sorry|axiom|admit|native_decide|unsafe)\\b|set_option\\s+maxHeartbeats\\s+0" --glob "*.lean" .
# no matches
```

## Suggested paper footnote

> A machine-checked Lean 4 proof of Theorems 1 and 3, plus the concrete
> class-balanced positive-`ℓ²` regularized finite equality-task version of
> Theorem 2 with minimizer existence discharged, is available at `<REPO_URL>`
> (base commit `2ff117e96785e7538126bbd181afa581f63d3ec8` plus the handoff
> updates), built against Mathlib `v4.30.0`
> (`c5ea00351c28e24afc9f0f84379aa41082b1188f`).
