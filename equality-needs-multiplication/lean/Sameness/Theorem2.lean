import Sameness.Basic

/-!
# Stronger Theorem 2: strict convexity supplies uniqueness

This file strengthens the Theorem 2 scaffold in `Sameness.lean`.

The compact handoff theorem in `Sameness.Basic` assumes uniqueness of the
minimizer.  Here the parameter space is represented as a genuine real vector
space, so Mathlib's `StrictConvexOn.eq_of_isMinOn` can derive that uniqueness
from strict convexity.
The result is the formal symmetry argument from the paper:

* a global minimizer of a strictly convex, permutation-invariant additive risk is
  fixed by every symbol swap;
* therefore both one-hot additive coordinate readouts are constant;
* therefore every query-key pair receives the same score;
* therefore the scalar constant-score chance helper returns exactly `1/2`.

The finite equality-task balanced-accuracy statement, with diagonal positives
and off-diagonal negatives, is proved in `Sameness.BalancedAccuracy`.
-/

namespace SamenessTheorem2

/-- Coordinates for a one-hot additive matcher: query coordinate, key
coordinate, and a global bias coordinate. -/
inductive Coord (S : Type*) where
  | query : S → Coord S
  | key : S → Coord S
  | bias : Coord S
  deriving DecidableEq, Fintype

/-- A one-hot additive parameter vector, represented as a function space so it
inherits the standard real vector-space structure from Mathlib. -/
abbrev Params (S : Type*) := Coord S → ℝ

/-- Query-side additive readout. -/
def a {S : Type*} (p : Params S) (s : S) : ℝ :=
  p (Coord.query s)

/-- Key-side additive readout. -/
def b {S : Type*} (p : Params S) (s : S) : ℝ :=
  p (Coord.key s)

/-- Global additive offset. -/
def c {S : Type*} (p : Params S) : ℝ :=
  p Coord.bias

/-- Additive score for a query-key pair. -/
def score {S : Type*} (p : Params S) (q k : S) : ℝ :=
  a p q + b p k + c p

/-- Simultaneous relabeling of the query and key one-hot coordinates. -/
def relabel {S : Type*} (σ : Equiv.Perm S) (p : Params S) : Params S
  | Coord.query s => p (Coord.query (σ.symm s))
  | Coord.key s => p (Coord.key (σ.symm s))
  | Coord.bias => p Coord.bias

@[simp]
theorem relabel_query {S : Type*} (σ : Equiv.Perm S) (p : Params S) (s : S) :
    relabel σ p (Coord.query s) = p (Coord.query (σ.symm s)) :=
  rfl

@[simp]
theorem relabel_key {S : Type*} (σ : Equiv.Perm S) (p : Params S) (s : S) :
    relabel σ p (Coord.key s) = p (Coord.key (σ.symm s)) :=
  rfl

@[simp]
theorem relabel_bias {S : Type*} (σ : Equiv.Perm S) (p : Params S) :
    relabel σ p Coord.bias = p Coord.bias :=
  rfl

/-- Relabeling parameters and then evaluating on relabeled symbols leaves the
score unchanged. -/
theorem score_relabel_apply {S : Type*} (σ : Equiv.Perm S) (p : Params S)
    (q k : S) :
    score (relabel σ p) (σ q) (σ k) = score p q k := by
  simp [score, a, b, c]

/-- Strict convexity turns global minimizers into unique global minimizers. -/
theorem strictConvex_minimizer_unique
    {P : Type*} [AddCommMonoid P] [SMul ℝ P]
    (risk : P → ℝ) {p q : P}
    (hstrict : StrictConvexOn ℝ Set.univ risk)
    (hp : IsMinOn risk Set.univ p) (hq : IsMinOn risk Set.univ q) :
    p = q :=
  hstrict.eq_of_isMinOn hp hq (by simp) (by simp)

/-- Strong Theorem 2 symmetry core.  If the additive one-hot risk is strictly
convex on the full parameter space, invariant under simultaneous symbol
permutations, and `p` is a global minimizer, then the optimal additive score is
constant on all query-key pairs. -/
theorem strictConvex_invariant_minimizer_constant
    {S : Type*}
    (risk : Params S → ℝ) (p : Params S)
    (hstrict : StrictConvexOn ℝ Set.univ risk)
    (hmin : IsMinOn risk Set.univ p)
    (hinv : ∀ (σ : Equiv.Perm S) q, risk (relabel σ q) = risk q) :
    (∀ x y, a p x = a p y) ∧
      (∀ x y, b p x = b p y) ∧
      (∀ q k q' k', score p q k = score p q' k') := by
  classical
  have hfixed : ∀ σ : Equiv.Perm S, relabel σ p = p := by
    intro σ
    have hmin_relabel : IsMinOn risk Set.univ (relabel σ p) := by
      intro r hr
      rw [hinv σ p]
      exact hmin hr
    exact strictConvex_minimizer_unique risk hstrict hmin_relabel hmin
  have ha_const : ∀ x y, a p x = a p y := by
    intro x y
    have hswap := congrFun (hfixed (Equiv.swap x y)) (Coord.query x)
    simp [relabel] at hswap
    exact hswap.symm
  have hb_const : ∀ x y, b p x = b p y := by
    intro x y
    have hswap := congrFun (hfixed (Equiv.swap x y)) (Coord.key x)
    simp [relabel] at hswap
    exact hswap.symm
  refine ⟨ha_const, hb_const, ?_⟩
  intro q k q' k'
  simp [score, ha_const q q', hb_const k k']

/-- Strong Theorem 2 combined statement.  A global minimizer of a strictly
convex, permutation-invariant additive one-hot risk is a constant-score matcher;
the scalar constant-score chance helper is exactly chance. -/
theorem strictConvex_exactly_chance_under_symmetry
    {S : Type*}
    (risk : Params S → ℝ) (p : Params S)
    (hstrict : StrictConvexOn ℝ Set.univ risk)
    (hmin : IsMinOn risk Set.univ p)
    (hinv : ∀ (σ : Equiv.Perm S) q, risk (relabel σ q) = risk q)
    (τ : ℝ) :
    (∀ q k q' k', score p q k = score p q' k') ∧
      (∀ q k, constantScoreBalancedAccuracy (score p q k) τ = (1 : ℝ) / 2) := by
  have hconst :=
    strictConvex_invariant_minimizer_constant
      (risk := risk) (p := p) hstrict hmin hinv
  refine ⟨hconst.2.2, ?_⟩
  intro q k
  exact constant_score_balancedAccuracy (score p q k) τ

end SamenessTheorem2
