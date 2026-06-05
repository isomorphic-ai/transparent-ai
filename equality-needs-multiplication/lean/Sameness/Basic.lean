import Mathlib

/-!
# Sameness Requires a Product — machine-checkable statements

Companion formalization to the note *Sameness Requires a Product: An Elementary
Obstruction to Additive Matching*.

GOAL: make this file build with `lake build` — **zero `sorry`, zero errors,
zero warnings about unproved goals**.

INTEGRITY RULES (read before editing):
* Do NOT delete, weaken, or trivialize a theorem statement to make it pass.
* If a statement must change to be provable (e.g. an extra hypothesis), make the
  change minimal, keep it faithful to the math in `PROOFS.md`, and record it with
  justification in `RESULTS.md`.
* Never leave a silent `sorry`. If you cannot prove something, leave it `sorry`
  AND document exactly what failed in `RESULTS.md`. A documented gap is fine; a
  hidden one is not.
* Do not close goals with `axiom`, `native_decide` hacks, or by assuming the
  conclusion. Proofs must be real.

Lemma names below follow Mathlib as of early 2026 and may have drifted. When a
name fails, search the current Mathlib (`exact?`, `apply?`, `rw?`, loogle) for
the right one rather than guessing.
-/

open scoped RealInnerProductSpace

/-! ## Theorem 1 — the obstruction (REQUIRED, should be a one-liner)

Equality of two symbols is XNOR. No additive readout `a q + b k`, under any
single threshold τ, can correctly classify the four pairs relating two symbols
`i` and `j`: the two diagonals `(i,i),(j,j)` and the two off-diagonals
`(i,j),(j,i)` share the same sum, so they cannot straddle τ. -/
theorem no_additive_matcher
    {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] {S : Type*}
    (a b : S → α) (i j : S) (τ : α)
    (h₁ : τ ≤ a i + b i) (h₂ : τ ≤ a j + b j)
    (h₃ : a i + b j < τ) (h₄ : a j + b i < τ) : False := by
  linarith

/-- Integer instance, provable in core Lean (`omega`); kept as a cross-check. -/
theorem no_additive_matcher_int
    {S : Type} (a b : S → Int) (i j : S) (τ : Int)
    (h₁ : τ ≤ a i + b i) (h₂ : τ ≤ a j + b j)
    (h₃ : a i + b j < τ) (h₄ : a j + b i < τ) : False := by
  omega

/-! ## Theorem 3 — sufficiency (REQUIRED)

With unit-norm features and off-diagonal coherence bounded by μ < τ ≤ 1, the
bilinear identity readout `⟪φ q, φ k⟫` classifies equality without error:
every diagonal score is `1 ≥ τ`, every off-diagonal score is `≤ μ < τ`. -/
theorem identity_matches
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S : Type*} (φ : S → E)
    (hunit : ∀ s, ‖φ s‖ = 1)
    (μ τ : ℝ)
    (hμ : ∀ i j, i ≠ j → ⟪φ i, φ j⟫ ≤ μ)
    (hlo : μ < τ) (hhi : τ ≤ 1) :
    (∀ q, τ ≤ ⟪φ q, φ q⟫) ∧ (∀ i j, i ≠ j → ⟪φ i, φ j⟫ < τ) := by
  refine ⟨fun q => ?_, fun i j hij => ?_⟩
  · -- ⟪φ q, φ q⟫ = ‖φ q‖² = 1 ≥ τ
    have h : ⟪φ q, φ q⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, hunit q]; norm_num
    rw [h]; exact hhi
  · -- off-diagonal ≤ μ < τ
    exact lt_of_le_of_lt (hμ i j hij) hlo

/-- Distinct unit vectors have pairwise coherence strictly below `1`
    (Cauchy-Schwarz equality case). For finite symbol sets this gives a uniform
    off-diagonal bound by taking a maximum; for infinite sets, a uniform
    coherence bound must be assumed separately. -/
theorem coherence_lt_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : u ≠ v) :
    ⟪u, v⟫ < 1 := by
  -- Outline (see PROOFS.md §3):
  --   ⟪u,v⟫ ≤ ‖u‖‖v‖ = 1 by Cauchy–Schwarz (`real_inner_le_norm`).
  --   If equality held, ‖u-v‖² = ‖u‖² - 2⟪u,v⟫ + ‖v‖² = 1 - 2 + 1 = 0,
  --   so u = v, contradicting `huv`.
  have hle : ⟪u, v⟫ ≤ 1 := by
    have h := real_inner_le_norm u v
    rwa [hu, hv, mul_one] at h
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    apply huv
    have hzsq : ‖u - v‖ ^ 2 = 0 := by
      rw [norm_sub_sq_real, hu, hv, h]; norm_num
    have hz : ‖u - v‖ = 0 := by
      simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzsq
    have : u - v = 0 := norm_eq_zero.mp hz
    rwa [sub_eq_zero] at this

/-! ## Theorem 2 — exactly chance (STRETCH GOAL, optional)

Under symbol symmetry, the loss-optimal additive matcher is constant and
achieves balanced accuracy exactly 1/2 (see PROOFS.md §2). This needs convex
analysis (strict-convex uniqueness) plus a permutation-invariance argument.

The formalization below proves the symmetry core of the argument abstractly:
if an additive one-hot risk has a unique minimizer and is invariant under every
symbol permutation, then both additive coordinate readouts are constant, hence
the score is constant on pairs.  Strict convexity is the standard way to supply
the `hunique` hypothesis for a concrete logistic risk, but we keep that analytic
layer abstract here.  We also prove the classifier consequence used in the
paper in a compact scalar form: thresholding any constant score gives the
constant-score chance helper exactly `1/2`.  The finite dataset-level balanced
accuracy theorem is in `Sameness.BalancedAccuracy`.
-/

/-- One-hot additive matcher parameters: two per-symbol readouts and a global
offset.  The score is `a q + b k + c`. -/
structure AdditiveParams (S : Type*) where
  a : S → ℝ
  b : S → ℝ
  c : ℝ

namespace AdditiveParams

/-- Simultaneous relabeling of the one-hot coordinates by a permutation. -/
def permute {S : Type*} (σ : Equiv.Perm S) (p : AdditiveParams S) :
    AdditiveParams S :=
  { a := fun s => p.a (σ.symm s)
    b := fun s => p.b (σ.symm s)
    c := p.c }

/-- Additive score for a query-key pair. -/
def score {S : Type*} (p : AdditiveParams S) (q k : S) : ℝ :=
  p.a q + p.b k + p.c

end AdditiveParams

/-- The symmetry core of Theorem 2: a unique minimizer of a permutation-invariant
additive risk is fixed by every swap, so its two coordinate readouts are
constant and every pair receives the same score. -/
theorem unique_invariant_minimizer_constant
    {S : Type*}
    (risk : AdditiveParams S → ℝ) (p : AdditiveParams S)
    (hmin : ∀ q, risk p ≤ risk q)
    (hunique : ∀ q, (∀ r, risk q ≤ risk r) → q = p)
    (hinv : ∀ (σ : Equiv.Perm S) q,
      risk (AdditiveParams.permute σ q) = risk q) :
    (∀ x y, p.a x = p.a y) ∧
      (∀ x y, p.b x = p.b y) ∧
      (∀ q k q' k', p.score q k = p.score q' k') := by
  classical
  have hfixed : ∀ σ : Equiv.Perm S, AdditiveParams.permute σ p = p := by
    intro σ
    apply hunique
    intro r
    rw [hinv σ p]
    exact hmin r
  have ha_const : ∀ x y, p.a x = p.a y := by
    intro x y
    have hswap := hfixed (Equiv.swap x y)
    have ha := congrArg (fun q : AdditiveParams S => q.a x) hswap
    simp [AdditiveParams.permute] at ha
    exact ha.symm
  have hb_const : ∀ x y, p.b x = p.b y := by
    intro x y
    have hswap := hfixed (Equiv.swap x y)
    have hb := congrArg (fun q : AdditiveParams S => q.b x) hswap
    simp [AdditiveParams.permute] at hb
    exact hb.symm
  refine ⟨ha_const, hb_const, ?_⟩
  intro q k q' k'
  simp [AdditiveParams.score, ha_const q q', hb_const k k']

/-- Scalar chance helper for a thresholded constant score.  The first branch is
the true-positive rate and the second branch is the true-negative rate for a
classifier that emits one label for every pair.  The finite equality-task metric
is formalized in `Sameness.BalancedAccuracy`. -/
noncomputable def constantScoreBalancedAccuracy (score τ : ℝ) : ℝ :=
  ((if τ ≤ score then (1 : ℝ) else 0) + (if τ ≤ score then (0 : ℝ) else 1)) / 2

/-- A constant classifier has the scalar chance helper exactly at chance: either
it always predicts positive, giving `(TPR,TNR)=(1,0)`, or it always predicts
negative, giving `(TPR,TNR)=(0,1)`. -/
theorem constant_score_balancedAccuracy (score τ : ℝ) :
    constantScoreBalancedAccuracy score τ = (1 : ℝ) / 2 := by
  by_cases h : τ ≤ score
  · simp [constantScoreBalancedAccuracy, h]
  · simp [constantScoreBalancedAccuracy, h]

/-- Combined abstract Theorem 2 statement: under permutation invariance and
unique optimality, the additive optimum is constant on all query-key pairs, and
the scalar constant-score chance helper is exactly chance. -/
theorem exactly_chance_under_symmetry
    {S : Type*}
    (risk : AdditiveParams S → ℝ) (p : AdditiveParams S)
    (hmin : ∀ q, risk p ≤ risk q)
    (hunique : ∀ q, (∀ r, risk q ≤ risk r) → q = p)
    (hinv : ∀ (σ : Equiv.Perm S) q,
      risk (AdditiveParams.permute σ q) = risk q)
    (τ : ℝ) :
    (∀ q k q' k', p.score q k = p.score q' k') ∧
      (∀ q k, constantScoreBalancedAccuracy (p.score q k) τ = (1 : ℝ) / 2) := by
  have hconst :=
    unique_invariant_minimizer_constant (risk := risk) (p := p) hmin hunique hinv
  refine ⟨hconst.2.2, ?_⟩
  intro q k
  exact constant_score_balancedAccuracy (p.score q k) τ
