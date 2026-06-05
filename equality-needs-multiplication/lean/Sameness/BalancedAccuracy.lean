import Sameness.Theorem2

/-!
# Balanced accuracy for the finite equality task

This module fills the modeling gap noted in review: balanced accuracy is a
metric of a thresholded classifier over a finite equality dataset, not a
property of one scalar score in isolation.

Positive examples are diagonal pairs `(s,s)`.  Negative examples are
off-diagonal pairs `(q,k)` with `q ≠ k`.  For a finite nontrivial alphabet, a
constant thresholded score predicts one label on both sets, so either
`(TPR,TNR)=(1,0)` or `(TPR,TNR)=(0,1)`, and balanced accuracy is exactly `1/2`.
-/

open scoped BigOperators

namespace SamenessTheorem2

noncomputable section

/-- Off-diagonal query-key pairs, i.e. the negative examples for equality. -/
def offDiagonalPairs (S : Type*) [Fintype S] [DecidableEq S] : Finset (S × S) :=
  Finset.univ.filter fun pair : S × S => pair.1 ≠ pair.2

/-- True-positive rate for a thresholded score on the equality task. -/
def equalityTruePositiveRate {S : Type*} [Fintype S] (score : S → S → ℝ) (τ : ℝ) : ℝ :=
  ((Finset.univ.filter fun s : S => τ ≤ score s s).card : ℝ) / Fintype.card S

/-- True-negative rate for a thresholded score on the equality task. -/
def equalityTrueNegativeRate {S : Type*} [Fintype S] [DecidableEq S]
    (score : S → S → ℝ) (τ : ℝ) : ℝ :=
  (((offDiagonalPairs S).filter fun pair : S × S => score pair.1 pair.2 < τ).card : ℝ) /
    (offDiagonalPairs S).card

/-- Balanced accuracy for a thresholded score on the finite equality task. -/
def equalityBalancedAccuracy {S : Type*} [Fintype S] [DecidableEq S]
    (score : S → S → ℝ) (τ : ℝ) : ℝ :=
  (equalityTruePositiveRate score τ + equalityTrueNegativeRate score τ) / 2

theorem offDiagonalPairs_nonempty (S : Type*) [Fintype S] [DecidableEq S] [Nontrivial S] :
    (offDiagonalPairs S).Nonempty := by
  classical
  obtain ⟨x, y, hxy⟩ := exists_pair_ne S
  exact ⟨(x, y), by simp [offDiagonalPairs, hxy]⟩

/-- A constant thresholded score has chance balanced accuracy on the finite
nontrivial equality task. -/
theorem equalityBalancedAccuracy_of_constant_score
    {S : Type*} [Fintype S] [DecidableEq S] [Nontrivial S]
    (score : S → S → ℝ) (τ : ℝ)
    (hconst : ∀ q k q' k', score q k = score q' k') :
    equalityBalancedAccuracy score τ = (1 : ℝ) / 2 := by
  classical
  let s₀ : S := Classical.arbitrary S
  have hS_ne : (Fintype.card S : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card S))
  have hoff_ne : ((offDiagonalPairs S).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (offDiagonalPairs_nonempty S))
  by_cases hpred : τ ≤ score s₀ s₀
  · have hdiag : ∀ s : S, τ ≤ score s s := by
      intro s
      rw [hconst s s s₀ s₀]
      exact hpred
    have hoff : ∀ pair ∈ offDiagonalPairs S, ¬ score pair.1 pair.2 < τ := by
      intro pair _
      rw [hconst pair.1 pair.2 s₀ s₀]
      exact not_lt.mpr hpred
    have hdiag_filter :
        (Finset.univ.filter fun s : S => τ ≤ score s s) = Finset.univ := by
      exact Finset.filter_eq_self.mpr (by intro s _; exact hdiag s)
    have hoff_filter :
        ((offDiagonalPairs S).filter fun pair : S × S => score pair.1 pair.2 < τ) = ∅ := by
      exact Finset.filter_eq_empty_iff.mpr (by intro pair hp hlt; exact hoff pair hp hlt)
    simp [equalityBalancedAccuracy, equalityTruePositiveRate, equalityTrueNegativeRate,
      hdiag_filter, hoff_filter, hS_ne]
  · have hdiag : ∀ s : S, ¬ τ ≤ score s s := by
      intro s hs
      apply hpred
      rwa [hconst s s s₀ s₀] at hs
    have hoff : ∀ pair ∈ offDiagonalPairs S, score pair.1 pair.2 < τ := by
      intro pair _
      apply lt_of_not_ge
      intro hp
      apply hpred
      rwa [hconst pair.1 pair.2 s₀ s₀] at hp
    have hdiag_filter :
        (Finset.univ.filter fun s : S => τ ≤ score s s) = ∅ := by
      exact Finset.filter_eq_empty_iff.mpr (by intro s _; exact hdiag s)
    have hoff_filter :
        ((offDiagonalPairs S).filter fun pair : S × S => score pair.1 pair.2 < τ) =
          offDiagonalPairs S := by
      exact Finset.filter_eq_self.mpr (by intro pair hp; exact hoff pair hp)
    simp [equalityBalancedAccuracy, equalityTruePositiveRate, equalityTrueNegativeRate,
      hdiag_filter, hoff_filter, hoff_ne]

/-- Dataset-level balanced-accuracy version of the abstract strict-convexity
Theorem 2. -/
theorem strictConvex_exactly_chance_under_symmetry_equalityBalancedAccuracy
    {S : Type*} [Fintype S] [DecidableEq S] [Nontrivial S]
    (risk : Params S → ℝ) (p : Params S)
    (hstrict : StrictConvexOn ℝ Set.univ risk)
    (hmin : IsMinOn risk Set.univ p)
    (hinv : ∀ (σ : Equiv.Perm S) q, risk (relabel σ q) = risk q)
    (τ : ℝ) :
    (∀ q k q' k', score p q k = score p q' k') ∧
      equalityBalancedAccuracy (score p) τ = (1 : ℝ) / 2 := by
  have hconst :=
    strictConvex_invariant_minimizer_constant
      (risk := risk) (p := p) hstrict hmin hinv
  exact ⟨hconst.2.2, equalityBalancedAccuracy_of_constant_score (score p) τ hconst.2.2⟩

end

end SamenessTheorem2
