import Sameness.BalancedAccuracy
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Concrete logistic risk for additive sameness

This module instantiates the abstract Theorem 2 risk with concrete logistic
losses, plus optional coordinatewise `ℓ²` regularization.  It includes both an
unweighted all-pairs empirical risk and the class-balanced diagonal/off-diagonal
risk used in the paper statement.  It proves the two structural facts that the
abstract theorem needs:

* the logistic risks are invariant under simultaneous relabeling;
* the scalar `softplus x = log (1 + exp x)` is convex, and therefore each
  logistic pair loss and the finite logistic risks are convex.

The final strict-convexity-to-chance theorem is stated for a positive
regularization coefficient.  The scalar logistic convexity, invariance, and
finite-dimensional minimizer existence parts are proved here from definitions.
-/

open scoped BigOperators

namespace SamenessTheorem2

noncomputable section

/-- The scalar logistic/softplus loss `log (1 + exp x)`. -/
def softplus (x : ℝ) : ℝ :=
  Real.log (1 + Real.exp x)

theorem softplus_deriv (x : ℝ) :
    deriv softplus x = Real.exp x / (1 + Real.exp x) := by
  unfold softplus
  rw [deriv.log]
  · simp [Real.deriv_exp]
  · fun_prop
  · positivity

theorem softplus_deriv_eq :
    deriv softplus = fun x : ℝ => Real.exp x / (1 + Real.exp x) := by
  funext x
  exact softplus_deriv x

theorem softplus_deriv2 (x : ℝ) :
    (deriv^[2]) softplus x = Real.exp x / (1 + Real.exp x) ^ 2 := by
  change deriv (deriv softplus) x = Real.exp x / (1 + Real.exp x) ^ 2
  rw [softplus_deriv_eq]
  have hden : 1 + Real.exp x ≠ 0 := by positivity
  rw [deriv_fun_div]
  · rw [Real.deriv_exp]
    simp [Real.deriv_exp]
    field_simp [hden]
    ring
  · fun_prop
  · fun_prop
  · exact hden

theorem differentiable_softplus : Differentiable ℝ softplus := by
  intro x
  unfold softplus
  apply DifferentiableAt.log
  · fun_prop
  · positivity

theorem differentiable_softplus_deriv : Differentiable ℝ (deriv softplus) := by
  rw [softplus_deriv_eq]
  apply Differentiable.fun_div
  · fun_prop
  · fun_prop
  · intro x
    positivity

/-- Convexity of the scalar logistic loss, proved by checking the sign of the
second derivative. -/
theorem convexOn_softplus : ConvexOn ℝ Set.univ softplus := by
  refine convexOn_univ_of_deriv2_nonneg differentiable_softplus differentiable_softplus_deriv ?_
  intro x
  rw [softplus_deriv2]
  positivity

/-- The linear functional extracting the additive score for one pair. -/
def scoreLinear {S : Type*} (q k : S) : Params S →ₗ[ℝ] ℝ where
  toFun p := score p q k
  map_add' p r := by
    simp [score, a, b, c, add_assoc, add_left_comm, add_comm]
  map_smul' t p := by
    simp [score, a, b, c, mul_add, add_assoc]

/-- Positive examples use `softplus (-score)` and negative examples use
`softplus score`. -/
def signedScoreLinear {S : Type*} [DecidableEq S] (q k : S) : Params S →ₗ[ℝ] ℝ where
  toFun p := (if q = k then (-1 : ℝ) else 1) * score p q k
  map_add' p r := by
    by_cases h : q = k <;>
      simp [h, score, a, b, c, add_assoc, add_left_comm, add_comm, mul_add]
  map_smul' t p := by
    by_cases h : q = k <;>
      simp [h, score, a, b, c, mul_add, add_assoc, mul_left_comm]

/-- Logistic loss for a single query-key pair. -/
def pairLogisticLoss {S : Type*} [DecidableEq S] (q k : S) (p : Params S) : ℝ :=
  softplus (signedScoreLinear q k p)

/-- The empirical logistic risk over all query-key pairs. -/
def empiricalLogisticRisk (S : Type*) [Fintype S] [DecidableEq S] (p : Params S) : ℝ :=
  ∑ pair : S × S, pairLogisticLoss pair.1 pair.2 p

/-- Coordinatewise squared `ℓ²` regularizer. -/
def l2Regularizer (S : Type*) [Fintype S] (p : Params S) : ℝ :=
  ∑ coord : Coord S, p coord ^ 2

/-- The induced permutation of query/key/bias coordinates. -/
def coordPerm {S : Type*} (σ : Equiv.Perm S) : Equiv.Perm (Coord S) where
  toFun
    | Coord.query s => Coord.query (σ s)
    | Coord.key s => Coord.key (σ s)
    | Coord.bias => Coord.bias
  invFun
    | Coord.query s => Coord.query (σ.symm s)
    | Coord.key s => Coord.key (σ.symm s)
    | Coord.bias => Coord.bias
  left_inv coord := by
    cases coord <;> simp
  right_inv coord := by
    cases coord <;> simp

/-- Relabeling is an `ℓ²`-coordinate permutation, hence it preserves the
coordinatewise squared regularizer. -/
theorem l2Regularizer_relabel (S : Type*) [Fintype S] (σ : Equiv.Perm S)
    (p : Params S) :
    l2Regularizer S (relabel σ p) = l2Regularizer S p := by
  classical
  unfold l2Regularizer
  let e : Coord S ≃ Coord S := coordPerm σ.symm
  exact
    Fintype.sum_equiv e
      (fun coord : Coord S => relabel σ p coord ^ 2)
      (fun coord : Coord S => p coord ^ 2)
      (by
        intro coord
        cases coord <;> simp [e, coordPerm, relabel])

/-- Concrete regularized logistic risk. -/
def regularizedLogisticRisk (S : Type*) [Fintype S] [DecidableEq S] (lam : ℝ)
    (p : Params S) : ℝ :=
  empiricalLogisticRisk S p + lam * l2Regularizer S p

/-- Class-balanced weight for diagonal equality positives. -/
def diagonalClassBalancedWeight (S : Type*) [Fintype S] : ℝ :=
  (2 * (Fintype.card S : ℝ))⁻¹

/-- Class-balanced weight for off-diagonal equality negatives. -/
def offDiagonalClassBalancedWeight (S : Type*) [Fintype S] [DecidableEq S] : ℝ :=
  (2 * ((offDiagonalPairs S).card : ℝ))⁻¹

/-- Positive diagonal logistic loss contribution. -/
def diagonalLogisticRisk (S : Type*) [Fintype S] (p : Params S) : ℝ :=
  ∑ q : S, softplus (-(score p q q))

/-- Negative off-diagonal logistic loss contribution. -/
def offDiagonalLogisticRisk (S : Type*) [Fintype S] [DecidableEq S]
    (p : Params S) : ℝ :=
  (offDiagonalPairs S).sum fun pair => softplus (score p pair.1 pair.2)

/-- Class-balanced regularized logistic risk:
`1/(2|S|)` times the diagonal loss, plus `1/(2|offdiag|)` times the
off-diagonal loss, plus coordinatewise `ℓ²` regularization. -/
def classBalancedRegularizedLogisticRisk
    (S : Type*) [Fintype S] [DecidableEq S] (lam : ℝ) (p : Params S) : ℝ :=
  diagonalClassBalancedWeight S * diagonalLogisticRisk S p +
    (offDiagonalClassBalancedWeight S * offDiagonalLogisticRisk S p +
      lam * l2Regularizer S p)

/-- Coordinate evaluation as a linear functional. -/
def coordEvalLinear {S : Type*} (coord : Coord S) : Params S →ₗ[ℝ] ℝ where
  toFun p := p coord
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem convexOn_square : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) := by
  simpa using (Even.convexOn_pow (show Even 2 by norm_num) :
    ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2))

theorem strictConvexOn_square : StrictConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) := by
  simpa using (Even.strictConvexOn_pow (show Even 2 by norm_num) (by norm_num) :
    StrictConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2))

theorem coord_square_convex {S : Type*} (coord : Coord S) :
    ConvexOn ℝ Set.univ (fun p : Params S => p coord ^ 2) := by
  simpa using convexOn_square.comp_linearMap (coordEvalLinear coord)

theorem pairLogisticLoss_convex {S : Type*} [DecidableEq S] (q k : S) :
    ConvexOn ℝ Set.univ (pairLogisticLoss q k : Params S → ℝ) := by
  simpa [pairLogisticLoss] using
    (convexOn_softplus.comp_linearMap (signedScoreLinear q k))

theorem convexOn_finset_sum
    {E ι : Type*} [AddCommMonoid E] [SMul ℝ E]
    (t : Finset ι) (f : ι → E → ℝ) :
    (∀ i ∈ t, ConvexOn ℝ Set.univ (f i)) →
      ConvexOn ℝ Set.univ (fun x => t.sum fun i => f i x) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      intro _
      simpa using convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set E))
  | insert i t hit ih =>
      intro h
      have hi : ConvexOn ℝ Set.univ (f i) := h i (by simp)
      have ht : ConvexOn ℝ Set.univ (fun x => t.sum fun j => f j x) := by
        apply ih
        intro j hj
        exact h j (by simp [hj])
      simpa [Finset.sum_insert, hit, Pi.add_apply] using hi.add ht

theorem empiricalLogisticRisk_convex (S : Type*) [Fintype S] [DecidableEq S] :
    ConvexOn ℝ Set.univ (empiricalLogisticRisk S : Params S → ℝ) := by
  classical
  unfold empiricalLogisticRisk
  apply convexOn_finset_sum Finset.univ
  intro pair _
  exact pairLogisticLoss_convex pair.1 pair.2

theorem l2Regularizer_convex (S : Type*) [Fintype S] :
    ConvexOn ℝ Set.univ (l2Regularizer S : Params S → ℝ) := by
  classical
  unfold l2Regularizer
  apply convexOn_finset_sum Finset.univ
  intro coord _
  exact coord_square_convex coord

theorem l2Regularizer_strictConvex (S : Type*) [Fintype S] :
    StrictConvexOn ℝ Set.univ (l2Regularizer S : Params S → ℝ) := by
  classical
  refine ⟨(l2Regularizer_convex S).1, ?_⟩
  intro p _ q _ hpq α β hα hβ hab
  have hcoord : ∃ coord : Coord S, p coord ≠ q coord := by
    by_contra h
    apply hpq
    funext coord
    by_contra hneq
    exact h ⟨coord, hneq⟩
  obtain ⟨coord₀, hcoord₀⟩ := hcoord
  simp only [l2Regularizer, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_lt_sum
  · intro coord _
    have h := convexOn_square.2
      (Set.mem_univ (p coord)) (Set.mem_univ (q coord)) hα.le hβ.le hab
    simpa [smul_eq_mul] using h
  · refine ⟨coord₀, by simp, ?_⟩
    have h := strictConvexOn_square.2
      (Set.mem_univ (p coord₀)) (Set.mem_univ (q coord₀)) hcoord₀ hα hβ hab
    simpa [smul_eq_mul] using h

theorem StrictConvexOn.pos_mul
    {E : Type*} [AddCommMonoid E] [SMul ℝ E] {s : Set E} {f : E → ℝ}
    {c : ℝ} (hf : StrictConvexOn ℝ s f) (hc : 0 < c) :
    StrictConvexOn ℝ s (fun x => c * f x) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy hxy α β hα hβ hab
  have h := hf.2 hx hy hxy hα hβ hab
  calc
    c * f (α • x + β • y) < c * (α • f x + β • f y) :=
      mul_lt_mul_of_pos_left h hc
    _ = α • (c * f x) + β • (c * f y) := by
      simp [smul_eq_mul]
      ring

theorem regularizedLogisticRisk_convex (S : Type*) [Fintype S] [DecidableEq S]
    {lam : ℝ} (hlam : 0 ≤ lam) :
    ConvexOn ℝ Set.univ (regularizedLogisticRisk S lam : Params S → ℝ) := by
  simpa [regularizedLogisticRisk, Pi.add_apply, smul_eq_mul] using
    (empiricalLogisticRisk_convex S).add ((l2Regularizer_convex S).smul hlam)

theorem regularizedLogisticRisk_strictConvex (S : Type*) [Fintype S] [DecidableEq S]
    {lam : ℝ} (hlam : 0 < lam) :
    StrictConvexOn ℝ Set.univ (regularizedLogisticRisk S lam : Params S → ℝ) := by
  simpa [regularizedLogisticRisk, Pi.add_apply, smul_eq_mul] using
    (empiricalLogisticRisk_convex S).add_strictConvexOn
      (StrictConvexOn.pos_mul (l2Regularizer_strictConvex S) hlam)

theorem diagonalClassBalancedWeight_nonneg (S : Type*) [Fintype S] :
    0 ≤ diagonalClassBalancedWeight S := by
  unfold diagonalClassBalancedWeight
  positivity

theorem offDiagonalClassBalancedWeight_nonneg (S : Type*) [Fintype S] [DecidableEq S] :
    0 ≤ offDiagonalClassBalancedWeight S := by
  unfold offDiagonalClassBalancedWeight
  positivity

theorem diagonalLogisticRisk_convex (S : Type*) [Fintype S] :
    ConvexOn ℝ Set.univ (diagonalLogisticRisk S : Params S → ℝ) := by
  classical
  unfold diagonalLogisticRisk
  apply convexOn_finset_sum Finset.univ
  intro q _
  simpa [scoreLinear] using
    (convexOn_softplus.comp_linearMap (-(scoreLinear q q)))

theorem offDiagonalLogisticRisk_convex (S : Type*) [Fintype S] [DecidableEq S] :
    ConvexOn ℝ Set.univ (offDiagonalLogisticRisk S : Params S → ℝ) := by
  classical
  unfold offDiagonalLogisticRisk
  apply convexOn_finset_sum (offDiagonalPairs S)
  intro pair _
  simpa [scoreLinear] using
    (convexOn_softplus.comp_linearMap (scoreLinear pair.1 pair.2))

theorem classBalancedRegularizedLogisticRisk_convex
    (S : Type*) [Fintype S] [DecidableEq S] {lam : ℝ} (hlam : 0 ≤ lam) :
    ConvexOn ℝ Set.univ (classBalancedRegularizedLogisticRisk S lam : Params S → ℝ) := by
  have hdiag := (diagonalLogisticRisk_convex S).smul
    (diagonalClassBalancedWeight_nonneg S)
  have hoff := (offDiagonalLogisticRisk_convex S).smul
    (offDiagonalClassBalancedWeight_nonneg S)
  simpa [classBalancedRegularizedLogisticRisk, Pi.add_apply, smul_eq_mul] using
    hdiag.add (hoff.add ((l2Regularizer_convex S).smul hlam))

theorem classBalancedRegularizedLogisticRisk_strictConvex
    (S : Type*) [Fintype S] [DecidableEq S] {lam : ℝ} (hlam : 0 < lam) :
    StrictConvexOn ℝ Set.univ
      (classBalancedRegularizedLogisticRisk S lam : Params S → ℝ) := by
  have hdiag := (diagonalLogisticRisk_convex S).smul
    (diagonalClassBalancedWeight_nonneg S)
  have hoff := (offDiagonalLogisticRisk_convex S).smul
    (offDiagonalClassBalancedWeight_nonneg S)
  simpa [classBalancedRegularizedLogisticRisk, Pi.add_apply, smul_eq_mul] using
    hdiag.add_strictConvexOn (hoff.add_strictConvexOn
      (StrictConvexOn.pos_mul (l2Regularizer_strictConvex S) hlam))

theorem softplus_continuous : Continuous softplus := by
  unfold softplus
  exact (continuous_const.add Real.continuous_exp).log (by
    intro x
    change 1 + Real.exp x ≠ 0
    have hx : 0 < Real.exp x := Real.exp_pos x
    have hpos : 0 < 1 + Real.exp x := by linarith
    exact ne_of_gt hpos)

theorem signedScoreLinear_continuous {S : Type*} [Finite S] [DecidableEq S] (q k : S) :
    Continuous fun p : Params S => signedScoreLinear q k p := by
  letI := Fintype.ofFinite S
  exact (signedScoreLinear q k).continuous_of_finiteDimensional

theorem pairLogisticLoss_continuous {S : Type*} [Finite S] [DecidableEq S] (q k : S) :
    Continuous (pairLogisticLoss q k : Params S → ℝ) := by
  letI := Fintype.ofFinite S
  simpa [pairLogisticLoss] using
    softplus_continuous.comp (signedScoreLinear_continuous q k)

theorem empiricalLogisticRisk_continuous (S : Type*) [Fintype S] [DecidableEq S] :
    Continuous (empiricalLogisticRisk S : Params S → ℝ) := by
  classical
  unfold empiricalLogisticRisk
  exact continuous_finsetSum Finset.univ fun pair _ =>
    pairLogisticLoss_continuous pair.1 pair.2

theorem l2Regularizer_continuous (S : Type*) [Fintype S] :
    Continuous (l2Regularizer S : Params S → ℝ) := by
  classical
  unfold l2Regularizer
  exact continuous_finsetSum Finset.univ fun coord _ =>
    (continuous_apply coord).pow 2

theorem regularizedLogisticRisk_continuous (S : Type*) [Fintype S] [DecidableEq S]
    (lam : ℝ) :
    Continuous (regularizedLogisticRisk S lam : Params S → ℝ) := by
  simpa [regularizedLogisticRisk] using
    (empiricalLogisticRisk_continuous S).add
      (continuous_const.mul (l2Regularizer_continuous S))

theorem diagonalLogisticRisk_continuous (S : Type*) [Fintype S] :
    Continuous (diagonalLogisticRisk S : Params S → ℝ) := by
  classical
  unfold diagonalLogisticRisk
  exact continuous_finsetSum Finset.univ fun q _ => by
    simpa [scoreLinear] using
      softplus_continuous.comp ((scoreLinear q q).continuous_of_finiteDimensional.neg)

theorem offDiagonalLogisticRisk_continuous (S : Type*) [Fintype S] [DecidableEq S] :
    Continuous (offDiagonalLogisticRisk S : Params S → ℝ) := by
  classical
  unfold offDiagonalLogisticRisk
  exact continuous_finsetSum (offDiagonalPairs S) fun pair _ => by
    simpa [scoreLinear] using
      softplus_continuous.comp ((scoreLinear pair.1 pair.2).continuous_of_finiteDimensional)

theorem classBalancedRegularizedLogisticRisk_continuous
    (S : Type*) [Fintype S] [DecidableEq S] (lam : ℝ) :
    Continuous (classBalancedRegularizedLogisticRisk S lam : Params S → ℝ) := by
  simpa [classBalancedRegularizedLogisticRisk] using
    ((continuous_const.mul (diagonalLogisticRisk_continuous S)).add
      ((continuous_const.mul (offDiagonalLogisticRisk_continuous S)).add
        (continuous_const.mul (l2Regularizer_continuous S))))

theorem softplus_nonneg (x : ℝ) : 0 ≤ softplus x := by
  unfold softplus
  apply Real.log_nonneg
  have hx : 0 < Real.exp x := Real.exp_pos x
  linarith

theorem pairLogisticLoss_nonneg {S : Type*} [DecidableEq S] (q k : S) (p : Params S) :
    0 ≤ pairLogisticLoss q k p :=
  softplus_nonneg _

theorem empiricalLogisticRisk_nonneg (S : Type*) [Fintype S] [DecidableEq S]
    (p : Params S) :
    0 ≤ empiricalLogisticRisk S p := by
  classical
  unfold empiricalLogisticRisk
  exact Finset.sum_nonneg fun pair _ => pairLogisticLoss_nonneg pair.1 pair.2 p

theorem diagonalLogisticRisk_nonneg (S : Type*) [Fintype S] (p : Params S) :
    0 ≤ diagonalLogisticRisk S p := by
  classical
  unfold diagonalLogisticRisk
  exact Finset.sum_nonneg fun q _ => softplus_nonneg _

theorem offDiagonalLogisticRisk_nonneg (S : Type*) [Fintype S] [DecidableEq S]
    (p : Params S) :
    0 ≤ offDiagonalLogisticRisk S p := by
  classical
  unfold offDiagonalLogisticRisk
  exact Finset.sum_nonneg fun pair _ => softplus_nonneg _

theorem l2Regularizer_nonneg (S : Type*) [Fintype S] (p : Params S) :
    0 ≤ l2Regularizer S p := by
  classical
  unfold l2Regularizer
  exact Finset.sum_nonneg fun coord _ => sq_nonneg (p coord)

theorem l2Regularizer_coord_le (S : Type*) [Fintype S] (p : Params S)
    (coord : Coord S) :
    p coord ^ 2 ≤ l2Regularizer S p := by
  classical
  unfold l2Regularizer
  exact Finset.single_le_sum (fun c _ => sq_nonneg (p c)) (Finset.mem_univ coord)

theorem regularizedLogisticRisk_sublevel_isBounded
    (S : Type*) [Fintype S] [DecidableEq S] {lam : ℝ} (hlam : 0 < lam) :
    Bornology.IsBounded
      {p : Params S | regularizedLogisticRisk S lam p ≤
        regularizedLogisticRisk S lam (0 : Params S)} := by
  classical
  let risk0 : ℝ := regularizedLogisticRisk S lam (0 : Params S)
  let R : ℝ := Real.sqrt (risk0 / lam)
  refine (Metric.isBounded_iff_subset_closedBall (0 : Params S)).2 ⟨R, ?_⟩
  intro p hp
  have hnorm : ‖p‖ ≤ R := by
    rw [pi_norm_le_iff_of_nonneg]
    · intro coord
      have hemp_nonneg : 0 ≤ empiricalLogisticRisk S p := empiricalLogisticRisk_nonneg S p
      have hcoord_l2 : p coord ^ 2 ≤ l2Regularizer S p :=
        l2Regularizer_coord_le S p coord
      have hlam_coord_le_l2 : lam * p coord ^ 2 ≤ lam * l2Regularizer S p :=
        mul_le_mul_of_nonneg_left hcoord_l2 hlam.le
      have hlam_l2_le_risk : lam * l2Regularizer S p ≤ regularizedLogisticRisk S lam p := by
        unfold regularizedLogisticRisk
        linarith
      have hcoord_le_risk0 : lam * p coord ^ 2 ≤ risk0 := by
        exact hlam_coord_le_l2.trans (hlam_l2_le_risk.trans hp)
      have hsq_le : p coord ^ 2 ≤ risk0 / lam := by
        rw [le_div_iff₀ hlam]
        simpa [mul_comm] using hcoord_le_risk0
      have habs : |p coord| ≤ Real.sqrt (risk0 / lam) := Real.abs_le_sqrt hsq_le
      simpa [R, Real.norm_eq_abs] using habs
    · exact Real.sqrt_nonneg _
  simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hnorm

theorem regularizedLogisticRisk_exists_isMinOn
    (S : Type*) [Fintype S] [DecidableEq S] {lam : ℝ} (hlam : 0 < lam) :
    ∃ p : Params S, IsMinOn (regularizedLogisticRisk S lam) Set.univ p := by
  classical
  obtain ⟨p, hp⟩ :=
    (regularizedLogisticRisk_continuous S lam).exists_forall_le_of_isBounded
      (0 : Params S) (regularizedLogisticRisk_sublevel_isBounded S hlam)
  exact ⟨p, by simpa [isMinOn_univ_iff] using hp⟩

theorem classBalancedLogisticPart_nonneg
    (S : Type*) [Fintype S] [DecidableEq S] (p : Params S) :
    0 ≤ diagonalClassBalancedWeight S * diagonalLogisticRisk S p +
      offDiagonalClassBalancedWeight S * offDiagonalLogisticRisk S p := by
  have hdiag : 0 ≤ diagonalClassBalancedWeight S * diagonalLogisticRisk S p := by
    exact mul_nonneg (diagonalClassBalancedWeight_nonneg S) (diagonalLogisticRisk_nonneg S p)
  have hoff : 0 ≤ offDiagonalClassBalancedWeight S * offDiagonalLogisticRisk S p := by
    exact mul_nonneg (offDiagonalClassBalancedWeight_nonneg S)
      (offDiagonalLogisticRisk_nonneg S p)
  exact add_nonneg hdiag hoff

theorem classBalancedRegularizedLogisticRisk_sublevel_isBounded
    (S : Type*) [Fintype S] [DecidableEq S] {lam : ℝ} (hlam : 0 < lam) :
    Bornology.IsBounded
      {p : Params S | classBalancedRegularizedLogisticRisk S lam p ≤
        classBalancedRegularizedLogisticRisk S lam (0 : Params S)} := by
  classical
  let risk0 : ℝ := classBalancedRegularizedLogisticRisk S lam (0 : Params S)
  let R : ℝ := Real.sqrt (risk0 / lam)
  refine (Metric.isBounded_iff_subset_closedBall (0 : Params S)).2 ⟨R, ?_⟩
  intro p hp
  have hnorm : ‖p‖ ≤ R := by
    rw [pi_norm_le_iff_of_nonneg]
    · intro coord
      have hbase_nonneg :
          0 ≤ diagonalClassBalancedWeight S * diagonalLogisticRisk S p +
            offDiagonalClassBalancedWeight S * offDiagonalLogisticRisk S p :=
        classBalancedLogisticPart_nonneg S p
      have hcoord_l2 : p coord ^ 2 ≤ l2Regularizer S p :=
        l2Regularizer_coord_le S p coord
      have hlam_coord_le_l2 : lam * p coord ^ 2 ≤ lam * l2Regularizer S p :=
        mul_le_mul_of_nonneg_left hcoord_l2 hlam.le
      have hlam_l2_le_risk : lam * l2Regularizer S p ≤
          classBalancedRegularizedLogisticRisk S lam p := by
        unfold classBalancedRegularizedLogisticRisk
        linarith
      have hcoord_le_risk0 : lam * p coord ^ 2 ≤ risk0 := by
        exact hlam_coord_le_l2.trans (hlam_l2_le_risk.trans hp)
      have hsq_le : p coord ^ 2 ≤ risk0 / lam := by
        rw [le_div_iff₀ hlam]
        simpa [mul_comm] using hcoord_le_risk0
      have habs : |p coord| ≤ Real.sqrt (risk0 / lam) := Real.abs_le_sqrt hsq_le
      simpa [R, Real.norm_eq_abs] using habs
    · exact Real.sqrt_nonneg _
  simpa [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hnorm

theorem classBalancedRegularizedLogisticRisk_exists_isMinOn
    (S : Type*) [Fintype S] [DecidableEq S] {lam : ℝ} (hlam : 0 < lam) :
    ∃ p : Params S, IsMinOn (classBalancedRegularizedLogisticRisk S lam) Set.univ p := by
  classical
  obtain ⟨p, hp⟩ :=
    (classBalancedRegularizedLogisticRisk_continuous S lam).exists_forall_le_of_isBounded
      (0 : Params S) (classBalancedRegularizedLogisticRisk_sublevel_isBounded S hlam)
  exact ⟨p, by simpa [isMinOn_univ_iff] using hp⟩

/-- Positive regularization gives a unique global minimizer for the
class-balanced risk. -/
theorem classBalancedRegularizedLogisticRisk_exists_unique_isMinOn
    (S : Type*) [Fintype S] [DecidableEq S]
    {lam : ℝ} (hlam : 0 < lam) :
    ∃! p : Params S,
      IsMinOn (classBalancedRegularizedLogisticRisk S lam) Set.univ p := by
  obtain ⟨p, hp⟩ := classBalancedRegularizedLogisticRisk_exists_isMinOn S hlam
  refine ⟨p, hp, ?_⟩
  intro q hq
  exact strictConvex_minimizer_unique
    (classBalancedRegularizedLogisticRisk S lam) (p := q) (q := p)
    (classBalancedRegularizedLogisticRisk_strictConvex S hlam)
    hq hp

theorem score_relabel_symm {S : Type*} (σ : Equiv.Perm S) (p : Params S)
    (q k : S) :
    score (relabel σ p) q k = score p (σ.symm q) (σ.symm k) := by
  simp [score, a, b, c, relabel]

theorem pairLogisticLoss_relabel {S : Type*} [DecidableEq S]
    (σ : Equiv.Perm S) (p : Params S) (q k : S) :
    pairLogisticLoss q k (relabel σ p) =
      pairLogisticLoss (σ.symm q) (σ.symm k) p := by
  unfold pairLogisticLoss
  have hscore := score_relabel_symm σ p q k
  have heq : (q = k) ↔ (σ.symm q = σ.symm k) := by
    constructor
    · intro h
      simp [h]
    · intro h
      exact σ.symm.injective h
  by_cases hqk : q = k
  · subst q
    simp [signedScoreLinear, score_relabel_symm]
  · have hsymm : σ.symm q ≠ σ.symm k := fun h => hqk (heq.mpr h)
    simp [signedScoreLinear, hqk, hsymm, hscore]

theorem empiricalLogisticRisk_invariant (S : Type*) [Fintype S] [DecidableEq S]
    (σ : Equiv.Perm S) (p : Params S) :
    empiricalLogisticRisk S (relabel σ p) = empiricalLogisticRisk S p := by
  classical
  unfold empiricalLogisticRisk
  calc
    (∑ pair : S × S, pairLogisticLoss pair.1 pair.2 (relabel σ p))
        = ∑ pair : S × S, pairLogisticLoss (σ.symm pair.1) (σ.symm pair.2) p := by
          apply Finset.sum_congr rfl
          intro pair _
          exact pairLogisticLoss_relabel σ p pair.1 pair.2
    _ = ∑ pair : S × S, pairLogisticLoss pair.1 pair.2 p := by
          let e : (S × S) ≃ (S × S) :=
            (Equiv.prodCongr σ.symm σ.symm)
          exact
            Fintype.sum_equiv e
              (fun pair : S × S => pairLogisticLoss (σ.symm pair.1) (σ.symm pair.2) p)
              (fun pair : S × S => pairLogisticLoss pair.1 pair.2 p)
              (by intro pair; rfl)

/-- Concrete logistic risk supplies the permutation-invariance hypothesis used
by the abstract strict-convexity theorem. -/
theorem regularizedLogisticRisk_invariant
    (S : Type*) [Fintype S] [DecidableEq S] (lam : ℝ) :
    ∀ (σ : Equiv.Perm S) p,
      regularizedLogisticRisk S lam (relabel σ p) = regularizedLogisticRisk S lam p := by
  intro σ p
  simp [regularizedLogisticRisk, empiricalLogisticRisk_invariant S σ p,
    l2Regularizer_relabel S σ p]

theorem diagonalLogisticRisk_relabel (S : Type*) [Fintype S]
    (σ : Equiv.Perm S) (p : Params S) :
    diagonalLogisticRisk S (relabel σ p) = diagonalLogisticRisk S p := by
  classical
  unfold diagonalLogisticRisk
  calc
    (∑ q : S, softplus (-(score (relabel σ p) q q)))
        = ∑ q : S, softplus (-(score p (σ.symm q) (σ.symm q))) := by
          apply Finset.sum_congr rfl
          intro q _
          simp [score_relabel_symm]
    _ = ∑ q : S, softplus (-(score p q q)) := by
          let e : S ≃ S := σ.symm
          exact
            Fintype.sum_equiv e
              (fun q : S => softplus (-(score p (σ.symm q) (σ.symm q))))
              (fun q : S => softplus (-(score p q q)))
              (by intro q; rfl)

theorem offDiagonalLogisticRisk_relabel (S : Type*) [Fintype S] [DecidableEq S]
    (σ : Equiv.Perm S) (p : Params S) :
    offDiagonalLogisticRisk S (relabel σ p) = offDiagonalLogisticRisk S p := by
  classical
  unfold offDiagonalLogisticRisk
  calc
    (offDiagonalPairs S).sum (fun pair => softplus (score (relabel σ p) pair.1 pair.2))
        = (offDiagonalPairs S).sum
            (fun pair => softplus (score p (σ.symm pair.1) (σ.symm pair.2))) := by
          apply Finset.sum_congr rfl
          intro pair _
          simp [score_relabel_symm]
    _ = (offDiagonalPairs S).sum (fun pair => softplus (score p pair.1 pair.2)) := by
          let e : (S × S) ≃ (S × S) := Equiv.prodCongr σ.symm σ.symm
          exact
            Finset.sum_equiv e
              (by intro pair; simp [offDiagonalPairs, e])
              (by intro pair _; rfl)

/-- The class-balanced regularized logistic risk supplies the
permutation-invariance hypothesis used by the abstract strict-convexity theorem. -/
theorem classBalancedRegularizedLogisticRisk_invariant
    (S : Type*) [Fintype S] [DecidableEq S] (lam : ℝ) :
    ∀ (σ : Equiv.Perm S) p,
      classBalancedRegularizedLogisticRisk S lam (relabel σ p) =
        classBalancedRegularizedLogisticRisk S lam p := by
  intro σ p
  simp [classBalancedRegularizedLogisticRisk, diagonalLogisticRisk_relabel S σ p,
    offDiagonalLogisticRisk_relabel S σ p, l2Regularizer_relabel S σ p]

/-- If a concrete regularized logistic risk is strictly convex and has a global
minimizer, the scalar constant-score chance conclusion follows with no separate
symmetry assumption: permutation invariance is proved above from the concrete
formula.  The finite equality-task metric version is proved below. -/
theorem concrete_regularized_logistic_exactly_chance
    (S : Type*) [Fintype S] [DecidableEq S]
    (lam τ : ℝ) (p : Params S)
    (hstrict : StrictConvexOn ℝ Set.univ (regularizedLogisticRisk S lam))
    (hmin : IsMinOn (regularizedLogisticRisk S lam) Set.univ p) :
    (∀ q k q' k', score p q k = score p q' k') ∧
      (∀ q k, constantScoreBalancedAccuracy (score p q k) τ = (1 : ℝ) / 2) := by
  exact strictConvex_exactly_chance_under_symmetry
    (risk := regularizedLogisticRisk S lam) (p := p) hstrict hmin
    (regularizedLogisticRisk_invariant S lam) τ

/-- Fully concrete scalar-compatibility theorem: for positive `ℓ²`
regularization, strict convexity and permutation invariance are both supplied by
the concrete risk formula.  This fixed-minimizer version is used by the
existential corollary below, which discharges minimizer existence. -/
theorem concrete_regularized_logistic_exactly_chance_of_pos_reg
    (S : Type*) [Fintype S] [DecidableEq S]
    {lam : ℝ} (hlam : 0 < lam) (τ : ℝ) (p : Params S)
    (hmin : IsMinOn (regularizedLogisticRisk S lam) Set.univ p) :
    (∀ q k q' k', score p q k = score p q' k') ∧
      (∀ q k, constantScoreBalancedAccuracy (score p q k) τ = (1 : ℝ) / 2) := by
  exact concrete_regularized_logistic_exactly_chance
    S lam τ p (regularizedLogisticRisk_strictConvex S hlam) hmin

/-- Existence version of the fully concrete scalar-compatibility theorem:
positive `ℓ²` regularization makes the finite-dimensional regularized logistic
risk attain a global minimum, and every such minimizer is a constant-score
matcher with scalar chance balanced accuracy. -/
theorem concrete_regularized_logistic_exactly_chance_exists_of_pos_reg
    (S : Type*) [Fintype S] [DecidableEq S]
    {lam : ℝ} (hlam : 0 < lam) (τ : ℝ) :
    ∃ p : Params S,
      IsMinOn (regularizedLogisticRisk S lam) Set.univ p ∧
        (∀ q k q' k', score p q k = score p q' k') ∧
          (∀ q k, constantScoreBalancedAccuracy (score p q k) τ = (1 : ℝ) / 2) := by
  obtain ⟨p, hmin⟩ := regularizedLogisticRisk_exists_isMinOn S hlam
  exact ⟨p, hmin, concrete_regularized_logistic_exactly_chance_of_pos_reg S hlam τ p hmin⟩

/-- Dataset-level concrete Theorem 2 for the finite equality task: if the
regularized logistic risk is strictly convex and `p` is a global minimizer, then
the additive score is constant and every threshold has balanced accuracy
exactly chance on diagonal-vs-off-diagonal equality examples. -/
theorem concrete_regularized_logistic_equalityBalancedAccuracy
    (S : Type*) [Fintype S] [DecidableEq S] [Nontrivial S]
    (lam τ : ℝ) (p : Params S)
    (hstrict : StrictConvexOn ℝ Set.univ (regularizedLogisticRisk S lam))
    (hmin : IsMinOn (regularizedLogisticRisk S lam) Set.univ p) :
    (∀ q k q' k', score p q k = score p q' k') ∧
      equalityBalancedAccuracy (score p) τ = (1 : ℝ) / 2 := by
  exact strictConvex_exactly_chance_under_symmetry_equalityBalancedAccuracy
    (risk := regularizedLogisticRisk S lam) (p := p) hstrict hmin
    (regularizedLogisticRisk_invariant S lam) τ

/-- Fully concrete dataset-level Theorem 2: positive `ℓ²` regularization
supplies strict convexity, and the risk formula supplies permutation
invariance.  This fixed-minimizer version is used by the existential
finite-task theorem below, which discharges minimizer existence. -/
theorem concrete_regularized_logistic_equalityBalancedAccuracy_of_pos_reg
    (S : Type*) [Fintype S] [DecidableEq S] [Nontrivial S]
    {lam : ℝ} (hlam : 0 < lam) (τ : ℝ) (p : Params S)
    (hmin : IsMinOn (regularizedLogisticRisk S lam) Set.univ p) :
    (∀ q k q' k', score p q k = score p q' k') ∧
      equalityBalancedAccuracy (score p) τ = (1 : ℝ) / 2 := by
  exact concrete_regularized_logistic_equalityBalancedAccuracy
    S lam τ p (regularizedLogisticRisk_strictConvex S hlam) hmin

/-- Hypothesis-free finite equality-task Theorem 2, except for the mathematical
premises that the alphabet is finite/nontrivial and the regularization
coefficient is positive: the regularized logistic risk has a global minimizer,
and any such optimum is forced to chance balanced accuracy. -/
theorem concrete_regularized_logistic_equalityBalancedAccuracy_exists_of_pos_reg
    (S : Type*) [Fintype S] [DecidableEq S] [Nontrivial S]
    {lam : ℝ} (hlam : 0 < lam) (τ : ℝ) :
    ∃ p : Params S,
      IsMinOn (regularizedLogisticRisk S lam) Set.univ p ∧
        (∀ q k q' k', score p q k = score p q' k') ∧
          equalityBalancedAccuracy (score p) τ = (1 : ℝ) / 2 := by
  obtain ⟨p, hmin⟩ := regularizedLogisticRisk_exists_isMinOn S hlam
  exact
    ⟨p, hmin,
      concrete_regularized_logistic_equalityBalancedAccuracy_of_pos_reg S hlam τ p hmin⟩

/-- Paper-aligned class-balanced finite equality-task Theorem 2: positive `ℓ²`
regularization supplies strict convexity, the class-balanced diagonal/off-
diagonal risk formula supplies permutation invariance, and every global
minimizer is forced to chance balanced accuracy. -/
theorem classBalanced_regularized_logistic_equalityBalancedAccuracy_of_pos_reg
    (S : Type*) [Fintype S] [DecidableEq S] [Nontrivial S]
    {lam : ℝ} (hlam : 0 < lam) (τ : ℝ) (p : Params S)
    (hmin : IsMinOn (classBalancedRegularizedLogisticRisk S lam) Set.univ p) :
    (∀ q k q' k', score p q k = score p q' k') ∧
      equalityBalancedAccuracy (score p) τ = (1 : ℝ) / 2 := by
  exact strictConvex_exactly_chance_under_symmetry_equalityBalancedAccuracy
    (risk := classBalancedRegularizedLogisticRisk S lam) (p := p)
    (classBalancedRegularizedLogisticRisk_strictConvex S hlam) hmin
    (classBalancedRegularizedLogisticRisk_invariant S lam) τ

/-- Existence version of the paper-aligned class-balanced finite equality-task
Theorem 2.  The only remaining hypotheses are the mathematical ones: finite
nontrivial alphabet and positive regularization. -/
theorem classBalanced_regularized_logistic_equalityBalancedAccuracy_exists_of_pos_reg
    (S : Type*) [Fintype S] [DecidableEq S] [Nontrivial S]
    {lam : ℝ} (hlam : 0 < lam) (τ : ℝ) :
    ∃ p : Params S,
      IsMinOn (classBalancedRegularizedLogisticRisk S lam) Set.univ p ∧
        (∀ q k q' k', score p q k = score p q' k') ∧
          equalityBalancedAccuracy (score p) τ = (1 : ℝ) / 2 := by
  obtain ⟨p, hmin⟩ := classBalancedRegularizedLogisticRisk_exists_isMinOn S hlam
  exact ⟨p, hmin,
    classBalanced_regularized_logistic_equalityBalancedAccuracy_of_pos_reg S hlam τ p hmin⟩

/-- There is one class-balanced global minimizer whose finite equality-task
balanced accuracy is chance for every threshold. -/
theorem classBalanced_regularized_logistic_equalityBalancedAccuracy_exists_all_thresholds
    (S : Type*) [Fintype S] [DecidableEq S] [Nontrivial S]
    {lam : ℝ} (hlam : 0 < lam) :
    ∃ p : Params S,
      IsMinOn (classBalancedRegularizedLogisticRisk S lam) Set.univ p ∧
        (∀ q k q' k', score p q k = score p q' k') ∧
          ∀ τ : ℝ, equalityBalancedAccuracy (score p) τ = (1 : ℝ) / 2 := by
  obtain ⟨p, hmin⟩ := classBalancedRegularizedLogisticRisk_exists_isMinOn S hlam
  have hzero :=
    classBalanced_regularized_logistic_equalityBalancedAccuracy_of_pos_reg
      S hlam 0 p hmin
  refine ⟨p, hmin, hzero.1, ?_⟩
  intro τ
  exact
    (classBalanced_regularized_logistic_equalityBalancedAccuracy_of_pos_reg
      S hlam τ p hmin).2

/-- The unique class-balanced global minimizer has finite equality-task
balanced accuracy `1 / 2` for every threshold. -/
theorem classBalanced_regularized_logistic_unique_minimizer_chance_all_thresholds
    (S : Type*) [Fintype S] [DecidableEq S] [Nontrivial S]
    {lam : ℝ} (hlam : 0 < lam) :
    ∃! p : Params S,
      IsMinOn (classBalancedRegularizedLogisticRisk S lam) Set.univ p ∧
        (∀ q k q' k', score p q k = score p q' k') ∧
          ∀ τ : ℝ, equalityBalancedAccuracy (score p) τ = (1 : ℝ) / 2 := by
  obtain ⟨p, hmin, hconst, hba⟩ :=
    classBalanced_regularized_logistic_equalityBalancedAccuracy_exists_all_thresholds S hlam
  refine ⟨p, ⟨hmin, hconst, hba⟩, ?_⟩
  intro q hq
  exact strictConvex_minimizer_unique
    (classBalancedRegularizedLogisticRisk S lam) (p := q) (q := p)
    (classBalancedRegularizedLogisticRisk_strictConvex S hlam)
    hq.1 hmin

/-- The same class-balanced existence theorem with the common `λ / 2`
regularizer normalization. -/
theorem classBalanced_regularized_logistic_equalityBalancedAccuracy_exists_of_pos_reg_half
    (S : Type*) [Fintype S] [DecidableEq S] [Nontrivial S]
    {lam : ℝ} (hlam : 0 < lam) (τ : ℝ) :
    ∃ p : Params S,
      IsMinOn (classBalancedRegularizedLogisticRisk S (lam / 2)) Set.univ p ∧
        (∀ q k q' k', score p q k = score p q' k') ∧
          equalityBalancedAccuracy (score p) τ = (1 : ℝ) / 2 := by
  have hhalf : 0 < lam / 2 := by positivity
  exact classBalanced_regularized_logistic_equalityBalancedAccuracy_exists_of_pos_reg
    S hhalf τ

end

end SamenessTheorem2
