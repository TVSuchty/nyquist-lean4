import Nyquist.Criterion
import Nyquist.ArgumentPrinciple
import Nyquist.Indentation
import Nyquist.TimeDelay
import Nyquist.Margins

/-!
# Concrete Verified Examples and ZFC Axiom Audit

This file demonstrates two classical control-theory applications of the Nyquist Stability
Criterion and prints the exact Lean axioms used by the main theorems to verify that only
the ZFC-interpretable core axioms (`propext`, `Classical.choice`, `Quot.sound`) appear.
-/

namespace Nyquist.Examples

open Complex Polynomial

/-! ### Example 1: Open-Loop Stable First-Order Plant `L(s) = K / (s + 1)`, `K > -1` -/

lemma example1_proper (K : ℝ) :
    IsProperNonDegenerate (C (K : ℂ)) (X + C (1 : ℂ)) := by
  refine strictlyProper_implies_properNonDegenerate (Polynomial.X_add_C_ne_zero 1) ?_
  rw [Polynomial.natDegree_C, Polynomial.natDegree_X_add_C]
  exact zero_lt_one

lemma example1_openLoop_hurwitz : IsHurwitz (X + C (1 : ℂ)) := by
  refine ⟨Polynomial.X_add_C_ne_zero 1, fun z hz => ?_⟩
  have h0 : z + 1 = 0 := by simpa [Polynomial.IsRoot] using hz
  have hz1 : z = -1 := eq_neg_of_add_eq_zero_left h0
  simp [hz1]

lemma example1_closedLoop_noImag (K : ℝ) (hK : -1 < K) :
    NoImagAxisRoots (X + C (1 : ℂ) + C (K : ℂ)) := by
  intro ω h0
  have hre : ((I * (ω : ℂ) + 1) + (K : ℂ)).re = 0 := by
    have := congr_arg Complex.re h0
    simpa using this
  simp only [add_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero,
    sub_self, zero_add, one_re] at hre
  linarith

lemma example1_closedLoop_hurwitz (K : ℝ) (hK : -1 < K) :
    IsHurwitz (X + C (1 : ℂ) + C (K : ℂ)) := by
  have heq : X + C (1 : ℂ) + C (K : ℂ) = X + C ((1 + K : ℝ) : ℂ) := by
    rw [add_assoc, ← C_add]
    push_cast
    rfl
  rw [heq]
  refine ⟨Polynomial.X_add_C_ne_zero _, fun z hz => ?_⟩
  have h0 : z + ((1 + K : ℝ) : ℂ) = 0 := by simpa [Polynomial.IsRoot] using hz
  have hz1 : z = -((1 + K : ℝ) : ℂ) := eq_neg_of_add_eq_zero_left h0
  simp only [hz1, neg_re, ofReal_re]
  linarith

theorem example1_nyquist_encirclements (K : ℝ) (hK : -1 < K) :
    nyquistEncirclementsCW (C (K : ℂ)) (X + C (1 : ℂ)) = 0 :=
  (nyquist_stability_criterion_openLoopStable (C (K : ℂ)) (X + C (1 : ℂ))
    (example1_proper K) example1_openLoop_hurwitz (example1_closedLoop_noImag K hK)).mp
    (example1_closedLoop_hurwitz K hK)

/-! ### Example 2: Unstable Open-Loop Plant Stabilized by Feedback `L(s) = 2 / (s - 1)` -/

lemma example2_proper :
    IsProperNonDegenerate (C (2 : ℂ)) (X - C (1 : ℂ)) := by
  refine strictlyProper_implies_properNonDegenerate (Polynomial.X_sub_C_ne_zero 1) ?_
  rw [Polynomial.natDegree_C, Polynomial.natDegree_X_sub_C]
  exact zero_lt_one

lemma example2_openLoop_noImag : NoImagAxisRoots (X - C (1 : ℂ)) := by
  intro ω h0
  have hre : (I * (ω : ℂ) - 1).re = 0 := by
    have := congr_arg Complex.re h0
    simpa using this
  simp at hre

lemma example2_closedLoop_noImag : NoImagAxisRoots (X - C (1 : ℂ) + C (2 : ℂ)) := by
  intro ω h0
  have hre : (I * (ω : ℂ) - 1 + 2).re = 0 := by
    have := congr_arg Complex.re h0
    simpa using this
  simp at hre
  norm_num at hre

lemma example2_rhp_poles : rhpRootCount (X - C (1 : ℂ)) = 1 := by
  unfold rhpRootCount
  rw [Polynomial.roots_X_sub_C, Multiset.filter_singleton, if_pos (by simp)]
  simp

lemma example2_closedLoop_hurwitz : IsHurwitz (X - C (1 : ℂ) + C (2 : ℂ)) := by
  have heq : X - C (1 : ℂ) + C (2 : ℂ) = X + C (1 : ℂ) := by
    rw [sub_eq_add_neg, add_assoc, ← C_neg, ← C_add]
    norm_num
  rw [heq]
  exact example1_openLoop_hurwitz

theorem example2_nyquist_encirclements_ccw :
    nyquistEncirclementsCCW (C (2 : ℂ)) (X - C (1 : ℂ)) = 1 := by
  have h := (nyquist_stability_criterion (C (2 : ℂ)) (X - C (1 : ℂ))
    example2_proper example2_openLoop_noImag example2_closedLoop_noImag).mp
    example2_closedLoop_hurwitz
  rw [example2_rhp_poles] at h
  simpa using h

theorem example2_nyquist_encirclements_cw :
    nyquistEncirclementsCW (C (2 : ℂ)) (X - C (1 : ℂ)) = -1 := by
  unfold nyquistEncirclementsCW
  rw [example2_nyquist_encirclements_ccw]

end Nyquist.Examples

/-! ### ZFC Axiom Audit -/

#print axioms Nyquist.nyquist_dContour_tendsto
#print axioms Nyquist.nyquist_semicircle_tendsto_zero
#print axioms Nyquist.nyquistIntegrand_integrable
#print axioms Nyquist.nyquist_encirclement_formula
#print axioms Nyquist.nyquist_phase_lift
#print axioms Nyquist.nyquist_phase_lift_unique
#print axioms Nyquist.nyquist_stability_criterion
#print axioms Nyquist.nyquist_stability_criterion_real
#print axioms Nyquist.argumentPrinciple_circle
#print axioms Nyquist.rouche_circle
#print axioms Nyquist.argumentPrinciple_rect
#print axioms Nyquist.nyquist_indented_origin_tendsto
#print axioms Nyquist.nyquist_indented_origin_criterion
#print axioms Nyquist.example_integrator_stable
#print axioms Nyquist.nyquist_delay_encirclement_tendsto
#print axioms Nyquist.nyquist_delay_stability_criterion
#print axioms Nyquist.nyquist_delay_small_gain
#print axioms Nyquist.example_delay_independent_stable
#print axioms Nyquist.nyquist_small_gain_hurwitz
#print axioms Nyquist.nyquist_gain_margin
#print axioms Nyquist.coprime_no_rhp_cancellation
