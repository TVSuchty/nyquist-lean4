import Nyquist.Defs
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Semicircle Contour Integral for a Single Pole

This file proves integrability and the large-radius asymptotic limit of the
logarithmic-derivative integral `(I * R * exp (I * θ)) / (R * exp (I * θ) - a)`
along the clockwise right semicircle `θ ∈ [π/2, -π/2]`.
-/

namespace Nyquist

open Complex MeasureTheory Filter

private lemma norm_circle_sub_pole_ge (a : ℂ) {R : ℝ} (hR : ‖a‖ < R) (θ : ℝ) :
    R - ‖a‖ ≤ ‖(R : ℂ) * Complex.exp (I * θ) - a‖ := by
  have hR0 : 0 ≤ R := (norm_nonneg a).trans hR.le
  have hnorm : ‖(R : ℂ) * Complex.exp (I * θ)‖ = R := by
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_of_nonneg hR0,
      Complex.norm_exp_I_mul_ofReal, mul_one]
  have htri : ‖(R : ℂ) * Complex.exp (I * θ)‖ ≤
      ‖(R : ℂ) * Complex.exp (I * θ) - a‖ + ‖a‖ := by
    simpa [sub_add_cancel] using norm_add_le ((R : ℂ) * Complex.exp (I * θ) - a) a
  linarith

private lemma circle_sub_pole_ne_zero (a : ℂ) {R : ℝ} (hR : ‖a‖ < R) (θ : ℝ) :
    (R : ℂ) * Complex.exp (I * θ) - a ≠ 0 := by
  rw [← norm_pos_iff]
  have hge := norm_circle_sub_pole_ge a hR θ
  linarith

lemma intervalIntegrable_single_pole_semicircle (a : ℂ) {R : ℝ} (hR : ‖a‖ < R) (u v : ℝ) :
    IntervalIntegrable
      (fun θ : ℝ => (I * R * Complex.exp (I * θ)) / (R * Complex.exp (I * θ) - a))
      volume u v := by
  have hcont_exp : Continuous (fun θ : ℝ => Complex.exp (I * θ)) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hcont : Continuous
      (fun θ : ℝ => (I * R * Complex.exp (I * θ)) / (R * Complex.exp (I * θ) - a)) := by
    apply Continuous.div₀
    · exact continuous_const.mul hcont_exp
    · exact (continuous_const.mul hcont_exp).sub continuous_const
    · exact circle_sub_pole_ne_zero a hR
  exact hcont.intervalIntegrable u v

theorem tendsto_integral_single_pole_semicircle (a : ℂ) :
    Tendsto (fun R : ℝ => ∫ θ in (Real.pi / 2)..(-Real.pi / 2),
      (I * R * Complex.exp (I * θ)) / (R * Complex.exp (I * θ) - a))
      atTop (nhds (-I * Real.pi)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ᶠ R : ℝ in atTop,
      ‖(∫ θ in (Real.pi / 2)..(-Real.pi / 2),
        (I * R * Complex.exp (I * θ)) / (R * Complex.exp (I * θ) - a)) - (-I * Real.pi)‖ ≤
      (‖a‖ / (R - ‖a‖)) * Real.pi := by
    refine (eventually_gt_atTop ‖a‖).mono fun R hR => ?_
    have hconst : ∫ θ in (Real.pi / 2)..(-Real.pi / 2), (I : ℂ) = -I * Real.pi := by
      rw [intervalIntegral.integral_const, Complex.real_smul]
      push_cast
      ring
    have hint_f := intervalIntegrable_single_pole_semicircle a hR (Real.pi / 2) (-Real.pi / 2)
    have hint_c :
        IntervalIntegrable (fun _ : ℝ => (I : ℂ)) volume (Real.pi / 2) (-Real.pi / 2) :=
      intervalIntegrable_const
    rw [← hconst, ← intervalIntegral.integral_sub hint_f hint_c]
    have hpoint : ∀ θ ∈ Set.uIoc (Real.pi / 2) (-Real.pi / 2),
        ‖(I * R * Complex.exp (I * θ)) / (R * Complex.exp (I * θ) - a) - I‖ ≤
          ‖a‖ / (R - ‖a‖) := by
      intro θ _
      have hne := circle_sub_pole_ne_zero a hR θ
      have heq : (I * R * Complex.exp (I * θ)) / (R * Complex.exp (I * θ) - a) - I =
          (I * a) / (R * Complex.exp (I * θ) - a) := by
        field_simp [hne]
        ring
      rw [heq, norm_div, Complex.norm_mul, Complex.norm_I, one_mul]
      exact div_le_div_of_nonneg_left (norm_nonneg a) (sub_pos.mpr hR)
        (norm_circle_sub_pole_ge a hR θ)
    calc ‖∫ θ in (Real.pi / 2)..(-Real.pi / 2),
          ((I * R * Complex.exp (I * θ)) / (R * Complex.exp (I * θ) - a) - I)‖
        ≤ (‖a‖ / (R - ‖a‖)) * |-Real.pi / 2 - Real.pi / 2| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hpoint
      _ = (‖a‖ / (R - ‖a‖)) * Real.pi := by
          have hpi : |-Real.pi / 2 - Real.pi / 2| = Real.pi := by
            have : -Real.pi / 2 - Real.pi / 2 = -Real.pi := by ring
            rw [this, abs_neg, abs_of_nonneg Real.pi_pos.le]
          rw [hpi]
  have htend_bound :
      Tendsto (fun R : ℝ => (‖a‖ / (R - ‖a‖)) * Real.pi) atTop (nhds 0) := by
    have hsub : Tendsto (fun R : ℝ => R - ‖a‖) atTop atTop :=
      tendsto_id.atTop_add (tendsto_const_nhds (x := -‖a‖))
    have hdiv : Tendsto (fun R : ℝ => ‖a‖ / (R - ‖a‖)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop hsub
    simpa [zero_mul] using hdiv.mul tendsto_const_nhds
  exact squeeze_zero' (Eventually.of_forall fun R => norm_nonneg _) hbound htend_bound

end Nyquist
