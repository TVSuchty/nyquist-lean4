import Nyquist.Defs
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Imaginary-Axis Integrals of Simple Poles

This file establishes the antiderivative, fundamental theorem of calculus, principal-value
limits as `R → ∞`, and `L¹` integrability of pole differences along the imaginary axis `i ℝ`.
-/

namespace Nyquist

open Complex MeasureTheory Filter

/-- Antiderivative of `ω ↦ I / (I * ω - a)` along the imaginary axis when `a.re ≠ 0`. -/
noncomputable def poleAntideriv (a : ℂ) (ω : ℝ) : ℂ :=
  ((1 / 2 : ℝ) * Real.log (a.re ^ 2 + (ω - a.im) ^ 2) : ℝ) -
    I * (Real.arctan ((ω - a.im) / a.re) : ℝ)

private lemma imagAxis_sub_ne_zero (a : ℂ) (ha : a.re ≠ 0) (ω : ℝ) : I * ω - a ≠ 0 := by
  intro h
  have hre : (I * (ω : ℂ) - a).re = 0 := by simp [h]
  simp only [sub_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self,
    zero_sub, neg_eq_zero] at hre
  exact ha hre

private lemma pos_re_sq_add_sub_im_sq (a : ℂ) (ha : a.re ≠ 0) (ω : ℝ) :
    0 < a.re ^ 2 + (ω - a.im) ^ 2 := by
  have h1 : 0 < a.re ^ 2 := sq_pos_of_ne_zero ha
  have h2 : 0 ≤ (ω - a.im) ^ 2 := sq_nonneg (ω - a.im)
  linarith

lemma hasDerivAt_poleAntideriv (a : ℂ) (ha : a.re ≠ 0) (ω : ℝ) :
    HasDerivAt (poleAntideriv a) (I / (I * ω - a)) ω := by
  have hq_pos : 0 < a.re ^ 2 + (ω - a.im) ^ 2 := pos_re_sq_add_sub_im_sq a ha ω
  have hq_ne : a.re ^ 2 + (ω - a.im) ^ 2 ≠ 0 := hq_pos.ne'
  have hsub : HasDerivAt (fun x : ℝ => x - a.im) 1 ω := (hasDerivAt_id ω).sub_const a.im
  have hsq : HasDerivAt (fun x : ℝ => (x - a.im) ^ 2) (2 * (ω - a.im)) ω := by
    convert hsub.mul hsub using 1
    · funext x; dsimp only [Pi.mul_apply]; ring
    · ring
  have hquad : HasDerivAt (fun x : ℝ => a.re ^ 2 + (x - a.im) ^ 2) (2 * (ω - a.im)) ω := by
    convert (hasDerivAt_const ω (a.re ^ 2)).add hsq using 1
    ring
  have hlog :
      HasDerivAt (fun x : ℝ => Real.log (a.re ^ 2 + (x - a.im) ^ 2))
        ((a.re ^ 2 + (ω - a.im) ^ 2)⁻¹ * (2 * (ω - a.im))) ω := by
    simpa only [Function.comp_def] using (Real.hasDerivAt_log hq_ne).comp ω hquad
  have hre_real :
      HasDerivAt (fun x : ℝ => (1 / 2 : ℝ) * Real.log (a.re ^ 2 + (x - a.im) ^ 2))
        ((ω - a.im) / (a.re ^ 2 + (ω - a.im) ^ 2)) ω := by
    convert hlog.const_mul (1 / 2 : ℝ) using 1
    field_simp
  have harg : HasDerivAt (fun x : ℝ => (x - a.im) / a.re) (1 / a.re) ω :=
    hsub.div_const a.re
  have harctan :
      HasDerivAt (fun x : ℝ => Real.arctan ((x - a.im) / a.re))
        (a.re / (a.re ^ 2 + (ω - a.im) ^ 2)) ω := by
    have hcomp :
        HasDerivAt (fun x : ℝ => Real.arctan ((x - a.im) / a.re))
          ((1 / (1 + ((ω - a.im) / a.re) ^ 2)) * (1 / a.re)) ω := by
      simpa only [Function.comp_def] using
        (Real.hasDerivAt_arctan ((ω - a.im) / a.re)).comp ω harg
    convert hcomp using 1
    field_simp [ha]
  have hre_c :
      HasDerivAt
        (fun x : ℝ => (((1 / 2 : ℝ) * Real.log (a.re ^ 2 + (x - a.im) ^ 2) : ℝ) : ℂ))
        (((ω - a.im) / (a.re ^ 2 + (ω - a.im) ^ 2) : ℝ) : ℂ) ω :=
    hre_real.ofReal_comp
  have him_c :
      HasDerivAt (fun x : ℝ => I * (Real.arctan ((x - a.im) / a.re) : ℝ))
        (I * ((a.re / (a.re ^ 2 + (ω - a.im) ^ 2) : ℝ) : ℂ)) ω :=
    harctan.ofReal_comp.const_mul I
  have hcomb :
      HasDerivAt (poleAntideriv a)
        (((ω - a.im) / (a.re ^ 2 + (ω - a.im) ^ 2) : ℝ) -
          I * ((a.re / (a.re ^ 2 + (ω - a.im) ^ 2) : ℝ) : ℂ)) ω := by
    unfold poleAntideriv
    exact hre_c.sub him_c
  convert hcomb using 1
  have hden : I * (ω : ℂ) - a ≠ 0 := imagAxis_sub_ne_zero a ha ω
  have hq_c : (a.re : ℂ) ^ 2 + ((ω : ℂ) - a.im) ^ 2 ≠ 0 := by
    exact_mod_cast hq_ne
  rw [div_eq_iff hden]
  push_cast
  field_simp [hq_c]
  apply Complex.ext <;> simp [sq] <;> ring

lemma intervalIntegrable_single_pole_imagAxis (a : ℂ) (ha : a.re ≠ 0) (u v : ℝ) :
    IntervalIntegrable (fun ω : ℝ => I / (I * ω - a)) volume u v := by
  refine Continuous.intervalIntegrable ?_ u v
  fun_prop (disch := intro ω; exact imagAxis_sub_ne_zero a ha ω)

theorem integral_single_pole_imagAxis (a : ℂ) (ha : a.re ≠ 0) (R : ℝ) :
    (∫ ω in (-R)..R, I / (I * ω - a)) = poleAntideriv a R - poleAntideriv a (-R) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun ω _ => hasDerivAt_poleAntideriv a ha ω)
    (intervalIntegrable_single_pole_imagAxis a ha (-R) R)

private lemma tendsto_poleAntideriv_log_diff (a : ℂ) (ha : a.re ≠ 0) :
    Tendsto
      (fun R : ℝ =>
        (1 / 2 : ℝ) * Real.log (a.re ^ 2 + (R - a.im) ^ 2) -
          (1 / 2 : ℝ) * Real.log (a.re ^ 2 + (-R - a.im) ^ 2))
      atTop (nhds 0) := by
  have hratio :
      Tendsto
        (fun R : ℝ => (a.re ^ 2 + (R - a.im) ^ 2) / (a.re ^ 2 + (-R - a.im) ^ 2))
        atTop (nhds 1) := by
    have hinv : Tendsto (fun R : ℝ => R⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
    have hinv_sq : Tendsto (fun R : ℝ => a.re ^ 2 * R⁻¹ ^ 2) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul (hinv.pow 2))
    have him_inv : Tendsto (fun R : ℝ => a.im * R⁻¹) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hinv)
    have hnum : Tendsto (fun R : ℝ => a.re ^ 2 * R⁻¹ ^ 2 + (1 - a.im * R⁻¹) ^ 2)
        atTop (nhds (0 + (1 - 0) ^ 2)) :=
      hinv_sq.add ((tendsto_const_nhds.sub him_inv).pow 2)
    have hden : Tendsto (fun R : ℝ => a.re ^ 2 * R⁻¹ ^ 2 + (-1 - a.im * R⁻¹) ^ 2)
        atTop (nhds (0 + (-1 - 0) ^ 2)) :=
      hinv_sq.add ((tendsto_const_nhds.sub him_inv).pow 2)
    have hdiv :
        Tendsto
          (fun R : ℝ =>
            (a.re ^ 2 * R⁻¹ ^ 2 + (1 - a.im * R⁻¹) ^ 2) /
              (a.re ^ 2 * R⁻¹ ^ 2 + (-1 - a.im * R⁻¹) ^ 2))
          atTop (nhds ((0 + (1 - 0) ^ 2) / (0 + (-1 - 0) ^ 2))) :=
      hnum.div hden (by norm_num)
    have hnorm : (0 + (1 - (0 : ℝ)) ^ 2) / (0 + (-1 - 0) ^ 2) = 1 := by norm_num
    rw [hnorm] at hdiv
    refine hdiv.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
    field_simp [hR]
  have hlog :
      Tendsto
        (fun R : ℝ =>
          Real.log ((a.re ^ 2 + (R - a.im) ^ 2) / (a.re ^ 2 + (-R - a.im) ^ 2)))
        atTop (nhds (Real.log 1)) :=
    (Real.continuousAt_log (by norm_num)).tendsto.comp hratio
  rw [Real.log_one] at hlog
  have hmul :
      Tendsto
        (fun R : ℝ =>
          (1 / 2 : ℝ) *
            Real.log ((a.re ^ 2 + (R - a.im) ^ 2) / (a.re ^ 2 + (-R - a.im) ^ 2)))
        atTop (nhds ((1 / 2 : ℝ) * 0)) :=
    tendsto_const_nhds.mul hlog
  rw [mul_zero] at hmul
  refine hmul.congr fun R => ?_
  have h1 : a.re ^ 2 + (R - a.im) ^ 2 ≠ 0 := (pos_re_sq_add_sub_im_sq a ha R).ne'
  have h2 : a.re ^ 2 + (-R - a.im) ^ 2 ≠ 0 := (pos_re_sq_add_sub_im_sq a ha (-R)).ne'
  rw [Real.log_div h1 h2]
  ring

private lemma poleAntideriv_sub_eq (a : ℂ) (R : ℝ) :
    poleAntideriv a R - poleAntideriv a (-R) =
      (((1 / 2 : ℝ) * Real.log (a.re ^ 2 + (R - a.im) ^ 2) -
        (1 / 2 : ℝ) * Real.log (a.re ^ 2 + (-R - a.im) ^ 2) : ℝ) : ℂ) -
        I * ((Real.arctan ((R - a.im) / a.re) -
          Real.arctan ((-R - a.im) / a.re) : ℝ) : ℂ) := by
  unfold poleAntideriv
  push_cast
  ring

private lemma tendsto_sub_const_atTop (c : ℝ) :
    Tendsto (fun R : ℝ => R - c) atTop atTop := by
  simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-c) tendsto_id

theorem tendsto_integral_single_pole_imagAxis_pos (a : ℂ) (ha : 0 < a.re) :
    Tendsto (fun R : ℝ => ∫ ω in (-R)..R, I / (I * ω - a))
      atTop (nhds (-I * Real.pi)) := by
  have hne : a.re ≠ 0 := ha.ne'
  have hlog :
      Tendsto
        (fun R : ℝ =>
          (((1 / 2 : ℝ) * Real.log (a.re ^ 2 + (R - a.im) ^ 2) -
            (1 / 2 : ℝ) * Real.log (a.re ^ 2 + (-R - a.im) ^ 2) : ℝ) : ℂ))
        atTop (nhds ((0 : ℝ) : ℂ)) := by
    simpa only [Function.comp_def] using
      (continuous_ofReal.tendsto 0).comp (tendsto_poleAntideriv_log_diff a hne)
  have harg_pos : Tendsto (fun R : ℝ => (R - a.im) / a.re) atTop atTop :=
    (tendsto_sub_const_atTop a.im).atTop_div_const ha
  have harg_neg : Tendsto (fun R : ℝ => (-R - a.im) / a.re) atTop atBot := by
    have h1 : Tendsto (fun R : ℝ => (R + a.im) / a.re) atTop atTop := by
      simpa only [sub_neg_eq_add] using (tendsto_sub_const_atTop (-a.im)).atTop_div_const ha
    have h2 : Tendsto (fun R : ℝ => -((R + a.im) / a.re)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp h1
    refine h2.congr fun R => ?_
    ring
  have harc1 :
      Tendsto (fun R : ℝ => Real.arctan ((R - a.im) / a.re)) atTop (nhds (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp harg_pos
  have harc2 :
      Tendsto (fun R : ℝ => Real.arctan ((-R - a.im) / a.re)) atTop (nhds (-(Real.pi / 2))) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot).comp harg_neg
  have harc_diff :
      Tendsto (fun R : ℝ => Real.arctan ((R - a.im) / a.re) - Real.arctan ((-R - a.im) / a.re))
        atTop (nhds Real.pi) := by
    have hpi : Real.pi / 2 - -(Real.pi / 2) = Real.pi := by ring
    rw [← hpi]
    exact harc1.sub harc2
  have him :
      Tendsto
        (fun R : ℝ =>
          I * ((Real.arctan ((R - a.im) / a.re) - Real.arctan ((-R - a.im) / a.re) : ℝ) : ℂ))
        atTop (nhds (I * (Real.pi : ℂ))) :=
    tendsto_const_nhds.mul ((continuous_ofReal.tendsto Real.pi).comp harc_diff)
  have hsub := hlog.sub him
  have hlim : ((0 : ℝ) : ℂ) - I * (Real.pi : ℂ) = -I * Real.pi := by simp
  rw [hlim] at hsub
  refine hsub.congr fun R => ?_
  rw [integral_single_pole_imagAxis a hne R, poleAntideriv_sub_eq]

theorem tendsto_integral_single_pole_imagAxis_neg (a : ℂ) (ha : a.re < 0) :
    Tendsto (fun R : ℝ => ∫ ω in (-R)..R, I / (I * ω - a))
      atTop (nhds (I * Real.pi)) := by
  have hne : a.re ≠ 0 := ha.ne
  have hlog :
      Tendsto
        (fun R : ℝ =>
          (((1 / 2 : ℝ) * Real.log (a.re ^ 2 + (R - a.im) ^ 2) -
            (1 / 2 : ℝ) * Real.log (a.re ^ 2 + (-R - a.im) ^ 2) : ℝ) : ℂ))
        atTop (nhds ((0 : ℝ) : ℂ)) := by
    simpa only [Function.comp_def] using
      (continuous_ofReal.tendsto 0).comp (tendsto_poleAntideriv_log_diff a hne)
  have harg_neg : Tendsto (fun R : ℝ => (R - a.im) / a.re) atTop atBot :=
    (tendsto_sub_const_atTop a.im).atTop_div_const_of_neg ha
  have harg_pos : Tendsto (fun R : ℝ => (-R - a.im) / a.re) atTop atTop := by
    have h1 : Tendsto (fun R : ℝ => (R + a.im) / (-a.re)) atTop atTop := by
      simpa only [sub_neg_eq_add] using
        (tendsto_sub_const_atTop (-a.im)).atTop_div_const (neg_pos.mpr ha)
    refine h1.congr fun R => ?_
    ring
  have harc1 :
      Tendsto (fun R : ℝ => Real.arctan ((R - a.im) / a.re)) atTop (nhds (-(Real.pi / 2))) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot).comp harg_neg
  have harc2 :
      Tendsto (fun R : ℝ => Real.arctan ((-R - a.im) / a.re)) atTop (nhds (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp harg_pos
  have harc_diff :
      Tendsto (fun R : ℝ => Real.arctan ((R - a.im) / a.re) - Real.arctan ((-R - a.im) / a.re))
        atTop (nhds (-Real.pi)) := by
    have hpi : -(Real.pi / 2) - Real.pi / 2 = -Real.pi := by ring
    rw [← hpi]
    exact harc1.sub harc2
  have him :
      Tendsto
        (fun R : ℝ =>
          I * ((Real.arctan ((R - a.im) / a.re) - Real.arctan ((-R - a.im) / a.re) : ℝ) : ℂ))
        atTop (nhds (I * ((-Real.pi : ℝ) : ℂ))) :=
    tendsto_const_nhds.mul ((continuous_ofReal.tendsto (-Real.pi)).comp harc_diff)
  have hsub := hlog.sub him
  have hlim : ((0 : ℝ) : ℂ) - I * ((-Real.pi : ℝ) : ℂ) = I * Real.pi := by simp
  rw [hlim] at hsub
  refine hsub.congr fun R => ?_
  rw [integral_single_pole_imagAxis a hne R, poleAntideriv_sub_eq]

private lemma normSq_imagAxis_sub (a : ℂ) (ω : ℝ) :
    ‖I * (ω : ℂ) - a‖ ^ 2 = a.re ^ 2 + (ω - a.im) ^ 2 := by
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply]
  ring

theorem integrable_pole_sub_ref (a : ℂ) (ha : a.re ≠ 0) :
    Integrable (fun ω : ℝ => I / (I * ω - a) - I / (I * ω - 1)) volume := by
  have h1_ne : (1 : ℂ).re ≠ 0 := by simp
  have hcont : Continuous (fun ω : ℝ => I / (I * ω - a) - I / (I * ω - 1)) := by
    fun_prop (disch := intro ω; first
      | exact imagAxis_sub_ne_zero a ha ω
      | exact imagAxis_sub_ne_zero 1 h1_ne ω)
  let K : ℝ := max ((1 + 2 * a.im ^ 2) / a.re ^ 2) 2
  have hK_ge_two : 2 ≤ K := le_max_right _ _
  have hK_ge_ratio : (1 + 2 * a.im ^ 2) / a.re ^ 2 ≤ K := le_max_left _ _
  have hK_pos : 0 < K := by linarith
  let C : ℝ := K * ‖a - 1‖
  have hdom : Integrable (fun ω : ℝ => C * (1 + ω ^ 2)⁻¹) volume :=
    integrable_inv_one_add_sq.const_mul C
  refine hdom.mono' hcont.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  have ha_ne := imagAxis_sub_ne_zero a ha ω
  have h1_ne' := imagAxis_sub_ne_zero 1 h1_ne ω
  have hdiff :
      I / (I * ω - a) - I / (I * ω - 1) = I * (a - 1) / ((I * ω - a) * (I * ω - 1)) := by
    field_simp [ha_ne, h1_ne']
    ring
  rw [hdiff, norm_div, norm_mul, norm_I, one_mul, norm_mul]
  have h_one_sq : ‖I * (ω : ℂ) - 1‖ ^ 2 = 1 + ω ^ 2 := by
    rw [normSq_imagAxis_sub 1 ω]
    simp
  have h_a_sq : ‖I * (ω : ℂ) - a‖ ^ 2 = a.re ^ 2 + (ω - a.im) ^ 2 :=
    normSq_imagAxis_sub a ω
  have hare_sq_pos : 0 < a.re ^ 2 := sq_pos_of_ne_zero ha
  have hbound_sq : 1 + ω ^ 2 ≤ K * ‖I * (ω : ℂ) - a‖ ^ 2 := by
    rw [h_a_sq]
    have hsq_split : ω ^ 2 ≤ 2 * (ω - a.im) ^ 2 + 2 * a.im ^ 2 := by
      have : 0 ≤ (ω - 2 * a.im) ^ 2 := sq_nonneg _
      nlinarith
    have hconst : 1 + 2 * a.im ^ 2 ≤ K * a.re ^ 2 := by
      calc 1 + 2 * a.im ^ 2 = ((1 + 2 * a.im ^ 2) / a.re ^ 2) * a.re ^ 2 := by
              field_simp [hare_sq_pos.ne']
        _ ≤ K * a.re ^ 2 := mul_le_mul_of_nonneg_right hK_ge_ratio hare_sq_pos.le
    have hvar : 2 * (ω - a.im) ^ 2 ≤ K * (ω - a.im) ^ 2 :=
      mul_le_mul_of_nonneg_right hK_ge_two (sq_nonneg _)
    nlinarith
  have hprod_sq :
      (1 + ω ^ 2) ^ 2 ≤ (K * (‖I * (ω : ℂ) - a‖ * ‖I * (ω : ℂ) - 1‖)) ^ 2 := by
    have h_pos_1 : 0 ≤ 1 + ω ^ 2 := by positivity
    have h_le_Ksq : K ≤ K ^ 2 := by nlinarith
    calc (1 + ω ^ 2) ^ 2 = (1 + ω ^ 2) * (1 + ω ^ 2) := sq (1 + ω ^ 2)
      _ ≤ (K * ‖I * (ω : ℂ) - a‖ ^ 2) * ‖I * (ω : ℂ) - 1‖ ^ 2 := by
            rw [h_one_sq]
            exact mul_le_mul_of_nonneg_right hbound_sq h_pos_1
      _ = K * (‖I * (ω : ℂ) - a‖ * ‖I * (ω : ℂ) - 1‖) ^ 2 := by ring
      _ ≤ K ^ 2 * (‖I * (ω : ℂ) - a‖ * ‖I * (ω : ℂ) - 1‖) ^ 2 :=
            mul_le_mul_of_nonneg_right h_le_Ksq (sq_nonneg _)
      _ = (K * (‖I * (ω : ℂ) - a‖ * ‖I * (ω : ℂ) - 1‖)) ^ 2 := by ring
  have hprod : 1 + ω ^ 2 ≤ K * (‖I * (ω : ℂ) - a‖ * ‖I * (ω : ℂ) - 1‖) := by
    nlinarith [sq_nonneg (1 + ω ^ 2),
      show 0 ≤ K * (‖I * (ω : ℂ) - a‖ * ‖I * (ω : ℂ) - 1‖) by positivity]
  have hden_pos : 0 < ‖I * (ω : ℂ) - a‖ * ‖I * (ω : ℂ) - 1‖ :=
    mul_pos (norm_pos_iff.mpr ha_ne) (norm_pos_iff.mpr h1_ne')
  have h1w_pos : 0 < 1 + ω ^ 2 := by positivity
  rw [div_eq_mul_inv,
    show C * (1 + ω ^ 2)⁻¹ = ‖a - 1‖ * (K * (1 + ω ^ 2)⁻¹) by dsimp [C]; ring]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [inv_le_iff_one_le_mul₀ hden_pos]
  calc 1 = (1 + ω ^ 2) * (1 + ω ^ 2)⁻¹ := (mul_inv_cancel₀ h1w_pos.ne').symm
    _ ≤ (K * (‖I * (ω : ℂ) - a‖ * ‖I * (ω : ℂ) - 1‖)) * (1 + ω ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hprod (inv_nonneg.mpr h1w_pos.le)
    _ = (K * (1 + ω ^ 2)⁻¹) * (‖I * (ω : ℂ) - a‖ * ‖I * (ω : ℂ) - 1‖) := by ring

end Nyquist
