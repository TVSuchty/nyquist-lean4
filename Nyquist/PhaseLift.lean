import Nyquist.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Order.IntermediateValue

/-!
# Continuous Phase Lift for Linear Factors

This file defines the continuous phase `factorPhase a ω` for linear factors `i ω - a`
(with `a.re ≠ 0`), establishes its continuity, polar representation, asymptotic limits at `±∞`,
and proves uniqueness of continuous phase lifts up to integer multiples of `2 * π`.
-/

namespace Nyquist

open Complex Filter

/-- Continuous phase of `i * ω - a` for `a.re ≠ 0`. -/
noncomputable def factorPhase (a : ℂ) (ω : ℝ) : ℝ :=
  if 0 < a.re then Real.pi - Real.arctan ((ω - a.im) / a.re)
  else -Real.arctan ((ω - a.im) / a.re)

lemma factorPhase_continuous (a : ℂ) (_ha : a.re ≠ 0) : Continuous (factorPhase a) := by
  have harg : Continuous (fun ω : ℝ => (ω - a.im) / a.re) :=
    (continuous_id.sub continuous_const).div_const a.re
  have harctan : Continuous (fun ω : ℝ => Real.arctan ((ω - a.im) / a.re)) :=
    Real.continuous_arctan.comp harg
  by_cases h : 0 < a.re
  · have h_eq : factorPhase a = fun ω => Real.pi - Real.arctan ((ω - a.im) / a.re) := by
      ext ω
      simp [factorPhase, h]
    rw [h_eq]
    exact continuous_const.sub harctan
  · have h_eq : factorPhase a = fun ω => -Real.arctan ((ω - a.im) / a.re) := by
      ext ω
      simp [factorPhase, h]
    rw [h_eq]
    exact harctan.neg

theorem I_mul_sub_eq_norm_mul_exp_factorPhase (a : ℂ) (ha : a.re ≠ 0) (ω : ℝ) :
    I * ω - a = ‖I * ω - a‖ * Complex.exp (I * factorPhase a ω) := by
  set t : ℝ := (ω - a.im) / a.re
  have hsq_pos : 0 < 1 + t ^ 2 := by positivity
  have hsqrt_ne : √(1 + t ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hsq_pos).ne'
  have hω : ω - a.im = a.re * t := by
    dsimp [t]
    field_simp [ha]
  have hnorm_sq : (-a.re) * (-a.re) + (ω - a.im) * (ω - a.im) = a.re ^ 2 * (1 + t ^ 2) := by
    rw [hω]
    ring
  have hnorm : ‖I * ω - a‖ = |a.re| * √(1 + t ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    have hre : (I * ω - a).re = -a.re := by simp
    have him : (I * ω - a).im = ω - a.im := by simp
    rw [hre, him, hnorm_sq, Real.sqrt_mul (sq_nonneg a.re), Real.sqrt_sq_eq_abs]
  have hexp :
      Complex.exp (I * factorPhase a ω) =
        Complex.cos (factorPhase a ω) + Complex.sin (factorPhase a ω) * I := by
    rw [mul_comm I _, Complex.exp_mul_I]
  apply Complex.ext
  · rw [Complex.mul_re, hexp]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im, mul_zero, sub_zero, add_zero, sub_re, mul_re, ofReal_re,
      ofReal_im, I_re, I_im, zero_mul, zero_sub]
    rw [hnorm]
    by_cases h : 0 < a.re
    · have hcos : Real.cos (factorPhase a ω) = -(1 / √(1 + t ^ 2)) := by
        simp [factorPhase, h, Real.cos_pi_sub, Real.cos_arctan, t]
      rw [hcos, abs_of_pos h]
      symm
      calc
        a.re * √(1 + t ^ 2) * -(1 / √(1 + t ^ 2))
            = -a.re * (√(1 + t ^ 2) / √(1 + t ^ 2)) := by ring
        _ = -a.re := by rw [div_self hsqrt_ne, mul_one]
    · have hlt : a.re < 0 := lt_of_le_of_ne (not_lt.mp h) ha
      have hcos : Real.cos (factorPhase a ω) = 1 / √(1 + t ^ 2) := by
        simp [factorPhase, h, Real.cos_neg, Real.cos_arctan, t]
      rw [hcos, abs_of_neg hlt]
      symm
      calc
        -a.re * √(1 + t ^ 2) * (1 / √(1 + t ^ 2))
            = -a.re * (√(1 + t ^ 2) / √(1 + t ^ 2)) := by ring
        _ = -a.re := by rw [div_self hsqrt_ne, mul_one]
  · rw [Complex.mul_im, hexp]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.cos_ofReal_im, Complex.sin_ofReal_re,
      Complex.sin_ofReal_im, mul_one, mul_zero, zero_mul, add_zero, zero_add, sub_im, mul_im,
      ofReal_re, ofReal_im, I_re, I_im, one_mul]
    rw [hnorm]
    by_cases h : 0 < a.re
    · have hsin : Real.sin (factorPhase a ω) = t / √(1 + t ^ 2) := by
        simp [factorPhase, h, Real.sin_pi_sub, Real.sin_arctan, t]
      rw [hsin, abs_of_pos h]
      symm
      calc
        a.re * √(1 + t ^ 2) * (t / √(1 + t ^ 2))
            = a.re * t * (√(1 + t ^ 2) / √(1 + t ^ 2)) := by ring
        _ = a.re * t := by rw [div_self hsqrt_ne, mul_one]
        _ = ω - a.im := hω.symm
    · have hlt : a.re < 0 := lt_of_le_of_ne (not_lt.mp h) ha
      have hsin : Real.sin (factorPhase a ω) = -(t / √(1 + t ^ 2)) := by
        simp [factorPhase, h, Real.sin_neg, Real.sin_arctan, t]
      rw [hsin, abs_of_neg hlt]
      symm
      calc
        -a.re * √(1 + t ^ 2) * -(t / √(1 + t ^ 2))
            = a.re * t * (√(1 + t ^ 2) / √(1 + t ^ 2)) := by ring
        _ = a.re * t := by rw [div_self hsqrt_ne, mul_one]
        _ = ω - a.im := hω.symm

private lemma tendsto_sub_div_pos_atTop (c : ℝ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun ω : ℝ => (ω - c) / r) atTop atTop := by
  have h1 : Tendsto (fun ω : ℝ => ω - c) atTop atTop :=
    tendsto_id.atTop_add (tendsto_const_nhds (x := -c))
  simpa [div_eq_mul_inv] using h1.atTop_mul_const (inv_pos.mpr hr)

private lemma tendsto_sub_div_pos_atBot (c : ℝ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun ω : ℝ => (ω - c) / r) atBot atBot := by
  have h1 : Tendsto (fun ω : ℝ => ω - c) atBot atBot := by
    simpa [sub_eq_add_neg] using tendsto_id.atBot_add (tendsto_const_nhds (x := -c))
  simpa [div_eq_mul_inv] using h1.atBot_mul_const (inv_pos.mpr hr)

private lemma tendsto_sub_div_neg_atTop (c : ℝ) {r : ℝ} (hr : r < 0) :
    Tendsto (fun ω : ℝ => (ω - c) / r) atTop atBot := by
  have h1 : Tendsto (fun ω : ℝ => (ω - c) / (-r)) atTop atTop :=
    tendsto_sub_div_pos_atTop c (neg_pos.mpr hr)
  have h2 : Tendsto (fun ω : ℝ => -((ω - c) / (-r))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp h1
  simpa [div_neg] using h2

private lemma tendsto_sub_div_neg_atBot (c : ℝ) {r : ℝ} (hr : r < 0) :
    Tendsto (fun ω : ℝ => (ω - c) / r) atBot atTop := by
  have h1 : Tendsto (fun ω : ℝ => (ω - c) / (-r)) atBot atBot :=
    tendsto_sub_div_pos_atBot c (neg_pos.mpr hr)
  have h2 : Tendsto (fun ω : ℝ => -((ω - c) / (-r))) atBot atTop :=
    tendsto_neg_atBot_atTop.comp h1
  simpa [div_neg] using h2

theorem tendsto_factorPhase_pos_atTop (a : ℂ) (ha : 0 < a.re) :
    Tendsto (factorPhase a) atTop (nhds (Real.pi / 2)) := by
  have h_eq : factorPhase a = fun ω => Real.pi - Real.arctan ((ω - a.im) / a.re) := by
    ext ω
    simp [factorPhase, ha]
  rw [h_eq]
  have harctan : Tendsto (fun ω => Real.arctan ((ω - a.im) / a.re)) atTop (nhds (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      (tendsto_sub_div_pos_atTop a.im ha)
  have hlim : Real.pi - Real.pi / 2 = Real.pi / 2 := by ring
  simpa [hlim] using (tendsto_const_nhds (x := Real.pi)).sub harctan

theorem tendsto_factorPhase_pos_atBot (a : ℂ) (ha : 0 < a.re) :
    Tendsto (factorPhase a) atBot (nhds (3 * Real.pi / 2)) := by
  have h_eq : factorPhase a = fun ω => Real.pi - Real.arctan ((ω - a.im) / a.re) := by
    ext ω
    simp [factorPhase, ha]
  rw [h_eq]
  have harctan :
      Tendsto (fun ω => Real.arctan ((ω - a.im) / a.re)) atBot (nhds (-(Real.pi / 2))) :=
    (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
      (tendsto_sub_div_pos_atBot a.im ha)
  have hlim : Real.pi - -(Real.pi / 2) = 3 * Real.pi / 2 := by ring
  simpa [hlim] using (tendsto_const_nhds (x := Real.pi)).sub harctan

theorem tendsto_factorPhase_neg_atTop (a : ℂ) (ha : a.re < 0) :
    Tendsto (factorPhase a) atTop (nhds (Real.pi / 2)) := by
  have hnot : ¬ (0 < a.re) := not_lt.mpr ha.le
  have h_eq : factorPhase a = fun ω => -Real.arctan ((ω - a.im) / a.re) := by
    ext ω
    simp [factorPhase, hnot]
  rw [h_eq]
  have harctan :
      Tendsto (fun ω => Real.arctan ((ω - a.im) / a.re)) atTop (nhds (-(Real.pi / 2))) :=
    (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
      (tendsto_sub_div_neg_atTop a.im ha)
  have hlim : -(-(Real.pi / 2)) = Real.pi / 2 := by ring
  simpa [hlim] using harctan.neg

theorem tendsto_factorPhase_neg_atBot (a : ℂ) (ha : a.re < 0) :
    Tendsto (factorPhase a) atBot (nhds (-Real.pi / 2)) := by
  have hnot : ¬ (0 < a.re) := not_lt.mpr ha.le
  have h_eq : factorPhase a = fun ω => -Real.arctan ((ω - a.im) / a.re) := by
    ext ω
    simp [factorPhase, hnot]
  rw [h_eq]
  have harctan : Tendsto (fun ω => Real.arctan ((ω - a.im) / a.re)) atBot (nhds (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      (tendsto_sub_div_neg_atBot a.im ha)
  have hlim : -(Real.pi / 2) = -Real.pi / 2 := by ring
  simpa [hlim] using harctan.neg

theorem continuous_phase_lift_unique (f : ℝ → ℂ) (hf : ∀ ω : ℝ, f ω ≠ 0)
    (Φ₁ Φ₂ : ℝ → ℝ) (hΦ₁ : Continuous Φ₁) (hΦ₂ : Continuous Φ₂)
    (h₁ : ∀ ω : ℝ, f ω = ‖f ω‖ * Complex.exp (I * Φ₁ ω))
    (h₂ : ∀ ω : ℝ, f ω = ‖f ω‖ * Complex.exp (I * Φ₂ ω)) :
    ∃ k : ℤ, ∀ ω : ℝ, Φ₁ ω - Φ₂ ω = 2 * Real.pi * k := by
  have h2pi_ne : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  let g : ℝ → ℝ := fun ω => (Φ₁ ω - Φ₂ ω) / (2 * Real.pi)
  have hg_cont : Continuous g := (hΦ₁.sub hΦ₂).div_const (2 * Real.pi)
  have hg_int : ∀ ω : ℝ, ∃ k : ℤ, g ω = k := by
    intro ω
    have hnorm_ne : (‖f ω‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hf ω))
    have hexp : Complex.exp (I * Φ₁ ω) = Complex.exp (I * Φ₂ ω) := by
      apply mul_left_cancel₀ hnorm_ne
      rw [← h₁ ω, ← h₂ ω]
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    have him : Φ₁ ω = Φ₂ ω + k * (2 * Real.pi) := by
      have := congr_arg Complex.im hk
      simpa using this
    refine ⟨k, ?_⟩
    dsimp [g]
    rw [him]
    field_simp [h2pi_ne]
    ring
  obtain ⟨k₀, hk₀⟩ := hg_int 0
  refine ⟨k₀, fun ω => ?_⟩
  have hgω : g ω = k₀ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨kω, hkω⟩ := hg_int ω
      have hk_lt : kω < k₀ := by
        exact_mod_cast (by linarith : (kω : ℝ) < k₀)
      have hk_le : (kω : ℝ) + 1 ≤ k₀ := by
        exact_mod_cast Int.add_one_le_iff.mpr hk_lt
      have hlt' : g ω ≤ g 0 := by linarith
      have hmid_mem : (k₀ : ℝ) - 1 / 2 ∈ Set.uIcc (g ω) (g 0) := by
        rw [Set.uIcc_of_le hlt', hkω, hk₀]
        constructor <;> linarith
      have hivt := intermediate_value_uIcc (a := ω) (b := (0 : ℝ)) hg_cont.continuousOn
      obtain ⟨c, _, hc⟩ := hivt hmid_mem
      obtain ⟨kc, hkc⟩ := hg_int c
      have hkc_eq : (kc : ℝ) = k₀ - 1 / 2 := hkc.symm.trans hc
      rcases le_or_gt kc (k₀ - 1) with hle | hgt'
      · have : (kc : ℝ) ≤ k₀ - 1 := by exact_mod_cast hle
        linarith
      · have hle' : k₀ ≤ kc := by omega
        have : (k₀ : ℝ) ≤ kc := by exact_mod_cast hle'
        linarith
    · obtain ⟨kω, hkω⟩ := hg_int ω
      have hk_lt : k₀ < kω := by
        exact_mod_cast (by linarith : (k₀ : ℝ) < kω)
      have hk_le : (k₀ : ℝ) + 1 ≤ kω := by
        exact_mod_cast Int.add_one_le_iff.mpr hk_lt
      have hgt' : g 0 ≤ g ω := by linarith
      have hmid_mem : (k₀ : ℝ) + 1 / 2 ∈ Set.uIcc (g 0) (g ω) := by
        rw [Set.uIcc_of_le hgt', hkω, hk₀]
        constructor <;> linarith
      have hivt := intermediate_value_uIcc (a := (0 : ℝ)) (b := ω) hg_cont.continuousOn
      obtain ⟨c, _, hc⟩ := hivt hmid_mem
      obtain ⟨kc, hkc⟩ := hg_int c
      have hkc_eq : (kc : ℝ) = k₀ + 1 / 2 := hkc.symm.trans hc
      rcases le_or_gt kc k₀ with hle | hgt''
      · have : (kc : ℝ) ≤ k₀ := by exact_mod_cast hle
        linarith
      · have hle' : k₀ + 1 ≤ kc := by omega
        have : (k₀ : ℝ) + 1 ≤ kc := by exact_mod_cast hle'
        linarith
  have hsub : (Φ₁ ω - Φ₂ ω) / (2 * Real.pi) = k₀ := hgω
  field_simp [h2pi_ne] at hsub ⊢
  linarith

end Nyquist
