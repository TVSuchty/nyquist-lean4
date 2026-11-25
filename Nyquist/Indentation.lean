import Nyquist.Defs
import Nyquist.LogDeriv
import Nyquist.ImagAxisIntegral
import Nyquist.SemicircleIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Indented Nyquist Contour for Open-Loop Poles at the Origin

This file extends the Nyquist stability criterion to open-loop plants `L(s) = N(s) / D(s)` that
may have poles at the origin `s = 0` (such as integrators `1 / s`), by indenting the imaginary-axis
contour around `0` via a small right-half-plane semicircle `θ ↦ ε * exp (I * θ)` for
`θ ∈ [-π / 2, π / 2]`.

Main results:
- `integral_origin_pole_imagAxis_cancel` and `integral_origin_pole_indent`: single-pole
  contributions at `a = 0`.
- `tendsto_indented_single_pole_R` and `tendsto_indentPoleError`: single-pole asymptotics for
  `a.re ≠ 0` on the indented contour as `R → ∞` and `ε → 0⁺`.
- `nyquist_indented_origin_tendsto` and `nyquist_indented_origin_criterion`: the indented Nyquist
  winding limit `P - Z` and stability equivalence `IsHurwitz (D + N) ↔ L(ε) → rhpRootCount D`.
- `example_integrator_stable`: verified stability of the integrator plant `L(s) = K / (s (s + 1))`
  for `K > 0`.
-/

namespace Nyquist

open Complex Polynomial MeasureTheory Filter
open scoped Topology

/-! ### Nonzero Imaginary-Axis Root Condition and Origin Pole Count -/

/-- No nonzero roots on the imaginary axis `i ℝ` (poles at `s = 0` are permitted). -/
def NoNonzeroImagAxisRoots (p : Polynomial ℂ) : Prop :=
  ∀ ω : ℝ, ω ≠ 0 → p.eval (I * ω) ≠ 0

lemma noNonzeroImagAxisRoots_ne_zero {p : Polynomial ℂ} (hp : NoNonzeroImagAxisRoots p) :
    p ≠ 0 := by
  intro h0
  have := hp 1 one_ne_zero
  simp [h0] at this

lemma eq_zero_or_re_ne_zero_of_mem_roots {p : Polynomial ℂ} (hp : NoNonzeroImagAxisRoots p)
    {z : ℂ} (hz : z ∈ p.roots) : z = 0 ∨ z.re ≠ 0 := by
  by_cases hre : z.re = 0
  · left
    have hp0 : p ≠ 0 := noNonzeroImagAxisRoots_ne_zero hp
    have heval : p.eval z = 0 := (mem_roots hp0).mp hz
    have hz_eq : z = I * (z.im : ℂ) := by
      apply Complex.ext <;> simp [hre]
    rw [hz_eq] at heval
    have him : z.im = 0 := by
      by_contra hne
      exact hp z.im hne heval
    apply Complex.ext <;> simp [hre, him]
  · right
    exact hre

/-- Number of poles at the origin `s = 0` (counted with multiplicity). -/
noncomputable def originPoleCount (D : Polynomial ℂ) : ℕ :=
  D.roots.count 0

private lemma rhpRootCount_add_lhpRootCount_add_originPoleCount {p : Polynomial ℂ}
    (_hp : p ≠ 0) (hImag : NoNonzeroImagAxisRoots p) :
    rhpRootCount p + lhpRootCount p + originPoleCount p = p.natDegree := by
  unfold rhpRootCount lhpRootCount originPoleCount
  have hnot_rhp :
      p.roots.filter (fun z : ℂ => ¬ (0 < z.re)) =
        p.roots.filter (fun z : ℂ => z.re < 0) + p.roots.filter (fun z : ℂ => z = 0) := by
    have h1 :
        p.roots.filter (fun z : ℂ => ¬ (0 < z.re)) =
          (p.roots.filter (fun z : ℂ => ¬ (0 < z.re))).filter (fun z : ℂ => z.re < 0) +
            (p.roots.filter (fun z : ℂ => ¬ (0 < z.re))).filter
              (fun z : ℂ => ¬ (z.re < 0)) :=
      (Multiset.filter_add_not (fun z : ℂ => z.re < 0)
        (p.roots.filter (fun z : ℂ => ¬ (0 < z.re)))).symm
    rw [h1]
    congr 1
    · rw [Multiset.filter_filter]
      refine Multiset.filter_congr fun z _ => ?_
      exact ⟨fun h => h.1, fun h => ⟨h, not_lt.mpr h.le⟩⟩
    · rw [Multiset.filter_filter]
      refine Multiset.filter_congr fun z hz => ?_
      constructor
      · intro ⟨hnot_neg, hnot_pos⟩
        rcases eq_zero_or_re_ne_zero_of_mem_roots hImag hz with rfl | hne
        · rfl
        · exfalso
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact hnot_neg hlt
          · exact hnot_pos hgt
      · rintro rfl
        simp
  have hcount : (p.roots.filter (fun z : ℂ => z = 0)).card = p.roots.count 0 := by
    have heq : p.roots.filter (fun z : ℂ => z = 0) = p.roots.filter (Eq (0 : ℂ)) := by
      refine Multiset.filter_congr fun z _ => eq_comm
    rw [heq, ← Multiset.count_eq_card_filter_eq]
  have hsplit := Multiset.filter_add_not (fun z : ℂ => 0 < z.re) p.roots
  have hcard :
      (p.roots.filter (fun z : ℂ => 0 < z.re)).card +
        ((p.roots.filter (fun z : ℂ => z.re < 0)).card + p.roots.count 0) = p.roots.card := by
    rw [← hcount, ← Multiset.card_add, ← hnot_rhp, ← Multiset.card_add, hsplit]
  rw [add_assoc, hcard]
  exact (IsAlgClosed.splits p).natDegree_eq_card_roots.symm

/-! ### Indented Nyquist Contour Integral -/

/-- Indented-at-origin Nyquist contour integral: traverses `[-iR, -iε]` upward,
indents around `0` along the right semicircle `θ ↦ ε * exp (i θ)` (`θ ∈ [-π/2, π/2]`),
and traverses `[iε, iR]` upward. -/
noncomputable def nyquistOriginIndentIntegral (N D : Polynomial ℂ) (R ε : ℝ) : ℂ :=
  (∫ ω in (-R)..(-ε), nyquistIntegrand N D ω) +
  (∫ θ in (-Real.pi / 2)..(Real.pi / 2), nyquistSemiIntegrand N D ε θ) +
  (∫ ω in ε..R, nyquistIntegrand N D ω)

/-- Single-pole integral on the indented contour. -/
noncomputable def singlePoleIndentedIntegral (a : ℂ) (R ε : ℝ) : ℂ :=
  (∫ ω in (-R)..(-ε), I / (I * ω - a)) +
  (∫ θ in (-Real.pi / 2)..(Real.pi / 2),
    (I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - a)) +
  (∫ ω in ε..R, I / (I * ω - a))

/-! ### Single-Pole Lemmas at the Origin `a = 0` -/

lemma integral_origin_pole_imagAxis_cancel (R ε : ℝ) (hε : 0 < ε) (hR : ε ≤ R) :
    (∫ ω in (-R)..(-ε), I / (I * ω - 0)) + (∫ ω in ε..R, I / (I * ω - 0)) = 0 := by
  have _ : 0 < R := hε.trans_le hR
  have hneg :
      (∫ ω in (-R)..(-ε), I / (I * ω - 0)) =
        ∫ ω in ε..R, I / (I * ((-ω : ℝ) : ℂ) - 0) := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg (a := ε) (b := R)
        (fun ω : ℝ => I / (I * (ω : ℂ) - 0))).symm
  have hodd :
      (fun ω : ℝ => I / (I * ((-ω : ℝ) : ℂ) - 0)) =
        fun ω : ℝ => -(I / (I * (ω : ℂ) - 0)) := by
    funext ω
    rw [ofReal_neg, mul_neg, sub_zero, sub_zero, div_neg]
  rw [hneg, hodd, intervalIntegral.integral_neg, neg_add_cancel]

lemma integral_origin_pole_indent (ε : ℝ) (hε : 0 < ε) :
    (∫ θ in (-Real.pi / 2)..(Real.pi / 2),
      (I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - 0)) = I * Real.pi := by
  have hεc : (ε : ℂ) ≠ 0 := ofReal_ne_zero.mpr hε.ne'
  have hfun :
      (fun θ : ℝ => (I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - 0)) =
        fun _ : ℝ => (I : ℂ) := by
    funext θ
    have hexp : Complex.exp (I * (θ : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    rw [sub_zero]
    field_simp [hεc, hexp]
  rw [hfun, intervalIntegral.integral_const, Complex.real_smul]
  push_cast
  ring

private lemma tendsto_indented_origin_pole (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun R : ℝ => singlePoleIndentedIntegral 0 R ε) atTop (nhds (I * Real.pi)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ε] with R hR
  unfold singlePoleIndentedIntegral
  have hsum :
      (∫ ω in (-R)..(-ε), I / (I * ω - 0)) +
          (∫ θ in (-Real.pi / 2)..(Real.pi / 2),
            (I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - 0)) +
          (∫ ω in ε..R, I / (I * ω - 0)) =
        ((∫ ω in (-R)..(-ε), I / (I * ω - 0)) + (∫ ω in ε..R, I / (I * ω - 0))) +
          (∫ θ in (-Real.pi / 2)..(Real.pi / 2),
            (I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - 0)) := by
    ring
  rw [hsum, integral_origin_pole_imagAxis_cancel R ε hε hR,
    integral_origin_pole_indent ε hε, zero_add]

/-! ### Single-Pole Lemmas for `a.re ≠ 0` on the Indented Contour -/

/-- Error between the small semicircular indentation integral around `0` and the skipped
imaginary-axis segment `[-iε, iε]` for a pole `a` with `a.re ≠ 0`. -/
noncomputable def indentPoleError (a : ℂ) (ε : ℝ) : ℂ :=
  (∫ θ in (-Real.pi / 2)..(Real.pi / 2),
    (I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - a)) -
  (∫ ω in (-ε)..ε, I / (I * ω - a))

lemma tendsto_indented_single_pole_R (a : ℂ) (ha : a.re ≠ 0) {ε : ℝ}
    (hε : 0 < ε) (hεa : ε < ‖a‖) :
    Tendsto (fun R : ℝ => singlePoleIndentedIntegral a R ε) atTop
      (nhds ((if 0 < a.re then -I * Real.pi else I * Real.pi) + indentPoleError a ε)) := by
  have _ := hε
  have _ := hεa
  have hsplit :
      ∀ R : ℝ, singlePoleIndentedIntegral a R ε =
        (∫ ω in (-R)..R, I / (I * ω - a)) + indentPoleError a ε := by
    intro R
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_single_pole_imagAxis a ha (-R) (-ε))
      (intervalIntegrable_single_pole_imagAxis a ha (-ε) ε)
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_single_pole_imagAxis a ha (-R) ε)
      (intervalIntegrable_single_pole_imagAxis a ha ε R)
    have htot :
        (∫ ω in (-R)..(-ε), I / (I * ω - a)) + (∫ ω in (-ε)..ε, I / (I * ω - a)) +
            (∫ ω in ε..R, I / (I * ω - a)) =
          ∫ ω in (-R)..R, I / (I * ω - a) := by
      rw [h1, h2]
    unfold singlePoleIndentedIntegral indentPoleError
    linear_combination htot
  have hmain :
      Tendsto (fun R : ℝ => ∫ ω in (-R)..R, I / (I * ω - a)) atTop
        (nhds (if 0 < a.re then -I * Real.pi else I * Real.pi)) := by
    rcases lt_or_gt_of_ne ha with hlt | hgt
    · simp only [not_lt.mpr hlt.le, ↓reduceIte]
      exact tendsto_integral_single_pole_imagAxis_neg a hlt
    · simp only [hgt, ↓reduceIte]
      exact tendsto_integral_single_pole_imagAxis_pos a hgt
  refine (hmain.add tendsto_const_nhds).congr fun R => ?_
  exact (hsplit R).symm

private lemma norm_circle_sub_pole_ge_of_lt (a : ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hεa : ε ≤ ‖a‖) (θ : ℝ) :
    ‖a‖ - ε ≤ ‖(ε : ℂ) * Complex.exp (I * θ) - a‖ := by
  have _ := hεa
  have hnorm : ‖(ε : ℂ) * Complex.exp (I * θ)‖ = ε := by
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_of_nonneg hε,
      Complex.norm_exp_I_mul_ofReal, mul_one]
  have htri :
      ‖a‖ ≤ ‖(ε : ℂ) * Complex.exp (I * θ) - a‖ +
        ‖(ε : ℂ) * Complex.exp (I * θ)‖ := by
    simpa [sub_sub_cancel, add_comm] using
      norm_sub_le ((ε : ℂ) * Complex.exp (I * θ)) ((ε : ℂ) * Complex.exp (I * θ) - a)
  linarith

private lemma norm_imagAxis_sub_ge_abs_re (a : ℂ) (ω : ℝ) :
    |a.re| ≤ ‖I * (ω : ℂ) - a‖ := by
  have hre : (I * (ω : ℂ) - a).re = -a.re := by simp
  calc |a.re| = |-(a.re)| := (abs_neg a.re).symm
    _ = |(I * (ω : ℂ) - a).re| := by rw [hre]
    _ ≤ ‖I * (ω : ℂ) - a‖ := Complex.abs_re_le_norm _

lemma tendsto_indentPoleError (a : ℂ) (ha : a.re ≠ 0) :
    Tendsto (indentPoleError a) (𝓝[>] 0) (nhds 0) := by
  have ha_ne : a ≠ 0 := fun h => ha (by simp [h])
  have ha_norm_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha_ne
  have ha_half_pos : 0 < ‖a‖ / 2 := half_pos ha_norm_pos
  have hare_pos : 0 < |a.re| := abs_pos.mpr ha
  have hsemi :
      Tendsto
        (fun ε : ℝ => ∫ θ in (-Real.pi / 2)..(Real.pi / 2),
          (I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - a))
        (𝓝[>] 0) (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound :
        ∀ᶠ ε : ℝ in 𝓝[>] 0,
          ‖(∫ θ in (-Real.pi / 2)..(Real.pi / 2),
            (I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - a)) - 0‖ ≤
          (2 * Real.pi / ‖a‖) * ε := by
      filter_upwards [Ioo_mem_nhdsGT ha_half_pos] with ε hε
      rcases hε with ⟨hε_pos, hε_half⟩
      have hε_le : ε ≤ ‖a‖ := by linarith
      have hpoint :
          ∀ θ ∈ Set.uIoc (-Real.pi / 2) (Real.pi / 2),
            ‖(I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - a)‖ ≤
              (2 / ‖a‖) * ε := by
        intro θ _
        have hden : ‖a‖ / 2 ≤ ‖(ε : ℂ) * Complex.exp (I * θ) - a‖ := by
          have := norm_circle_sub_pole_ge_of_lt a hε_pos.le hε_le θ
          linarith
        have hnum : ‖I * (ε : ℂ) * Complex.exp (I * θ)‖ = ε := by
          rw [norm_mul, norm_mul, norm_I, one_mul, Complex.norm_real,
            Real.norm_of_nonneg hε_pos.le, Complex.norm_exp_I_mul_ofReal, mul_one]
        rw [norm_div, hnum]
        calc ε / ‖(ε : ℂ) * Complex.exp (I * θ) - a‖
            ≤ ε / (‖a‖ / 2) := div_le_div_of_nonneg_left hε_pos.le ha_half_pos hden
          _ = (2 / ‖a‖) * ε := by ring
      have hpi : |Real.pi / 2 - (-Real.pi / 2)| = Real.pi := by
        have : Real.pi / 2 - (-Real.pi / 2) = Real.pi := by ring
        rw [this, abs_of_nonneg Real.pi_pos.le]
      rw [sub_zero]
      calc ‖∫ θ in (-Real.pi / 2)..(Real.pi / 2),
            (I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - a)‖
          ≤ ((2 / ‖a‖) * ε) * |Real.pi / 2 - (-Real.pi / 2)| :=
            intervalIntegral.norm_integral_le_of_norm_le_const hpoint
        _ = (2 * Real.pi / ‖a‖) * ε := by rw [hpi]; ring
    have htend_bound :
        Tendsto (fun ε : ℝ => (2 * Real.pi / ‖a‖) * ε) (𝓝[>] 0) (nhds 0) := by
      have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (nhds 0) :=
        continuousWithinAt_id
      simpa [mul_zero] using tendsto_const_nhds.mul hid
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound htend_bound
  have himag :
      Tendsto (fun ε : ℝ => ∫ ω in (-ε)..ε, I / (I * ω - a)) (𝓝[>] 0) (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound :
        ∀ᶠ ε : ℝ in 𝓝[>] 0,
          ‖(∫ ω in (-ε)..ε, I / (I * ω - a)) - 0‖ ≤ (2 / |a.re|) * ε := by
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      have hpoint :
          ∀ ω ∈ Set.uIoc (-ε) ε, ‖I / (I * (ω : ℂ) - a)‖ ≤ 1 / |a.re| := by
        intro ω _
        rw [norm_div, norm_I]
        exact div_le_div_of_nonneg_left zero_le_one hare_pos (norm_imagAxis_sub_ge_abs_re a ω)
      have hlen : |ε - (-ε)| = 2 * ε := by
        have : ε - (-ε) = 2 * ε := by ring
        rw [this, abs_of_nonneg (by linarith)]
      rw [sub_zero]
      calc ‖∫ ω in (-ε)..ε, I / (I * (ω : ℂ) - a)‖
          ≤ (1 / |a.re|) * |ε - (-ε)| :=
            intervalIntegral.norm_integral_le_of_norm_le_const hpoint
        _ = (2 / |a.re|) * ε := by rw [hlen]; ring
    have htend_bound : Tendsto (fun ε : ℝ => (2 / |a.re|) * ε) (𝓝[>] 0) (nhds 0) := by
      have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (nhds 0) :=
        continuousWithinAt_id
      simpa [mul_zero] using tendsto_const_nhds.mul hid
    exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound htend_bound
  have hsub := hsemi.sub himag
  rw [sub_zero] at hsub
  exact hsub

/-! ### Multiset Helpers for the Indented Contour -/

private lemma nyquistIntegrand_eq_sum_roots_of_ne_zero (N D : Polynomial ℂ)
    (hD0 : D ≠ 0) (hC0 : D + N ≠ 0) {ω : ℝ}
    (hDω : D.eval (I * ω) ≠ 0) (hCω : (D + N).eval (I * ω) ≠ 0) :
    nyquistIntegrand N D ω =
      ((D + N).roots.map fun z => I / (I * ω - z)).sum -
        (D.roots.map fun p => I / (I * ω - p)).sum := by
  unfold nyquistIntegrand
  have hD_cont : ContinuousAt (fun t : ℝ => D.eval (I * t)) ω :=
    (hasDerivAt_eval_comp_I_mul_ofReal D ω).continuousAt
  have hev_ne : ∀ᶠ t : ℝ in nhds ω, D.eval (I * t) ≠ 0 :=
    hD_cont.eventually_ne hDω
  have hev_eq : (fun t : ℝ => returnDifference N D (I * t)) =ᶠ[nhds ω]
      fun t : ℝ => (D + N).eval (I * t) / D.eval (I * t) :=
    hev_ne.mono fun (_ : ℝ) ht => returnDifference_eq_div ht
  have hDerivDiv : HasDerivAt
      (fun t : ℝ => (D + N).eval (I * t) / D.eval (I * t))
      ((I * (Polynomial.derivative (D + N)).eval (I * ω) * D.eval (I * ω) -
        (D + N).eval (I * ω) * (I * (Polynomial.derivative D).eval (I * ω))) /
        (D.eval (I * ω)) ^ 2) ω :=
    (hasDerivAt_eval_comp_I_mul_ofReal (D + N) ω).div
      (hasDerivAt_eval_comp_I_mul_ofReal D ω) hDω
  have hDeriv : HasDerivAt (fun t : ℝ => returnDifference N D (I * t))
      ((I * (Polynomial.derivative (D + N)).eval (I * ω) * D.eval (I * ω) -
        (D + N).eval (I * ω) * (I * (Polynomial.derivative D).eval (I * ω))) /
        (D.eval (I * ω)) ^ 2) ω :=
    hDerivDiv.congr_of_eventuallyEq hev_eq
  rw [hDeriv.deriv, returnDifference_eq_div hDω]
  have hsplit :
      ((I * (Polynomial.derivative (D + N)).eval (I * ω) * D.eval (I * ω) -
        (D + N).eval (I * ω) * (I * (Polynomial.derivative D).eval (I * ω))) /
        (D.eval (I * ω)) ^ 2) / ((D + N).eval (I * ω) / D.eval (I * ω)) =
      I * ((Polynomial.derivative (D + N)).eval (I * ω) / (D + N).eval (I * ω)) -
        I * ((Polynomial.derivative D).eval (I * ω) / D.eval (I * ω)) := by
    field_simp [hDω, hCω]
  have hmul : ∀ (c s : ℂ) (m : Multiset ℂ),
      c * (m.map fun a => (s - a)⁻¹).sum = (m.map fun a => c / (s - a)).sum := by
    intro c s m
    induction m using Multiset.induction_on with
    | empty => simp
    | cons a m ih => simp only [Multiset.map_cons, Multiset.sum_cons, mul_add, ih, div_eq_mul_inv]
  rw [hsplit, poly_logDeriv_eq_sum_roots (D + N) hC0 (I * ω) hCω,
    poly_logDeriv_eq_sum_roots D hD0 (I * ω) hDω,
    hmul I (I * ω), hmul I (I * ω)]

private lemma exists_pos_lt_nonzero_norms (m : Multiset ℂ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ a ∈ m, a ≠ 0 → ε₀ < ‖a‖ := by
  induction m using Multiset.induction_on with
  | empty => exact ⟨1, one_pos, fun _ h => (Multiset.notMem_zero _ h).elim⟩
  | cons a m ih =>
    obtain ⟨ε₁, hε₁, hm⟩ := ih
    by_cases ha : a = 0
    · refine ⟨ε₁, hε₁, fun b hb hb0 => ?_⟩
      rcases Multiset.mem_cons.mp hb with rfl | hb'
      · exact (hb0 ha).elim
      · exact hm b hb' hb0
    · refine ⟨min ε₁ (‖a‖ / 2), lt_min hε₁ (half_pos (norm_pos_iff.mpr ha)), ?_⟩
      intro b hb hb0
      rcases Multiset.mem_cons.mp hb with rfl | hb'
      · exact lt_of_le_of_lt (min_le_right _ _) (half_lt_self (norm_pos_iff.mpr ha))
      · exact lt_of_le_of_lt (min_le_left _ _) (hm b hb' hb0)

private lemma intervalIntegrable_single_pole_imagAxis_of_zero_notMem (a : ℂ)
    (ha : a = 0 ∨ a.re ≠ 0) {u v : ℝ} (h0 : (0 : ℝ) ∉ Set.uIcc u v) :
    IntervalIntegrable (fun ω : ℝ => I / (I * ω - a)) volume u v := by
  rcases ha with rfl | hre
  · refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div₀ continuousOn_const
      ((continuous_const.mul Complex.continuous_ofReal).sub continuous_const).continuousOn ?_
    intro ω hω
    have hω0 : ω ≠ 0 := fun h => h0 (h ▸ hω)
    simp [I_ne_zero, ofReal_ne_zero.mpr hω0]
  · exact intervalIntegrable_single_pole_imagAxis a hre u v

private lemma intervalIntegrable_sum_poles_imagAxis_of_zero_notMem (m : Multiset ℂ)
    (hm : ∀ a ∈ m, a = 0 ∨ a.re ≠ 0) {u v : ℝ} (h0 : (0 : ℝ) ∉ Set.uIcc u v) :
    IntervalIntegrable (fun ω : ℝ => (m.map fun a => I / (I * ω - a)).sum) volume u v := by
  induction m using Multiset.induction_on with
  | empty => simp [intervalIntegrable_const]
  | cons a m ih =>
    have ha := hm a (Multiset.mem_cons_self a m)
    have hm' : ∀ b ∈ m, b = 0 ∨ b.re ≠ 0 := fun b hb => hm b (Multiset.mem_cons_of_mem hb)
    have h_eq : (fun ω : ℝ => ((a ::ₘ m).map fun z => I / (I * ω - z)).sum) =
        fun ω : ℝ => I / (I * ω - a) + (m.map fun z => I / (I * ω - z)).sum := by
      funext ω
      simp [Multiset.map_cons, Multiset.sum_cons]
    rw [h_eq]
    exact (intervalIntegrable_single_pole_imagAxis_of_zero_notMem a ha h0).add (ih hm')

private lemma intervalIntegrable_single_pole_circle_of_norm_ne (a : ℂ) {ε : ℝ}
    (h_ne : |ε| ≠ ‖a‖) (u v : ℝ) :
    IntervalIntegrable
      (fun θ : ℝ => (I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - a))
      volume u v := by
  have hcont_exp : Continuous (fun θ : ℝ => Complex.exp (I * θ)) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  refine (Continuous.div₀ (continuous_const.mul hcont_exp)
    ((continuous_const.mul hcont_exp).sub continuous_const) ?_).intervalIntegrable u v
  intro θ hzero
  apply h_ne
  have heq : (ε : ℂ) * Complex.exp (I * θ) = a := sub_eq_zero.mp hzero
  have hnorm : ‖(ε : ℂ) * Complex.exp (I * θ)‖ = |ε| := by
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp_I_mul_ofReal, mul_one]
  rw [← hnorm, heq]

private lemma intervalIntegrable_sum_poles_circle_of_norm_ne (m : Multiset ℂ) {ε : ℝ}
    (hm : ∀ a ∈ m, |ε| ≠ ‖a‖) (u v : ℝ) :
    IntervalIntegrable
      (fun θ : ℝ =>
        (m.map fun a => (I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - a)).sum)
      volume u v := by
  induction m using Multiset.induction_on with
  | empty => simp [intervalIntegrable_const]
  | cons a m ih =>
    have ha := hm a (Multiset.mem_cons_self a m)
    have hm' : ∀ b ∈ m, |ε| ≠ ‖b‖ := fun b hb => hm b (Multiset.mem_cons_of_mem hb)
    have h_eq :
        (fun θ : ℝ =>
          ((a ::ₘ m).map fun z =>
            (I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - z)).sum) =
          fun θ : ℝ =>
            (I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - a) +
              (m.map fun z =>
                (I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - z)).sum := by
      funext θ
      simp [Multiset.map_cons, Multiset.sum_cons]
    rw [h_eq]
    exact (intervalIntegrable_single_pole_circle_of_norm_ne a ha u v).add (ih hm')

private lemma sum_singlePoleIndentedIntegral (m : Multiset ℂ)
    (hm_zero : ∀ a ∈ m, a = 0 ∨ a.re ≠ 0) {R ε : ℝ} (hε : 0 < ε) (hR : ε ≤ R)
    (hm_ne : ∀ a ∈ m, |ε| ≠ ‖a‖) :
    (∫ ω in (-R)..(-ε), (m.map fun a => I / (I * ω - a)).sum) +
      (∫ θ in (-Real.pi / 2)..(Real.pi / 2),
        (m.map fun a => (I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - a)).sum) +
      (∫ ω in ε..R, (m.map fun a => I / (I * ω - a)).sum) =
    (m.map fun a => singlePoleIndentedIntegral a R ε).sum := by
  have h0_neg : (0 : ℝ) ∉ Set.uIcc (-R) (-ε) := by
    rw [Set.uIcc_of_le (by linarith)]
    intro hmem
    linarith [hmem.2]
  have h0_pos : (0 : ℝ) ∉ Set.uIcc ε R := by
    rw [Set.uIcc_of_le hR]
    intro hmem
    linarith [hmem.1]
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    have ha_zero := hm_zero a (Multiset.mem_cons_self a m)
    have hm_zero' : ∀ b ∈ m, b = 0 ∨ b.re ≠ 0 :=
      fun b hb => hm_zero b (Multiset.mem_cons_of_mem hb)
    have ha_ne := hm_ne a (Multiset.mem_cons_self a m)
    have hm_ne' : ∀ b ∈ m, |ε| ≠ ‖b‖ := fun b hb => hm_ne b (Multiset.mem_cons_of_mem hb)
    have h_eq1 :
        (fun ω : ℝ => ((a ::ₘ m).map fun z => I / (I * ω - z)).sum) =
          fun ω : ℝ => I / (I * ω - a) + (m.map fun z => I / (I * ω - z)).sum := by
      funext ω; simp [Multiset.map_cons, Multiset.sum_cons]
    have h_eq2 :
        (fun θ : ℝ =>
          ((a ::ₘ m).map fun z =>
            (I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - z)).sum) =
          fun θ : ℝ =>
            (I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - a) +
              (m.map fun z =>
                (I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - z)).sum := by
      funext θ; simp [Multiset.map_cons, Multiset.sum_cons]
    rw [h_eq1, h_eq2,
      intervalIntegral.integral_add
        (intervalIntegrable_single_pole_imagAxis_of_zero_notMem a ha_zero h0_neg)
        (intervalIntegrable_sum_poles_imagAxis_of_zero_notMem m hm_zero' h0_neg),
      intervalIntegral.integral_add
        (intervalIntegrable_single_pole_circle_of_norm_ne a ha_ne (-Real.pi / 2) (Real.pi / 2))
        (intervalIntegrable_sum_poles_circle_of_norm_ne m hm_ne' (-Real.pi / 2) (Real.pi / 2)),
      intervalIntegral.integral_add
        (intervalIntegrable_single_pole_imagAxis_of_zero_notMem a ha_zero h0_pos)
        (intervalIntegrable_sum_poles_imagAxis_of_zero_notMem m hm_zero' h0_pos)]
    simp only [Multiset.map_cons, Multiset.sum_cons]
    have ih' := ih hm_zero' hm_ne'
    simp only [singlePoleIndentedIntegral] at ih' ⊢
    linear_combination ih'

/-! ### Limit of Multiset Pole Sums on the Indented Contour -/

private noncomputable def singlePoleIndentedLimit (a : ℂ) (ε : ℝ) : ℂ :=
  if a = 0 then I * Real.pi
  else (if 0 < a.re then -I * Real.pi else I * Real.pi) + indentPoleError a ε

private lemma tendsto_sum_singlePoleIndentedIntegral (m : Multiset ℂ)
    (hm_zero : ∀ a ∈ m, a = 0 ∨ a.re ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hm_lt : ∀ a ∈ m, a ≠ 0 → ε < ‖a‖) :
    Tendsto (fun R : ℝ => (m.map fun a => singlePoleIndentedIntegral a R ε).sum) atTop
      (nhds (m.map fun a => singlePoleIndentedLimit a ε).sum) := by
  induction m using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.sum_zero]
    exact tendsto_const_nhds
  | cons a m ih =>
    have ha_zero := hm_zero a (Multiset.mem_cons_self a m)
    have hm_zero' : ∀ b ∈ m, b = 0 ∨ b.re ≠ 0 :=
      fun b hb => hm_zero b (Multiset.mem_cons_of_mem hb)
    have ha_lt : a ≠ 0 → ε < ‖a‖ := fun h => hm_lt a (Multiset.mem_cons_self a m) h
    have hm_lt' : ∀ b ∈ m, b ≠ 0 → ε < ‖b‖ :=
      fun b hb h => hm_lt b (Multiset.mem_cons_of_mem hb) h
    have ha_tendsto :
        Tendsto (fun R : ℝ => singlePoleIndentedIntegral a R ε) atTop
          (nhds (singlePoleIndentedLimit a ε)) := by
      unfold singlePoleIndentedLimit
      rcases ha_zero with rfl | hre
      · simp only [↓reduceIte]
        exact tendsto_indented_origin_pole ε hε
      · have ha_ne : a ≠ 0 := fun h => hre (by simp [h])
        simp only [ha_ne, ↓reduceIte]
        exact tendsto_indented_single_pole_R a hre hε (ha_lt ha_ne)
    simpa only [Multiset.map_cons, Multiset.sum_cons] using ha_tendsto.add (ih hm_zero' hm_lt')

private lemma tendsto_sum_singlePoleIndentedLimit (m : Multiset ℂ)
    (hm_zero : ∀ a ∈ m, a = 0 ∨ a.re ≠ 0) :
    Tendsto (fun ε : ℝ => (m.map fun a => singlePoleIndentedLimit a ε).sum) (𝓝[>] 0)
      (nhds ((((m.filter fun z : ℂ => z.re < 0).card + m.count 0 : ℂ) -
        ((m.filter fun z : ℂ => 0 < z.re).card : ℂ)) * (I * Real.pi))) := by
  induction m using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.sum_zero, Multiset.filter_zero, Multiset.card_zero,
      Multiset.count_zero, Nat.cast_zero, add_zero, sub_self, zero_mul]
    exact tendsto_const_nhds
  | cons a m ih =>
    have ha_zero := hm_zero a (Multiset.mem_cons_self a m)
    have hm_zero' : ∀ b ∈ m, b = 0 ∨ b.re ≠ 0 :=
      fun b hb => hm_zero b (Multiset.mem_cons_of_mem hb)
    have ih' := ih hm_zero'
    have ha_tendsto :
        Tendsto (fun ε : ℝ => singlePoleIndentedLimit a ε) (𝓝[>] 0)
          (nhds (if a = 0 then I * Real.pi
            else if 0 < a.re then -I * Real.pi else I * Real.pi)) := by
      unfold singlePoleIndentedLimit
      rcases ha_zero with rfl | hre
      · simp only [↓reduceIte]
        exact tendsto_const_nhds
      · have ha_ne : a ≠ 0 := fun h => hre (by simp [h])
        simp only [ha_ne, ↓reduceIte]
        simpa only [add_zero] using tendsto_const_nhds.add (tendsto_indentPoleError a hre)
    have hsum := ha_tendsto.add ih'
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rcases ha_zero with rfl | hre
    · have hcard_l :
          ((0 ::ₘ m).filter fun z : ℂ => z.re < 0).card =
            (m.filter fun z : ℂ => z.re < 0).card := by
        simp [Multiset.filter_cons_of_neg]
      have hcard_r :
          ((0 ::ₘ m).filter fun z : ℂ => 0 < z.re).card =
            (m.filter fun z : ℂ => 0 < z.re).card := by
        simp [Multiset.filter_cons_of_neg]
      have hcnt : (0 ::ₘ m).count 0 = m.count 0 + 1 := by
        simp [Multiset.count_cons_self]
      have hlim :
          (if (0 : ℂ) = 0 then I * Real.pi
              else if 0 < (0 : ℂ).re then -I * Real.pi else I * Real.pi) +
              (((m.filter fun z : ℂ => z.re < 0).card + m.count 0 : ℂ) -
                ((m.filter fun z : ℂ => 0 < z.re).card : ℂ)) * (I * Real.pi) =
            ((((0 ::ₘ m).filter fun z : ℂ => z.re < 0).card + (0 ::ₘ m).count 0 : ℂ) -
              (((0 ::ₘ m).filter fun z : ℂ => 0 < z.re).card : ℂ)) * (I * Real.pi) := by
        rw [hcard_l, hcard_r, hcnt]
        simp only [↓reduceIte]
        push_cast
        ring
      rw [hlim] at hsum
      exact hsum
    · have ha_ne : a ≠ 0 := fun h => hre (by simp [h])
      have hcnt : (a ::ₘ m).count 0 = m.count 0 := by
        rw [Multiset.count_cons_of_ne ha_ne.symm]
      rcases lt_or_gt_of_ne hre with hlt | hgt
      · have hnot : ¬ (0 < a.re) := not_lt.mpr hlt.le
        have hcard_l :
            ((a ::ₘ m).filter fun z : ℂ => z.re < 0).card =
              (m.filter fun z : ℂ => z.re < 0).card + 1 := by
          simp [Multiset.filter_cons_of_pos, hlt]
        have hcard_r :
            ((a ::ₘ m).filter fun z : ℂ => 0 < z.re).card =
              (m.filter fun z : ℂ => 0 < z.re).card := by
          simp [Multiset.filter_cons_of_neg, hnot]
        have hlim :
            (if a = 0 then I * Real.pi else if 0 < a.re then -I * Real.pi else I * Real.pi) +
                (((m.filter fun z : ℂ => z.re < 0).card + m.count 0 : ℂ) -
                  ((m.filter fun z : ℂ => 0 < z.re).card : ℂ)) * (I * Real.pi) =
              ((((a ::ₘ m).filter fun z : ℂ => z.re < 0).card + (a ::ₘ m).count 0 : ℂ) -
                (((a ::ₘ m).filter fun z : ℂ => 0 < z.re).card : ℂ)) * (I * Real.pi) := by
          rw [hcard_l, hcard_r, hcnt]
          simp only [ha_ne, hnot, ↓reduceIte]
          push_cast
          ring
        rw [hlim] at hsum
        exact hsum
      · have hnot : ¬ (a.re < 0) := not_lt.mpr hgt.le
        have hcard_l :
            ((a ::ₘ m).filter fun z : ℂ => z.re < 0).card =
              (m.filter fun z : ℂ => z.re < 0).card := by
          simp [Multiset.filter_cons_of_neg, hnot]
        have hcard_r :
            ((a ::ₘ m).filter fun z : ℂ => 0 < z.re).card =
              (m.filter fun z : ℂ => 0 < z.re).card + 1 := by
          simp [Multiset.filter_cons_of_pos, hgt]
        have hlim :
            (if a = 0 then I * Real.pi else if 0 < a.re then -I * Real.pi else I * Real.pi) +
                (((m.filter fun z : ℂ => z.re < 0).card + m.count 0 : ℂ) -
                  ((m.filter fun z : ℂ => 0 < z.re).card : ℂ)) * (I * Real.pi) =
              ((((a ::ₘ m).filter fun z : ℂ => z.re < 0).card + (a ::ₘ m).count 0 : ℂ) -
                (((a ::ₘ m).filter fun z : ℂ => 0 < z.re).card : ℂ)) * (I * Real.pi) := by
          rw [hcard_l, hcard_r, hcnt]
          simp only [ha_ne, hgt, ↓reduceIte]
          push_cast
          ring
        rw [hlim] at hsum
        exact hsum

/-! ### Main Indented Origin Nyquist Theorems -/

/-- **Indented-Origin Nyquist Winding Limit:**
For a proper non-degenerate system `L(s) = N(s) / D(s)` whose open-loop denominator `D` has no
nonzero imaginary-axis roots (poles at `s = 0` are allowed) and whose closed-loop polynomial
`D + N` has no imaginary-axis roots, the indented contour integral converges as `R → ∞` for all
sufficiently small `ε > 0` to `L ε`, and `L ε → P - Z` as `ε → 0⁺`. -/
theorem nyquist_indented_origin_tendsto (N D : Polynomial ℂ)
    (hProp : IsProperNonDegenerate N D)
    (hD : NoNonzeroImagAxisRoots D) (hC : NoImagAxisRoots (D + N)) :
    ∃ L : ℝ → ℂ,
      (∀ᶠ ε : ℝ in 𝓝[>] 0,
        Tendsto (fun R : ℝ => (1 / (2 * Real.pi * I)) * nyquistOriginIndentIntegral N D R ε)
          atTop (nhds (L ε))) ∧
      Tendsto L (𝓝[>] 0) (nhds ((rhpRootCount D : ℂ) - (rhpRootCount (D + N) : ℂ))) := by
  have hD0 : D ≠ 0 := hProp.1
  have hC0 : D + N ≠ 0 := hProp.2.1
  have hmD : ∀ a ∈ D.roots, a = 0 ∨ a.re ≠ 0 :=
    fun a ha => eq_zero_or_re_ne_zero_of_mem_roots hD ha
  have hmC : ∀ a ∈ (D + N).roots, a = 0 ∨ a.re ≠ 0 :=
    fun a ha => Or.inr (re_ne_zero_of_mem_roots hC ha)
  obtain ⟨ε₁, hε₁, hε₁_D⟩ := exists_pos_lt_nonzero_norms D.roots
  obtain ⟨ε₂, hε₂, hε₂_C⟩ := exists_pos_lt_nonzero_norms (D + N).roots
  let ε₀ : ℝ := min ε₁ ε₂
  have hε₀ : 0 < ε₀ := lt_min hε₁ hε₂
  let L : ℝ → ℂ := fun ε =>
    (1 / (2 * Real.pi * I)) *
      ((D + N).roots.map (fun z => singlePoleIndentedLimit z ε)).sum -
    (1 / (2 * Real.pi * I)) *
      (D.roots.map (fun p => singlePoleIndentedLimit p ε)).sum
  refine ⟨L, ?_, ?_⟩
  · filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
    rcases hε with ⟨hε_pos, hε_lt⟩
    have hε_lt₁ : ε < ε₁ := lt_of_lt_of_le hε_lt (min_le_left _ _)
    have hε_lt₂ : ε < ε₂ := lt_of_lt_of_le hε_lt (min_le_right _ _)
    have hmD_lt : ∀ a ∈ D.roots, a ≠ 0 → ε < ‖a‖ :=
      fun a ha ha0 => hε_lt₁.trans (hε₁_D a ha ha0)
    have hmC_lt : ∀ a ∈ (D + N).roots, a ≠ 0 → ε < ‖a‖ :=
      fun a ha ha0 => hε_lt₂.trans (hε₂_C a ha ha0)
    have hmD_ne : ∀ a ∈ D.roots, |ε| ≠ ‖a‖ := by
      intro a ha
      rw [abs_of_pos hε_pos]
      by_cases ha0 : a = 0
      · subst ha0; simpa using hε_pos.ne'
      · exact (hmD_lt a ha ha0).ne
    have hmC_ne : ∀ a ∈ (D + N).roots, |ε| ≠ ‖a‖ := by
      intro a ha
      rw [abs_of_pos hε_pos]
      have ha0 : a ≠ 0 := fun h => re_ne_zero_of_mem_roots hC ha (by simp [h])
      exact (hmC_lt a ha ha0).ne
    have hD_circle : ∀ θ : ℝ, D.eval (ε * Complex.exp (I * θ)) ≠ 0 := by
      intro θ heval
      have hmem : (ε : ℂ) * Complex.exp (I * θ) ∈ D.roots := (mem_roots hD0).mpr heval
      have hnorm : ‖(ε : ℂ) * Complex.exp (I * θ)‖ = |ε| := by
        rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_exp_I_mul_ofReal, mul_one]
      exact hmD_ne _ hmem hnorm.symm
    have hC_circle : ∀ θ : ℝ, (D + N).eval (ε * Complex.exp (I * θ)) ≠ 0 := by
      intro θ heval
      have hmem : (ε : ℂ) * Complex.exp (I * θ) ∈ (D + N).roots := (mem_roots hC0).mpr heval
      have hnorm : ‖(ε : ℂ) * Complex.exp (I * θ)‖ = |ε| := by
        rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_exp_I_mul_ofReal, mul_one]
      exact hmC_ne _ hmem hnorm.symm
    have htC := tendsto_sum_singlePoleIndentedIntegral (D + N).roots hmC hε_pos hmC_lt
    have htD := tendsto_sum_singlePoleIndentedIntegral D.roots hmD hε_pos hmD_lt
    have hcomb := (tendsto_const_nhds (x := 1 / (2 * (Real.pi : ℂ) * I)).mul htC).sub
      (tendsto_const_nhds (x := 1 / (2 * (Real.pi : ℂ) * I)).mul htD)
    refine hcomb.congr' ?_
    filter_upwards [eventually_ge_atTop ε] with R hR
    have h0_neg : (0 : ℝ) ∉ Set.uIcc (-R) (-ε) := by
      rw [Set.uIcc_of_le (by linarith)]
      intro hmem; linarith [hmem.2]
    have h0_pos : (0 : ℝ) ∉ Set.uIcc ε R := by
      rw [Set.uIcc_of_le hR]
      intro hmem; linarith [hmem.1]
    have heq_neg :
        ∫ ω in (-R)..(-ε), nyquistIntegrand N D ω =
          (∫ ω in (-R)..(-ε), ((D + N).roots.map fun z => I / (I * ω - z)).sum) -
            (∫ ω in (-R)..(-ε), (D.roots.map fun p => I / (I * ω - p)).sum) := by
      have hcongr :
          Set.EqOn (nyquistIntegrand N D)
            (fun ω : ℝ =>
              ((D + N).roots.map fun z => I / (I * ω - z)).sum -
                (D.roots.map fun p => I / (I * ω - p)).sum)
            (Set.uIcc (-R) (-ε)) := by
        intro ω hω
        have hω0 : ω ≠ 0 := fun h => h0_neg (h ▸ hω)
        exact nyquistIntegrand_eq_sum_roots_of_ne_zero N D hD0 hC0 (hD ω hω0) (hC ω)
      rw [intervalIntegral.integral_congr hcongr]
      exact intervalIntegral.integral_sub
        (intervalIntegrable_sum_poles_imagAxis_of_zero_notMem (D + N).roots hmC h0_neg)
        (intervalIntegrable_sum_poles_imagAxis_of_zero_notMem D.roots hmD h0_neg)
    have heq_pos :
        ∫ ω in ε..R, nyquistIntegrand N D ω =
          (∫ ω in ε..R, ((D + N).roots.map fun z => I / (I * ω - z)).sum) -
            (∫ ω in ε..R, (D.roots.map fun p => I / (I * ω - p)).sum) := by
      have hcongr :
          Set.EqOn (nyquistIntegrand N D)
            (fun ω : ℝ =>
              ((D + N).roots.map fun z => I / (I * ω - z)).sum -
                (D.roots.map fun p => I / (I * ω - p)).sum)
            (Set.uIcc ε R) := by
        intro ω hω
        have hω0 : ω ≠ 0 := fun h => h0_pos (h ▸ hω)
        exact nyquistIntegrand_eq_sum_roots_of_ne_zero N D hD0 hC0 (hD ω hω0) (hC ω)
      rw [intervalIntegral.integral_congr hcongr]
      exact intervalIntegral.integral_sub
        (intervalIntegrable_sum_poles_imagAxis_of_zero_notMem (D + N).roots hmC h0_pos)
        (intervalIntegrable_sum_poles_imagAxis_of_zero_notMem D.roots hmD h0_pos)
    have heq_semi :
        ∫ θ in (-Real.pi / 2)..(Real.pi / 2), nyquistSemiIntegrand N D ε θ =
          (∫ θ in (-Real.pi / 2)..(Real.pi / 2),
            ((D + N).roots.map fun z =>
              (I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - z)).sum) -
          (∫ θ in (-Real.pi / 2)..(Real.pi / 2),
            (D.roots.map fun p =>
              (I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - p)).sum) := by
      have hfun : nyquistSemiIntegrand N D ε = fun θ : ℝ =>
          ((D + N).roots.map fun z =>
            (I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - z)).sum -
          (D.roots.map fun p =>
            (I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - p)).sum := by
        funext θ
        exact nyquistSemiIntegrand_eq_sum_roots N D hD0 hC0 ε θ (hD_circle θ) (hC_circle θ)
      rw [hfun]
      exact intervalIntegral.integral_sub
        (intervalIntegrable_sum_poles_circle_of_norm_ne (D + N).roots hmC_ne
          (-Real.pi / 2) (Real.pi / 2))
        (intervalIntegrable_sum_poles_circle_of_norm_ne D.roots hmD_ne
          (-Real.pi / 2) (Real.pi / 2))
    have hsumC := sum_singlePoleIndentedIntegral (D + N).roots hmC hε_pos hR hmC_ne
    have hsumD := sum_singlePoleIndentedIntegral D.roots hmD hε_pos hR hmD_ne
    unfold nyquistOriginIndentIntegral
    rw [heq_neg, heq_semi, heq_pos]
    have hsplit_all :
        (∫ ω in (-R)..(-ε), ((D + N).roots.map fun z => I / (I * ω - z)).sum) -
          (∫ ω in (-R)..(-ε), (D.roots.map fun p => I / (I * ω - p)).sum) +
          ((∫ θ in (-Real.pi / 2)..(Real.pi / 2),
            ((D + N).roots.map fun z =>
              (I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - z)).sum) -
           (∫ θ in (-Real.pi / 2)..(Real.pi / 2),
            (D.roots.map fun p =>
              (I * ε * Complex.exp (I * θ)) / (ε * Complex.exp (I * θ) - p)).sum)) +
          ((∫ ω in ε..R, ((D + N).roots.map fun z => I / (I * ω - z)).sum) -
           (∫ ω in ε..R, (D.roots.map fun p => I / (I * ω - p)).sum)) =
        ((D + N).roots.map fun z => singlePoleIndentedIntegral z R ε).sum -
          (D.roots.map fun p => singlePoleIndentedIntegral p R ε).sum := by
      linear_combination hsumC - hsumD
    rw [hsplit_all]
    ring
  · have htC := tendsto_sum_singlePoleIndentedLimit (D + N).roots hmC
    have htD := tendsto_sum_singlePoleIndentedLimit D.roots hmD
    have hcomb := (tendsto_const_nhds (x := 1 / (2 * (Real.pi : ℂ) * I)).mul htC).sub
      (tendsto_const_nhds (x := 1 / (2 * (Real.pi : ℂ) * I)).mul htD)
    have hcntC : (D + N).roots.count 0 = 0 := by
      rw [Multiset.count_eq_zero]
      intro hmem
      exact re_ne_zero_of_mem_roots hC hmem (by simp)
    have hdeg_eq :
        rhpRootCount (D + N) + lhpRootCount (D + N) =
          rhpRootCount D + lhpRootCount D + originPoleCount D := by
      rw [rhpRootCount_add_lhpRootCount hC0 hC,
        rhpRootCount_add_lhpRootCount_add_originPoleCount hD0 hD, hProp.2.2]
    have h2piI : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
      simp [Real.pi_ne_zero, I_ne_zero]
    have hlim :
        1 / (2 * (Real.pi : ℂ) * I) *
            ((((((D + N).roots.filter fun z : ℂ => z.re < 0).card +
                (D + N).roots.count 0 : ℂ) -
              (((D + N).roots.filter fun z : ℂ => 0 < z.re).card : ℂ)) * (I * Real.pi))) -
          1 / (2 * (Real.pi : ℂ) * I) *
            ((((D.roots.filter fun z : ℂ => z.re < 0).card + D.roots.count 0 : ℂ) -
              ((D.roots.filter fun z : ℂ => 0 < z.re).card : ℂ)) * (I * Real.pi)) =
        (rhpRootCount D : ℂ) - (rhpRootCount (D + N) : ℂ) := by
      change 1 / (2 * (Real.pi : ℂ) * I) *
          ((((lhpRootCount (D + N) : ℂ) + ((D + N).roots.count 0 : ℂ) -
            (rhpRootCount (D + N) : ℂ)) * (I * Real.pi))) -
        1 / (2 * (Real.pi : ℂ) * I) *
          ((((lhpRootCount D : ℂ) + (originPoleCount D : ℂ) -
            (rhpRootCount D : ℂ)) * (I * Real.pi))) =
        (rhpRootCount D : ℂ) - (rhpRootCount (D + N) : ℂ)
      rw [hcntC]
      have hdeg_c :
          (rhpRootCount (D + N) : ℂ) + (lhpRootCount (D + N) : ℂ) =
            (rhpRootCount D : ℂ) + (lhpRootCount D : ℂ) + (originPoleCount D : ℂ) := by
        exact_mod_cast hdeg_eq
      have hlhp_c :
          (lhpRootCount (D + N) : ℂ) - ((lhpRootCount D : ℂ) + (originPoleCount D : ℂ)) =
            (rhpRootCount D : ℂ) - (rhpRootCount (D + N) : ℂ) := by
        linear_combination hdeg_c
      push_cast
      field_simp [h2piI, Real.pi_ne_zero, I_ne_zero]
      linear_combination hlhp_c
    rw [hlim] at hcomb
    exact hcomb

/-- **Indented-Origin Nyquist Stability Criterion:**
Under properness (`deg (D + N) = deg D`), no nonzero imaginary-axis poles of `D`, and no
imaginary-axis zeros of `D + N`, the closed-loop polynomial `D + N` is Hurwitz stable if and only
if the `R → ∞` limit `L ε` of the indented contour winding integral converges to
`rhpRootCount D` as `ε → 0⁺`. -/
theorem nyquist_indented_origin_criterion (N D : Polynomial ℂ)
    (hProp : IsProperNonDegenerate N D)
    (hD : NoNonzeroImagAxisRoots D) (hC : NoImagAxisRoots (D + N))
    (L : ℝ → ℂ)
    (hL : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      Tendsto (fun R : ℝ => (1 / (2 * Real.pi * I)) * nyquistOriginIndentIntegral N D R ε)
        atTop (nhds (L ε))) :
    IsHurwitz (D + N) ↔ Tendsto L (𝓝[>] 0) (nhds (rhpRootCount D : ℂ)) := by
  obtain ⟨L₀, hL₀_ev, hL₀_lim⟩ := nyquist_indented_origin_tendsto N D hProp hD hC
  have hLeq : L =ᶠ[𝓝[>] 0] L₀ := by
    filter_upwards [hL, hL₀_ev] with ε h1 h2
    exact tendsto_nhds_unique h1 h2
  have hL_lim :
      Tendsto L (𝓝[>] 0) (nhds ((rhpRootCount D : ℂ) - (rhpRootCount (D + N) : ℂ))) :=
    hL₀_lim.congr' hLeq.symm
  have hC0 : D + N ≠ 0 := hProp.2.1
  rw [isHurwitz_iff_rhpRootCount_eq_zero hC0 hC]
  constructor
  · intro hZ
    simpa [hZ] using hL_lim
  · intro hlim
    have heq : (rhpRootCount D : ℂ) - (rhpRootCount (D + N) : ℂ) = (rhpRootCount D : ℂ) :=
      tendsto_nhds_unique hL_lim hlim
    have hZ0 : (rhpRootCount (D + N) : ℂ) = 0 := by
      linear_combination -heq
    exact_mod_cast hZ0

/-! ### Verified Example: Integrator Plant `L(s) = K / (s (s + 1))` -/

/-- For `K > 0`, the integrator plant `L(s) = K / (s (s + 1))` is proper and non-degenerate, has
no nonzero imaginary-axis poles and no right-half-plane open-loop poles, and yields a Hurwitz-stable
closed-loop system `s (s + 1) + K` with no imaginary-axis zeros. -/
theorem example_integrator_stable (K : ℝ) (hK : 0 < K) :
    IsProperNonDegenerate (C (K : ℂ)) (X * (X + C 1)) ∧
    NoNonzeroImagAxisRoots (X * (X + C 1)) ∧
    NoImagAxisRoots (X * (X + C 1) + C (K : ℂ)) ∧
    rhpRootCount (X * (X + C 1)) = 0 ∧
    IsHurwitz (X * (X + C 1) + C (K : ℂ)) := by
  have hD0 : X * (X + C (1 : ℂ)) ≠ 0 :=
    mul_ne_zero Polynomial.X_ne_zero (Polynomial.X_add_C_ne_zero 1)
  have hdegD : (X * (X + C (1 : ℂ))).natDegree = 2 := by
    rw [Polynomial.natDegree_mul Polynomial.X_ne_zero (Polynomial.X_add_C_ne_zero 1),
      Polynomial.natDegree_X, Polynomial.natDegree_X_add_C]
  have hProp : IsProperNonDegenerate (C (K : ℂ)) (X * (X + C 1)) := by
    refine strictlyProper_implies_properNonDegenerate hD0 ?_
    rw [Polynomial.natDegree_C, hdegD]
    norm_num
  have hD_no : NoNonzeroImagAxisRoots (X * (X + C 1)) := by
    intro ω hω heval
    simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_C,
      mul_eq_zero] at heval
    rcases heval with h0 | h1
    · have : (ω : ℂ) = 0 := by simpa [I_ne_zero] using h0
      exact hω (ofReal_eq_zero.mp this)
    · have hre := congr_arg Complex.re h1
      simp at hre
  have hHurwitz : IsHurwitz (X * (X + C 1) + C (K : ℂ)) := by
    refine ⟨hProp.2.1, fun z hz => ?_⟩
    have heval : z * (z + 1) + (K : ℂ) = 0 := by
      simpa [Polynomial.IsRoot] using hz
    by_contra hnot
    have hzre : 0 ≤ z.re := not_lt.mp hnot
    have him := congr_arg Complex.im heval
    simp only [add_im, mul_im, add_re, one_re, one_im, add_zero, ofReal_im, zero_im] at him
    have him_fac : (2 * z.re + 1) * z.im = 0 := by linarith
    have h2pos : 0 < 2 * z.re + 1 := by linarith
    have hzim : z.im = 0 := (mul_eq_zero.mp him_fac).resolve_left h2pos.ne'
    have hre := congr_arg Complex.re heval
    simp only [add_re, mul_re, one_re, add_im, one_im, add_zero, ofReal_re, zero_re, hzim,
      mul_zero, sub_zero] at hre
    have hnonneg : 0 ≤ z.re * (z.re + 1) := mul_nonneg hzre (by linarith)
    linarith
  have hC_no : NoImagAxisRoots (X * (X + C 1) + C (K : ℂ)) := by
    intro ω hω
    have hlt := hHurwitz.2 (I * (ω : ℂ)) hω
    simp at hlt
  have hrhp : rhpRootCount (X * (X + C 1)) = 0 := by
    unfold rhpRootCount
    rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro z hz hpos
    have heval : z * (z + 1) = 0 := by
      simpa using (mem_roots hD0).mp hz
    rcases mul_eq_zero.mp heval with rfl | h1
    · simp at hpos
    · have hre := congr_arg Complex.re h1
      simp at hre
      linarith
  exact ⟨hProp, hD_no, hC_no, hrhp, hHurwitz⟩

end Nyquist
