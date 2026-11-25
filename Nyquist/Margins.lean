import Nyquist.Criterion
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Robustness Margins, Small-Gain Theorem, and Coprimeness

This file applies the Nyquist stability criterion to establish:
- `nyquist_small_gain_hurwitz`: the Nyquist small-gain theorem (`‖L(i ω)‖ < 1` implies
  closed-loop Hurwitz stability for open-loop stable proper non-degenerate plants);
- `nyquist_gain_margin`: homotopy/gain-margin stability along `k ∈ [0, K_max]` when
  `1 + k L(i ω)` never vanishes;
- `coprime_no_rhp_cancellation`: coprime numerator and denominator share no roots and remain
  coprime under unity negative feedback.
-/

namespace Nyquist

open Complex Polynomial MeasureTheory Filter

/-! ### Auxiliary Helpers -/

private lemma noImagAxisRoots_of_isHurwitz {p : Polynomial ℂ} (hp : IsHurwitz p) :
    NoImagAxisRoots p := by
  intro ω hzero
  have hlt := hp.2 (I * (ω : ℂ)) hzero
  simp at hlt

private lemma tendsto_abs_inv_atTop :
    Tendsto (fun ω : ℝ => |ω|⁻¹) atTop (nhds 0) := by
  refine tendsto_inv_atTop_zero.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with ω hω
  rw [abs_of_nonneg hω]

private lemma tendsto_abs_inv_atBot :
    Tendsto (fun ω : ℝ => |ω|⁻¹) atBot (nhds 0) := by
  have h : Tendsto (fun ω : ℝ => (-ω)⁻¹) atBot (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_neg_atBot_atTop
  refine h.congr' ?_
  filter_upwards [eventually_le_atBot (0 : ℝ)] with ω hω
  rw [abs_of_nonpos hω]

private lemma tendsto_eval_div_pow (Q : Polynomial ℂ) {m : ℕ} (hm : Q.natDegree ≤ m)
    (F : Filter ℝ) (hinv : Tendsto (fun ω : ℝ => |ω|⁻¹) F (nhds 0))
    (hne : ∀ᶠ ω : ℝ in F, ω ≠ 0) :
    Tendsto (fun ω : ℝ => Q.eval (I * ω) / (I * (ω : ℂ)) ^ m) F (nhds (Q.coeff m)) := by
  have hsum_tendsto :
      Tendsto
        (fun ω : ℝ =>
          ∑ i ∈ Finset.range m, Q.coeff i * (I * (ω : ℂ)) ^ i / (I * (ω : ℂ)) ^ m)
        F (nhds (∑ _ ∈ Finset.range m, (0 : ℂ))) := by
    refine tendsto_finsetSum _ fun i hi => ?_
    have him : i < m := Finset.mem_range.mp hi
    have hpow_ne : 0 < m - i := Nat.sub_pos_of_lt him
    have hnorm_tendsto :
        Tendsto (fun ω : ℝ => ‖Q.coeff i * (I * (ω : ℂ)) ^ i / (I * (ω : ℂ)) ^ m‖)
          F (nhds (‖Q.coeff i‖ * (0 : ℝ) ^ (m - i))) := by
      have hpow0 : Tendsto (fun ω : ℝ => |ω|⁻¹ ^ (m - i)) F (nhds ((0 : ℝ) ^ (m - i))) :=
        hinv.pow (m - i)
      refine (tendsto_const_nhds.mul hpow0).congr' ?_
      filter_upwards [hne] with ω hω
      have hnorm_Iw : ‖I * (ω : ℂ)‖ = |ω| := by
        rw [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      have habs_ne : |ω| ≠ 0 := abs_ne_zero.mpr hω
      rw [norm_div, norm_mul, norm_pow, norm_pow, hnorm_Iw, mul_div_assoc]
      have hdiv_pow : |ω| ^ i / |ω| ^ m = |ω|⁻¹ ^ (m - i) := by
        calc |ω| ^ i / |ω| ^ m
            = |ω| ^ i / |ω| ^ (i + (m - i)) := by rw [Nat.add_sub_of_le him.le]
          _ = |ω| ^ i / (|ω| ^ i * |ω| ^ (m - i)) := by rw [pow_add]
          _ = |ω|⁻¹ ^ (m - i) := by
              rw [div_mul_eq_div_div, div_self (pow_ne_zero i habs_ne), one_div, inv_pow]
      rw [hdiv_pow]
    rw [zero_pow hpow_ne.ne', mul_zero] at hnorm_tendsto
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm_tendsto
  simp only [Finset.sum_const_zero] at hsum_tendsto
  have hadd := hsum_tendsto.add (tendsto_const_nhds (x := Q.coeff m))
  rw [zero_add] at hadd
  refine hadd.congr' ?_
  filter_upwards [hne] with ω hω
  have hIw_ne : I * (ω : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hω)
  have hpow_ne : (I * (ω : ℂ)) ^ m ≠ 0 := pow_ne_zero m hIw_ne
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_iff.mpr hm), Finset.sum_range_succ,
    add_div, Finset.sum_div, mul_div_cancel_right₀ _ hpow_ne]

private lemma tendsto_returnDifference_atTop_and_atBot (N D : Polynomial ℂ)
    (hProp : IsProperNonDegenerate N D) :
    Tendsto (fun R : ℝ => returnDifference N D (I * R)) atTop
        (nhds ((D + N).leadingCoeff / D.leadingCoeff)) ∧
      Tendsto (fun R : ℝ => returnDifference N D (I * (-R))) atTop
        (nhds ((D + N).leadingCoeff / D.leadingCoeff)) := by
  have hD0 : D ≠ 0 := hProp.1
  have hC0 : D + N ≠ 0 := hProp.2.1
  have hdeg : (D + N).natDegree = D.natDegree := hProp.2.2
  have hDlc : D.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hD0
  have hC_top := tendsto_eval_div_pow (D + N) hdeg.le atTop
    tendsto_abs_inv_atTop (eventually_ne_atTop 0)
  have hD_top := tendsto_eval_div_pow D le_rfl atTop
    tendsto_abs_inv_atTop (eventually_ne_atTop 0)
  have hC_bot := tendsto_eval_div_pow (D + N) hdeg.le atBot
    tendsto_abs_inv_atBot (eventually_ne_atBot 0)
  have hD_bot := tendsto_eval_div_pow D le_rfl atBot
    tendsto_abs_inv_atBot (eventually_ne_atBot 0)
  have hC_top' : Tendsto (fun ω : ℝ => (D + N).eval (I * ω) / (I * (ω : ℂ)) ^ D.natDegree)
      atTop (nhds (D + N).leadingCoeff) := by
    rwa [Polynomial.leadingCoeff, hdeg]
  have hC_bot' : Tendsto (fun ω : ℝ => (D + N).eval (I * ω) / (I * (ω : ℂ)) ^ D.natDegree)
      atBot (nhds (D + N).leadingCoeff) := by
    rwa [Polynomial.leadingCoeff, hdeg]
  change Tendsto _ atTop (nhds D.leadingCoeff) at hD_top
  change Tendsto _ atBot (nhds D.leadingCoeff) at hD_bot
  have hdiv_top := hC_top'.div hD_top hDlc
  have hdiv_bot := (hC_bot'.div hD_bot hDlc).comp tendsto_neg_atTop_atBot
  have hev_top : ∀ᶠ R : ℝ in atTop, D.eval (I * R) ≠ 0 := by
    obtain ⟨R₀, _, hR₀D, _⟩ := exists_radius_above_roots N D
    filter_upwards [eventually_gt_atTop R₀] with R hR hzero
    have hmem : I * (R : ℂ) ∈ D.roots := (mem_roots hD0).mpr hzero
    have hlt := hR₀D _ hmem
    have hnorm : ‖I * (R : ℂ)‖ = |R| := by
      rw [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm] at hlt
    have hle : R ≤ |R| := le_abs_self R
    linarith
  have hev_neg : ∀ᶠ R : ℝ in atTop, D.eval (I * (-R : ℝ)) ≠ 0 := by
    obtain ⟨R₀, _, hR₀D, _⟩ := exists_radius_above_roots N D
    filter_upwards [eventually_gt_atTop R₀] with R hR hzero
    have hmem : I * ((-R : ℝ) : ℂ) ∈ D.roots := (mem_roots hD0).mpr hzero
    have hlt := hR₀D _ hmem
    have hnorm : ‖I * ((-R : ℝ) : ℂ)‖ = |R| := by
      rw [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg]
    rw [hnorm] at hlt
    have hle : R ≤ |R| := le_abs_self R
    linarith
  refine ⟨hdiv_top.congr' ?_, hdiv_bot.congr' ?_⟩
  · filter_upwards [eventually_ne_atTop (0 : ℝ), hev_top] with R hR hDR
    have hpow_ne : (I * (R : ℂ)) ^ D.natDegree ≠ 0 :=
      pow_ne_zero _ (mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hR))
    dsimp only [Pi.div_apply]
    rw [returnDifference_eq_div hDR, div_div_div_cancel_right₀ hpow_ne]
  · filter_upwards [eventually_ne_atTop (0 : ℝ), hev_neg] with R hR hDR
    have hpow_ne : (I * ((-R : ℝ) : ℂ)) ^ D.natDegree ≠ 0 :=
      pow_ne_zero _ (mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr hR)))
    dsimp only [Function.comp_def, Pi.div_apply]
    rw [Complex.ofReal_neg, returnDifference_eq_div (by simpa using hDR),
      div_div_div_cancel_right₀ (by simpa using hpow_ne)]

/-! ### Theorem 1: Nyquist Small-Gain Theorem -/

/-- **Nyquist Small-Gain Theorem:**
If the open-loop plant `D` is Hurwitz stable, `L = N / D` is proper and non-degenerate, and
`‖L(i ω)‖ < 1` for all `ω : ℝ`, then the closed-loop characteristic polynomial `D + N` is
Hurwitz stable. -/
theorem nyquist_small_gain_hurwitz (N D : Polynomial ℂ)
    (hProp : IsProperNonDegenerate N D)
    (hHurwitzD : IsHurwitz D)
    (hSG : ∀ ω : ℝ, ‖nyquistCurve N D ω‖ < 1) :
    IsHurwitz (D + N) := by
  have hD0 : D ≠ 0 := hHurwitzD.1
  have hC0 : D + N ≠ 0 := hProp.2.1
  have hD : NoImagAxisRoots D := noImagAxisRoots_of_isHurwitz hHurwitzD
  have hret_re_pos : ∀ ω : ℝ, 0 < (returnDifference N D (I * ω)).re := by
    intro ω
    have hnorm : ‖nyquistCurve N D ω‖ < 1 := hSG ω
    have hre_le : -(nyquistCurve N D ω).re ≤ ‖nyquistCurve N D ω‖ := by
      calc -(nyquistCurve N D ω).re = (-nyquistCurve N D ω).re := by simp
        _ ≤ ‖-nyquistCurve N D ω‖ := Complex.re_le_norm _
        _ = ‖nyquistCurve N D ω‖ := norm_neg _
    have hre_gt : -1 < (nyquistCurve N D ω).re := by linarith
    change 0 < (1 + nyquistCurve N D ω).re
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hret_slit : ∀ ω : ℝ, returnDifference N D (I * ω) ∈ Complex.slitPlane :=
    fun ω => Complex.mem_slitPlane_iff.mpr (Or.inl (hret_re_pos ω))
  have hret_ne : ∀ ω : ℝ, returnDifference N D (I * ω) ≠ 0 :=
    fun ω => Complex.slitPlane_ne_zero (hret_slit ω)
  have hC : NoImagAxisRoots (D + N) := by
    intro ω hzero
    apply hret_ne ω
    rw [returnDifference_eq_div (hD ω), hzero, zero_div]
  have hlog_deriv : ∀ ω : ℝ,
      HasDerivAt (fun t : ℝ => Complex.log (returnDifference N D (I * t)))
        (nyquistIntegrand N D ω) ω := by
    intro ω
    have hfun : (fun t : ℝ => returnDifference N D (I * t)) =
        fun t : ℝ => (D + N).eval (I * t) / D.eval (I * t) := by
      funext t
      exact returnDifference_eq_div (hD t)
    have hDeriv : HasDerivAt (fun t : ℝ => returnDifference N D (I * t))
        ((I * (Polynomial.derivative (D + N)).eval (I * ω) * D.eval (I * ω) -
          (D + N).eval (I * ω) * (I * (Polynomial.derivative D).eval (I * ω))) /
          (D.eval (I * ω)) ^ 2) ω := by
      rw [hfun]
      exact (hasDerivAt_eval_comp_I_mul_ofReal (D + N) ω).div
        (hasDerivAt_eval_comp_I_mul_ofReal D ω) (hD ω)
    have hDeriv' : HasDerivAt (fun t : ℝ => returnDifference N D (I * t))
        (deriv (fun t : ℝ => returnDifference N D (I * t)) ω) ω := by
      rwa [hDeriv.deriv]
    exact hDeriv'.clog_real (hret_slit ω)
  have hint : Integrable (nyquistIntegrand N D) volume :=
    nyquistIntegrand_integrable N D hProp hD hC
  have himag_eq : ∀ R : ℝ,
      nyquistImagIntegral N D R =
        Complex.log (returnDifference N D (I * R)) -
          Complex.log (returnDifference N D (I * (-R : ℝ))) := by
    intro R
    unfold nyquistImagIntegral
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun ω _ => hlog_deriv ω) hint.intervalIntegrable
  obtain ⟨htop, hbot⟩ := tendsto_returnDifference_atTop_and_atBot N D hProp
  let c : ℂ := (D + N).leadingCoeff / D.leadingCoeff
  have hc_ne : c ≠ 0 := div_ne_zero
    (Polynomial.leadingCoeff_ne_zero.mpr hC0) (Polynomial.leadingCoeff_ne_zero.mpr hD0)
  have hc_re_nonneg : 0 ≤ c.re := by
    have hre_tendsto : Tendsto (fun R : ℝ => (returnDifference N D (I * R)).re)
        atTop (nhds c.re) :=
      (Complex.continuous_re.tendsto c).comp htop
    exact ge_of_tendsto hre_tendsto (Eventually.of_forall fun R => (hret_re_pos R).le)
  have hc_slit : c ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    by_cases hre : 0 < c.re
    · exact Or.inl hre
    · refine Or.inr ?_
      have hre0 : c.re = 0 := le_antisymm (not_lt.mp hre) hc_re_nonneg
      intro him0
      apply hc_ne
      exact Complex.ext hre0 him0
  have hlog_top :
      Tendsto (fun R : ℝ => Complex.log (returnDifference N D (I * R)))
        atTop (nhds (Complex.log c)) :=
    (continuousAt_clog hc_slit).tendsto.comp htop
  have hlog_bot :
      Tendsto (fun R : ℝ => Complex.log (returnDifference N D (I * (-R : ℝ))))
        atTop (nhds (Complex.log c)) :=
    (continuousAt_clog hc_slit).tendsto.comp hbot
  have htend_log : Tendsto (nyquistImagIntegral N D) atTop (nhds 0) := by
    have hsub := hlog_top.sub hlog_bot
    rw [sub_self] at hsub
    exact hsub.congr fun R => (himag_eq R).symm
  have htend_int : Tendsto (nyquistImagIntegral N D) atTop
      (nhds (∫ ω : ℝ, nyquistIntegrand N D ω)) :=
    intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
  have hint_zero : (∫ ω : ℝ, nyquistIntegrand N D ω) = 0 :=
    tendsto_nhds_unique htend_int htend_log
  have hcw_zero : nyquistEncirclementsCW N D = 0 := by
    unfold nyquistEncirclementsCW nyquistEncirclementsCCW
    rw [hint_zero, mul_zero, neg_zero]
  exact (nyquist_stability_criterion_openLoopStable N D hProp hHurwitzD hC).mpr hcw_zero

/-! ### Theorem 2: Nyquist Gain Margin -/

private lemma nyquistIntegrand_gain_eq (N D : Polynomial ℂ) (hD : NoImagAxisRoots D)
    (k ω : ℝ) :
    nyquistIntegrand (C (k : ℂ) * N) D ω =
      ((k : ℂ) * I *
        ((D * Polynomial.derivative N - N * Polynomial.derivative D).eval (I * ω) /
          D.eval (I * ω) ^ 2)) /
        (1 + (k : ℂ) * nyquistCurve N D ω) := by
  let P : Polynomial ℂ := D * Polynomial.derivative N - N * Polynomial.derivative D
  have hfun : (fun t : ℝ => returnDifference (C (k : ℂ) * N) D (I * t)) =
      fun t : ℝ => 1 + (k : ℂ) * (N.eval (I * t) / D.eval (I * t)) := by
    funext t
    unfold returnDifference evalTransfer
    simp [Polynomial.eval_mul, Polynomial.eval_C, mul_div_assoc]
  have hdiv : HasDerivAt (fun t : ℝ => N.eval (I * t) / D.eval (I * t))
      ((I * (Polynomial.derivative N).eval (I * ω) * D.eval (I * ω) -
        N.eval (I * ω) * (I * (Polynomial.derivative D).eval (I * ω))) /
        D.eval (I * ω) ^ 2) ω :=
    (hasDerivAt_eval_comp_I_mul_ofReal N ω).div (hasDerivAt_eval_comp_I_mul_ofReal D ω) (hD ω)
  have hret_deriv : HasDerivAt (fun t : ℝ => returnDifference (C (k : ℂ) * N) D (I * t))
      ((k : ℂ) * ((I * (Polynomial.derivative N).eval (I * ω) * D.eval (I * ω) -
        N.eval (I * ω) * (I * (Polynomial.derivative D).eval (I * ω))) /
        D.eval (I * ω) ^ 2)) ω := by
    rw [hfun]
    convert (hasDerivAt_const ω (1 : ℂ)).add (hdiv.const_mul (k : ℂ)) using 1
    rw [zero_add]
  unfold nyquistIntegrand
  rw [hret_deriv.deriv]
  have hret_val : returnDifference (C (k : ℂ) * N) D (I * ω) =
      1 + (k : ℂ) * nyquistCurve N D ω := by
    unfold returnDifference nyquistCurve evalTransfer
    simp [Polynomial.eval_mul, Polynomial.eval_C, mul_div_assoc]
  rw [hret_val]
  congr 1
  have hP_eval : P.eval (I * ω) =
      D.eval (I * ω) * (Polynomial.derivative N).eval (I * ω) -
        N.eval (I * ω) * (Polynomial.derivative D).eval (I * ω) := by
    simp [P, Polynomial.eval_sub, Polynomial.eval_mul]
  rw [hP_eval]
  ring

private lemma tendsto_nyquistCurve_zero (N D : Polynomial ℂ)
    (hD0 : D ≠ 0) (hdeg : N.natDegree < D.natDegree) :
    Tendsto (fun ω : ℝ => ‖nyquistCurve N D ω‖) atTop (nhds 0) ∧
      Tendsto (fun ω : ℝ => ‖nyquistCurve N D ω‖) atBot (nhds 0) := by
  have hDlc : D.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hD0
  have hNcoeff : N.coeff D.natDegree = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hdeg
  have hN_top := tendsto_eval_div_pow N hdeg.le atTop
    tendsto_abs_inv_atTop (eventually_ne_atTop 0)
  have hD_top := tendsto_eval_div_pow D le_rfl atTop
    tendsto_abs_inv_atTop (eventually_ne_atTop 0)
  have hN_bot := tendsto_eval_div_pow N hdeg.le atBot
    tendsto_abs_inv_atBot (eventually_ne_atBot 0)
  have hD_bot := tendsto_eval_div_pow D le_rfl atBot
    tendsto_abs_inv_atBot (eventually_ne_atBot 0)
  rw [hNcoeff] at hN_top hN_bot
  rw [← Polynomial.leadingCoeff] at hD_top hD_bot
  have hdiv_top := hN_top.div hD_top hDlc
  have hdiv_bot := hN_bot.div hD_bot hDlc
  rw [zero_div] at hdiv_top hdiv_bot
  have hev_top : ∀ᶠ ω : ℝ in atTop, nyquistCurve N D ω =
      (N.eval (I * ω) / (I * (ω : ℂ)) ^ D.natDegree) /
        (D.eval (I * ω) / (I * (ω : ℂ)) ^ D.natDegree) := by
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with ω hω
    have hpow_ne : (I * (ω : ℂ)) ^ D.natDegree ≠ 0 :=
      pow_ne_zero _ (mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hω))
    unfold nyquistCurve evalTransfer
    rw [div_div_div_cancel_right₀ hpow_ne]
  have hev_bot : ∀ᶠ ω : ℝ in atBot, nyquistCurve N D ω =
      (N.eval (I * ω) / (I * (ω : ℂ)) ^ D.natDegree) /
        (D.eval (I * ω) / (I * (ω : ℂ)) ^ D.natDegree) := by
    filter_upwards [eventually_ne_atBot (0 : ℝ)] with ω hω
    have hpow_ne : (I * (ω : ℂ)) ^ D.natDegree ≠ 0 :=
      pow_ne_zero _ (mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hω))
    unfold nyquistCurve evalTransfer
    rw [div_div_div_cancel_right₀ hpow_ne]
  exact ⟨(hdiv_top.congr' (hev_top.mono fun _ h => h.symm)).norm.trans (by simp),
    (hdiv_bot.congr' (hev_bot.mono fun _ h => h.symm)).norm.trans (by simp)⟩

private lemma exists_lower_bound_one_add_mul_nyquistCurve (N D : Polynomial ℂ)
    (hHurwitzD : IsHurwitz D) (hdeg : N.natDegree < D.natDegree)
    {K_max : ℝ} (hK : 0 ≤ K_max)
    (hNoZero :
      ∀ k ∈ Set.Icc (0 : ℝ) K_max, ∀ ω : ℝ, 1 + (k : ℂ) * nyquistCurve N D ω ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ k ∈ Set.Icc (0 : ℝ) K_max, ∀ ω : ℝ,
        δ ≤ ‖1 + (k : ℂ) * nyquistCurve N D ω‖ := by
  have hD : NoImagAxisRoots D := noImagAxisRoots_of_isHurwitz hHurwitzD
  obtain ⟨htop, hbot⟩ := tendsto_nyquistCurve_zero N D hHurwitzD.1 hdeg
  have hK1 : 0 < K_max + 1 := by linarith
  have heps : 0 < 1 / (2 * (K_max + 1)) := by positivity
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.mp (htop.eventually (Metric.ball_mem_nhds 0 heps))
  obtain ⟨R₂, hR₂⟩ := eventually_atBot.mp (hbot.eventually (Metric.ball_mem_nhds 0 heps))
  let R₀ : ℝ := max 1 (max R₁ (-R₂))
  have hR₀_nonneg : 0 ≤ R₀ := by positivity
  have hcont_L : Continuous (nyquistCurve N D) := by
    unfold nyquistCurve evalTransfer
    refine Continuous.div ?_ ?_ (fun ω => hD ω)
    · exact N.continuous.comp (continuous_const.mul continuous_ofReal)
    · exact D.continuous.comp (continuous_const.mul continuous_ofReal)
  let f : ℝ × ℝ → ℝ := fun p => ‖1 + (p.1 : ℂ) * nyquistCurve N D p.2‖
  have hcont_f : Continuous f := by
    refine Continuous.norm ?_
    refine continuous_const.add ?_
    exact (continuous_ofReal.comp continuous_fst).mul (hcont_L.comp continuous_snd)
  let S : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) K_max ×ˢ Set.Icc (-R₀) R₀
  have hS_compact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hS_ne : S.Nonempty :=
    ⟨(0, 0), ⟨le_rfl, hK⟩, ⟨neg_nonpos.mpr hR₀_nonneg, hR₀_nonneg⟩⟩
  obtain ⟨⟨k₀, ω₀⟩, hk₀S, hk₀min⟩ :=
    hS_compact.exists_isMinOn hS_ne hcont_f.continuousOn
  have hk₀_mem : k₀ ∈ Set.Icc (0 : ℝ) K_max := hk₀S.1
  have hδ₀_pos : 0 < f (k₀, ω₀) := norm_pos_iff.mpr (hNoZero k₀ hk₀_mem ω₀)
  refine ⟨min (1 / 2) (f (k₀, ω₀)), lt_min (by norm_num) hδ₀_pos, fun k hk ω => ?_⟩
  by_cases hω : ω ∈ Set.Icc (-R₀) R₀
  · have hmin : f (k₀, ω₀) ≤ f (k, ω) := hk₀min ⟨hk, hω⟩
    exact (min_le_right _ _).trans hmin
  · refine (min_le_left _ _).trans ?_
    have hL_le : ‖nyquistCurve N D ω‖ ≤ 1 / (2 * (K_max + 1)) := by
      rcases not_and_or.mp hω with hlt | hgt
      · have hω_le : ω ≤ R₂ := by
          have : -R₂ ≤ R₀ := le_trans (le_max_right _ _) (le_max_right _ _)
          linarith [not_le.mp hlt]
        have hd := hR₂ ω hω_le
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hd
        exact hd.le
      · have hω_ge : R₁ ≤ ω := by
          have : R₁ ≤ R₀ := le_trans (le_max_left _ _) (le_max_right _ _)
          linarith [not_le.mp hgt]
        have hd := hR₁ ω hω_ge
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hd
        exact hd.le
    have hmul_le : ‖(k : ℂ) * nyquistCurve N D ω‖ ≤ 1 / 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk.1]
      calc k * ‖nyquistCurve N D ω‖
          ≤ (K_max + 1) * (1 / (2 * (K_max + 1))) :=
            mul_le_mul (by linarith [hk.2]) hL_le (norm_nonneg _) hK1.le
        _ = 1 / 2 := by field_simp [hK1.ne']
    have htri : ‖(1 : ℂ)‖ - ‖(k : ℂ) * nyquistCurve N D ω‖ ≤
        ‖1 + (k : ℂ) * nyquistCurve N D ω‖ := by
      have h := norm_sub_norm_le (1 : ℂ) (-((k : ℂ) * nyquistCurve N D ω))
      rw [sub_neg_eq_add, norm_neg] at h
      exact h
    rw [norm_one] at htri
    linarith

private lemma exists_bound_wronskian_div_D_sq (N D : Polynomial ℂ)
    (hHurwitzD : IsHurwitz D) (hdeg : N.natDegree < D.natDegree) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ ω : ℝ,
      ‖(D * Polynomial.derivative N - N * Polynomial.derivative D).eval (I * ω)‖ /
        ‖D.eval (I * ω)‖ ^ 2 ≤ C₂ * (1 + ω ^ 2)⁻¹ := by
  have hD0 : D ≠ 0 := hHurwitzD.1
  have hD : NoImagAxisRoots D := noImagAxisRoots_of_isHurwitz hHurwitzD
  let d : ℕ := D.natDegree
  have hd_pos : 1 ≤ d := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) hdeg)
  let m : ℕ := 2 * d - 2
  have hm_add : m + 2 = 2 * d := by omega
  let P : Polynomial ℂ := D * Polynomial.derivative N - N * Polynomial.derivative D
  have hP_deg : P.natDegree ≤ m := by
    have h1 : (D * Polynomial.derivative N).natDegree ≤ m := by
      by_cases hN0 : N.natDegree = 0
      · have hN_C : N = C (N.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hN0
        have hdN : Polynomial.derivative N = 0 := by rw [hN_C, Polynomial.derivative_C]
        simp [hdN]
      · have hdN_le : (Polynomial.derivative N).natDegree ≤ N.natDegree - 1 :=
          Polynomial.natDegree_derivative_le N
        have hdN_le' : (Polynomial.derivative N).natDegree ≤ d - 2 := by omega
        calc (D * Polynomial.derivative N).natDegree
            ≤ d + (Polynomial.derivative N).natDegree := Polynomial.natDegree_mul_le
          _ ≤ d + (d - 2) := Nat.add_le_add_left hdN_le' d
          _ = m := by omega
    have h2 : (N * Polynomial.derivative D).natDegree ≤ m := by
      have hdD_le : (Polynomial.derivative D).natDegree ≤ d - 1 :=
        Polynomial.natDegree_derivative_le D
      calc (N * Polynomial.derivative D).natDegree
          ≤ N.natDegree + (Polynomial.derivative D).natDegree := Polynomial.natDegree_mul_le
        _ ≤ (d - 1) + (d - 1) := Nat.add_le_add (by omega) hdD_le
        _ = m := by omega
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le h1 h2)
  let h : ℝ → ℝ :=
    fun ω => (1 + ω ^ 2) * (‖P.eval (I * ω)‖ / ‖D.eval (I * ω)‖ ^ 2)
  have hcont_h : Continuous h := by
    refine (continuous_const.add (continuous_pow 2)).mul ?_
    refine Continuous.div ?_ ?_ (fun ω => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hD ω)))
    · exact (P.continuous.comp (continuous_const.mul continuous_ofReal)).norm
    · exact ((D.continuous.comp (continuous_const.mul continuous_ofReal)).norm).pow 2
  have hDlc : D.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hD0
  have hDlc_norm_pos : 0 < ‖D.leadingCoeff‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hDlc)
  let L : ℝ := ‖P.coeff m‖ / ‖D.leadingCoeff‖ ^ 2
  have h_tendsto : ∀ (F : Filter ℝ),
      Tendsto (fun ω : ℝ => |ω|⁻¹) F (nhds 0) → (∀ᶠ ω : ℝ in F, ω ≠ 0) →
      Tendsto h F (nhds L) := by
    intro F hinv hne
    have hP_ten := (tendsto_eval_div_pow P hP_deg F hinv hne).norm
    have hD_ten := (tendsto_eval_div_pow D le_rfl F hinv hne).norm.pow 2
    rw [← Polynomial.leadingCoeff] at hD_ten
    have h1w_ten : Tendsto (fun ω : ℝ => (1 + ω ^ 2) / ω ^ 2) F (nhds 1) := by
      have hinv2 : Tendsto (fun ω : ℝ => |ω|⁻¹ ^ 2) F (nhds ((0 : ℝ) ^ 2)) := hinv.pow 2
      rw [zero_pow two_ne_zero] at hinv2
      have hadd := hinv2.add (tendsto_const_nhds (x := (1 : ℝ)))
      rw [zero_add] at hadd
      refine hadd.congr' ?_
      filter_upwards [hne] with ω hω
      have hsq : |ω| ^ 2 = ω ^ 2 := sq_abs ω
      rw [inv_pow, hsq]
      field_simp [hω]
    have hcomb := (h1w_ten.mul hP_ten).div hD_ten hDlc_norm_pos.ne'
    have hlim : 1 * ‖P.coeff m‖ / ‖D.leadingCoeff‖ ^ 2 = L := by simp [L]
    rw [hlim] at hcomb
    refine hcomb.congr' ?_
    filter_upwards [hne] with ω hω
    have hnorm_Iw : ‖I * (ω : ℂ)‖ = |ω| := by
      rw [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have habs_ne : |ω| ≠ 0 := abs_ne_zero.mpr hω
    dsimp only [h, Pi.div_apply, Pi.mul_apply]
    rw [norm_div, norm_div, norm_pow, norm_pow, hnorm_Iw, div_pow, ← pow_mul]
    have hpow_eq : |ω| ^ (D.natDegree * 2) = ω ^ 2 * |ω| ^ m := by
      rw [← sq_abs ω, ← pow_add, show 2 + m = D.natDegree * 2 by omega]
    field_simp [hω, habs_ne]
    rw [hpow_eq]
    ring
  have htop := h_tendsto atTop tendsto_abs_inv_atTop (eventually_ne_atTop 0)
  have hbot := h_tendsto atBot tendsto_abs_inv_atBot (eventually_ne_atBot 0)
  obtain ⟨R₁, hR₁⟩ :=
    eventually_atTop.mp (htop.eventually (ge_mem_nhds (by linarith : L < L + 1)))
  obtain ⟨R₂, hR₂⟩ :=
    eventually_atBot.mp (hbot.eventually (ge_mem_nhds (by linarith : L < L + 1)))
  let R : ℝ := max 1 (max R₁ (-R₂))
  have hR_nonneg : 0 ≤ R := by positivity
  have hIcc_ne : (Set.Icc (-R) R).Nonempty := ⟨0, neg_nonpos.mpr hR_nonneg, hR_nonneg⟩
  obtain ⟨ω₀, _, hω₀max⟩ := isCompact_Icc.exists_isMaxOn hIcc_ne hcont_h.continuousOn
  let C₂ : ℝ := max (L + 1) (h ω₀)
  have hL_nonneg : 0 ≤ L := div_nonneg (norm_nonneg _) (sq_nonneg _)
  have hC₂_nonneg : 0 ≤ C₂ := le_trans (by linarith) (le_max_left _ _)
  refine ⟨C₂, hC₂_nonneg, fun ω => ?_⟩
  have h_le_C₂ : h ω ≤ C₂ := by
    by_cases hω : ω ∈ Set.Icc (-R) R
    · exact (hω₀max hω).trans (le_max_right _ _)
    · refine le_trans ?_ (le_max_left _ _)
      rcases not_and_or.mp hω with hlt | hgt
      · have hω_le : ω ≤ R₂ := by
          have : -R₂ ≤ R := le_trans (le_max_right _ _) (le_max_right _ _)
          linarith [not_le.mp hlt]
        exact hR₂ ω hω_le
      · have hω_ge : R₁ ≤ ω := by
          have : R₁ ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
          linarith [not_le.mp hgt]
        exact hR₁ ω hω_ge
  have h1w_pos : 0 < 1 + ω ^ 2 := by positivity
  dsimp only [h] at h_le_C₂
  rw [div_eq_mul_inv] at h_le_C₂ ⊢
  calc ‖P.eval (I * ω)‖ * (‖D.eval (I * ω)‖ ^ 2)⁻¹
      = ((1 + ω ^ 2) * (‖P.eval (I * ω)‖ * (‖D.eval (I * ω)‖ ^ 2)⁻¹)) *
          (1 + ω ^ 2)⁻¹ := by
        field_simp [h1w_pos.ne']
    _ ≤ C₂ * (1 + ω ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right h_le_C₂ (inv_nonneg.mpr h1w_pos.le)

/-- **Nyquist Gain Margin Theorem:**
If `D` is Hurwitz stable, `deg N < deg D`, and the return difference `1 + k L(i ω)` never
vanishes for `k ∈ [0, K_max]` and `ω : ℝ`, then `D + k N` is Hurwitz stable for every
`k ∈ [0, K_max]`. -/
theorem nyquist_gain_margin (N D : Polynomial ℂ)
    (hHurwitzD : IsHurwitz D) (hdeg : N.natDegree < D.natDegree)
    {K_max : ℝ} (hK : 0 ≤ K_max)
    (hNoZero :
      ∀ k ∈ Set.Icc (0 : ℝ) K_max, ∀ ω : ℝ, 1 + (k : ℂ) * nyquistCurve N D ω ≠ 0) :
    ∀ k ∈ Set.Icc (0 : ℝ) K_max, IsHurwitz (D + C (k : ℂ) * N) := by
  have hD0 : D ≠ 0 := hHurwitzD.1
  have hD : NoImagAxisRoots D := noImagAxisRoots_of_isHurwitz hHurwitzD
  have hrD : rhpRootCount D = 0 := (isHurwitz_iff_rhpRootCount_eq_zero hD0 hD).mp hHurwitzD
  have hdeg_k : ∀ k : ℝ, (C (k : ℂ) * N).natDegree < D.natDegree := fun k =>
    lt_of_le_of_lt (Polynomial.natDegree_C_mul_le (k : ℂ) N) hdeg
  have hProp_k : ∀ k : ℝ, IsProperNonDegenerate (C (k : ℂ) * N) D := fun k =>
    strictlyProper_implies_properNonDegenerate hD0 (hdeg_k k)
  have hC_k : ∀ k ∈ Set.Icc (0 : ℝ) K_max, NoImagAxisRoots (D + C (k : ℂ) * N) := by
    intro k hk ω hzero
    apply hNoZero k hk ω
    have hret : 1 + (k : ℂ) * nyquistCurve N D ω =
        returnDifference (C (k : ℂ) * N) D (I * ω) := by
      unfold returnDifference nyquistCurve evalTransfer
      simp [Polynomial.eval_mul, Polynomial.eval_C, mul_div_assoc]
    rw [hret, returnDifference_eq_div (hD ω), hzero, zero_div]
  obtain ⟨δ, hδ_pos, hδ_bound⟩ :=
    exists_lower_bound_one_add_mul_nyquistCurve N D hHurwitzD hdeg hK hNoZero
  obtain ⟨C₂, hC₂_nonneg, hC₂_bound⟩ :=
    exists_bound_wronskian_div_D_sq N D hHurwitzD hdeg
  let F : ℝ → ℝ → ℂ := fun k ω => nyquistIntegrand (C (k : ℂ) * N) D ω
  let C_bound : ℝ := K_max * C₂ / δ
  let bound : ℝ → ℝ := fun ω => C_bound * (1 + ω ^ 2)⁻¹
  have hF_meas : ∀ k ∈ Set.Icc (0 : ℝ) K_max, AEStronglyMeasurable (F k) volume :=
    fun k hk => (nyquistIntegrand_integrable (C (k : ℂ) * N) D (hProp_k k) hD (hC_k k hk)).1
  have h_bound :
      ∀ k ∈ Set.Icc (0 : ℝ) K_max, ∀ᵐ ω ∂volume, ‖F k ω‖ ≤ bound ω := by
    intro k hk
    refine ae_of_all _ fun ω => ?_
    dsimp only [F, bound]
    rw [nyquistIntegrand_gain_eq N D hD k ω, norm_div, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk.1, norm_I, mul_one,
      norm_div, norm_pow]
    have hden_pos : 0 < δ := hδ_pos
    have hnum_le :
        k * (‖(D * Polynomial.derivative N - N * Polynomial.derivative D).eval (I * ω)‖ /
          ‖D.eval (I * ω)‖ ^ 2) ≤ K_max * (C₂ * (1 + ω ^ 2)⁻¹) :=
      mul_le_mul hk.2 (hC₂_bound ω) (by positivity) hK
    calc k * (‖(D * Polynomial.derivative N - N * Polynomial.derivative D).eval (I * ω)‖ /
            ‖D.eval (I * ω)‖ ^ 2) / ‖1 + (k : ℂ) * nyquistCurve N D ω‖
        ≤ (K_max * (C₂ * (1 + ω ^ 2)⁻¹)) / δ :=
          div_le_div₀ (by positivity) hnum_le hden_pos (hδ_bound k hk ω)
      _ = C_bound * (1 + ω ^ 2)⁻¹ := by dsimp [C_bound]; ring
  have hbound_int : Integrable bound volume := integrable_inv_one_add_sq.const_mul C_bound
  have h_cont :
      ∀ᵐ ω ∂volume, ContinuousOn (fun k : ℝ => F k ω) (Set.Icc (0 : ℝ) K_max) := by
    refine ae_of_all _ fun ω => ?_
    let numC : ℂ :=
      (D * Polynomial.derivative N - N * Polynomial.derivative D).eval (I * ω) /
        D.eval (I * ω) ^ 2
    let b : ℂ := nyquistCurve N D ω
    have hcont_rhs : ContinuousOn (fun k : ℝ => ((k : ℂ) * I * numC) / (1 + (k : ℂ) * b))
        (Set.Icc (0 : ℝ) K_max) := by
      fun_prop (disch := intro k hk; exact hNoZero k hk ω)
    exact hcont_rhs.congr fun k _ => nyquistIntegrand_gain_eq N D hD k ω
  have hint_cont : ContinuousOn (fun k : ℝ => ∫ ω : ℝ, F k ω) (Set.Icc (0 : ℝ) K_max) :=
    continuousOn_of_dominated hF_meas h_bound hbound_int h_cont
  let g : ℝ → ℝ := fun k => (nyquistEncirclementsCW (C (k : ℂ) * N) D).re
  have hg_cont : ContinuousOn g (Set.Icc (0 : ℝ) K_max) := by
    have hcont_rhs : ContinuousOn (fun k : ℝ =>
        (-(1 / (2 * (Real.pi : ℂ) * I)) * ∫ ω : ℝ, F k ω).re) (Set.Icc (0 : ℝ) K_max) :=
      Complex.continuous_re.comp_continuousOn (continuousOn_const.mul hint_cont)
    exact hcont_rhs.congr fun k _ => by
      simp [g, nyquistEncirclementsCW, nyquistEncirclementsCCW, F]
  have hg_val : ∀ k ∈ Set.Icc (0 : ℝ) K_max,
      g k = (rhpRootCount (D + C (k : ℂ) * N) : ℝ) := by
    intro k hk
    dsimp [g]
    rw [nyquist_encirclement_formula_cw (C (k : ℂ) * N) D (hProp_k k) hD (hC_k k hk), hrD]
    simp
  have hg0 : g 0 = 0 := by
    rw [hg_val 0 ⟨le_rfl, hK⟩]
    simp [hrD]
  intro k hk
  have hZ_zero : rhpRootCount (D + C (k : ℂ) * N) = 0 := by
    by_contra hne
    have hZ_ge : 1 ≤ rhpRootCount (D + C (k : ℂ) * N) :=
      Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne)
    have hgk_ge : (1 : ℝ) ≤ g k := by
      rw [hg_val k hk]
      exact_mod_cast hZ_ge
    have hmid : (1 / 2 : ℝ) ∈ Set.Icc (g 0) (g k) := ⟨by linarith, by linarith⟩
    have hivt := intermediate_value_Icc hk.1 (hg_cont.mono (Set.Icc_subset_Icc_right hk.2))
    obtain ⟨c, hc_mem, hc_eq⟩ := hivt hmid
    have hc_Icc : c ∈ Set.Icc (0 : ℝ) K_max := ⟨hc_mem.1, hc_mem.2.trans hk.2⟩
    rw [hg_val c hc_Icc] at hc_eq
    have hnat_eq : (2 : ℝ) * (rhpRootCount (D + C (c : ℂ) * N) : ℝ) = 1 := by linarith
    have hnat : 2 * rhpRootCount (D + C (c : ℂ) * N) = 1 := by exact_mod_cast hnat_eq
    omega
  exact (isHurwitz_iff_rhpRootCount_eq_zero (hProp_k k).2.1 (hC_k k hk)).mpr hZ_zero

/-! ### Theorem 3: Coprime No RHP Cancellation -/

/-- If `N` and `D` are coprime polynomials over `ℂ`, then `D` and `D + N` share no roots
(in particular no RHP pole-zero cancellations occur) and `D + N` remains coprime to `D`. -/
theorem coprime_no_rhp_cancellation (N D : Polynomial ℂ) (hcop : IsCoprime N D) :
    (∀ z : ℂ, D.IsRoot z → ¬ (D + N).IsRoot z) ∧ IsCoprime (D + N) D := by
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨?_, ⟨a, b - a, by linear_combination hab⟩⟩
  intro z hzD hzC
  have hDz : D.eval z = 0 := hzD
  have hCz : (D + N).eval z = 0 := hzC
  have hNz : N.eval z = 0 := by
    rw [Polynomial.eval_add, hDz, zero_add] at hCz
    exact hCz
  have h1 := congr_arg (Polynomial.eval z) hab
  simp [hDz, hNz] at h1

end Nyquist
