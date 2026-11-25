import Nyquist.Defs
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Meromorphic.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Argument Principle, Rouché's Theorem, and Rectangle Contour Integrals

This file establishes:
1. `argumentPrinciple_circle`: the meromorphic Argument Principle on a circle `C(c, R)`.
2. `rouche_circle`: Rouché's theorem on a circle `C(c, R)`.
3. `rectBoundaryIntegral` and `argumentPrinciple_rect`: linearity, Cauchy-Goursat / residue
   evaluation of `(s - u)⁻¹` on rectangle boundaries, and the meromorphic Argument Principle
   on a rectangle `[[z.re, w.re]] ×ℂ [[z.im, w.im]]`.
-/

namespace Nyquist

open Complex Filter MeasureTheory

open scoped Interval

/-!
## Shared Meromorphic Logarithmic-Derivative Decomposition
-/

private lemma meromorphicOrderAt_sub_const_ne_top (u x : ℂ) :
    meromorphicOrderAt (fun z : ℂ => z - u) x ≠ ⊤ := by
  intro htop
  have h0 : ∀ᶠ z in nhdsWithin x {x}ᶜ, z - u = 0 := meromorphicOrderAt_eq_top_iff.mp htop
  have h1 : ∀ᶠ z in nhdsWithin x {x}ᶜ, z ≠ u := by
    by_cases hxu : x = u
    · subst hxu
      exact eventually_mem_nhdsWithin
    · exact mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds hxu)
  obtain ⟨z, hz0, hzu⟩ := (h0.and h1).exists
  exact hzu (sub_eq_zero.mp hz0)

private lemma logDeriv_sub_const (u z : ℂ) :
    logDeriv (fun t : ℂ => t - u) z = (z - u)⁻¹ := by
  rw [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]

private lemma exists_analytic_logDeriv_eq {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : MeromorphicOn f U) (hf_ne : ∀ z ∈ U, meromorphicOrderAt f z ≠ ⊤)
    (hfin : (MeromorphicOn.divisor f U).support.Finite) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ (∀ u ∈ U, g u ≠ 0) ∧
      logDeriv f =ᶠ[codiscreteWithin U]
        fun z => logDeriv g z +
          ∑ u ∈ hfin.toFinset, ((MeromorphicOn.divisor f U u : ℂ) * (z - u)⁻¹) := by
  classical
  set D := MeromorphicOn.divisor f U
  obtain ⟨g, hg_an, hg_ne, hfg⟩ := hf.extract_zeros_poles (fun u => hf_ne u.1 u.2) hfin
  refine ⟨g, hg_an, fun u hu => hg_ne ⟨u, hu⟩, ?_⟩
  have h1 : logDeriv f =ᶠ[codiscreteWithin U] logDeriv (Function.factorizedRational D * g) :=
    logDeriv_congr_codiscreteWithin hU hfg
  have hφ : MeromorphicOn (Function.factorizedRational D) U :=
    (Function.FactorizedRational.meromorphicNFOn D U).meromorphicOn
  have hφ_ne : ∀ z ∈ U, meromorphicOrderAt (Function.factorizedRational D) z ≠ ⊤ :=
    fun z _ => Function.FactorizedRational.meromorphicOrderAt_ne_top D
  have hg_ne' : ∀ z ∈ U, meromorphicOrderAt g z ≠ ⊤ := by
    intro z hz
    rw [(hg_an z hz).meromorphicOrderAt_eq,
      (hg_an z hz).analyticOrderAt_eq_zero.mpr (hg_ne ⟨z, hz⟩)]
    simp
  have h2 : logDeriv (Function.factorizedRational D * g) =ᶠ[codiscreteWithin U]
      logDeriv (Function.factorizedRational D) + logDeriv g :=
    MeromorphicOn.logDeriv_mul_eventuallyEq hφ hg_an.meromorphicOn hφ_ne hg_ne'
  have h3 : logDeriv (Function.factorizedRational D) =ᶠ[codiscreteWithin U]
      fun z => ∑ᶠ u, D u • logDeriv (fun t : ℂ => t - u) z := by
    change logDeriv (∏ᶠ u, (fun t : ℂ => t - u) ^ D u) =ᶠ[codiscreteWithin U] _
    exact MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq hfin
      (fun u => (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn)
      (fun u x _ => meromorphicOrderAt_sub_const_ne_top u x)
  have h4 : (fun z => ∑ᶠ u, D u • logDeriv (fun t : ℂ => t - u) z) =
      fun z => ∑ u ∈ hfin.toFinset, (D u : ℂ) * (z - u)⁻¹ := by
    ext z
    have hsub : Function.support (fun u => D u • logDeriv (fun t : ℂ => t - u) z) ⊆
        hfin.toFinset := by
      intro u hu
      simp only [Function.mem_support, ne_eq, zsmul_eq_mul, mul_eq_zero, Int.cast_eq_zero] at hu
      exact hfin.mem_toFinset.mpr fun h0 => hu (Or.inl h0)
    rw [finsum_eq_sum_of_support_subset _ hsub]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [zsmul_eq_mul, logDeriv_sub_const]
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
  rw [hz1, hz2]
  simp only [Pi.add_apply, hz3]
  rw [add_comm, congrFun h4 z]

private lemma differentiableOn_logDeriv_of_analyticOnNhd {g : ℂ → ℂ} {U : Set ℂ}
    (hg_an : AnalyticOnNhd ℂ g U) (hg_ne : ∀ u ∈ U, g u ≠ 0) :
    DifferentiableOn ℂ (logDeriv g) U := by
  intro z hz
  have hdiff : DifferentiableAt ℂ g z := (hg_an z hz).differentiableAt
  have hderiv : DifferentiableAt ℂ (deriv g) z := (hg_an.deriv z hz).differentiableAt
  exact (hderiv.div hdiff (hg_ne z hz)).differentiableWithinAt

/-!
## 1. Argument Principle on a Circle
-/

/-- The meromorphic Argument Principle on a circle `C(c, R)`:
`(2πi)⁻¹ ∮_{C(c, R)} (f'/f)(z) dz` equals the sum of the orders of zeros minus poles of `f`
inside the open ball `Metric.ball c R`. -/
theorem argumentPrinciple_circle {c : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hcU : Metric.closedBall c R ⊆ U) (hf : MeromorphicOn f U)
    (hf_ne : ∀ z ∈ U, meromorphicOrderAt f z ≠ ⊤)
    (hfin : (MeromorphicOn.divisor f U).support.Finite)
    (hS : ∀ z ∈ Metric.sphere c R, meromorphicOrderAt f z = 0) :
    (2 * Real.pi * I)⁻¹ * (∮ z in C(c, R), logDeriv f z) =
      ∑ᶠ u ∈ Metric.ball c R, ((meromorphicOrderAt f u).untop₀ : ℂ) := by
  classical
  set D := MeromorphicOn.divisor f U
  obtain ⟨g, hg_an, hg_ne, hfg⟩ := exists_analytic_logDeriv_eq hU hf hf_ne hfin
  have hsphere_sub : Metric.sphere c |R| ⊆ U := by
    rw [abs_of_pos hR]
    exact Metric.sphere_subset_closedBall.trans hcU
  have hfg_sphere : logDeriv f =ᶠ[codiscreteWithin (Metric.sphere c |R|)]
      fun z => logDeriv g z + ∑ u ∈ hfin.toFinset, (D u : ℂ) * (z - u)⁻¹ :=
    hfg.filter_mono (codiscreteWithin_mono hsphere_sub)
  rw [circleIntegral.circleIntegral_congr_codiscreteWithin hfg_sphere hR.ne']
  have hlog_diff : DifferentiableOn ℂ (logDeriv g) U :=
    differentiableOn_logDeriv_of_analyticOnNhd hg_an hg_ne
  have hg_int : CircleIntegrable (logDeriv g) c R := by
    apply ContinuousOn.circleIntegrable'
    exact (hlog_diff.mono hsphere_sub).continuousOn
  have hu_not_sphere : ∀ u ∈ hfin.toFinset, u ∉ Metric.sphere c R := by
    intro u hu hus
    have hu_supp : u ∈ D.support := hfin.mem_toFinset.mp hu
    have hu_U : u ∈ U := hcU (Metric.sphere_subset_closedBall hus)
    have hD_eq : D u = (meromorphicOrderAt f u).untop₀ := hf.divisor_apply hu_U
    rw [Function.mem_support, hD_eq, hS u hus] at hu_supp
    exact hu_supp rfl
  have hu_int : ∀ u ∈ hfin.toFinset,
      CircleIntegrable (fun z => (D u : ℂ) * (z - u)⁻¹) c R := by
    intro u hu
    have hus : u ∉ Metric.sphere c |R| := by
      rw [abs_of_pos hR]
      exact hu_not_sphere u hu
    exact (circleIntegrable_sub_inv_iff.mpr (Or.inr hus)).const_mul (D u : ℂ)
  have hsum_int :
      CircleIntegrable (fun z => ∑ u ∈ hfin.toFinset, (D u : ℂ) * (z - u)⁻¹) c R :=
    CircleIntegrable.fun_sum hfin.toFinset hu_int
  rw [circleIntegral.integral_add hg_int hsum_int]
  have hg_zero : (∮ z in C(c, R), logDeriv g z) = 0 := by
    refine circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le Set.countable_empty
      (hlog_diff.mono hcU).continuousOn fun z hz => ?_
    exact (hlog_diff z (hcU (Metric.ball_subset_closedBall hz.1))).differentiableAt
      (hU.mem_nhds (hcU (Metric.ball_subset_closedBall hz.1)))
  rw [hg_zero, zero_add, circleIntegral.integral_fun_sum hu_int]
  have hterm : ∀ u ∈ hfin.toFinset,
      (∮ z in C(c, R), (D u : ℂ) * (z - u)⁻¹) =
        if u ∈ Metric.ball c R then (D u : ℂ) * (2 * Real.pi * I) else 0 := by
    intro u hu
    rw [circleIntegral.integral_const_mul]
    split_ifs with hub
    · rw [circleIntegral.integral_sub_inv_of_mem_ball hub]
    · have hucb : u ∉ Metric.closedBall c R := by
        intro hcb
        rcases lt_or_eq_of_le (Metric.mem_closedBall.mp hcb) with hlt | heq
        · exact hub (Metric.mem_ball.mpr hlt)
        · exact hu_not_sphere u hu (Metric.mem_sphere.mpr heq)
      have hdiff_inv : DifferentiableOn ℂ (fun z => (z - u)⁻¹) (Metric.closedBall c R) := by
        intro z hz
        have hne : z - u ≠ 0 := sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hucb)
        exact ((differentiableAt_id.sub_const u).inv hne).differentiableWithinAt
      have hzero : (∮ z in C(c, R), (z - u)⁻¹) = 0 :=
        circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le Set.countable_empty
          hdiff_inv.continuousOn fun z hz =>
          (differentiableAt_id.sub_const u).inv
            (sub_ne_zero.mpr (ne_of_mem_of_not_mem (Metric.ball_subset_closedBall hz.1) hucb))
      rw [hzero, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  have h2piI : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  rw [← Finset.sum_filter, ← Finset.sum_mul, mul_left_comm, inv_mul_cancel₀ h2piI, mul_one]
  have hsum_eq : ∑ u ∈ hfin.toFinset with u ∈ Metric.ball c R, (D u : ℂ) =
      ∑ u ∈ hfin.toFinset with u ∈ Metric.ball c R,
        ((meromorphicOrderAt f u).untop₀ : ℂ) := by
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu_U : u ∈ U := hcU (Metric.ball_subset_closedBall (Finset.mem_filter.mp hu).2)
    rw [hf.divisor_apply hu_U]
  rw [hsum_eq]
  symm
  refine finsum_mem_eq_sum_of_inter_support_eq _ ?_
  ext u
  simp only [Set.mem_inter_iff, Metric.mem_ball, Function.mem_support, ne_eq,
    Int.cast_eq_zero, Finset.coe_filter, Set.mem_ofPred_eq, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨hu_ball, hu_ne⟩
    refine ⟨⟨?_, hu_ball⟩, hu_ne⟩
    have hu_U : u ∈ U := hcU (Metric.ball_subset_closedBall hu_ball)
    change D u ≠ 0
    rw [hf.divisor_apply hu_U]
    exact hu_ne
  · rintro ⟨⟨_, hu_ball⟩, hu_ne⟩
    exact ⟨hu_ball, hu_ne⟩

open scoped Classical in
/-- `Finset`-sum corollary of `argumentPrinciple_circle`: the winding integral equals the sum
of `(meromorphicOrderAt f u).untop₀` over `(hfin.toFinset.filter (· ∈ Metric.ball c R))`. -/
theorem argumentPrinciple_circle_finset {c : ℂ} {R : ℝ} (hR : 0 < R) {f : ℂ → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hcU : Metric.closedBall c R ⊆ U) (hf : MeromorphicOn f U)
    (hf_ne : ∀ z ∈ U, meromorphicOrderAt f z ≠ ⊤)
    (hfin : (MeromorphicOn.divisor f U).support.Finite)
    (hS : ∀ z ∈ Metric.sphere c R, meromorphicOrderAt f z = 0) :
    (2 * Real.pi * I)⁻¹ * (∮ z in C(c, R), logDeriv f z) =
      ∑ u ∈ hfin.toFinset with u ∈ Metric.ball c R,
        ((meromorphicOrderAt f u).untop₀ : ℂ) := by
  rw [argumentPrinciple_circle hR hU hcU hf hf_ne hfin hS]
  refine finsum_mem_eq_sum_of_inter_support_eq _ ?_
  ext u
  simp only [Set.mem_inter_iff, Metric.mem_ball, Function.mem_support, ne_eq,
    Int.cast_eq_zero, Finset.coe_filter, Set.mem_ofPred_eq, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨hu_ball, hu_ne⟩
    refine ⟨⟨?_, hu_ball⟩, hu_ne⟩
    have hu_U : u ∈ U := hcU (Metric.ball_subset_closedBall hu_ball)
    change MeromorphicOn.divisor f U u ≠ 0
    rw [hf.divisor_apply hu_U]
    exact hu_ne
  · rintro ⟨⟨_, hu_ball⟩, hu_ne⟩
    exact ⟨hu_ball, hu_ne⟩

/-!
## 2. Rouché's Theorem on a Circle
-/

private lemma exists_ball_supset_closedBall_subset {c : ℂ} {R : ℝ} (hR : 0 ≤ R) {U : Set ℂ}
    (hU : IsOpen U) (hcU : Metric.closedBall c R ⊆ U) :
    ∃ R' > R, Metric.ball c R' ⊆ U := by
  obtain ⟨δ, hδ, hthick⟩ := (isCompact_closedBall c R).exists_thickening_subset_open hU hcU
  refine ⟨R + δ, lt_add_of_pos_right R hδ, fun y hy => hthick ?_⟩
  rw [Metric.mem_thickening_iff]
  by_cases hyc : y ∈ Metric.closedBall c R
  · exact ⟨y, hyc, by simpa using hδ⟩
  · have hdist_gt : R < dist y c := not_le.mp (fun h => hyc (Metric.mem_closedBall.mpr h))
    have hdist_pos : 0 < dist y c := hR.trans_lt hdist_gt
    let z : ℂ := c + (R / dist y c) • (y - c)
    have hzc : z ∈ Metric.closedBall c R := by
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg (div_nonneg hR hdist_pos.le), ← dist_eq_norm,
        div_mul_cancel₀ _ hdist_pos.ne']
    have hyz : dist y z < δ := by
      have hyz_eq : y - z = (1 - R / dist y c) • (y - c) := by
        simp only [z, sub_smul, one_smul]
        abel
      rw [dist_eq_norm, hyz_eq, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ((div_le_one hdist_pos).mpr hdist_gt.le)),
        ← dist_eq_norm, sub_mul, one_mul, div_mul_cancel₀ _ hdist_pos.ne']
      linarith [Metric.mem_ball.mp hy]
    exact ⟨z, hzc, hyz⟩

/-- Rouché's theorem on a circle `C(c, R)`:
If `f` and `g` are analytic on an open neighborhood `U` of `Metric.closedBall c R` and
`‖g z‖ < ‖f z‖` on `Metric.sphere c R`, then `f + g` and `f` have the same number of zeros
(counted with multiplicity) in `Metric.ball c R`. -/
theorem rouche_circle {c : ℂ} {R : ℝ} (hR : 0 < R) {f g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hcU : Metric.closedBall c R ⊆ U)
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hf_ne : ∀ z ∈ U, meromorphicOrderAt f z ≠ ⊤)
    (hfin_f : (MeromorphicOn.divisor f U).support.Finite)
    (hfin_fg : (MeromorphicOn.divisor (f + g) U).support.Finite)
    (hbound : ∀ z ∈ Metric.sphere c R, ‖g z‖ < ‖f z‖) :
    ∑ᶠ u ∈ Metric.ball c R, ((meromorphicOrderAt (f + g) u).untop₀ : ℂ) =
      ∑ᶠ u ∈ Metric.ball c R, ((meromorphicOrderAt f u).untop₀ : ℂ) := by
  classical
  obtain ⟨R', hRR', hballU⟩ := exists_ball_supset_closedBall_subset hR.le hU hcU
  let U' : Set ℂ := Metric.ball c R'
  have hU' : IsOpen U' := Metric.isOpen_ball
  have hcU' : Metric.closedBall c R ⊆ U' := Metric.closedBall_subset_ball hRR'
  have hf' : AnalyticOnNhd ℂ f U' := hf.mono hballU
  have hg' : AnalyticOnNhd ℂ g U' := hg.mono hballU
  have hfg' : AnalyticOnNhd ℂ (f + g) U' := hf'.add hg'
  have hsphere_ne_f : ∀ z ∈ Metric.sphere c R, f z ≠ 0 := fun z hz =>
    norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg (g z)) (hbound z hz))
  have hsphere_ne_fg : ∀ z ∈ Metric.sphere c R, (f + g) z ≠ 0 := by
    intro z hz
    have htri : ‖f z‖ ≤ ‖(f + g) z‖ + ‖g z‖ := by
      have h := norm_add_le (f z + g z) (-g z)
      simpa using h
    exact norm_pos_iff.mp (by linarith [hbound z hz])
  have hfg_ne_top : ∀ z ∈ U', meromorphicOrderAt (f + g) z ≠ ⊤ := by
    let z₀ : ℂ := c + R
    have hz₀_sphere : z₀ ∈ Metric.sphere c R := by
      simp [z₀, abs_of_pos hR]
    have hz₀_U' : z₀ ∈ U' := hcU' (Metric.sphere_subset_closedBall hz₀_sphere)
    have hz₀_ne : meromorphicOrderAt (f + g) z₀ ≠ ⊤ := by
      rw [(hfg' z₀ hz₀_U').meromorphicOrderAt_eq,
        (hfg' z₀ hz₀_U').analyticOrderAt_eq_zero.mpr (hsphere_ne_fg z₀ hz₀_sphere)]
      simp
    intro z hz
    exact hfg'.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_ball c R').isPreconnected hz₀_U' hz hz₀_ne
  let q : ℂ → ℂ := fun z => (f z + g z) / f z
  have hq_mero : MeromorphicOn q U' := hfg'.meromorphicOn.div hf'.meromorphicOn
  have hq_ord : ∀ z ∈ U',
      meromorphicOrderAt q z = meromorphicOrderAt (f + g) z - meromorphicOrderAt f z :=
    fun z hz => meromorphicOrderAt_div (hfg'.meromorphicOn z hz) (hf'.meromorphicOn z hz)
  have hq_ne : ∀ z ∈ U', meromorphicOrderAt q z ≠ ⊤ := by
    intro z hz
    rw [hq_ord z hz]
    have h1 := hfg_ne_top z hz
    have h2 := hf_ne z (hballU hz)
    lift meromorphicOrderAt (f + g) z to ℤ using h1 with n hn
    lift meromorphicOrderAt f z to ℤ using h2 with m hm
    rw [show (n : WithTop ℤ) - (m : WithTop ℤ) = ((n - m : ℤ) : WithTop ℤ) from rfl]
    exact WithTop.coe_ne_top
  have hq_untop : ∀ z ∈ U',
      (meromorphicOrderAt q z).untop₀ =
        (meromorphicOrderAt (f + g) z).untop₀ - (meromorphicOrderAt f z).untop₀ := by
    intro z hz
    rw [hq_ord z hz]
    have h1 := hfg_ne_top z hz
    have h2 := hf_ne z (hballU hz)
    lift meromorphicOrderAt (f + g) z to ℤ using h1 with n hn
    lift meromorphicOrderAt f z to ℤ using h2 with m hm
    rw [show (n : WithTop ℤ) - (m : WithTop ℤ) = ((n - m : ℤ) : WithTop ℤ) from rfl,
      WithTop.untop₀_coe, WithTop.untop₀_coe, WithTop.untop₀_coe]
  have hq_fin : (MeromorphicOn.divisor q U').support.Finite := by
    refine (hfin_fg.union hfin_f).subset fun z hz => ?_
    rw [Function.mem_support] at hz
    have hz_U' : z ∈ U' := by
      by_contra hnot
      exact hz (by simp [hnot])
    have hz_U : z ∈ U := hballU hz_U'
    have hdiv_eq : MeromorphicOn.divisor q U' z =
        MeromorphicOn.divisor (f + g) U z - MeromorphicOn.divisor f U z := by
      rw [hq_mero.divisor_apply hz_U', hq_untop z hz_U',
        (hf.add hg).meromorphicOn.divisor_apply hz_U, hf.meromorphicOn.divisor_apply hz_U]
    rw [hdiv_eq] at hz
    by_contra hnot
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hnot
    exact hz (by simp [hnot.1, hnot.2])
  have hq_sphere : ∀ z ∈ Metric.sphere c R, meromorphicOrderAt q z = 0 := by
    intro z hz
    have hz_U' : z ∈ U' := hcU' (Metric.sphere_subset_closedBall hz)
    have hq_an : AnalyticAt ℂ q z := (hfg' z hz_U').div (hf' z hz_U') (hsphere_ne_f z hz)
    have hq_val : q z ≠ 0 := div_ne_zero (hsphere_ne_fg z hz) (hsphere_ne_f z hz)
    rw [hq_an.meromorphicOrderAt_eq, hq_an.analyticOrderAt_eq_zero.mpr hq_val]
    simp
  have hq_slit : ∀ z ∈ Metric.sphere c R, q z ∈ Complex.slitPlane := by
    intro z hz
    have hfz : f z ≠ 0 := hsphere_ne_f z hz
    have hq_eq : q z = 1 + g z / f z := by
      simp only [q, add_div, div_self hfz]
    have hnorm_div : ‖g z / f z‖ < 1 := by
      rw [norm_div, div_lt_one (norm_pos_iff.mpr hfz)]
      exact hbound z hz
    have hre_lt : |(g z / f z).re| < 1 := (abs_re_le_norm (g z / f z)).trans_lt hnorm_div
    have hre_pos : 0 < (q z).re := by
      rw [hq_eq, add_re, one_re]
      linarith [(abs_lt.mp hre_lt).1]
    exact Complex.mem_slitPlane_iff.mpr (Or.inl hre_pos)
  have hq_int_zero : (∮ z in C(c, R), logDeriv q z) = 0 := by
    have hderiv : ∀ θ : ℝ,
        HasDerivAt (fun t : ℝ => Complex.log (q (circleMap c R t)))
          (deriv (circleMap c R) θ • logDeriv q (circleMap c R θ)) θ := by
      intro θ
      have hzθ : circleMap c R θ ∈ Metric.sphere c R := circleMap_mem_sphere c hR.le θ
      have hzθ_U' : circleMap c R θ ∈ U' := hcU' (Metric.sphere_subset_closedBall hzθ)
      have hq_diff : HasDerivAt q (deriv q (circleMap c R θ)) (circleMap c R θ) :=
        ((hfg' _ hzθ_U').div (hf' _ hzθ_U') (hsphere_ne_f _ hzθ)).differentiableAt.hasDerivAt
      have hcm : HasDerivAt (circleMap c R) (deriv (circleMap c R) θ) θ := by
        rw [deriv_circleMap]
        exact hasDerivAt_circleMap c R θ
      have hcomp := (hq_diff.scomp θ hcm).clog_real (hq_slit _ hzθ)
      refine hcomp.congr_deriv ?_
      simp only [Function.comp_def, smul_eq_mul, logDeriv_apply]
      ring
    have hcont : Continuous
        (fun θ : ℝ => deriv (circleMap c R) θ • logDeriv q (circleMap c R θ)) := by
      simp only [smul_eq_mul]
      refine Continuous.mul ?_ ?_
      · rw [funext (deriv_circleMap _ _)]
        fun_prop
      · rw [continuous_iff_continuousAt]
        intro θ
        have hzθ : circleMap c R θ ∈ Metric.sphere c R := circleMap_mem_sphere c hR.le θ
        have hzθ_U' : circleMap c R θ ∈ U' := hcU' (Metric.sphere_subset_closedBall hzθ)
        have hq_an : AnalyticAt ℂ q (circleMap c R θ) :=
          (hfg' _ hzθ_U').div (hf' _ hzθ_U') (hsphere_ne_f _ hzθ)
        have hlog_cont : ContinuousAt (logDeriv q) (circleMap c R θ) :=
          (hq_an.deriv.continuousAt).div hq_an.continuousAt
            (div_ne_zero (hsphere_ne_fg _ hzθ) (hsphere_ne_f _ hzθ))
        exact hlog_cont.comp (continuous_circleMap c R).continuousAt
    have hint : IntervalIntegrable
        (fun θ : ℝ => deriv (circleMap c R) θ • logDeriv q (circleMap c R θ))
        volume 0 (2 * Real.pi) :=
      hcont.intervalIntegrable 0 (2 * Real.pi)
    rw [circleIntegral,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hderiv θ) hint]
    simp [circleMap]
  have harg_q := argumentPrinciple_circle hR hU' hcU' hq_mero hq_ne hq_fin hq_sphere
  rw [hq_int_zero, mul_zero] at harg_q
  let S : Finset ℂ := (hfin_fg.union hfin_f).toFinset.filter (· ∈ Metric.ball c R)
  have hS_q : ∑ᶠ u ∈ Metric.ball c R, ((meromorphicOrderAt q u).untop₀ : ℂ) =
      ∑ u ∈ S, ((meromorphicOrderAt q u).untop₀ : ℂ) := by
    refine finsum_mem_eq_sum_of_subset _ ?_ ?_
    · rintro u ⟨hu_ball, hu_ne⟩
      have hu_U' : u ∈ U' := hcU' (Metric.ball_subset_closedBall hu_ball)
      rw [Function.mem_support, ne_eq, Int.cast_eq_zero, hq_untop u hu_U'] at hu_ne
      simp only [S, Finset.coe_filter, Set.mem_ofPred_eq, Set.Finite.mem_toFinset,
        Set.mem_union, Function.mem_support]
      refine ⟨?_, hu_ball⟩
      by_contra hnot
      simp only [not_or, not_not] at hnot
      have hu_U : u ∈ U := hballU hu_U'
      rw [(hf.add hg).meromorphicOn.divisor_apply hu_U] at hnot
      rw [hf.meromorphicOn.divisor_apply hu_U] at hnot
      exact hu_ne (by simp [hnot.1, hnot.2])
    · intro u hu
      simp only [S, Finset.coe_filter, Set.mem_ofPred_eq] at hu
      exact hu.2
  have hS_fg : ∑ᶠ u ∈ Metric.ball c R, ((meromorphicOrderAt (f + g) u).untop₀ : ℂ) =
      ∑ u ∈ S, ((meromorphicOrderAt (f + g) u).untop₀ : ℂ) := by
    refine finsum_mem_eq_sum_of_subset _ ?_ ?_
    · rintro u ⟨hu_ball, hu_ne⟩
      have hu_U : u ∈ U := hcU (Metric.ball_subset_closedBall hu_ball)
      rw [Function.mem_support, ne_eq, Int.cast_eq_zero] at hu_ne
      simp only [S, Finset.coe_filter, Set.mem_ofPred_eq, Set.Finite.mem_toFinset,
        Set.mem_union, Function.mem_support]
      refine ⟨Or.inl ?_, hu_ball⟩
      rw [(hf.add hg).meromorphicOn.divisor_apply hu_U]
      exact hu_ne
    · intro u hu
      simp only [S, Finset.coe_filter, Set.mem_ofPred_eq] at hu
      exact hu.2
  have hS_f : ∑ᶠ u ∈ Metric.ball c R, ((meromorphicOrderAt f u).untop₀ : ℂ) =
      ∑ u ∈ S, ((meromorphicOrderAt f u).untop₀ : ℂ) := by
    refine finsum_mem_eq_sum_of_subset _ ?_ ?_
    · rintro u ⟨hu_ball, hu_ne⟩
      have hu_U : u ∈ U := hcU (Metric.ball_subset_closedBall hu_ball)
      rw [Function.mem_support, ne_eq, Int.cast_eq_zero] at hu_ne
      simp only [S, Finset.coe_filter, Set.mem_ofPred_eq, Set.Finite.mem_toFinset,
        Set.mem_union, Function.mem_support]
      refine ⟨Or.inr ?_, hu_ball⟩
      rw [hf.meromorphicOn.divisor_apply hu_U]
      exact hu_ne
    · intro u hu
      simp only [S, Finset.coe_filter, Set.mem_ofPred_eq] at hu
      exact hu.2
  rw [hS_q] at harg_q
  have hS_diff : ∑ u ∈ S, ((meromorphicOrderAt q u).untop₀ : ℂ) =
      ∑ u ∈ S, (((meromorphicOrderAt (f + g) u).untop₀ : ℂ) -
        ((meromorphicOrderAt f u).untop₀ : ℂ)) := by
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu_ball : u ∈ Metric.ball c R := (Finset.mem_filter.mp hu).2
    have hu_U' : u ∈ U' := hcU' (Metric.ball_subset_closedBall hu_ball)
    rw [hq_untop u hu_U', Int.cast_sub]
  rw [hS_diff, Finset.sum_sub_distrib, ← hS_fg, ← hS_f] at harg_q
  exact (sub_eq_zero.mp harg_q.symm)

/-!
## 3. Rectangle Boundary Integral and Argument Principle on a Rectangle
-/

/-- Counterclockwise contour integral of `f` around the boundary of the rectangle
`[[z.re, w.re]] ×ℂ [[z.im, w.im]]`. -/
noncomputable def rectBoundaryIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) -
  (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
  I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
  I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

theorem rectBoundaryIntegral_smul (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    rectBoundaryIntegral (fun s => c • f s) z w = c • rectBoundaryIntegral f z w := by
  simp only [rectBoundaryIntegral, intervalIntegral.integral_smul, smul_sub, smul_add]
  congr 1
  · congr 1
    rw [smul_comm]
  · rw [smul_comm]

theorem rectBoundaryIntegral_add {f g : ℂ → ℂ} {z w : ℂ}
    (hf1 : IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re w.re)
    (hf2 : IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re w.re)
    (hf3 : IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im w.im)
    (hf4 : IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im w.im)
    (hg1 : IntervalIntegrable (fun x : ℝ => g (x + z.im * I)) volume z.re w.re)
    (hg2 : IntervalIntegrable (fun x : ℝ => g (x + w.im * I)) volume z.re w.re)
    (hg3 : IntervalIntegrable (fun y : ℝ => g (w.re + y * I)) volume z.im w.im)
    (hg4 : IntervalIntegrable (fun y : ℝ => g (z.re + y * I)) volume z.im w.im) :
    rectBoundaryIntegral (fun s => f s + g s) z w =
      rectBoundaryIntegral f z w + rectBoundaryIntegral g z w := by
  simp only [rectBoundaryIntegral, intervalIntegral.integral_add hf1 hg1,
    intervalIntegral.integral_add hf2 hg2, intervalIntegral.integral_add hf3 hg3,
    intervalIntegral.integral_add hf4 hg4, smul_add]
  ring

theorem rectBoundaryIntegral_finset_sum {ι : Type*} (s : Finset ι)
    (F : ι → ℂ → ℂ) {z w : ℂ}
    (h1 : ∀ i ∈ s, IntervalIntegrable (fun x : ℝ => F i (x + z.im * I)) volume z.re w.re)
    (h2 : ∀ i ∈ s, IntervalIntegrable (fun x : ℝ => F i (x + w.im * I)) volume z.re w.re)
    (h3 : ∀ i ∈ s, IntervalIntegrable (fun y : ℝ => F i (w.re + y * I)) volume z.im w.im)
    (h4 : ∀ i ∈ s, IntervalIntegrable (fun y : ℝ => F i (z.re + y * I)) volume z.im w.im) :
    rectBoundaryIntegral (fun t => ∑ i ∈ s, F i t) z w =
      ∑ i ∈ s, rectBoundaryIntegral (F i) z w := by
  simp only [rectBoundaryIntegral, intervalIntegral.integral_finsetSum h1,
    intervalIntegral.integral_finsetSum h2, intervalIntegral.integral_finsetSum h3,
    intervalIntegral.integral_finsetSum h4, Finset.smul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

/-- Cauchy-Goursat for `(s - u)⁻¹` on a rectangle boundary when `u` lies outside the closed
rectangle `[[z.re, w.re]] ×ℂ [[z.im, w.im]]`. -/
theorem rectBoundaryIntegral_sub_inv_of_not_mem {z w u : ℂ}
    (hu : u ∉ [[z.re, w.re]] ×ℂ [[z.im, w.im]]) :
    rectBoundaryIntegral (fun s => (s - u)⁻¹) z w = 0 := by
  unfold rectBoundaryIntegral
  refine integral_boundary_rect_eq_zero_of_differentiableOn (fun s => (s - u)⁻¹) z w ?_
  intro s hs
  have hne : s - u ≠ 0 := sub_ne_zero.mpr (ne_of_mem_of_not_mem hs hu)
  exact ((differentiableAt_id.sub_const u).inv hne).differentiableWithinAt

private noncomputable def rectHorizAntideriv (a b y x : ℝ) : ℂ :=
  ((1 / 2 : ℝ) * Real.log ((x - a) ^ 2 + (y - b) ^ 2) : ℝ) -
    I * (Real.arctan ((x - a) / (y - b)) : ℝ)

private noncomputable def rectVertAntideriv (a b x y : ℝ) : ℂ :=
  ((1 / 2 : ℝ) * Real.log ((x - a) ^ 2 + (y - b) ^ 2) : ℝ) +
    I * (Real.arctan ((y - b) / (x - a)) : ℝ)

private lemma hasDerivAt_rectHorizAntideriv {u : ℂ} {y : ℝ} (hy : y ≠ u.im) (x : ℝ) :
    HasDerivAt (rectHorizAntideriv u.re u.im y) ((x : ℂ) + (y : ℂ) * I - u)⁻¹ x := by
  set a := u.re
  set b := u.im
  have hyb : y - b ≠ 0 := sub_ne_zero.mpr hy
  let r2 : ℝ → ℝ := fun t => (t - a) ^ 2 + (y - b) ^ 2
  have hr2_pos : ∀ t : ℝ, 0 < r2 t := fun t =>
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hyb)
  have hr2_deriv : HasDerivAt r2 (2 * (x - a)) x := by
    have h1 : HasDerivAt (fun t : ℝ => (t - a) ^ 2) (2 * (x - a) ^ 1 * 1) x :=
      ((hasDerivAt_id x).sub_const a).pow 2
    simpa [r2] using h1.add_const ((y - b) ^ 2)
  have hlog : HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * Real.log (r2 t))
      ((x - a) / r2 x) x := by
    have h1 : HasDerivAt (fun t : ℝ => Real.log (r2 t)) ((r2 x)⁻¹ * (2 * (x - a))) x :=
      (Real.hasDerivAt_log (hr2_pos x).ne').comp x hr2_deriv
    refine (h1.const_mul (1 / 2 : ℝ)).congr_deriv ?_
    field_simp [(hr2_pos x).ne']
  have harctan : HasDerivAt (fun t : ℝ => Real.arctan ((t - a) / (y - b)))
      ((y - b) / r2 x) x := by
    have h1 : HasDerivAt (fun t : ℝ => (t - a) / (y - b)) (1 / (y - b)) x := by
      simpa using ((hasDerivAt_id x).sub_const a).div_const (y - b)
    refine h1.arctan.congr_deriv ?_
    have hr2_ne : r2 x ≠ 0 := (hr2_pos x).ne'
    dsimp only [r2] at hr2_ne ⊢
    field_simp [hyb, hr2_ne]
    ring
  have hsub := hlog.ofReal_comp.sub (harctan.ofReal_comp.const_mul I)
  refine hsub.congr_deriv ?_
  have hz_eq : (x : ℂ) + (y : ℂ) * I - u =
      ((x - a : ℝ) : ℂ) + I * ((y - b : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [a, b]
  rw [hz_eq]
  have hz_ne : ((x - a : ℝ) : ℂ) + I * ((y - b : ℝ) : ℂ) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    exact hyb this
  rw [← one_div, eq_div_iff hz_ne]
  dsimp only [r2]
  push_cast
  have hr2_c : ((x - a : ℂ) ^ 2 + (y - b : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (hr2_pos x).ne'
  field_simp [hr2_c]
  calc
    _ = ((x : ℂ) - a) ^ 2 - (I * I) * (y - b) ^ 2 := by ring
    _ = ((x : ℂ) - a) ^ 2 + (y - b) ^ 2 := by rw [I_mul_I]; ring

private lemma hasDerivAt_rectVertAntideriv {u : ℂ} {x : ℝ} (hx : x ≠ u.re) (y : ℝ) :
    HasDerivAt (rectVertAntideriv u.re u.im x) (I * ((x : ℂ) + (y : ℂ) * I - u)⁻¹) y := by
  set a := u.re
  set b := u.im
  have hxa : x - a ≠ 0 := sub_ne_zero.mpr hx
  let r2 : ℝ → ℝ := fun t => (x - a) ^ 2 + (t - b) ^ 2
  have hr2_pos : ∀ t : ℝ, 0 < r2 t := fun t =>
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hxa) (sq_nonneg _)
  have hr2_deriv : HasDerivAt r2 (2 * (y - b)) y := by
    have h1 : HasDerivAt (fun t : ℝ => (t - b) ^ 2) (2 * (y - b) ^ 1 * 1) y :=
      ((hasDerivAt_id y).sub_const b).pow 2
    simpa [r2] using h1.const_add ((x - a) ^ 2)
  have hlog : HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * Real.log (r2 t))
      ((y - b) / r2 y) y := by
    have h1 : HasDerivAt (fun t : ℝ => Real.log (r2 t)) ((r2 y)⁻¹ * (2 * (y - b))) y :=
      (Real.hasDerivAt_log (hr2_pos y).ne').comp y hr2_deriv
    refine (h1.const_mul (1 / 2 : ℝ)).congr_deriv ?_
    field_simp [(hr2_pos y).ne']
  have harctan : HasDerivAt (fun t : ℝ => Real.arctan ((t - b) / (x - a)))
      ((x - a) / r2 y) y := by
    have h1 : HasDerivAt (fun t : ℝ => (t - b) / (x - a)) (1 / (x - a)) y := by
      simpa using ((hasDerivAt_id y).sub_const b).div_const (x - a)
    refine h1.arctan.congr_deriv ?_
    have hr2_ne : r2 y ≠ 0 := (hr2_pos y).ne'
    dsimp only [r2] at hr2_ne ⊢
    field_simp [hxa, hr2_ne]
  have hadd := hlog.ofReal_comp.add (harctan.ofReal_comp.const_mul I)
  refine hadd.congr_deriv ?_
  have hz_eq : (x : ℂ) + (y : ℂ) * I - u =
      ((x - a : ℝ) : ℂ) + I * ((y - b : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [a, b]
  rw [hz_eq]
  have hz_ne : ((x - a : ℝ) : ℂ) + I * ((y - b : ℝ) : ℂ) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    exact hxa this
  rw [← div_eq_mul_inv, eq_div_iff hz_ne]
  dsimp only [r2]
  push_cast
  have hr2_c : ((x - a : ℂ) ^ 2 + (y - b : ℂ) ^ 2) ≠ 0 := by
    exact_mod_cast (hr2_pos y).ne'
  field_simp [hr2_c]
  calc
    _ = I * ((x - a) ^ 2 + (y - b) ^ 2) + (1 + I * I) * (x - a) * (y - b) := by ring
    _ = ((x - a) ^ 2 + (y - b) ^ 2) * I := by rw [I_mul_I]; ring

private lemma intervalIntegrable_sub_inv_horiz {u : ℂ} {y : ℝ} (hy : y ≠ u.im) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => ((x : ℂ) + (y : ℂ) * I - u)⁻¹) volume a b := by
  have hcont : Continuous (fun x : ℝ => ((x : ℂ) + (y : ℂ) * I - u)⁻¹) := by
    refine Continuous.inv₀ (by fun_prop) fun x => ?_
    intro h0
    have := congrArg Complex.im h0
    simp at this
    exact hy (sub_eq_zero.mp this)
  exact hcont.intervalIntegrable a b

private lemma intervalIntegrable_sub_inv_vert {u : ℂ} {x : ℝ} (hx : x ≠ u.re) (a b : ℝ) :
    IntervalIntegrable (fun y : ℝ => ((x : ℂ) + (y : ℂ) * I - u)⁻¹) volume a b := by
  have hcont : Continuous (fun y : ℝ => ((x : ℂ) + (y : ℂ) * I - u)⁻¹) := by
    refine Continuous.inv₀ (by fun_prop) fun y => ?_
    intro h0
    have := congrArg Complex.re h0
    simp at this
    exact hx (sub_eq_zero.mp this)
  exact hcont.intervalIntegrable a b

private lemma arctan_add_arctan_div_pos {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    Real.arctan (u / v) + Real.arctan (v / u) = Real.pi / 2 := by
  rw [show v / u = (u / v)⁻¹ from (inv_div u v).symm,
    Real.arctan_inv_of_pos (div_pos hu hv)]
  ring

private lemma arctan_add_arctan_div_neg_neg {u v : ℝ} (hu : u < 0) (hv : v < 0) :
    Real.arctan (u / v) + Real.arctan (v / u) = Real.pi / 2 := by
  rw [show v / u = (u / v)⁻¹ from (inv_div u v).symm,
    Real.arctan_inv_of_pos (div_pos_of_neg_of_neg hu hv)]
  ring

private lemma arctan_add_arctan_div_pos_neg {u v : ℝ} (hu : 0 < u) (hv : v < 0) :
    Real.arctan (u / v) + Real.arctan (v / u) = -(Real.pi / 2) := by
  rw [show v / u = (u / v)⁻¹ from (inv_div u v).symm,
    Real.arctan_inv_of_neg (div_neg_of_pos_of_neg hu hv)]
  ring

private lemma arctan_add_arctan_div_neg_pos {u v : ℝ} (hu : u < 0) (hv : 0 < v) :
    Real.arctan (u / v) + Real.arctan (v / u) = -(Real.pi / 2) := by
  rw [show v / u = (u / v)⁻¹ from (inv_div u v).symm,
    Real.arctan_inv_of_neg (div_neg_of_neg_of_pos hu hv)]
  ring

/-- Residue evaluation of `(s - u)⁻¹` around a rectangle boundary when `u` lies strictly inside
the open rectangle `(z.re, w.re) × (z.im, w.im)`. -/
theorem rectBoundaryIntegral_sub_inv_of_mem {z w u : ℂ}
    (hzre : z.re < u.re) (hwre : u.re < w.re)
    (hzim : z.im < u.im) (hwim : u.im < w.im) :
    rectBoundaryIntegral (fun s => (s - u)⁻¹) z w = 2 * Real.pi * I := by
  unfold rectBoundaryIntegral
  have h1 : (∫ x : ℝ in z.re..w.re, ((x : ℂ) + (z.im : ℂ) * I - u)⁻¹) =
      rectHorizAntideriv u.re u.im z.im w.re - rectHorizAntideriv u.re u.im z.im z.re :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_rectHorizAntideriv hzim.ne x)
      (intervalIntegrable_sub_inv_horiz hzim.ne z.re w.re)
  have h2 : (∫ x : ℝ in z.re..w.re, ((x : ℂ) + (w.im : ℂ) * I - u)⁻¹) =
      rectHorizAntideriv u.re u.im w.im w.re - rectHorizAntideriv u.re u.im w.im z.re :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_rectHorizAntideriv hwim.ne' x)
      (intervalIntegrable_sub_inv_horiz hwim.ne' z.re w.re)
  have h3 : I • (∫ y : ℝ in z.im..w.im, ((w.re : ℂ) + (y : ℂ) * I - u)⁻¹) =
      rectVertAntideriv u.re u.im w.re w.im - rectVertAntideriv u.re u.im w.re z.im := by
    rw [← intervalIntegral.integral_smul]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => hasDerivAt_rectVertAntideriv hwre.ne' y)
      ((intervalIntegrable_sub_inv_vert hwre.ne' z.im w.im).smul I)
  have h4 : I • (∫ y : ℝ in z.im..w.im, ((z.re : ℂ) + (y : ℂ) * I - u)⁻¹) =
      rectVertAntideriv u.re u.im z.re w.im - rectVertAntideriv u.re u.im z.re z.im := by
    rw [← intervalIntegral.integral_smul]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => hasDerivAt_rectVertAntideriv hzre.ne y)
      ((intervalIntegrable_sub_inv_vert hzre.ne z.im w.im).smul I)
  rw [h1, h2, h3, h4]
  simp only [rectHorizAntideriv, rectVertAntideriv]
  have hdx1 : z.re - u.re < 0 := sub_neg.mpr hzre
  have hdx2 : 0 < w.re - u.re := sub_pos.mpr hwre
  have hdy1 : z.im - u.im < 0 := sub_neg.mpr hzim
  have hdy2 : 0 < w.im - u.im := sub_pos.mpr hwim
  have hc1 := arctan_add_arctan_div_pos hdx2 hdy2
  have hc2 := arctan_add_arctan_div_pos_neg hdx2 hdy1
  have hc3 := arctan_add_arctan_div_neg_pos hdx1 hdy2
  have hc4 := arctan_add_arctan_div_neg_neg hdx1 hdy1
  have hsum_real :
      Real.arctan ((w.re - u.re) / (w.im - u.im)) + Real.arctan ((w.im - u.im) / (w.re - u.re)) -
      (Real.arctan ((w.re - u.re) / (z.im - u.im)) + Real.arctan ((z.im - u.im) / (w.re - u.re))) -
      (Real.arctan ((z.re - u.re) / (w.im - u.im)) + Real.arctan ((w.im - u.im) / (z.re - u.re))) +
      (Real.arctan ((z.re - u.re) / (z.im - u.im)) + Real.arctan ((z.im - u.im) / (z.re - u.re))) =
        2 * Real.pi := by
    rw [hc1, hc2, hc3, hc4]
    ring
  have hsum_c := congrArg (fun r : ℝ => (r : ℂ) * I) hsum_real
  push_cast at hsum_c
  rw [← hsum_c]
  ring

private lemma intervalIntegrable_congr_finite_compl {f g : ℂ → ℂ} {E : Set ℂ}
    (hE : E.Finite) {a b : ℝ} {y : ℝ}
    (heq : ∀ x ∈ Set.uIcc a b, (x : ℂ) + (y : ℂ) * I ∉ E →
      f (x + y * I) = g (x + y * I)) :
    (∫ x : ℝ in a..b, f (x + y * I)) = ∫ x : ℝ in a..b, g (x + y * I) := by
  refine intervalIntegral.integral_congr_ae ?_
  have hpre : ((fun x : ℝ => (x : ℂ) + (y : ℂ) * I) ⁻¹' E).Countable := by
    refine Set.Finite.countable (hE.preimage ?_)
    intro x₁ _ x₂ _ h
    have := congrArg Complex.re h
    simpa using this
  filter_upwards [hpre.ae_notMem volume] with x hx hmem
  exact heq x (Set.uIoc_subset_uIcc hmem) hx

private lemma intervalIntegrable_congr_finite_compl_vert {f g : ℂ → ℂ} {E : Set ℂ}
    (hE : E.Finite) {a b : ℝ} {x : ℝ}
    (heq : ∀ y ∈ Set.uIcc a b, (x : ℂ) + (y : ℂ) * I ∉ E →
      f (x + y * I) = g (x + y * I)) :
    (∫ y : ℝ in a..b, f (x + y * I)) = ∫ y : ℝ in a..b, g (x + y * I) := by
  refine intervalIntegral.integral_congr_ae ?_
  have hpre : ((fun y : ℝ => (x : ℂ) + (y : ℂ) * I) ⁻¹' E).Countable := by
    refine Set.Finite.countable (hE.preimage ?_)
    intro y₁ _ y₂ _ h
    have := congrArg Complex.im h
    simpa using this
  filter_upwards [hpre.ae_notMem volume] with y hy hmem
  exact heq y (Set.uIoc_subset_uIcc hmem) hy

/-- The meromorphic Argument Principle on a rectangle `[[z.re, w.re]] ×ℂ [[z.im, w.im]]`:
`(2πi)⁻¹ rectBoundaryIntegral (logDeriv f) z w` equals the sum of the orders of zeros minus
poles of `f` inside the open rectangle `Set.Ioo z.re w.re ×ℂ Set.Ioo z.im w.im`. -/
theorem argumentPrinciple_rect {z w : ℂ} (hzre : z.re < w.re) (hzim : z.im < w.im)
    {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hcU : [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ U)
    (hf : MeromorphicOn f U) (hf_ne : ∀ u ∈ U, meromorphicOrderAt f u ≠ ⊤)
    (hfin : (MeromorphicOn.divisor f U).support.Finite)
    (hb : ∀ x ∈ [[z.re, w.re]], (x : ℂ) + z.im * I ∉ (MeromorphicOn.divisor f U).support)
    (ht : ∀ x ∈ [[z.re, w.re]], (x : ℂ) + w.im * I ∉ (MeromorphicOn.divisor f U).support)
    (hl : ∀ y ∈ [[z.im, w.im]], (z.re : ℂ) + y * I ∉ (MeromorphicOn.divisor f U).support)
    (hr : ∀ y ∈ [[z.im, w.im]], (w.re : ℂ) + y * I ∉ (MeromorphicOn.divisor f U).support) :
    (2 * Real.pi * I)⁻¹ * rectBoundaryIntegral (logDeriv f) z w =
      ∑ᶠ u ∈ Set.Ioo z.re w.re ×ℂ Set.Ioo z.im w.im,
        ((meromorphicOrderAt f u).untop₀ : ℂ) := by
  classical
  set D := MeromorphicOn.divisor f U
  set K : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]
  obtain ⟨g, hg_an, hg_ne, hfg⟩ := exists_analytic_logDeriv_eq hU hf hf_ne hfin
  let h : ℂ → ℂ := fun s => logDeriv g s + ∑ u ∈ hfin.toFinset, (D u : ℂ) * (s - u)⁻¹
  have hK_compact : IsCompact K := isCompact_uIcc.reProdIm isCompact_uIcc
  have hfg_K : logDeriv f =ᶠ[codiscreteWithin K] h := hfg.filter_mono (codiscreteWithin_mono hcU)
  have hE_fin : (K \ {s | logDeriv f s = h s}).Finite :=
    hK_compact.finite_sdiff_of_mem_codiscreteWithin hfg_K
  have hrect_congr : rectBoundaryIntegral (logDeriv f) z w = rectBoundaryIntegral h z w := by
    unfold rectBoundaryIntegral
    have hi1 : (∫ x : ℝ in z.re..w.re, logDeriv f (x + z.im * I)) =
        ∫ x : ℝ in z.re..w.re, h (x + z.im * I) := by
      refine intervalIntegrable_congr_finite_compl hE_fin fun x hx hnot => ?_
      by_contra hne
      apply hnot
      exact ⟨Complex.mem_reProdIm.mpr ⟨by simp [hx], by simp⟩, hne⟩
    have hi2 : (∫ x : ℝ in z.re..w.re, logDeriv f (x + w.im * I)) =
        ∫ x : ℝ in z.re..w.re, h (x + w.im * I) := by
      refine intervalIntegrable_congr_finite_compl hE_fin fun x hx hnot => ?_
      by_contra hne
      apply hnot
      exact ⟨Complex.mem_reProdIm.mpr ⟨by simp [hx], by simp⟩, hne⟩
    have hi3 : (∫ y : ℝ in z.im..w.im, logDeriv f (w.re + y * I)) =
        ∫ y : ℝ in z.im..w.im, h (w.re + y * I) := by
      refine intervalIntegrable_congr_finite_compl_vert hE_fin fun y hy hnot => ?_
      by_contra hne
      apply hnot
      exact ⟨Complex.mem_reProdIm.mpr ⟨by simp, by simp [hy]⟩, hne⟩
    have hi4 : (∫ y : ℝ in z.im..w.im, logDeriv f (z.re + y * I)) =
        ∫ y : ℝ in z.im..w.im, h (z.re + y * I) := by
      refine intervalIntegrable_congr_finite_compl_vert hE_fin fun y hy hnot => ?_
      by_contra hne
      apply hnot
      exact ⟨Complex.mem_reProdIm.mpr ⟨by simp, by simp [hy]⟩, hne⟩
    rw [hi1, hi2, hi3, hi4]
  rw [hrect_congr]
  have hlog_diff : DifferentiableOn ℂ (logDeriv g) U :=
    differentiableOn_logDeriv_of_analyticOnNhd hg_an hg_ne
  have hlog_cont : ContinuousOn (logDeriv g) K := (hlog_diff.mono hcU).continuousOn
  have hg1 : IntervalIntegrable (fun x : ℝ => logDeriv g (x + z.im * I)) volume z.re w.re := by
    refine ContinuousOn.intervalIntegrable (hlog_cont.comp (by fun_prop) fun x hx => ?_)
    exact Complex.mem_reProdIm.mpr ⟨by simp [hx], by simp⟩
  have hg2 : IntervalIntegrable (fun x : ℝ => logDeriv g (x + w.im * I)) volume z.re w.re := by
    refine ContinuousOn.intervalIntegrable (hlog_cont.comp (by fun_prop) fun x hx => ?_)
    exact Complex.mem_reProdIm.mpr ⟨by simp [hx], by simp⟩
  have hg3 : IntervalIntegrable (fun y : ℝ => logDeriv g (w.re + y * I)) volume z.im w.im := by
    refine ContinuousOn.intervalIntegrable (hlog_cont.comp (by fun_prop) fun y hy => ?_)
    exact Complex.mem_reProdIm.mpr ⟨by simp, by simp [hy]⟩
  have hg4 : IntervalIntegrable (fun y : ℝ => logDeriv g (z.re + y * I)) volume z.im w.im := by
    refine ContinuousOn.intervalIntegrable (hlog_cont.comp (by fun_prop) fun y hy => ?_)
    exact Complex.mem_reProdIm.mpr ⟨by simp, by simp [hy]⟩
  have hu_not_bdry : ∀ u ∈ hfin.toFinset,
      (∀ x ∈ [[z.re, w.re]], (x : ℂ) + z.im * I ≠ u) ∧
      (∀ x ∈ [[z.re, w.re]], (x : ℂ) + w.im * I ≠ u) ∧
      (∀ y ∈ [[z.im, w.im]], (z.re : ℂ) + y * I ≠ u) ∧
      (∀ y ∈ [[z.im, w.im]], (w.re : ℂ) + y * I ≠ u) := by
    intro u hu
    have hus : u ∈ D.support := hfin.mem_toFinset.mp hu
    refine ⟨fun x hx h0 => hb x hx (h0 ▸ hus), fun x hx h0 => ht x hx (h0 ▸ hus),
      fun y hy h0 => hl y hy (h0 ▸ hus), fun y hy h0 => hr y hy (h0 ▸ hus)⟩
  have hi1 : ∀ u ∈ hfin.toFinset, IntervalIntegrable
      (fun x : ℝ => (D u : ℂ) * (x + z.im * I - u)⁻¹) volume z.re w.re := by
    intro u hu
    refine IntervalIntegrable.const_mul ?_ _
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_
    exact sub_ne_zero.mpr ((hu_not_bdry u hu).1 x hx)
  have hi2 : ∀ u ∈ hfin.toFinset, IntervalIntegrable
      (fun x : ℝ => (D u : ℂ) * (x + w.im * I - u)⁻¹) volume z.re w.re := by
    intro u hu
    refine IntervalIntegrable.const_mul ?_ _
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_
    exact sub_ne_zero.mpr ((hu_not_bdry u hu).2.1 x hx)
  have hi3 : ∀ u ∈ hfin.toFinset, IntervalIntegrable
      (fun y : ℝ => (D u : ℂ) * (w.re + y * I - u)⁻¹) volume z.im w.im := by
    intro u hu
    refine IntervalIntegrable.const_mul ?_ _
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ (by fun_prop) fun y hy => ?_
    exact sub_ne_zero.mpr ((hu_not_bdry u hu).2.2.2 y hy)
  have hi4 : ∀ u ∈ hfin.toFinset, IntervalIntegrable
      (fun y : ℝ => (D u : ℂ) * (z.re + y * I - u)⁻¹) volume z.im w.im := by
    intro u hu
    refine IntervalIntegrable.const_mul ?_ _
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.inv₀ (by fun_prop) fun y hy => ?_
    exact sub_ne_zero.mpr ((hu_not_bdry u hu).2.2.1 y hy)
  have hs1 : IntervalIntegrable
      (fun x : ℝ => ∑ u ∈ hfin.toFinset, (D u : ℂ) * (x + z.im * I - u)⁻¹)
      volume z.re w.re := by
    rw [show (fun x : ℝ => ∑ u ∈ hfin.toFinset, (D u : ℂ) * (x + z.im * I - u)⁻¹) =
        ∑ u ∈ hfin.toFinset, fun x : ℝ => (D u : ℂ) * (x + z.im * I - u)⁻¹ by ext; simp]
    exact IntervalIntegrable.sum hfin.toFinset hi1
  have hs2 : IntervalIntegrable
      (fun x : ℝ => ∑ u ∈ hfin.toFinset, (D u : ℂ) * (x + w.im * I - u)⁻¹)
      volume z.re w.re := by
    rw [show (fun x : ℝ => ∑ u ∈ hfin.toFinset, (D u : ℂ) * (x + w.im * I - u)⁻¹) =
        ∑ u ∈ hfin.toFinset, fun x : ℝ => (D u : ℂ) * (x + w.im * I - u)⁻¹ by ext; simp]
    exact IntervalIntegrable.sum hfin.toFinset hi2
  have hs3 : IntervalIntegrable
      (fun y : ℝ => ∑ u ∈ hfin.toFinset, (D u : ℂ) * (w.re + y * I - u)⁻¹)
      volume z.im w.im := by
    rw [show (fun y : ℝ => ∑ u ∈ hfin.toFinset, (D u : ℂ) * (w.re + y * I - u)⁻¹) =
        ∑ u ∈ hfin.toFinset, fun y : ℝ => (D u : ℂ) * (w.re + y * I - u)⁻¹ by ext; simp]
    exact IntervalIntegrable.sum hfin.toFinset hi3
  have hs4 : IntervalIntegrable
      (fun y : ℝ => ∑ u ∈ hfin.toFinset, (D u : ℂ) * (z.re + y * I - u)⁻¹)
      volume z.im w.im := by
    rw [show (fun y : ℝ => ∑ u ∈ hfin.toFinset, (D u : ℂ) * (z.re + y * I - u)⁻¹) =
        ∑ u ∈ hfin.toFinset, fun y : ℝ => (D u : ℂ) * (z.re + y * I - u)⁻¹ by ext; simp]
    exact IntervalIntegrable.sum hfin.toFinset hi4
  have hadd : rectBoundaryIntegral h z w =
      rectBoundaryIntegral (logDeriv g) z w +
        rectBoundaryIntegral (fun s => ∑ u ∈ hfin.toFinset, (D u : ℂ) * (s - u)⁻¹) z w :=
    rectBoundaryIntegral_add hg1 hg2 hg3 hg4 hs1 hs2 hs3 hs4
  rw [hadd]
  have hg_zero : rectBoundaryIntegral (logDeriv g) z w = 0 := by
    unfold rectBoundaryIntegral
    exact integral_boundary_rect_eq_zero_of_differentiableOn (logDeriv g) z w (hlog_diff.mono hcU)
  rw [hg_zero, zero_add, rectBoundaryIntegral_finset_sum hfin.toFinset _ hi1 hi2 hi3 hi4]
  have hterm : ∀ u ∈ hfin.toFinset,
      rectBoundaryIntegral (fun s => (D u : ℂ) * (s - u)⁻¹) z w =
        if u ∈ Set.Ioo z.re w.re ×ℂ Set.Ioo z.im w.im then
          (D u : ℂ) * (2 * Real.pi * I)
        else 0 := by
    intro u hu
    change rectBoundaryIntegral (fun s => (D u : ℂ) • (s - u)⁻¹) z w = _
    rw [rectBoundaryIntegral_smul, smul_eq_mul]
    split_ifs with huo
    · rcases huo with ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      rw [rectBoundaryIntegral_sub_inv_of_mem h1 h2 h3 h4]
    · have hu_not_K : u ∉ K := by
        intro huK
        rcases huK with ⟨hre, him⟩
        rw [Set.uIcc_of_le hzre.le] at hre
        rw [Set.uIcc_of_le hzim.le] at him
        rcases eq_or_lt_of_le hre.1 with heq1 | hlt1
        · exact (hu_not_bdry u hu).2.2.1 u.im (Set.uIcc_of_le hzim.le ▸ him)
            (by apply Complex.ext <;> simp [heq1])
        · rcases eq_or_lt_of_le hre.2 with heq2 | hlt2
          · exact (hu_not_bdry u hu).2.2.2 u.im (Set.uIcc_of_le hzim.le ▸ him)
              (by apply Complex.ext <;> simp [heq2])
          · rcases eq_or_lt_of_le him.1 with heq3 | hlt3
            · exact (hu_not_bdry u hu).1 u.re (Set.uIcc_of_le hzre.le ▸ hre)
                (by apply Complex.ext <;> simp [heq3])
            · rcases eq_or_lt_of_le him.2 with heq4 | hlt4
              · exact (hu_not_bdry u hu).2.1 u.re (Set.uIcc_of_le hzre.le ▸ hre)
                  (by apply Complex.ext <;> simp [heq4])
              · exact huo ⟨⟨hlt1, hlt2⟩, ⟨hlt3, hlt4⟩⟩
      rw [rectBoundaryIntegral_sub_inv_of_not_mem hu_not_K, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  have h2piI : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  rw [← Finset.sum_filter, ← Finset.sum_mul, mul_left_comm, inv_mul_cancel₀ h2piI, mul_one]
  have hsum_eq :
      ∑ u ∈ hfin.toFinset with u ∈ Set.Ioo z.re w.re ×ℂ Set.Ioo z.im w.im, (D u : ℂ) =
      ∑ u ∈ hfin.toFinset with u ∈ Set.Ioo z.re w.re ×ℂ Set.Ioo z.im w.im,
        ((meromorphicOrderAt f u).untop₀ : ℂ) := by
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu_ioo := (Finset.mem_filter.mp hu).2
    have hu_K : u ∈ K := ⟨
      by rw [Set.uIcc_of_le hzre.le]; exact Set.Ioo_subset_Icc_self hu_ioo.1,
      by rw [Set.uIcc_of_le hzim.le]; exact Set.Ioo_subset_Icc_self hu_ioo.2⟩
    rw [hf.divisor_apply (hcU hu_K)]
  rw [hsum_eq]
  symm
  refine finsum_mem_eq_sum_of_inter_support_eq _ ?_
  ext u
  simp only [Set.mem_inter_iff, Function.mem_support, ne_eq, Int.cast_eq_zero,
    Finset.coe_filter, Set.mem_ofPred_eq, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨hu_ioo, hu_ne⟩
    refine ⟨⟨?_, hu_ioo⟩, hu_ne⟩
    have hu_K : u ∈ K := by
      refine ⟨?_, ?_⟩
      · rw [Set.uIcc_of_le hzre.le]
        exact Set.Ioo_subset_Icc_self hu_ioo.1
      · rw [Set.uIcc_of_le hzim.le]
        exact Set.Ioo_subset_Icc_self hu_ioo.2
    change D u ≠ 0
    rw [hf.divisor_apply (hcU hu_K)]
    exact hu_ne
  · rintro ⟨⟨_, hu_ioo⟩, hu_ne⟩
    exact ⟨hu_ioo, hu_ne⟩

end Nyquist
