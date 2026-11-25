import Nyquist.Defs
import Nyquist.ArgumentPrinciple
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Nyquist Stability Criterion for Retarded Time-Delay Systems

This file extends the Nyquist stability criterion to retarded linear time-invariant
time-delay systems with open-loop transfer function `L_τ(s) = (N(s) / D(s)) * exp (-τ * s)`
(`τ ≥ 0`, `deg N < deg D`).
-/

namespace Nyquist

open Complex Polynomial MeasureTheory Filter

open scoped Interval

/-! ## 1. Definitions for Retarded Time-Delay Systems -/

/-- Open-loop retarded time-delay transfer function `L_τ(s) = (N(s) / D(s)) * exp (-τ * s)`. -/
noncomputable def delayTransfer (N D : Polynomial ℂ) (τ : ℝ) (s : ℂ) : ℂ :=
  (N.eval s / D.eval s) * Complex.exp (-τ * s)

/-- Return difference `F_τ(s) = 1 + L_τ(s)` for the retarded time-delay system. -/
noncomputable def delayReturnDiff (N D : Polynomial ℂ) (τ : ℝ) (s : ℂ) : ℂ :=
  1 + delayTransfer N D τ s

/-- Characteristic quasipolynomial `Δ_τ(s) = D(s) + N(s) * exp (-τ * s)`. -/
noncomputable def delayCharQuasiPoly (N D : Polynomial ℂ) (τ : ℝ) (s : ℂ) : ℂ :=
  D.eval s + N.eval s * Complex.exp (-τ * s)

/-- Closed-RHP stability for the delay quasipolynomial: no zeros with `0 ≤ s.re`. -/
def IsDelayHurwitz (N D : Polynomial ℂ) (τ : ℝ) : Prop :=
  ∀ s : ℂ, 0 ≤ s.re → delayCharQuasiPoly N D τ s ≠ 0

/-- Total multiplicity of open-RHP zeros of `delayCharQuasiPoly N D τ`. -/
noncomputable def delayRhpZeroCount (N D : Polynomial ℂ) (τ : ℝ) : ℂ :=
  ∑ᶠ u ∈ {s : ℂ | 0 < s.re}, ((meromorphicOrderAt (delayCharQuasiPoly N D τ) u).untop₀ : ℂ)

/-- Logarithmic-derivative integrand of `1 + L_τ(i ω)` along the imaginary axis. -/
noncomputable def delayNyquistIntegrand (N D : Polynomial ℂ) (τ : ℝ) (ω : ℝ) : ℂ :=
  deriv (fun t : ℝ => delayReturnDiff N D τ (I * t)) ω / delayReturnDiff N D τ (I * ω)

/-- Truncated counterclockwise Nyquist encirclement integral along `[-i R, i R]`. -/
noncomputable def delayNyquistEncirclementsCCW (N D : Polynomial ℂ) (τ : ℝ) (R : ℝ) : ℂ :=
  (1 / (2 * Real.pi * I)) * ∫ ω in (-R)..R, delayNyquistIntegrand N D τ ω

/-! ## 2. Analyticity, Meromorphy, and Asymptotic Bounds -/

lemma poly_eval_analyticOnNhd (p : Polynomial ℂ) (U : Set ℂ) :
    AnalyticOnNhd ℂ (fun s : ℂ => p.eval s) U := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro s hs
    have hfun : (fun t : ℂ => (p + q).eval t) =
        (fun t : ℂ => p.eval t) + (fun t : ℂ => q.eval t) := by
      ext t
      simp
    rw [hfun]
    exact (hp s hs).add (hq s hs)
  | monomial n a =>
    intro s _
    have hfun : (fun t : ℂ => (monomial n a).eval t) = (fun _ : ℂ => a) * (id ^ n) := by
      ext t
      simp
    rw [hfun]
    exact analyticAt_const.mul (analyticAt_id.pow n)

lemma delayCharQuasiPoly_analytic (N D : Polynomial ℂ) (τ : ℝ) :
    AnalyticOnNhd ℂ (delayCharQuasiPoly N D τ) Set.univ := by
  unfold delayCharQuasiPoly
  refine (poly_eval_analyticOnNhd D Set.univ).add ?_
  refine (poly_eval_analyticOnNhd N Set.univ).mul ?_
  exact (analyticOnNhd_const.mul analyticOnNhd_id).cexp

lemma delayCharQuasiPoly_meromorphicOn (N D : Polynomial ℂ) (τ : ℝ) (U : Set ℂ) :
    MeromorphicOn (delayCharQuasiPoly N D τ) U :=
  ((delayCharQuasiPoly_analytic N D τ).mono (Set.subset_univ U)).meromorphicOn

lemma delayReturnDiff_meromorphicOn (N D : Polynomial ℂ) (τ : ℝ) (U : Set ℂ) :
    MeromorphicOn (delayReturnDiff N D τ) U := by
  unfold delayReturnDiff delayTransfer
  refine analyticOnNhd_const.meromorphicOn.add ?_
  refine ((poly_eval_analyticOnNhd N U).meromorphicOn.div
    (poly_eval_analyticOnNhd D U).meromorphicOn).mul ?_
  exact ((analyticOnNhd_const.mul analyticOnNhd_id).cexp).meromorphicOn

private lemma norm_exp_neg_ofReal_mul_le_one {τ : ℝ} (hτ : 0 ≤ τ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖Complex.exp (-τ * s)‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have hre : (-(τ : ℂ) * s).re = -τ * s.re := by simp
  rw [hre, Real.exp_le_one_iff]
  nlinarith

private lemma norm_poly_eval_le (N : Polynomial ℂ) {s : ℂ} (hs : 1 ≤ ‖s‖) :
    ‖N.eval s‖ ≤ (∑ i ∈ Finset.range (N.natDegree + 1), ‖N.coeff i‖) * ‖s‖ ^ N.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  calc ‖∑ i ∈ Finset.range (N.natDegree + 1), N.coeff i * s ^ i‖
      ≤ ∑ i ∈ Finset.range (N.natDegree + 1), ‖N.coeff i * s ^ i‖ := norm_sum_le _ _
    _ = ∑ i ∈ Finset.range (N.natDegree + 1), ‖N.coeff i‖ * ‖s‖ ^ i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, norm_pow]
    _ ≤ ∑ i ∈ Finset.range (N.natDegree + 1), ‖N.coeff i‖ * ‖s‖ ^ N.natDegree := by
        refine Finset.sum_le_sum fun i hi => ?_
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact pow_le_pow_right₀ hs (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    _ = (∑ i ∈ Finset.range (N.natDegree + 1), ‖N.coeff i‖) * ‖s‖ ^ N.natDegree := by
        rw [← Finset.sum_mul]

private lemma norm_poly_eval_ge (D : Polynomial ℂ) (_hD0 : D ≠ 0) {s : ℂ}
    (hs : 2 * (D.roots.map norm).sum ≤ ‖s‖) (_hspos : 0 < ‖s‖) :
    ‖D.leadingCoeff‖ * (‖s‖ / 2) ^ D.natDegree ≤ ‖D.eval s‖ := by
  have hfac : D = C D.leadingCoeff * (D.roots.map fun a => X - C a).prod :=
    (C_leadingCoeff_mul_prod_multiset_X_sub_C
      (IsAlgClosed.splits D).natDegree_eq_card_roots.symm).symm
  have heval : D.eval s = D.leadingCoeff * (D.roots.map fun a => s - a).prod := by
    conv_lhs => rw [hfac]
    simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod, Multiset.map_map]
  rw [heval, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hle : ∀ a ∈ D.roots, ‖s‖ / 2 ≤ ‖s - a‖ := by
    intro a ha
    have ha_le : ‖a‖ ≤ (D.roots.map norm).sum :=
      Multiset.single_le_sum (fun y hy => by
        rcases Multiset.mem_map.mp hy with ⟨b, _, rfl⟩
        exact norm_nonneg b) ‖a‖ (Multiset.mem_map_of_mem norm ha)
    have htri : ‖s‖ ≤ ‖s - a‖ + ‖a‖ := by
      simpa [sub_add_cancel] using norm_add_le (s - a) a
    linarith
  have hprod_le : ∀ m : Multiset ℂ, (∀ a ∈ m, ‖s‖ / 2 ≤ ‖s - a‖) →
      (‖s‖ / 2) ^ m.card ≤ ‖(m.map fun a => s - a).prod‖ := by
    intro m hm
    induction m using Multiset.induction_on with
    | empty => simp
    | cons a m ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ', norm_mul]
      refine mul_le_mul (hm a (Multiset.mem_cons_self a m))
        (ih fun b hb => hm b (Multiset.mem_cons_of_mem hb)) (by positivity) (norm_nonneg _)
  rw [(IsAlgClosed.splits D).natDegree_eq_card_roots]
  exact hprod_le D.roots hle

theorem delayTransfer_rhp_bound (N D : Polynomial ℂ) (τ : ℝ)
    (hD0 : D ≠ 0) (hdeg : N.natDegree < D.natDegree) (hτ : 0 ≤ τ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℝ, 0 < R₀ ∧
      ∀ s : ℂ, 0 ≤ s.re → R₀ ≤ ‖s‖ → D.eval s ≠ 0 ∧ ‖delayTransfer N D τ s‖ < ε := by
  let CN : ℝ := ∑ i ∈ Finset.range (N.natDegree + 1), ‖N.coeff i‖
  let K : ℝ := (CN * (2 : ℝ) ^ D.natDegree) / ‖D.leadingCoeff‖
  let R₀ : ℝ := max 1 (max (2 * (D.roots.map norm).sum) ((K + 1) / ε))
  have hR₀_ge1 : 1 ≤ R₀ := le_max_left _ _
  have hR₀_pos : 0 < R₀ := lt_of_lt_of_le zero_lt_one hR₀_ge1
  refine ⟨R₀, hR₀_pos, fun s hsre hsR => ?_⟩
  have hs1 : 1 ≤ ‖s‖ := hR₀_ge1.trans hsR
  have hspos : 0 < ‖s‖ := lt_of_lt_of_le zero_lt_one hs1
  have hs_sum : 2 * (D.roots.map norm).sum ≤ ‖s‖ :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hsR
  have hD_ge : ‖D.leadingCoeff‖ * (‖s‖ / 2) ^ D.natDegree ≤ ‖D.eval s‖ :=
    norm_poly_eval_ge D hD0 hs_sum hspos
  have hlc_pos : 0 < ‖D.leadingCoeff‖ :=
    norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hD0)
  have hD_norm_pos : 0 < ‖D.eval s‖ :=
    lt_of_lt_of_le (mul_pos hlc_pos (pow_pos (by linarith) _)) hD_ge
  refine ⟨norm_pos_iff.mp hD_norm_pos, ?_⟩
  have hN_le : ‖N.eval s‖ ≤ CN * ‖s‖ ^ N.natDegree := norm_poly_eval_le N hs1
  have hexp_le : ‖Complex.exp (-τ * s)‖ ≤ 1 := norm_exp_neg_ofReal_mul_le_one hτ hsre
  have hdiv_le : ‖N.eval s / D.eval s‖ ≤ K * ‖s‖⁻¹ := by
    rw [norm_div]
    have hpow_le : ‖s‖ ^ N.natDegree ≤ ‖s‖ ^ D.natDegree * ‖s‖⁻¹ := by
      have hp : ‖s‖ ^ (N.natDegree + 1) ≤ ‖s‖ ^ D.natDegree := pow_le_pow_right₀ hs1 hdeg
      rw [pow_succ] at hp
      calc ‖s‖ ^ N.natDegree = (‖s‖ ^ N.natDegree * ‖s‖) * ‖s‖⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ hspos.ne', mul_one]
        _ ≤ ‖s‖ ^ D.natDegree * ‖s‖⁻¹ := mul_le_mul_of_nonneg_right hp (inv_nonneg.mpr hspos.le)
    have hdenom_pos : 0 < ‖D.leadingCoeff‖ * (‖s‖ / 2) ^ D.natDegree :=
      mul_pos hlc_pos (pow_pos (by linarith) _)
    calc ‖N.eval s‖ / ‖D.eval s‖
        ≤ (CN * ‖s‖ ^ N.natDegree) / (‖D.leadingCoeff‖ * (‖s‖ / 2) ^ D.natDegree) :=
          div_le_div₀ (by positivity) hN_le hdenom_pos hD_ge
      _ ≤ (CN * (‖s‖ ^ D.natDegree * ‖s‖⁻¹)) / (‖D.leadingCoeff‖ * (‖s‖ / 2) ^ D.natDegree) := by
          refine div_le_div_of_nonneg_right ?_ hdenom_pos.le
          exact mul_le_mul_of_nonneg_left hpow_le (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      _ = K * ‖s‖⁻¹ := by
          have hsD_ne : ‖s‖ ^ D.natDegree ≠ 0 := pow_ne_zero _ hspos.ne'
          dsimp only [K]
          rw [div_pow]
          field_simp [hlc_pos.ne', hsD_ne, hspos.ne']
  have hK_nonneg : 0 ≤ K := by
    have hCN : 0 ≤ CN := Finset.sum_nonneg fun _ _ => norm_nonneg _
    positivity
  have hR_bound : (K + 1) / ε ≤ ‖s‖ :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hsR
  have hK_lt : K * ‖s‖⁻¹ < ε := by
    have hinv_le : ‖s‖⁻¹ ≤ ε / (K + 1) := by
      have h1 : K + 1 ≤ ε * ‖s‖ := by linarith [(div_le_iff₀ hε).mp hR_bound]
      have hK1 : 0 < K + 1 := by linarith
      calc ‖s‖⁻¹ = ((K + 1) * ‖s‖⁻¹) / (K + 1) := by
            field_simp [hK1.ne']
        _ ≤ ((ε * ‖s‖) * ‖s‖⁻¹) / (K + 1) := by
            gcongr
        _ = ε / (K + 1) := by
            field_simp [hspos.ne']
    calc K * ‖s‖⁻¹ ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hinv_le hK_nonneg
      _ < (K + 1) * (ε / (K + 1)) :=
          mul_lt_mul_of_pos_right (by linarith) (div_pos hε (by linarith))
      _ = ε := by
          have hK1 : K + 1 ≠ 0 := by linarith
          field_simp [hK1]
  calc ‖delayTransfer N D τ s‖
      = ‖N.eval s / D.eval s‖ * ‖Complex.exp (-τ * s)‖ := by
        unfold delayTransfer
        rw [norm_mul]
    _ ≤ ‖N.eval s / D.eval s‖ * 1 := mul_le_mul_of_nonneg_left hexp_le (norm_nonneg _)
    _ = ‖N.eval s / D.eval s‖ := mul_one _
    _ ≤ K * ‖s‖⁻¹ := hdiv_le
    _ < ε := hK_lt

/-! ## 3. Orders, Finiteness of RHP Zeros, and Polynomial Root Counts -/

private lemma delayReturnDiff_eq_div {N D : Polynomial ℂ} {τ : ℝ} {s : ℂ} (hD : D.eval s ≠ 0) :
    delayReturnDiff N D τ s = delayCharQuasiPoly N D τ s / D.eval s := by
  unfold delayReturnDiff delayTransfer delayCharQuasiPoly
  field_simp [hD]

private lemma mem_slitPlane_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    (1 + z) ∈ Complex.slitPlane := by
  have hre : |z.re| < 1 := (abs_re_le_norm z).trans_lt hz
  have hpos : 0 < (1 + z).re := by
    rw [add_re, one_re]
    linarith [(abs_lt.mp hre).1]
  exact Complex.mem_slitPlane_iff.mpr (Or.inl hpos)

private lemma delayCharQuasiPoly_ne_zero_of_bound {N D : Polynomial ℂ} {τ : ℝ}
    (hD0 : D ≠ 0) (hdeg : N.natDegree < D.natDegree) (hτ : 0 ≤ τ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ s : ℂ, 0 ≤ s.re → R₀ ≤ ‖s‖ →
      D.eval s ≠ 0 ∧ delayReturnDiff N D τ s ∈ Complex.slitPlane ∧
        delayCharQuasiPoly N D τ s ≠ 0 := by
  obtain ⟨R₀, hR₀, hbound⟩ :=
    delayTransfer_rhp_bound N D τ hD0 hdeg hτ (ε := 1 / 2) (by norm_num)
  refine ⟨R₀, hR₀, fun s hsre hsR => ?_⟩
  obtain ⟨hDs, hTs⟩ := hbound s hsre hsR
  have hslit : delayReturnDiff N D τ s ∈ Complex.slitPlane :=
    mem_slitPlane_of_norm_lt_one (hTs.trans (by norm_num))
  have hFne : delayReturnDiff N D τ s ≠ 0 := fun h0 =>
    Complex.zero_notMem_slitPlane (h0 ▸ hslit)
  have hCne : delayCharQuasiPoly N D τ s ≠ 0 := by
    rw [delayReturnDiff_eq_div hDs] at hFne
    exact left_ne_zero_of_mul (by simpa [div_eq_mul_inv] using hFne)
  exact ⟨hDs, hslit, hCne⟩

private lemma delayCharQuasiPoly_meromorphicOrderAt_ne_top (N D : Polynomial ℂ) (τ : ℝ)
    (hD0 : D ≠ 0) (hdeg : N.natDegree < D.natDegree) (hτ : 0 ≤ τ) (z : ℂ) :
    meromorphicOrderAt (delayCharQuasiPoly N D τ) z ≠ ⊤ := by
  obtain ⟨R₀, hR₀, hbound⟩ := delayCharQuasiPoly_ne_zero_of_bound hD0 hdeg hτ
  have hz₀_re : 0 ≤ (R₀ : ℂ).re := by simpa using hR₀.le
  have hz₀_norm : R₀ ≤ ‖(R₀ : ℂ)‖ := by simp [abs_of_pos hR₀]
  have hz₀_ne : delayCharQuasiPoly N D τ (R₀ : ℂ) ≠ 0 := (hbound (R₀ : ℂ) hz₀_re hz₀_norm).2.2
  have han : AnalyticOnNhd ℂ (delayCharQuasiPoly N D τ) Set.univ :=
    delayCharQuasiPoly_analytic N D τ
  have hz₀_ord : meromorphicOrderAt (delayCharQuasiPoly N D τ) (R₀ : ℂ) ≠ ⊤ := by
    rw [(han (R₀ : ℂ) (Set.mem_univ _)).meromorphicOrderAt_eq,
      (han (R₀ : ℂ) (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hz₀_ne]
    simp
  exact han.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ _) (Set.mem_univ z) hz₀_ord

private lemma meromorphicOrderAt_prod_X_sub_C (m : Multiset ℂ) (u : ℂ) :
    meromorphicOrderAt (fun s : ℂ => ((m.map fun a => X - C a).prod).eval s) u =
      ((m.count u : ℤ) : WithTop ℤ) := by
  induction m using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, Polynomial.eval_one, Multiset.count_zero,
      Nat.cast_zero, WithTop.coe_zero]
    rw [analyticAt_const.meromorphicOrderAt_eq, analyticAt_const.analyticOrderAt_eq_zero.mpr
      one_ne_zero]
    simp
  | cons a m ih =>
    have hfun : (fun s : ℂ => (((a ::ₘ m).map fun b => X - C b).prod).eval s) =
        (fun s : ℂ => s - a) * (fun s : ℂ => ((m.map fun b => X - C b).prod).eval s) := by
      ext s
      simp [Multiset.map_cons, Multiset.prod_cons, Polynomial.eval_mul]
    rw [hfun]
    have h1 : MeromorphicAt (fun s : ℂ => s - a) u :=
      (analyticAt_id.sub analyticAt_const).meromorphicAt
    have h2 : MeromorphicAt (fun s : ℂ => ((m.map fun b => X - C b).prod).eval s) u :=
      (poly_eval_analyticOnNhd _ Set.univ u (Set.mem_univ _)).meromorphicAt
    rw [meromorphicOrderAt_mul h1 h2, ih]
    by_cases hua : u = a
    · subst hua
      have hord1 : meromorphicOrderAt (fun s : ℂ => s - u) u = (1 : WithTop ℤ) :=
        meromorphicOrderAt_id_sub_const
      rw [hord1, Multiset.count_cons_self]
      norm_cast
      omega
    · have hne : u - a ≠ 0 := sub_ne_zero.mpr hua
      have han1 : AnalyticAt ℂ (fun s : ℂ => s - a) u := analyticAt_id.sub analyticAt_const
      have hord1 : meromorphicOrderAt (fun s : ℂ => s - a) u = 0 := by
        rw [han1.meromorphicOrderAt_eq, han1.analyticOrderAt_eq_zero.mpr hne]
        simp
      rw [hord1, zero_add, Multiset.count_cons_of_ne hua]

private lemma meromorphicOrderAt_poly_eval (D : Polynomial ℂ) (hD0 : D ≠ 0) (u : ℂ) :
    meromorphicOrderAt (fun s : ℂ => D.eval s) u = ((D.roots.count u : ℤ) : WithTop ℤ) := by
  have hfac : D = C D.leadingCoeff * (D.roots.map fun a => X - C a).prod :=
    (C_leadingCoeff_mul_prod_multiset_X_sub_C
      (IsAlgClosed.splits D).natDegree_eq_card_roots.symm).symm
  have hfun : (fun s : ℂ => D.eval s) = (fun _ : ℂ => D.leadingCoeff) *
      (fun s : ℂ => ((D.roots.map fun a => X - C a).prod).eval s) := by
    ext s
    conv_lhs => rw [hfac]
    simp [Polynomial.eval_mul, Polynomial.eval_C]
  rw [hfun]
  have hlc : D.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hD0
  have h1 : MeromorphicAt (fun _ : ℂ => D.leadingCoeff) u := analyticAt_const.meromorphicAt
  have h2 : MeromorphicAt (fun s : ℂ => ((D.roots.map fun a => X - C a).prod).eval s) u :=
    (poly_eval_analyticOnNhd _ Set.univ u (Set.mem_univ _)).meromorphicAt
  have hord1 : meromorphicOrderAt (fun _ : ℂ => D.leadingCoeff) u = 0 := by
    rw [analyticAt_const.meromorphicOrderAt_eq, analyticAt_const.analyticOrderAt_eq_zero.mpr hlc]
    simp
  rw [meromorphicOrderAt_mul h1 h2, hord1, zero_add, meromorphicOrderAt_prod_X_sub_C]

private lemma poly_eval_meromorphicOrderAt_ne_top (D : Polynomial ℂ) (hD0 : D ≠ 0) (u : ℂ) :
    meromorphicOrderAt (fun s : ℂ => D.eval s) u ≠ ⊤ := by
  rw [meromorphicOrderAt_poly_eval D hD0 u]
  exact WithTop.coe_ne_top

private lemma meromorphicOrderAt_poly_eval_untop₀ (D : Polynomial ℂ) (hD0 : D ≠ 0) (u : ℂ) :
    (meromorphicOrderAt (fun s : ℂ => D.eval s) u).untop₀ = (D.roots.count u : ℤ) := by
  rw [meromorphicOrderAt_poly_eval D hD0 u, WithTop.untop₀_coe]

private lemma sum_count_eq_card_of_toFinset_subset {α : Type*} [DecidableEq α]
    (m : Multiset α) (S : Finset α) (hmS : m.toFinset ⊆ S) :
    ∑ u ∈ S, m.count u = m.card := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    have haS : a ∈ S := hmS (Multiset.mem_toFinset.mpr (Multiset.mem_cons_self a m))
    have hmS' : m.toFinset ⊆ S := fun x hx =>
      hmS (Multiset.mem_toFinset.mpr (Multiset.mem_cons_of_mem (Multiset.mem_toFinset.mp hx)))
    have hcount : ∑ u ∈ S, (a ::ₘ m).count u =
        ∑ u ∈ S, (m.count u + if u = a then 1 else 0) := by
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hua : u = a
      · subst hua; simp [Multiset.count_cons_self]
      · simp [Multiset.count_cons_of_ne hua, hua]
    rw [hcount, Finset.sum_add_distrib, ih hmS', Finset.sum_ite_eq']
    simp [haS]

private lemma rhpRootCount_eq_finsum (D : Polynomial ℂ) (hD0 : D ≠ 0) :
    (rhpRootCount D : ℂ) =
      ∑ᶠ u ∈ {s : ℂ | 0 < s.re},
        ((meromorphicOrderAt (fun s : ℂ => D.eval s) u).untop₀ : ℂ) := by
  classical
  let m : Multiset ℂ := D.roots.filter (fun z : ℂ => 0 < z.re)
  let S : Finset ℂ := m.toFinset
  have hsum_eq :
      ∑ᶠ u ∈ {s : ℂ | 0 < s.re},
        ((meromorphicOrderAt (fun s : ℂ => D.eval s) u).untop₀ : ℂ) =
      ∑ u ∈ S, ((meromorphicOrderAt (fun s : ℂ => D.eval s) u).untop₀ : ℂ) := by
    refine finsum_mem_eq_sum_of_subset _ ?_ ?_
    · rintro u ⟨hu_re, hu_supp⟩
      rw [Function.mem_support, ne_eq, Int.cast_eq_zero,
        meromorphicOrderAt_poly_eval_untop₀ D hD0 u, Int.natCast_eq_zero] at hu_supp
      have hu_mem : u ∈ D.roots := Multiset.count_pos.mp (Nat.pos_of_ne_zero hu_supp)
      exact Multiset.mem_toFinset.mpr (Multiset.mem_filter.mpr ⟨hu_mem, hu_re⟩)
    · intro u hu
      exact (Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hu)).2
  rw [hsum_eq]
  have hcast : ∑ u ∈ S, ((meromorphicOrderAt (fun s : ℂ => D.eval s) u).untop₀ : ℂ) =
      ((∑ u ∈ S, m.count u : ℕ) : ℂ) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu_re : 0 < u.re := (Multiset.mem_filter.mp (Multiset.mem_toFinset.mp hu)).2
    rw [meromorphicOrderAt_poly_eval_untop₀ D hD0 u]
    simp [m, hu_re]
  rw [hcast, sum_count_eq_card_of_toFinset_subset m S Finset.Subset.rfl]
  rfl

private lemma delayCharQuasiPoly_rhp_zeros_finite (N D : Polynomial ℂ) (τ : ℝ)
    (hD0 : D ≠ 0) (hdeg : N.natDegree < D.natDegree) (hτ : 0 ≤ τ) :
    {u : ℂ | 0 < u.re ∧ (meromorphicOrderAt (delayCharQuasiPoly N D τ) u).untop₀ ≠ 0}.Finite := by
  obtain ⟨R₀, hR₀, hbound⟩ := delayCharQuasiPoly_ne_zero_of_bound hD0 hdeg hτ
  have hmero : MeromorphicOn (delayCharQuasiPoly N D τ) (Metric.closedBall 0 (R₀ + 1)) :=
    delayCharQuasiPoly_meromorphicOn N D τ _
  have hfin : (MeromorphicOn.divisor (delayCharQuasiPoly N D τ)
      (Metric.ball 0 (R₀ + 1))).support.Finite :=
    hmero.divisor_ball_support_finite
  refine hfin.subset ?_
  rintro u ⟨hu_re, hu_ord⟩
  have hu_norm : ‖u‖ < R₀ + 1 := by
    by_contra hnot
    have hge : R₀ ≤ ‖u‖ := by linarith [not_lt.mp hnot]
    have hne : delayCharQuasiPoly N D τ u ≠ 0 := (hbound u hu_re.le hge).2.2
    have han := delayCharQuasiPoly_analytic N D τ u (Set.mem_univ u)
    have hord0 : meromorphicOrderAt (delayCharQuasiPoly N D τ) u = 0 := by
      rw [han.meromorphicOrderAt_eq, han.analyticOrderAt_eq_zero.mpr hne]
      simp
    exact hu_ord (by simp [hord0])
  have hu_ball : u ∈ Metric.ball (0 : ℂ) (R₀ + 1) := by simpa [Metric.mem_ball] using hu_norm
  rw [Function.mem_support, (delayCharQuasiPoly_meromorphicOn N D τ _).divisor_apply hu_ball]
  exact hu_ord

private lemma finsum_mem_eq_of_inter_support_eq {f : ℂ → ℂ} {A B : Set ℂ}
    (hfinA : (A ∩ Function.support f).Finite)
    (heq : A ∩ Function.support f = B ∩ Function.support f) :
    ∑ᶠ u ∈ A, f u = ∑ᶠ u ∈ B, f u := by
  have hfinB : (B ∩ Function.support f).Finite := heq ▸ hfinA
  have h1 : ∑ᶠ u ∈ A, f u = ∑ u ∈ hfinA.toFinset, f u :=
    finsum_mem_eq_sum_of_subset f (fun u hu => hfinA.mem_toFinset.mpr hu)
      (fun u hu => (hfinA.mem_toFinset.mp hu).1)
  have h2 : ∑ᶠ u ∈ B, f u = ∑ u ∈ hfinB.toFinset, f u :=
    finsum_mem_eq_sum_of_subset f (fun u hu => hfinB.mem_toFinset.mpr hu)
      (fun u hu => (hfinB.mem_toFinset.mp hu).1)
  rw [h1, h2]
  refine Finset.sum_congr (Finset.ext fun u => ?_) fun _ _ => rfl
  simp [Set.Finite.mem_toFinset, heq]

private lemma rhpRootCount_eq_rect_finsum (D : Polynomial ℂ) (hD0 : D ≠ 0)
    {R₀ R : ℝ} (_hR₀ : 0 < R₀) (hR : R₀ < R)
    (hbound : ∀ s : ℂ, 0 ≤ s.re → R₀ ≤ ‖s‖ → D.eval s ≠ 0) :
    ∑ᶠ u ∈ Set.Ioo (0 : ℝ) R ×ℂ Set.Ioo (-R) R,
      ((meromorphicOrderAt (fun s : ℂ => D.eval s) u).untop₀ : ℂ) =
    (rhpRootCount D : ℂ) := by
  rw [rhpRootCount_eq_finsum D hD0]
  refine finsum_mem_eq_of_inter_support_eq ?_ ?_
  · refine D.roots.toFinset.finite_toSet.subset ?_
    rintro u ⟨_, hne⟩
    rw [Function.mem_support, ne_eq, Int.cast_eq_zero,
      meromorphicOrderAt_poly_eval_untop₀ D hD0 u, Int.natCast_eq_zero] at hne
    exact Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (Nat.pos_of_ne_zero hne))
  ext u
  simp only [Set.mem_inter_iff, Function.mem_support, ne_eq, Int.cast_eq_zero,
    Complex.mem_reProdIm, Set.mem_Ioo, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨⟨h1, _⟩, _⟩, hne⟩
    exact ⟨h1, hne⟩
  · rintro ⟨hu_re, hne⟩
    have hu_norm : ‖u‖ < R₀ := by
      by_contra hnot
      have hge : R₀ ≤ ‖u‖ := not_lt.mp hnot
      have hDne := hbound u hu_re.le hge
      have han := poly_eval_analyticOnNhd D Set.univ u (Set.mem_univ u)
      have hord0 : meromorphicOrderAt (fun s : ℂ => D.eval s) u = 0 := by
        rw [han.meromorphicOrderAt_eq, han.analyticOrderAt_eq_zero.mpr hDne]
        simp
      exact hne (by simp [hord0])
    have hu_re_lt : u.re < R :=
      lt_of_le_of_lt ((le_abs_self u.re).trans (Complex.abs_re_le_norm u)) (hu_norm.trans hR)
    have hu_im_lt : |u.im| < R :=
      lt_of_le_of_lt (Complex.abs_im_le_norm u) (hu_norm.trans hR)
    exact ⟨⟨⟨hu_re, hu_re_lt⟩, abs_lt.mp hu_im_lt⟩, hne⟩

private lemma delayRhpZeroCount_eq_rect_finsum (N D : Polynomial ℂ) (τ : ℝ)
    (hD0 : D ≠ 0) (hdeg : N.natDegree < D.natDegree) (hτ : 0 ≤ τ)
    {R₀ R : ℝ} (hR : R₀ < R)
    (hbound : ∀ s : ℂ, 0 ≤ s.re → R₀ ≤ ‖s‖ → delayCharQuasiPoly N D τ s ≠ 0) :
    ∑ᶠ u ∈ Set.Ioo (0 : ℝ) R ×ℂ Set.Ioo (-R) R,
      ((meromorphicOrderAt (delayCharQuasiPoly N D τ) u).untop₀ : ℂ) =
    delayRhpZeroCount N D τ := by
  unfold delayRhpZeroCount
  refine finsum_mem_eq_of_inter_support_eq ?_ ?_
  · refine (delayCharQuasiPoly_rhp_zeros_finite N D τ hD0 hdeg hτ).subset ?_
    rintro u ⟨⟨⟨h1, _⟩, _⟩, hne⟩
    rw [Function.mem_support, ne_eq, Int.cast_eq_zero] at hne
    exact ⟨h1, hne⟩
  ext u
  simp only [Set.mem_inter_iff, Function.mem_support, ne_eq, Int.cast_eq_zero,
    Complex.mem_reProdIm, Set.mem_Ioo, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨⟨h1, _⟩, _⟩, hne⟩
    exact ⟨h1, hne⟩
  · rintro ⟨hu_re, hne⟩
    have hu_norm : ‖u‖ < R₀ := by
      by_contra hnot
      have hge : R₀ ≤ ‖u‖ := not_lt.mp hnot
      have hCne := hbound u hu_re.le hge
      have han := delayCharQuasiPoly_analytic N D τ u (Set.mem_univ u)
      have hord0 : meromorphicOrderAt (delayCharQuasiPoly N D τ) u = 0 := by
        rw [han.meromorphicOrderAt_eq, han.analyticOrderAt_eq_zero.mpr hCne]
        simp
      exact hne (by simp [hord0])
    have hu_re_lt : u.re < R :=
      lt_of_le_of_lt ((le_abs_self u.re).trans (Complex.abs_re_le_norm u)) (hu_norm.trans hR)
    have hu_im_lt : |u.im| < R :=
      lt_of_le_of_lt (Complex.abs_im_le_norm u) (hu_norm.trans hR)
    exact ⟨⟨⟨hu_re, hu_re_lt⟩, abs_lt.mp hu_im_lt⟩, hne⟩

/-! ## 4. Rectangle Contour Identity and Argument Principle -/

private lemma hasDerivAt_delayReturnDiff {N D : Polynomial ℂ} {τ : ℝ} {s : ℂ}
    (hDs : D.eval s ≠ 0) :
    DifferentiableAt ℂ (delayReturnDiff N D τ) s := by
  unfold delayReturnDiff delayTransfer
  refine (differentiableAt_const _).add ?_
  refine DifferentiableAt.mul ?_ ?_
  · refine DifferentiableAt.div ?_ ?_ hDs
    · exact (poly_eval_analyticOnNhd N Set.univ s (Set.mem_univ s)).differentiableAt
    · exact (poly_eval_analyticOnNhd D Set.univ s (Set.mem_univ s)).differentiableAt
  · exact ((differentiableAt_const (-(τ : ℂ))).mul differentiableAt_id).cexp

private lemma delayNyquistIntegrand_eq_I_mul_logDeriv {N D : Polynomial ℂ} {τ : ℝ} {ω : ℝ}
    (hDω : D.eval (I * ω) ≠ 0) :
    delayNyquistIntegrand N D τ ω = I * logDeriv (delayReturnDiff N D τ) (I * ω) := by
  have hdiff : DifferentiableAt ℂ (delayReturnDiff N D τ) (I * ω) :=
    hasDerivAt_delayReturnDiff hDω
  have h1 : HasDerivAt (delayReturnDiff N D τ) (deriv (delayReturnDiff N D τ) (I * ω)) (I * ω) :=
    hdiff.hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => I * (t : ℂ)) I ω := by
    simpa only [ofReal_one, mul_one, id_def] using (hasDerivAt_id ω).ofReal_comp.const_mul I
  have hcomp : HasDerivAt (fun t : ℝ => delayReturnDiff N D τ (I * t))
      (I * deriv (delayReturnDiff N D τ) (I * ω)) ω := by
    simpa only [Function.comp_def, smul_eq_mul] using h1.scomp ω h2
  unfold delayNyquistIntegrand
  rw [hcomp.deriv, logDeriv_apply]
  ring

private lemma logDeriv_delayReturnDiff_eq_div {N D : Polynomial ℂ} {τ : ℝ} {s : ℂ}
    (hDs : D.eval s ≠ 0) :
    logDeriv (delayReturnDiff N D τ) s =
      logDeriv (fun z : ℂ => delayCharQuasiPoly N D τ z / D.eval z) s := by
  have hev : delayReturnDiff N D τ =ᶠ[nhds s]
      fun z : ℂ => delayCharQuasiPoly N D τ z / D.eval z := by
    have hcont : ContinuousAt (fun z : ℂ => D.eval z) s :=
      (poly_eval_analyticOnNhd D Set.univ s (Set.mem_univ s)).continuousAt
    filter_upwards [hcont.eventually_ne hDs] with z hz
    exact delayReturnDiff_eq_div hz
  simp only [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]

private lemma norm_ge_of_mem_rect_outer {R : ℝ} (hR : 0 < R) :
    (∀ x ∈ [[(0 : ℝ), R]], R ≤ ‖(x : ℂ) + (-R : ℝ) * I‖) ∧
    (∀ x ∈ [[(0 : ℝ), R]], R ≤ ‖(x : ℂ) + (R : ℝ) * I‖) ∧
    (∀ y ∈ [[(-R : ℝ), R]], R ≤ ‖(R : ℂ) + y * I‖) := by
  refine ⟨fun x _ => ?_, fun x _ => ?_, fun y _ => ?_⟩
  · calc R = |(-R)| := by rw [abs_neg, abs_of_pos hR]
      _ = ‖((x : ℂ) + (-R : ℝ) * I).im‖ := by simp
      _ ≤ ‖(x : ℂ) + (-R : ℝ) * I‖ := Complex.abs_im_le_norm _
  · calc R = |R| := (abs_of_pos hR).symm
      _ = ‖((x : ℂ) + (R : ℝ) * I).im‖ := by simp
      _ ≤ ‖(x : ℂ) + (R : ℝ) * I‖ := Complex.abs_im_le_norm _
  · calc R = |R| := (abs_of_pos hR).symm
      _ = ‖((R : ℂ) + y * I).re‖ := by simp
      _ ≤ ‖(R : ℂ) + y * I‖ := Complex.abs_re_le_norm _

private lemma re_nonneg_of_mem_rect_outer {R : ℝ} (hR : 0 < R) :
    (∀ x ∈ [[(0 : ℝ), R]], 0 ≤ ((x : ℂ) + (-R : ℝ) * I).re) ∧
    (∀ x ∈ [[(0 : ℝ), R]], 0 ≤ ((x : ℂ) + (R : ℝ) * I).re) ∧
    (∀ y ∈ [[(-R : ℝ), R]], 0 ≤ ((R : ℂ) + y * I).re) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun y _ => ?_⟩
  · rw [Set.uIcc_of_le hR.le] at hx
    simpa using hx.1
  · rw [Set.uIcc_of_le hR.le] at hx
    simpa using hx.1
  · simpa using hR.le

private lemma continuousOn_logDeriv_of_ne {f : ℂ → ℂ} {K : Set ℂ}
    (han : ∀ s ∈ K, AnalyticAt ℂ f s) (hne : ∀ s ∈ K, f s ≠ 0) :
    ContinuousOn (logDeriv f) K := by
  intro s hs
  have ha := han s hs
  exact ((ha.deriv.continuousAt.div ha.continuousAt (hne s hs))).continuousWithinAt

private lemma analyticAt_delayReturnDiff {N D : Polynomial ℂ} {τ : ℝ} {s : ℂ}
    (hDs : D.eval s ≠ 0) :
    AnalyticAt ℂ (delayReturnDiff N D τ) s := by
  unfold delayReturnDiff delayTransfer
  refine analyticAt_const.add ?_
  refine AnalyticAt.mul ?_ ?_
  · refine AnalyticAt.div ?_ ?_ hDs
    · exact poly_eval_analyticOnNhd N Set.univ s (Set.mem_univ s)
    · exact poly_eval_analyticOnNhd D Set.univ s (Set.mem_univ s)
  · exact (analyticAt_const.mul analyticAt_id).cexp

private lemma integral_logDeriv_horiz (N D : Polynomial ℂ) (τ : ℝ) (y R : ℝ)
    (hbound : ∀ x ∈ [[(0 : ℝ), R]],
      D.eval (x + y * I) ≠ 0 ∧ delayReturnDiff N D τ (x + y * I) ∈ Complex.slitPlane) :
    (∫ x : ℝ in (0 : ℝ)..R, logDeriv (delayReturnDiff N D τ) (x + y * I)) =
      Complex.log (delayReturnDiff N D τ (R + y * I)) -
        Complex.log (delayReturnDiff N D τ ((0 : ℝ) + y * I)) := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) R,
      HasDerivAt (fun t : ℝ => Complex.log (delayReturnDiff N D τ (t + y * I)))
        (logDeriv (delayReturnDiff N D τ) (x + y * I)) x := by
    intro x hx
    have hs := hbound x hx
    have hFdiff : HasDerivAt (delayReturnDiff N D τ)
        (deriv (delayReturnDiff N D τ) (x + y * I)) (x + y * I) :=
      (hasDerivAt_delayReturnDiff hs.1).hasDerivAt
    have hline : HasDerivAt (fun t : ℝ => (t : ℂ) + (y : ℂ) * I) 1 x := by
      simpa using (hasDerivAt_id x).ofReal_comp.add_const ((y : ℂ) * I)
    have hcomp := (hFdiff.scomp x hline).clog_real
      (by simpa only [Function.comp_def] using hs.2)
    refine hcomp.congr_deriv ?_
    dsimp only [Function.comp_def]
    rw [logDeriv_apply, smul_eq_mul, one_mul]
  have hint : IntervalIntegrable
      (fun x : ℝ => logDeriv (delayReturnDiff N D τ) (x + y * I)) volume 0 R := by
    refine ContinuousOn.intervalIntegrable fun x hx => ?_
    have hs := hbound x hx
    have hFne : delayReturnDiff N D τ (x + y * I) ≠ 0 :=
      fun h0 => Complex.zero_notMem_slitPlane (h0 ▸ hs.2)
    have han := analyticAt_delayReturnDiff (N := N) (D := D) (τ := τ) hs.1
    have hlog_cont : ContinuousAt (logDeriv (delayReturnDiff N D τ)) (x + y * I) :=
      han.deriv.continuousAt.div han.continuousAt hFne
    have hline_cont : ContinuousAt (fun t : ℝ => (t : ℂ) + (y : ℂ) * I) x :=
      Complex.continuous_ofReal.continuousAt.add continuousAt_const
    have hcomp_cont : ContinuousAt
        (logDeriv (delayReturnDiff N D τ) ∘ fun t : ℝ => (t : ℂ) + (y : ℂ) * I) x :=
      Filter.Tendsto.comp hlog_cont hline_cont
    exact hcomp_cont.continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

private lemma integral_logDeriv_vert (N D : Polynomial ℂ) (τ : ℝ) (x R : ℝ)
    (hbound : ∀ y ∈ [[(-R : ℝ), R]],
      D.eval (x + y * I) ≠ 0 ∧ delayReturnDiff N D τ (x + y * I) ∈ Complex.slitPlane) :
    I • (∫ y : ℝ in (-R)..R, logDeriv (delayReturnDiff N D τ) (x + y * I)) =
      Complex.log (delayReturnDiff N D τ (x + (R : ℝ) * I)) -
        Complex.log (delayReturnDiff N D τ (x + (-R : ℝ) * I)) := by
  rw [← intervalIntegral.integral_smul]
  have hderiv : ∀ y ∈ Set.uIcc (-R) R,
      HasDerivAt (fun t : ℝ => Complex.log (delayReturnDiff N D τ (x + t * I)))
        (I • logDeriv (delayReturnDiff N D τ) (x + y * I)) y := by
    intro y hy
    have hs := hbound y hy
    have hFdiff : HasDerivAt (delayReturnDiff N D τ)
        (deriv (delayReturnDiff N D τ) (x + y * I)) (x + y * I) :=
      (hasDerivAt_delayReturnDiff hs.1).hasDerivAt
    have hline : HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * I) I y := by
      simpa using ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (x : ℂ)
    have hcomp := (hFdiff.scomp y hline).clog_real
      (by simpa only [Function.comp_def] using hs.2)
    refine hcomp.congr_deriv ?_
    dsimp only [Function.comp_def]
    rw [logDeriv_apply, smul_eq_mul, smul_eq_mul, mul_div_assoc]
  have hint : IntervalIntegrable
      (fun y : ℝ => I • logDeriv (delayReturnDiff N D τ) (x + y * I)) volume (-R) R := by
    refine IntervalIntegrable.smul (ContinuousOn.intervalIntegrable fun y hy => ?_) I
    have hs := hbound y hy
    have hFne : delayReturnDiff N D τ (x + y * I) ≠ 0 :=
      fun h0 => Complex.zero_notMem_slitPlane (h0 ▸ hs.2)
    have han := analyticAt_delayReturnDiff (N := N) (D := D) (τ := τ) hs.1
    have hlog_cont : ContinuousAt (logDeriv (delayReturnDiff N D τ)) (x + y * I) :=
      han.deriv.continuousAt.div han.continuousAt hFne
    have hline_cont : ContinuousAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * I) y :=
      continuousAt_const.add (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)
    have hcomp_cont : ContinuousAt
        (logDeriv (delayReturnDiff N D τ) ∘ fun t : ℝ => (x : ℂ) + (t : ℂ) * I) y :=
      Filter.Tendsto.comp hlog_cont hline_cont
    exact hcomp_cont.continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

private lemma rectBoundaryIntegral_logDeriv_delayReturnDiff
    (N D : Polynomial ℂ) (τ : ℝ) (hD : NoImagAxisRoots D)
    {R₀ R : ℝ} (hR₀ : 0 < R₀) (hR : R₀ < R)
    (hbound : ∀ s : ℂ, 0 ≤ s.re → R₀ ≤ ‖s‖ →
      D.eval s ≠ 0 ∧ delayReturnDiff N D τ s ∈ Complex.slitPlane) :
    rectBoundaryIntegral (logDeriv (delayReturnDiff N D τ)) (-I * R) (R + I * R) =
      (Complex.log (delayReturnDiff N D τ (I * R)) -
        Complex.log (delayReturnDiff N D τ (-I * R))) -
        ∫ ω in (-R)..R, delayNyquistIntegrand N D τ ω := by
  have hR_pos : 0 < R := hR₀.trans hR
  have hnorm := norm_ge_of_mem_rect_outer hR_pos
  have hre := re_nonneg_of_mem_rect_outer hR_pos
  have hzre_eq : (-I * (R : ℂ)).re = 0 := by simp
  have hzim_eq : (-I * (R : ℂ)).im = -R := by simp
  have hwre_eq : ((R : ℂ) + I * R).re = R := by simp
  have hwim_eq : ((R : ℂ) + I * R).im = R := by simp
  unfold rectBoundaryIntegral
  rw [hzre_eq, hzim_eq, hwre_eq, hwim_eq]
  have hbot := integral_logDeriv_horiz N D τ (-R) R fun x hx =>
    hbound _ (hre.1 x hx) (hR.le.trans (hnorm.1 x hx))
  have htop := integral_logDeriv_horiz N D τ R R fun x hx =>
    hbound _ (hre.2.1 x hx) (hR.le.trans (hnorm.2.1 x hx))
  have hright := integral_logDeriv_vert N D τ R R fun y hy =>
    hbound _ (hre.2.2 y hy) (hR.le.trans (hnorm.2.2 y hy))
  have hleft : I • (∫ y : ℝ in (-R)..R,
      logDeriv (delayReturnDiff N D τ) ((0 : ℝ) + y * I)) =
      ∫ ω in (-R)..R, delayNyquistIntegrand N D τ ω := by
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun ω _ => ?_
    have hDω : D.eval (I * ω) ≠ 0 := hD ω
    rw [smul_eq_mul, delayNyquistIntegrand_eq_I_mul_logDeriv hDω]
    simp [mul_comm]
  rw [hbot, htop, hright, hleft]
  have heq1 : ((0 : ℝ) : ℂ) + (-R : ℝ) * I = -I * R := by push_cast; ring
  have heq2 : ((0 : ℝ) : ℂ) + (R : ℝ) * I = I * R := by push_cast; ring
  rw [heq1, heq2]
  ring

private lemma delayNyquistEncirclementsCCW_eq
    (N D : Polynomial ℂ) (τ : ℝ) (hD0 : D ≠ 0) (hdeg : N.natDegree < D.natDegree) (hτ : 0 ≤ τ)
    (hD : NoImagAxisRoots D) (hC : ∀ ω : ℝ, delayCharQuasiPoly N D τ (I * ω) ≠ 0) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ < R →
      delayNyquistEncirclementsCCW N D τ R =
        ((rhpRootCount D : ℂ) - delayRhpZeroCount N D τ) +
          (2 * Real.pi * I)⁻¹ *
            (Complex.log (delayReturnDiff N D τ (I * R)) -
              Complex.log (delayReturnDiff N D τ (-I * R))) := by
  obtain ⟨R₀, hR₀, hbound⟩ := delayCharQuasiPoly_ne_zero_of_bound hD0 hdeg hτ
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  have hR_pos : 0 < R := hR₀.trans hR
  set f : ℂ → ℂ := fun s => delayCharQuasiPoly N D τ s / D.eval s
  set U : Set ℂ := Metric.ball 0 (2 * R + 1)
  have hU : IsOpen U := Metric.isOpen_ball
  set z : ℂ := -I * R
  set w : ℂ := R + I * R
  have hzre_eq : z.re = 0 := by simp [z]
  have hzim_eq : z.im = -R := by simp [z]
  have hwre_eq : w.re = R := by simp [w]
  have hwim_eq : w.im = R := by simp [w]
  have hzre : z.re < w.re := by rw [hzre_eq, hwre_eq]; exact hR_pos
  have hzim : z.im < w.im := by rw [hzim_eq, hwim_eq]; linarith
  have hcU : [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ U := by
    intro s hs
    rcases hs with ⟨hsre, hsim⟩
    rw [hzre_eq, hwre_eq, Set.uIcc_of_le hR_pos.le] at hsre
    rw [hzim_eq, hwim_eq, Set.uIcc_of_le (by linarith : -R ≤ R)] at hsim
    have hs_re_bound : |s.re| ≤ R := abs_le.mpr (by constructor <;> linarith [hsre.1, hsre.2])
    have hs_im_bound : |s.im| ≤ R := abs_le.mpr (by constructor <;> linarith [hsim.1, hsim.2])
    have hnorm : ‖s‖ ≤ 2 * R := by
      have hre_im : s = (s.re : ℂ) + (s.im : ℂ) * I := by apply Complex.ext <;> simp
      calc ‖s‖ = ‖(s.re : ℂ) + (s.im : ℂ) * I‖ := by conv_lhs => rw [hre_im]
        _ ≤ ‖(s.re : ℂ)‖ + ‖(s.im : ℂ) * I‖ := norm_add_le _ _
        _ = |s.re| + |s.im| := by simp
        _ ≤ R + R := add_le_add hs_re_bound hs_im_bound
        _ = 2 * R := by ring
    simp only [U, Metric.mem_ball, dist_zero_right]
    linarith
  have hf_cb : MeromorphicOn f (Metric.closedBall 0 (2 * R + 1)) :=
    (delayCharQuasiPoly_meromorphicOn N D τ _).div
      (poly_eval_analyticOnNhd D _).meromorphicOn
  have hf : MeromorphicOn f U := fun s hs => hf_cb s (Metric.ball_subset_closedBall hs)
  have hf_ord : ∀ u : ℂ, meromorphicOrderAt f u =
      meromorphicOrderAt (delayCharQuasiPoly N D τ) u -
        meromorphicOrderAt (fun s : ℂ => D.eval s) u := by
    intro u
    exact meromorphicOrderAt_div
      ((delayCharQuasiPoly_analytic N D τ u (Set.mem_univ u)).meromorphicAt)
      ((poly_eval_analyticOnNhd D Set.univ u (Set.mem_univ u)).meromorphicAt)
  have hf_ne : ∀ u ∈ U, meromorphicOrderAt f u ≠ ⊤ := by
    intro u _
    rw [hf_ord u]
    have h1 := delayCharQuasiPoly_meromorphicOrderAt_ne_top N D τ hD0 hdeg hτ u
    have h2 := poly_eval_meromorphicOrderAt_ne_top D hD0 u
    lift meromorphicOrderAt (delayCharQuasiPoly N D τ) u to ℤ using h1 with n hn
    lift meromorphicOrderAt (fun s : ℂ => D.eval s) u to ℤ using h2 with m hm
    rw [show (n : WithTop ℤ) - (m : WithTop ℤ) = ((n - m : ℤ) : WithTop ℤ) from rfl]
    exact WithTop.coe_ne_top
  have hfin : (MeromorphicOn.divisor f U).support.Finite := hf_cb.divisor_ball_support_finite
  have hf_ne_bdry : ∀ s : ℂ, D.eval s ≠ 0 → delayCharQuasiPoly N D τ s ≠ 0 →
      s ∉ (MeromorphicOn.divisor f U).support := by
    intro s hDs hCs hsupp
    have hsU : s ∈ U := (MeromorphicOn.divisor f U).supportWithinDomain hsupp
    have hf_an : AnalyticAt ℂ f s :=
      (delayCharQuasiPoly_analytic N D τ s (Set.mem_univ s)).div
        (poly_eval_analyticOnNhd D Set.univ s (Set.mem_univ s)) hDs
    have hf_val : f s ≠ 0 := div_ne_zero hCs hDs
    have hord0 : meromorphicOrderAt f s = 0 := by
      rw [hf_an.meromorphicOrderAt_eq, hf_an.analyticOrderAt_eq_zero.mpr hf_val]
      simp
    rw [Function.mem_support, hf.divisor_apply hsU, hord0] at hsupp
    exact hsupp rfl
  have hnorm_bdry := norm_ge_of_mem_rect_outer hR_pos
  have hre_bdry := re_nonneg_of_mem_rect_outer hR_pos
  have hb : ∀ x ∈ [[z.re, w.re]], (x : ℂ) + z.im * I ∉ (MeromorphicOn.divisor f U).support := by
    intro x hx
    rw [hzre_eq, hwre_eq] at hx
    rw [hzim_eq]
    have hs := hbound _ (hre_bdry.1 x hx) (hR.le.trans (hnorm_bdry.1 x hx))
    exact hf_ne_bdry _ hs.1 hs.2.2
  have ht : ∀ x ∈ [[z.re, w.re]], (x : ℂ) + w.im * I ∉ (MeromorphicOn.divisor f U).support := by
    intro x hx
    rw [hzre_eq, hwre_eq] at hx
    rw [hwim_eq]
    have hs := hbound _ (hre_bdry.2.1 x hx) (hR.le.trans (hnorm_bdry.2.1 x hx))
    exact hf_ne_bdry _ hs.1 hs.2.2
  have hl : ∀ y ∈ [[z.im, w.im]], (z.re : ℂ) + y * I ∉ (MeromorphicOn.divisor f U).support := by
    intro y _
    rw [hzre_eq]
    have h0y : ((0 : ℝ) : ℂ) + (y : ℂ) * I = I * y := by simp [mul_comm]
    rw [h0y]
    exact hf_ne_bdry _ (hD y) (hC y)
  have hr : ∀ y ∈ [[z.im, w.im]], (w.re : ℂ) + y * I ∉ (MeromorphicOn.divisor f U).support := by
    intro y hy
    rw [hzim_eq, hwim_eq] at hy
    rw [hwre_eq]
    have hs := hbound _ (hre_bdry.2.2 y hy) (hR.le.trans (hnorm_bdry.2.2 y hy))
    exact hf_ne_bdry _ hs.1 hs.2.2
  have harg := argumentPrinciple_rect hzre hzim hU hcU hf hf_ne hfin hb ht hl hr
  have hcongr_rect :
      rectBoundaryIntegral (logDeriv f) z w =
        rectBoundaryIntegral (logDeriv (delayReturnDiff N D τ)) z w := by
    unfold rectBoundaryIntegral
    have hi1 : (∫ x : ℝ in z.re..w.re, logDeriv f (x + z.im * I)) =
        ∫ x : ℝ in z.re..w.re, logDeriv (delayReturnDiff N D τ) (x + z.im * I) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [hzre_eq, hwre_eq] at hx
      rw [hzim_eq]
      exact (logDeriv_delayReturnDiff_eq_div
        (hbound _ (hre_bdry.1 x hx) (hR.le.trans (hnorm_bdry.1 x hx))).1).symm
    have hi2 : (∫ x : ℝ in z.re..w.re, logDeriv f (x + w.im * I)) =
        ∫ x : ℝ in z.re..w.re, logDeriv (delayReturnDiff N D τ) (x + w.im * I) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [hzre_eq, hwre_eq] at hx
      rw [hwim_eq]
      exact (logDeriv_delayReturnDiff_eq_div
        (hbound _ (hre_bdry.2.1 x hx) (hR.le.trans (hnorm_bdry.2.1 x hx))).1).symm
    have hi3 : (∫ y : ℝ in z.im..w.im, logDeriv f (w.re + y * I)) =
        ∫ y : ℝ in z.im..w.im, logDeriv (delayReturnDiff N D τ) (w.re + y * I) := by
      refine intervalIntegral.integral_congr fun y hy => ?_
      rw [hzim_eq, hwim_eq] at hy
      rw [hwre_eq]
      exact (logDeriv_delayReturnDiff_eq_div
        (hbound _ (hre_bdry.2.2 y hy) (hR.le.trans (hnorm_bdry.2.2 y hy))).1).symm
    have hi4 : (∫ y : ℝ in z.im..w.im, logDeriv f (z.re + y * I)) =
        ∫ y : ℝ in z.im..w.im, logDeriv (delayReturnDiff N D τ) (z.re + y * I) := by
      refine intervalIntegral.integral_congr fun y _ => ?_
      rw [hzre_eq]
      have h0y : ((0 : ℝ) : ℂ) + (y : ℂ) * I = I * y := by simp [mul_comm]
      rw [h0y]
      exact (logDeriv_delayReturnDiff_eq_div (hD y)).symm
    rw [hi1, hi2, hi3, hi4]
  have hRHS_eq :
      ∑ᶠ u ∈ Set.Ioo z.re w.re ×ℂ Set.Ioo z.im w.im, ((meromorphicOrderAt f u).untop₀ : ℂ) =
        delayRhpZeroCount N D τ - (rhpRootCount D : ℂ) := by
    rw [hzre_eq, hwre_eq, hzim_eq, hwim_eq]
    have huntop : ∀ u : ℂ, ((meromorphicOrderAt f u).untop₀ : ℂ) =
        ((meromorphicOrderAt (delayCharQuasiPoly N D τ) u).untop₀ : ℂ) -
          ((meromorphicOrderAt (fun s : ℂ => D.eval s) u).untop₀ : ℂ) := by
      intro u
      rw [hf_ord u]
      have h1 := delayCharQuasiPoly_meromorphicOrderAt_ne_top N D τ hD0 hdeg hτ u
      have h2 := poly_eval_meromorphicOrderAt_ne_top D hD0 u
      lift meromorphicOrderAt (delayCharQuasiPoly N D τ) u to ℤ using h1 with n hn
      lift meromorphicOrderAt (fun s : ℂ => D.eval s) u to ℤ using h2 with m hm
      rw [show (n : WithTop ℤ) - (m : WithTop ℤ) = ((n - m : ℤ) : WithTop ℤ) from rfl,
        WithTop.untop₀_coe, WithTop.untop₀_coe, WithTop.untop₀_coe, Int.cast_sub]
    simp_rw [huntop]
    have hfin_C : ({u : ℂ | u ∈ Set.Ioo (0 : ℝ) R ×ℂ Set.Ioo (-R) R} ∩
        Function.support (fun u : ℂ =>
          ((meromorphicOrderAt (delayCharQuasiPoly N D τ) u).untop₀ : ℂ))).Finite := by
      refine (delayCharQuasiPoly_rhp_zeros_finite N D τ hD0 hdeg hτ).subset ?_
      rintro u ⟨⟨⟨h1, _⟩, _⟩, hne⟩
      rw [Function.mem_support, ne_eq, Int.cast_eq_zero] at hne
      exact ⟨h1, hne⟩
    have hfin_D : ({u : ℂ | u ∈ Set.Ioo (0 : ℝ) R ×ℂ Set.Ioo (-R) R} ∩
        Function.support (fun u : ℂ =>
          ((meromorphicOrderAt (fun s : ℂ => D.eval s) u).untop₀ : ℂ))).Finite := by
      refine D.roots.toFinset.finite_toSet.subset ?_
      rintro u ⟨_, hne⟩
      rw [Function.mem_support, ne_eq, Int.cast_eq_zero,
        meromorphicOrderAt_poly_eval_untop₀ D hD0 u, Int.natCast_eq_zero] at hne
      exact Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (Nat.pos_of_ne_zero hne))
    have hS_sub : ∑ᶠ u ∈ Set.Ioo (0 : ℝ) R ×ℂ Set.Ioo (-R) R,
        (((meromorphicOrderAt (delayCharQuasiPoly N D τ) u).untop₀ : ℂ) -
          ((meromorphicOrderAt (fun s : ℂ => D.eval s) u).untop₀ : ℂ)) =
        (∑ᶠ u ∈ Set.Ioo (0 : ℝ) R ×ℂ Set.Ioo (-R) R,
          ((meromorphicOrderAt (delayCharQuasiPoly N D τ) u).untop₀ : ℂ)) -
        (∑ᶠ u ∈ Set.Ioo (0 : ℝ) R ×ℂ Set.Ioo (-R) R,
          ((meromorphicOrderAt (fun s : ℂ => D.eval s) u).untop₀ : ℂ)) := by
      let A : Set ℂ := Set.Ioo (0 : ℝ) R ×ℂ Set.Ioo (-R) R
      let g₁ : ℂ → ℂ := fun u => ((meromorphicOrderAt (delayCharQuasiPoly N D τ) u).untop₀ : ℂ)
      let g₂ : ℂ → ℂ := fun u => ((meromorphicOrderAt (fun s : ℂ => D.eval s) u).untop₀ : ℂ)
      let S : Finset ℂ := hfin_C.toFinset ∪ hfin_D.toFinset
      have hSA : (S : Set ℂ) ⊆ A := by
        intro u hu
        rcases Finset.mem_union.mp hu with h1 | h2
        · exact (hfin_C.mem_toFinset.mp h1).1
        · exact (hfin_D.mem_toFinset.mp h2).1
      have hsum12 : ∑ᶠ u ∈ A, (g₁ u - g₂ u) = ∑ u ∈ S, (g₁ u - g₂ u) := by
        refine finsum_mem_eq_sum_of_subset _ ?_ (fun u hu => hSA hu)
        rintro u ⟨huA, hne⟩
        rw [Function.mem_support, sub_ne_zero] at hne
        by_cases h1 : g₁ u = 0
        · have h2 : g₂ u ≠ 0 := fun h2 => hne (by rw [h1, h2])
          exact Finset.mem_coe.mpr (Finset.mem_union_right _ (hfin_D.mem_toFinset.mpr ⟨huA, h2⟩))
        · exact Finset.mem_coe.mpr (Finset.mem_union_left _ (hfin_C.mem_toFinset.mpr ⟨huA, h1⟩))
      have hsum1 : ∑ᶠ u ∈ A, g₁ u = ∑ u ∈ S, g₁ u := by
        refine finsum_mem_eq_sum_of_subset _ ?_ (fun u hu => hSA hu)
        rintro u hu
        exact Finset.mem_coe.mpr (Finset.mem_union_left _ (hfin_C.mem_toFinset.mpr hu))
      have hsum2 : ∑ᶠ u ∈ A, g₂ u = ∑ u ∈ S, g₂ u := by
        refine finsum_mem_eq_sum_of_subset _ ?_ (fun u hu => hSA hu)
        rintro u hu
        exact Finset.mem_coe.mpr (Finset.mem_union_right _ (hfin_D.mem_toFinset.mpr hu))
      rw [hsum12, hsum1, hsum2, Finset.sum_sub_distrib]
    rw [hS_sub]
    rw [delayRhpZeroCount_eq_rect_finsum N D τ hD0 hdeg hτ hR
        (fun s hs1 hs2 => (hbound s hs1 hs2).2.2),
      rhpRootCount_eq_rect_finsum D hD0 hR₀ hR (fun s hs1 hs2 => (hbound s hs1 hs2).1)]
  rw [hcongr_rect, rectBoundaryIntegral_logDeriv_delayReturnDiff N D τ hD hR₀ hR
    (fun s hs1 hs2 => ⟨(hbound s hs1 hs2).1, (hbound s hs1 hs2).2.1⟩)] at harg
  rw [hRHS_eq] at harg
  unfold delayNyquistEncirclementsCCW
  rw [one_div]
  have heq : (2 * (Real.pi : ℂ) * I)⁻¹ *
      ((Complex.log (delayReturnDiff N D τ (I * R)) -
          Complex.log (delayReturnDiff N D τ (-I * R))) -
        ∫ ω in (-R)..R, delayNyquistIntegrand N D τ ω) =
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        (Complex.log (delayReturnDiff N D τ (I * R)) -
          Complex.log (delayReturnDiff N D τ (-I * R))) -
      (2 * (Real.pi : ℂ) * I)⁻¹ * ∫ ω in (-R)..R, delayNyquistIntegrand N D τ ω := by
    ring
  rw [heq] at harg
  linear_combination -harg

/-! ## 5. Main Nyquist Stability Theorems for Time-Delay Systems -/

private lemma tendsto_delayReturnDiff_imagAxis_atTop (N D : Polynomial ℂ) (τ : ℝ)
    (hD0 : D ≠ 0) (hdeg : N.natDegree < D.natDegree) (hτ : 0 ≤ τ) :
    Tendsto (fun R : ℝ => delayReturnDiff N D τ (I * R)) atTop (nhds 1) ∧
      Tendsto (fun R : ℝ => delayReturnDiff N D τ (-I * R)) atTop (nhds 1) := by
  have htend_T_pos : Tendsto (fun R : ℝ => delayTransfer N D τ (I * R)) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨R₀, _, hbound⟩ := delayTransfer_rhp_bound N D τ hD0 hdeg hτ hε
    refine ⟨R₀, fun R hR => ?_⟩
    have hre : 0 ≤ (I * (R : ℂ)).re := by simp
    have hnorm : R₀ ≤ ‖I * (R : ℂ)‖ := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact hR.trans (le_abs_self R)
    simpa [dist_zero_right] using (hbound (I * R) hre hnorm).2
  have htend_T_neg : Tendsto (fun R : ℝ => delayTransfer N D τ (-I * R)) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨R₀, _, hbound⟩ := delayTransfer_rhp_bound N D τ hD0 hdeg hτ hε
    refine ⟨R₀, fun R hR => ?_⟩
    have hre : 0 ≤ (-I * (R : ℂ)).re := by simp
    have hnorm : R₀ ≤ ‖-I * (R : ℂ)‖ := by
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact hR.trans (le_abs_self R)
    simpa [dist_zero_right] using (hbound (-I * R) hre hnorm).2
  refine ⟨?_, ?_⟩
  · simpa [delayReturnDiff] using tendsto_const_nhds.add htend_T_pos
  · simpa [delayReturnDiff] using tendsto_const_nhds.add htend_T_neg

/-- The Nyquist winding integral along `[-i R, i R]` converges to `P - Z_τ` as `R → ∞`, where
`P = rhpRootCount D` is the number of open-RHP poles of `L_τ` and `Z_τ = delayRhpZeroCount N D τ`
is the number of open-RHP zeros of the characteristic quasipolynomial `D(s) + N(s) exp(-τ s)`. -/
theorem nyquist_delay_encirclement_tendsto (N D : Polynomial ℂ) (τ : ℝ)
    (hD0 : D ≠ 0) (hdeg : N.natDegree < D.natDegree) (hτ : 0 ≤ τ)
    (hD : NoImagAxisRoots D) (hC : ∀ ω : ℝ, delayCharQuasiPoly N D τ (I * ω) ≠ 0) :
    Tendsto (delayNyquistEncirclementsCCW N D τ) atTop
      (nhds ((rhpRootCount D : ℂ) - delayRhpZeroCount N D τ)) := by
  obtain ⟨R₀, _, hformula⟩ :=
    delayNyquistEncirclementsCCW_eq N D τ hD0 hdeg hτ hD hC
  have htend_F := tendsto_delayReturnDiff_imagAxis_atTop N D τ hD0 hdeg hτ
  have hlog_pos : Tendsto (fun R : ℝ => Complex.log (delayReturnDiff N D τ (I * R)))
      atTop (nhds 0) := by
    rw [← Complex.log_one]
    exact htend_F.1.clog Complex.one_mem_slitPlane
  have hlog_neg : Tendsto (fun R : ℝ => Complex.log (delayReturnDiff N D τ (-I * R)))
      atTop (nhds 0) := by
    rw [← Complex.log_one]
    exact htend_F.2.clog Complex.one_mem_slitPlane
  have herr : Tendsto
      (fun R : ℝ => ((rhpRootCount D : ℂ) - delayRhpZeroCount N D τ) +
        (2 * Real.pi * I)⁻¹ *
          (Complex.log (delayReturnDiff N D τ (I * R)) -
            Complex.log (delayReturnDiff N D τ (-I * R))))
      atTop (nhds ((rhpRootCount D : ℂ) - delayRhpZeroCount N D τ)) := by
    have hdiff : Tendsto
        (fun R : ℝ => Complex.log (delayReturnDiff N D τ (I * R)) -
          Complex.log (delayReturnDiff N D τ (-I * R)))
        atTop (nhds 0) := by
      simpa using hlog_pos.sub hlog_neg
    have hmul : Tendsto
        (fun R : ℝ => (2 * (Real.pi : ℂ) * I)⁻¹ *
          (Complex.log (delayReturnDiff N D τ (I * R)) -
            Complex.log (delayReturnDiff N D τ (-I * R))))
        atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (2 * (Real.pi : ℂ) * I)⁻¹)).mul hdiff
    simpa using tendsto_const_nhds.add hmul
  refine herr.congr' ?_
  filter_upwards [eventually_gt_atTop R₀] with R hR
  exact (hformula R hR).symm

private lemma isDelayHurwitz_iff_delayRhpZeroCount_eq_zero (N D : Polynomial ℂ) (τ : ℝ)
    (hD0 : D ≠ 0) (hdeg : N.natDegree < D.natDegree) (hτ : 0 ≤ τ)
    (hC : ∀ ω : ℝ, delayCharQuasiPoly N D τ (I * ω) ≠ 0) :
    IsDelayHurwitz N D τ ↔ delayRhpZeroCount N D τ = 0 := by
  classical
  let hfin := delayCharQuasiPoly_rhp_zeros_finite N D τ hD0 hdeg hτ
  let S : Finset ℂ := hfin.toFinset
  have hcount_eq : delayRhpZeroCount N D τ =
      ((∑ u ∈ S, analyticOrderNatAt (delayCharQuasiPoly N D τ) u : ℕ) : ℂ) := by
    unfold delayRhpZeroCount
    rw [finsum_mem_eq_sum_of_subset _
      (fun u ⟨hu_re, hu_supp⟩ => by
        rw [Function.mem_support, ne_eq, Int.cast_eq_zero] at hu_supp
        exact Finset.mem_coe.mpr (hfin.mem_toFinset.mpr ⟨hu_re, hu_supp⟩))
      (fun u hu => (hfin.mem_toFinset.mp hu).1)]
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    have han := delayCharQuasiPoly_analytic N D τ u (Set.mem_univ u)
    have hne_top := delayCharQuasiPoly_meromorphicOrderAt_ne_top N D τ hD0 hdeg hτ u
    have han_ne_top : analyticOrderAt (delayCharQuasiPoly N D τ) u ≠ ⊤ := by
      intro htop
      rw [han.meromorphicOrderAt_eq, htop] at hne_top
      exact hne_top rfl
    have hcast : (analyticOrderAt (delayCharQuasiPoly N D τ) u) =
        ((analyticOrderNatAt (delayCharQuasiPoly N D τ) u : ℕ) : ℕ∞) :=
      (Nat.cast_analyticOrderNatAt han_ne_top).symm
    rw [han.meromorphicOrderAt_eq, hcast]
    simp
  rw [hcount_eq, Nat.cast_eq_zero, Finset.sum_eq_zero_iff]
  constructor
  · intro hHurwitz u hu
    have hu_re : 0 < u.re := (hfin.mem_toFinset.mp hu).1
    have hne : delayCharQuasiPoly N D τ u ≠ 0 := hHurwitz u hu_re.le
    have han := delayCharQuasiPoly_analytic N D τ u (Set.mem_univ u)
    have hord0 : analyticOrderAt (delayCharQuasiPoly N D τ) u = 0 :=
      han.analyticOrderAt_eq_zero.mpr hne
    simp [analyticOrderNatAt, hord0]
  · intro hzero s hs
    rcases eq_or_lt_of_le hs with hs0 | hspos
    · have hs_eq : s = I * (s.im : ℂ) := by apply Complex.ext <;> simp [hs0.symm]
      rw [hs_eq]
      exact hC s.im
    · intro hs_eval
      have han := delayCharQuasiPoly_analytic N D τ s (Set.mem_univ s)
      have hne_top := delayCharQuasiPoly_meromorphicOrderAt_ne_top N D τ hD0 hdeg hτ s
      have han_ne_top : analyticOrderAt (delayCharQuasiPoly N D τ) s ≠ ⊤ := by
        intro htop
        rw [han.meromorphicOrderAt_eq, htop] at hne_top
        exact hne_top rfl
      have han_ne_zero : analyticOrderAt (delayCharQuasiPoly N D τ) s ≠ 0 :=
        han.analyticOrderAt_ne_zero.mpr hs_eval
      have hnat_ne : analyticOrderNatAt (delayCharQuasiPoly N D τ) s ≠ 0 := by
        intro h0
        apply han_ne_zero
        rw [← Nat.cast_analyticOrderNatAt han_ne_top, h0, Nat.cast_zero]
      have hmer_ne : (meromorphicOrderAt (delayCharQuasiPoly N D τ) s).untop₀ ≠ 0 := by
        rw [han.meromorphicOrderAt_eq, ← Nat.cast_analyticOrderNatAt han_ne_top]
        simpa using hnat_ne
      have hsS : s ∈ S := hfin.mem_toFinset.mpr ⟨hspos, hmer_ne⟩
      exact hnat_ne (hzero s hsS)

/-- **Nyquist Stability Criterion for Retarded Time-Delay Systems**:
`IsDelayHurwitz N D τ` holds if and only if the truncated counterclockwise Nyquist winding
integral `delayNyquistEncirclementsCCW N D τ R` converges to `rhpRootCount D` as `R → ∞`. -/
theorem nyquist_delay_stability_criterion (N D : Polynomial ℂ) (τ : ℝ)
    (hD0 : D ≠ 0) (hdeg : N.natDegree < D.natDegree) (hτ : 0 ≤ τ)
    (hD : NoImagAxisRoots D) (hC : ∀ ω : ℝ, delayCharQuasiPoly N D τ (I * ω) ≠ 0) :
    IsDelayHurwitz N D τ ↔
      Tendsto (delayNyquistEncirclementsCCW N D τ) atTop (nhds (rhpRootCount D : ℂ)) := by
  have htend := nyquist_delay_encirclement_tendsto N D τ hD0 hdeg hτ hD hC
  rw [isDelayHurwitz_iff_delayRhpZeroCount_eq_zero N D τ hD0 hdeg hτ hC]
  constructor
  · intro hz
    simpa [hz] using htend
  · intro htend_D
    have heq := tendsto_nhds_unique htend htend_D
    linear_combination -heq

/-- **Small-Gain / Delay-Independent Stability Theorem**:
If `D` is Hurwitz, `deg N < deg D`, `τ ≥ 0`, and `‖L(i ω)‖ < 1` for all `ω ∈ ℝ`,
then the time-delay system is Hurwitz stable (`IsDelayHurwitz N D τ`). -/
theorem nyquist_delay_small_gain (N D : Polynomial ℂ) (τ : ℝ)
    (hD : IsHurwitz D) (hdeg : N.natDegree < D.natDegree) (hτ : 0 ≤ τ)
    (hgain : ∀ ω : ℝ, ‖evalTransfer N D (I * ω)‖ < 1) :
    IsDelayHurwitz N D τ := by
  have hD0 : D ≠ 0 := hD.1
  have hD_imag : NoImagAxisRoots D := by
    intro ω hω
    have hlt := hD.2 (I * ω) hω
    simp at hlt
  have hslit_imag : ∀ ω : ℝ, delayReturnDiff N D τ (I * ω) ∈ Complex.slitPlane := by
    intro ω
    have hexp : ‖Complex.exp (-τ * (I * ω))‖ = 1 := by
      rw [Complex.norm_exp]
      have hre : (-(τ : ℂ) * (I * ω)).re = 0 := by simp
      rw [hre, Real.exp_zero]
    have hT : ‖delayTransfer N D τ (I * ω)‖ < 1 := by
      unfold delayTransfer
      rw [norm_mul, hexp, mul_one]
      exact hgain ω
    exact mem_slitPlane_of_norm_lt_one hT
  have hC : ∀ ω : ℝ, delayCharQuasiPoly N D τ (I * ω) ≠ 0 := by
    intro ω
    have hFne : delayReturnDiff N D τ (I * ω) ≠ 0 := fun h0 =>
      Complex.zero_notMem_slitPlane (h0 ▸ hslit_imag ω)
    rw [delayReturnDiff_eq_div (hD_imag ω)] at hFne
    exact left_ne_zero_of_mul (by simpa [div_eq_mul_inv] using hFne)
  have hP0 : rhpRootCount D = 0 :=
    (isHurwitz_iff_rhpRootCount_eq_zero hD0 hD_imag).mp hD
  rw [nyquist_delay_stability_criterion N D τ hD0 hdeg hτ hD_imag hC, hP0, Nat.cast_zero]
  have hint_eq : ∀ R : ℝ, ∫ ω in (-R)..R, delayNyquistIntegrand N D τ ω =
      Complex.log (delayReturnDiff N D τ (I * R)) -
        Complex.log (delayReturnDiff N D τ (-I * R)) := by
    intro R
    have hderiv : ∀ ω ∈ Set.uIcc (-R) R,
        HasDerivAt (fun t : ℝ => Complex.log (delayReturnDiff N D τ (I * t)))
          (delayNyquistIntegrand N D τ ω) ω := by
      intro ω _
      have hFdiff : HasDerivAt (delayReturnDiff N D τ)
          (deriv (delayReturnDiff N D τ) (I * ω)) (I * ω) :=
        (hasDerivAt_delayReturnDiff (hD_imag ω)).hasDerivAt
      have hline : HasDerivAt (fun t : ℝ => I * (t : ℂ)) I ω := by
        simpa only [ofReal_one, mul_one, id_def] using (hasDerivAt_id ω).ofReal_comp.const_mul I
      have hcomp : HasDerivAt (fun t : ℝ => delayReturnDiff N D τ (I * t))
          (I * deriv (delayReturnDiff N D τ) (I * ω)) ω := by
        simpa only [Function.comp_def, smul_eq_mul] using hFdiff.scomp ω hline
      have hlog := hcomp.clog_real (hslit_imag ω)
      refine hlog.congr_deriv ?_
      rw [delayNyquistIntegrand_eq_I_mul_logDeriv (hD_imag ω), logDeriv_apply]
      ring
    have hint : IntervalIntegrable (delayNyquistIntegrand N D τ) volume (-R) R := by
      refine Continuous.intervalIntegrable ?_ (-R) R
      rw [continuous_iff_continuousAt]
      intro ω
      have hFne : delayReturnDiff N D τ (I * ω) ≠ 0 := fun h0 =>
        Complex.zero_notMem_slitPlane (h0 ▸ hslit_imag ω)
      have han := analyticAt_delayReturnDiff (N := N) (D := D) (τ := τ) (hD_imag ω)
      have hlog_cont : ContinuousAt (logDeriv (delayReturnDiff N D τ)) (I * ω) :=
        han.deriv.continuousAt.div han.continuousAt hFne
      have hline_cont : ContinuousAt (fun t : ℝ => I * (t : ℂ)) ω :=
        continuousAt_const.mul Complex.continuous_ofReal.continuousAt
      have hcont : ContinuousAt (fun t : ℝ => I * logDeriv (delayReturnDiff N D τ) (I * t)) ω :=
        continuousAt_const.mul
          (ContinuousAt.comp (f := fun t : ℝ => I * (t : ℂ)) hlog_cont hline_cont)
      refine hcont.congr ?_
      filter_upwards with t
      exact (delayNyquistIntegrand_eq_I_mul_logDeriv (hD_imag t)).symm
    have heval := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    simpa [mul_neg, neg_mul] using heval
  have htend_F := tendsto_delayReturnDiff_imagAxis_atTop N D τ hD0 hdeg hτ
  have hlog_pos : Tendsto (fun R : ℝ => Complex.log (delayReturnDiff N D τ (I * R)))
      atTop (nhds 0) := by
    rw [← Complex.log_one]
    exact htend_F.1.clog Complex.one_mem_slitPlane
  have hlog_neg : Tendsto (fun R : ℝ => Complex.log (delayReturnDiff N D τ (-I * R)))
      atTop (nhds 0) := by
    rw [← Complex.log_one]
    exact htend_F.2.clog Complex.one_mem_slitPlane
  have htend_ccw : Tendsto
      (fun R : ℝ => (1 / (2 * (Real.pi : ℂ) * I)) *
        (Complex.log (delayReturnDiff N D τ (I * R)) -
          Complex.log (delayReturnDiff N D τ (-I * R))))
      atTop (nhds 0) := by
    have hdiff : Tendsto
        (fun R : ℝ => Complex.log (delayReturnDiff N D τ (I * R)) -
          Complex.log (delayReturnDiff N D τ (-I * R)))
        atTop (nhds 0) := by
      simpa using hlog_pos.sub hlog_neg
    simpa using (tendsto_const_nhds (x := 1 / (2 * (Real.pi : ℂ) * I))).mul hdiff
  refine htend_ccw.congr fun R => ?_
  unfold delayNyquistEncirclementsCCW
  rw [hint_eq R]

/-- **Verified Example (Delay-Independent Stability)**:
For all `τ ≥ 0`, the characteristic quasipolynomial `s + 2 + exp (-τ * s)` has no roots
in the closed right half-plane `0 ≤ s.re`. -/
theorem example_delay_independent_stable (τ : ℝ) (hτ : 0 ≤ τ) :
    IsDelayHurwitz (C (1 : ℂ)) (X + C (2 : ℂ)) τ := by
  refine nyquist_delay_small_gain (C (1 : ℂ)) (X + C (2 : ℂ)) τ ?_ ?_ hτ ?_
  · refine ⟨Polynomial.X_add_C_ne_zero 2, fun z hz => ?_⟩
    have h0 : z + 2 = 0 := by simpa [Polynomial.IsRoot] using hz
    have hz2 : z = -2 := eq_neg_of_add_eq_zero_left h0
    simp [hz2]
  · rw [Polynomial.natDegree_C, Polynomial.natDegree_X_add_C]
    exact zero_lt_one
  · intro ω
    unfold evalTransfer
    simp only [Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_X, norm_div, norm_one]
    have hre : (I * (ω : ℂ) + 2).re = 2 := by simp
    have hge : (2 : ℝ) ≤ ‖I * (ω : ℂ) + 2‖ := by
      calc (2 : ℝ) = |(I * (ω : ℂ) + 2).re| := by rw [hre]; norm_num
        _ ≤ ‖I * (ω : ℂ) + 2‖ := Complex.abs_re_le_norm _
    have hpos : 0 < ‖I * (ω : ℂ) + 2‖ := lt_of_lt_of_le (by norm_num) hge
    rw [one_div, inv_lt_one_iff₀]
    exact Or.inr (lt_of_lt_of_le (by norm_num) hge)

end Nyquist

