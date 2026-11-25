import Nyquist.Defs
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Logarithmic Derivatives of Polynomials and Nyquist Integrands

This file establishes the partial-fraction (sum-over-roots) expansions of the logarithmic
derivatives of complex polynomials along the imaginary axis and the right semicircle, together
with root-radius bounds ensuring the contour avoids all poles and zeros.
-/

namespace Nyquist

open Complex Polynomial

lemma poly_eq_C_leadingCoeff_mul_prod_roots (p : Polynomial ℂ) (_hp : p ≠ 0) :
    p = C p.leadingCoeff * (p.roots.map fun a => X - C a).prod :=
  (C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.splits p).natDegree_eq_card_roots.symm).symm

private lemma multiset_prod_X_sub_C_eval_ne_zero (m : Multiset ℂ) (s : ℂ)
    (hs : ((m.map fun a => X - C a).prod).eval s ≠ 0) : ∀ a ∈ m, s - a ≠ 0 := by
  intro a ha hzero
  apply hs
  rw [Polynomial.eval_multiset_prod]
  refine Multiset.prod_eq_zero ?_
  rw [Multiset.mem_map]
  refine ⟨X - C a, Multiset.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
  simpa [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using hzero

private lemma multiset_prod_X_sub_C_logDeriv (m : Multiset ℂ) (s : ℂ)
    (hs : ((m.map fun a => X - C a).prod).eval s ≠ 0) :
    (Polynomial.derivative (m.map fun a => X - C a).prod).eval s /
        ((m.map fun a => X - C a).prod).eval s =
      (m.map fun a => (s - a)⁻¹).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    have ha_ne : s - a ≠ 0 :=
      multiset_prod_X_sub_C_eval_ne_zero (a ::ₘ m) s hs a (Multiset.mem_cons_self a m)
    have hm_ne : ((m.map fun b => X - C b).prod).eval s ≠ 0 := by
      intro hzero
      apply hs
      simp [Multiset.map_cons, Multiset.prod_cons, Polynomial.eval_mul, hzero]
    have h_ih := ih hm_ne
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons,
      Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_X,
      Polynomial.derivative_C, sub_zero, one_mul, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    rw [← h_ih]
    field_simp [ha_ne, hm_ne]

lemma poly_logDeriv_eq_sum_roots (p : Polynomial ℂ) (hp : p ≠ 0) (s : ℂ)
    (hs : p.eval s ≠ 0) :
    (Polynomial.derivative p).eval s / p.eval s = (p.roots.map fun a => (s - a)⁻¹).sum := by
  have hfac := poly_eq_C_leadingCoeff_mul_prod_roots p hp
  have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hq_ne : ((p.roots.map fun a => X - C a).prod).eval s ≠ 0 := by
    intro hzero
    apply hs
    conv_lhs => rw [hfac]
    simp [Polynomial.eval_mul, hzero]
  have h_log := multiset_prod_X_sub_C_logDeriv p.roots s hq_ne
  conv_lhs => rw [hfac]
  rw [Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_mul,
    Polynomial.eval_C, mul_div_mul_left _ _ hlc]
  exact h_log

lemma hasDerivAt_eval_comp_I_mul_ofReal (p : Polynomial ℂ) (ω : ℝ) :
    HasDerivAt (fun t : ℝ => p.eval (I * t))
      (I * (Polynomial.derivative p).eval (I * ω)) ω := by
  have h1 : HasDerivAt (fun z : ℂ => p.eval z)
      ((Polynomial.derivative p).eval (I * ω)) (I * ω) :=
    p.hasDerivAt (I * (ω : ℂ))
  have h2 : HasDerivAt (fun t : ℝ => I * (t : ℂ)) I ω := by
    simpa only [ofReal_one, mul_one, id_def] using (hasDerivAt_id ω).ofReal_comp.const_mul I
  simpa only [Function.comp_def, smul_eq_mul] using h1.scomp ω h2

lemma hasDerivAt_eval_comp_circle (p : Polynomial ℂ) (R θ : ℝ) :
    HasDerivAt (fun t : ℝ => p.eval (R * Complex.exp (I * t)))
      (I * R * Complex.exp (I * θ) *
        (Polynomial.derivative p).eval (R * Complex.exp (I * θ))) θ := by
  have h_it : HasDerivAt (fun t : ℝ => I * (t : ℂ)) I θ := by
    simpa only [ofReal_one, mul_one, id_def] using (hasDerivAt_id θ).ofReal_comp.const_mul I
  have h_exp : HasDerivAt (fun t : ℝ => Complex.exp (I * t)) (I * Complex.exp (I * θ)) θ := by
    simpa only [Function.comp_def, smul_eq_mul] using
      (Complex.hasDerivAt_exp (I * θ)).scomp θ h_it
  have h_Rexp : HasDerivAt (fun t : ℝ => (R : ℂ) * Complex.exp (I * t))
      (I * R * Complex.exp (I * θ)) θ := by
    simpa only [mul_assoc, mul_left_comm] using h_exp.const_mul (R : ℂ)
  have h_p : HasDerivAt (fun z : ℂ => p.eval z)
      ((Polynomial.derivative p).eval (R * Complex.exp (I * θ))) (R * Complex.exp (I * θ)) :=
    p.hasDerivAt (R * Complex.exp (I * θ))
  simpa only [Function.comp_def, smul_eq_mul, mul_assoc] using h_p.scomp θ h_Rexp

private lemma mul_sum_inv_sub (c s : ℂ) (m : Multiset ℂ) :
    c * (m.map fun a => (s - a)⁻¹).sum = (m.map fun a => c / (s - a)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, mul_add, ih, div_eq_mul_inv]

theorem nyquistIntegrand_eq_sum_roots (N D : Polynomial ℂ) (hD0 : D ≠ 0) (hC0 : D + N ≠ 0)
    (hD : NoImagAxisRoots D) (hC : NoImagAxisRoots (D + N)) (ω : ℝ) :
    nyquistIntegrand N D ω =
      ((D + N).roots.map fun z => I / (I * ω - z)).sum -
        (D.roots.map fun p => I / (I * ω - p)).sum := by
  unfold nyquistIntegrand
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
  rw [hDeriv.deriv, returnDifference_eq_div (hD ω)]
  have hDω : D.eval (I * ω) ≠ 0 := hD ω
  have hCω : (D + N).eval (I * ω) ≠ 0 := hC ω
  have hsplit :
      ((I * (Polynomial.derivative (D + N)).eval (I * ω) * D.eval (I * ω) -
        (D + N).eval (I * ω) * (I * (Polynomial.derivative D).eval (I * ω))) /
        (D.eval (I * ω)) ^ 2) / ((D + N).eval (I * ω) / D.eval (I * ω)) =
      I * ((Polynomial.derivative (D + N)).eval (I * ω) / (D + N).eval (I * ω)) -
        I * ((Polynomial.derivative D).eval (I * ω) / D.eval (I * ω)) := by
    field_simp [hDω, hCω]
  rw [hsplit, poly_logDeriv_eq_sum_roots (D + N) hC0 (I * ω) hCω,
    poly_logDeriv_eq_sum_roots D hD0 (I * ω) hDω,
    mul_sum_inv_sub I (I * ω), mul_sum_inv_sub I (I * ω)]

theorem nyquistSemiIntegrand_eq_sum_roots (N D : Polynomial ℂ) (hD0 : D ≠ 0) (hC0 : D + N ≠ 0)
    (R θ : ℝ) (hDs : D.eval (R * Complex.exp (I * θ)) ≠ 0)
    (hCs : (D + N).eval (R * Complex.exp (I * θ)) ≠ 0) :
    nyquistSemiIntegrand N D R θ =
      ((D + N).roots.map fun z =>
          (I * R * Complex.exp (I * θ)) / (R * Complex.exp (I * θ) - z)).sum -
        (D.roots.map fun p =>
          (I * R * Complex.exp (I * θ)) / (R * Complex.exp (I * θ) - p)).sum := by
  unfold nyquistSemiIntegrand
  have hD_cont : ContinuousAt (fun t : ℝ => D.eval (R * Complex.exp (I * t))) θ :=
    (hasDerivAt_eval_comp_circle D R θ).continuousAt
  have hev_ne : ∀ᶠ t : ℝ in nhds θ, D.eval (R * Complex.exp (I * t)) ≠ 0 :=
    hD_cont.eventually_ne hDs
  have hev_eq : (fun t : ℝ => returnDifference N D (R * Complex.exp (I * t))) =ᶠ[nhds θ]
      fun t : ℝ => (D + N).eval (R * Complex.exp (I * t)) / D.eval (R * Complex.exp (I * t)) :=
    hev_ne.mono fun (_ : ℝ) ht => returnDifference_eq_div ht
  have hDerivDiv : HasDerivAt
      (fun t : ℝ => (D + N).eval (R * Complex.exp (I * t)) / D.eval (R * Complex.exp (I * t)))
      ((I * R * Complex.exp (I * θ) *
          (Polynomial.derivative (D + N)).eval (R * Complex.exp (I * θ)) *
          D.eval (R * Complex.exp (I * θ)) -
        (D + N).eval (R * Complex.exp (I * θ)) *
          (I * R * Complex.exp (I * θ) *
            (Polynomial.derivative D).eval (R * Complex.exp (I * θ)))) /
        (D.eval (R * Complex.exp (I * θ))) ^ 2) θ :=
    (hasDerivAt_eval_comp_circle (D + N) R θ).div (hasDerivAt_eval_comp_circle D R θ) hDs
  have hDeriv : HasDerivAt (fun t : ℝ => returnDifference N D (R * Complex.exp (I * t)))
      ((I * R * Complex.exp (I * θ) *
          (Polynomial.derivative (D + N)).eval (R * Complex.exp (I * θ)) *
          D.eval (R * Complex.exp (I * θ)) -
        (D + N).eval (R * Complex.exp (I * θ)) *
          (I * R * Complex.exp (I * θ) *
            (Polynomial.derivative D).eval (R * Complex.exp (I * θ)))) /
        (D.eval (R * Complex.exp (I * θ))) ^ 2) θ :=
    hDerivDiv.congr_of_eventuallyEq hev_eq
  rw [hDeriv.deriv, returnDifference_eq_div hDs]
  have hsplit :
      ((I * R * Complex.exp (I * θ) *
          (Polynomial.derivative (D + N)).eval (R * Complex.exp (I * θ)) *
          D.eval (R * Complex.exp (I * θ)) -
        (D + N).eval (R * Complex.exp (I * θ)) *
          (I * R * Complex.exp (I * θ) *
            (Polynomial.derivative D).eval (R * Complex.exp (I * θ)))) /
        (D.eval (R * Complex.exp (I * θ))) ^ 2) /
      ((D + N).eval (R * Complex.exp (I * θ)) / D.eval (R * Complex.exp (I * θ))) =
      (I * R * Complex.exp (I * θ)) *
        ((Polynomial.derivative (D + N)).eval (R * Complex.exp (I * θ)) /
          (D + N).eval (R * Complex.exp (I * θ))) -
      (I * R * Complex.exp (I * θ)) *
        ((Polynomial.derivative D).eval (R * Complex.exp (I * θ)) /
          D.eval (R * Complex.exp (I * θ))) := by
    field_simp [hDs, hCs]
  rw [hsplit,
    poly_logDeriv_eq_sum_roots (D + N) hC0 (R * Complex.exp (I * θ)) hCs,
    poly_logDeriv_eq_sum_roots D hD0 (R * Complex.exp (I * θ)) hDs,
    mul_sum_inv_sub (I * R * Complex.exp (I * θ)) (R * Complex.exp (I * θ)),
    mul_sum_inv_sub (I * R * Complex.exp (I * θ)) (R * Complex.exp (I * θ))]

private lemma sum_norm_nonneg (m : Multiset ℂ) : 0 ≤ (m.map norm).sum :=
  Multiset.sum_nonneg fun _ hx => by
    rcases Multiset.mem_map.mp hx with ⟨a, _, rfl⟩
    exact norm_nonneg a

private lemma norm_le_sum_norm {m : Multiset ℂ} {a : ℂ} (ha : a ∈ m) :
    ‖a‖ ≤ (m.map norm).sum :=
  Multiset.single_le_sum (fun _ hx => by
    rcases Multiset.mem_map.mp hx with ⟨b, _, rfl⟩
    exact norm_nonneg b) _ (Multiset.mem_map.mpr ⟨a, ha, rfl⟩)

lemma exists_radius_above_roots (N D : Polynomial ℂ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ (∀ a ∈ D.roots, ‖a‖ < R₀) ∧
      (∀ a ∈ (D + N).roots, ‖a‖ < R₀) := by
  refine ⟨(D.roots.map norm).sum + ((D + N).roots.map norm).sum + 1, ?_, ?_, ?_⟩
  · have h1 := sum_norm_nonneg D.roots
    have h2 := sum_norm_nonneg (D + N).roots
    linarith
  · intro a ha
    have hle := norm_le_sum_norm ha
    have h2 := sum_norm_nonneg (D + N).roots
    linarith
  · intro a ha
    have hle := norm_le_sum_norm ha
    have h1 := sum_norm_nonneg D.roots
    linarith

lemma eval_ne_zero_on_circle_of_radius_gt (p : Polynomial ℂ) (hp : p ≠ 0) {R₀ R : ℝ}
    (hR₀ : ∀ a ∈ p.roots, ‖a‖ < R₀) (hR : R₀ ≤ R) (θ : ℝ) :
    p.eval (R * Complex.exp (I * θ)) ≠ 0 := by
  intro heval
  have hmem : (R : ℂ) * Complex.exp (I * θ) ∈ p.roots := (mem_roots hp).mpr heval
  have hlt : ‖(R : ℂ) * Complex.exp (I * θ)‖ < R₀ := hR₀ _ hmem
  have hnorm : ‖(R : ℂ) * Complex.exp (I * θ)‖ = |R| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    simp
  rw [hnorm] at hlt
  have hle : R ≤ |R| := le_abs_self R
  linarith

end Nyquist
