import Nyquist.Defs
import Nyquist.LogDeriv
import Nyquist.ImagAxisIntegral
import Nyquist.SemicircleIntegral
import Nyquist.PhaseLift
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Nyquist Stability Criterion

This file combines the logarithmic-derivative expansions, imaginary-axis and semicircle
contour integrals, and continuous phase lifts to prove:
- `nyquist_dContour_tendsto`: the rational argument principle on the Nyquist D-contour;
- `nyquist_semicircle_tendsto_zero`: vanishing of the semicircle contribution for proper
  non-degenerate systems;
- `nyquistIntegrand_integrable`, `nyquist_encirclement_formula`, and
  `nyquist_encirclement_formula_cw`: Lebesgue integrability along `i ℝ` and the exact
  encirclement count;
- `nyquist_phase_lift` and `nyquist_phase_lift_unique`: the topological phase-lift
  formulation;
- `nyquist_stability_criterion`, `nyquist_stability_criterion_cw`,
  `nyquist_stability_criterion_strictlyProper`, `nyquist_stability_criterion_openLoopStable`,
  and `nyquist_stability_criterion_real`.
-/

namespace Nyquist

open Complex Polynomial MeasureTheory Filter

/-! ### Multiset Helpers for Contour Integrals -/

private lemma intervalIntegrable_sum_poles_imagAxis (m : Multiset ℂ)
    (hm : ∀ a ∈ m, a.re ≠ 0) (u v : ℝ) :
    IntervalIntegrable (fun ω : ℝ => (m.map fun a => I / (I * ω - a)).sum) volume u v := by
  induction m using Multiset.induction_on with
  | empty => simp [intervalIntegrable_const]
  | cons a m ih =>
    have ha : a.re ≠ 0 := hm a (Multiset.mem_cons_self a m)
    have hm' : ∀ b ∈ m, b.re ≠ 0 := fun b hb => hm b (Multiset.mem_cons_of_mem hb)
    have h_eq : (fun ω : ℝ => ((a ::ₘ m).map fun z => I / (I * ω - z)).sum) =
        fun ω : ℝ => I / (I * ω - a) + (m.map fun z => I / (I * ω - z)).sum := by
      funext ω
      simp [Multiset.map_cons, Multiset.sum_cons]
    rw [h_eq]
    exact (intervalIntegrable_single_pole_imagAxis a ha u v).add (ih hm')

private lemma tendsto_integral_sum_poles_imagAxis (m : Multiset ℂ)
    (hm : ∀ a ∈ m, a.re ≠ 0) :
    Tendsto
      (fun R : ℝ => ∫ ω in (-R)..R, (m.map fun a => I / (I * ω - a)).sum)
      atTop
      (nhds ((((m.filter fun z : ℂ => z.re < 0).card : ℂ) -
        ((m.filter fun z : ℂ => 0 < z.re).card : ℂ)) * (I * Real.pi))) := by
  induction m using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.sum_zero, intervalIntegral.integral_zero,
      Multiset.filter_zero, Multiset.card_zero, Nat.cast_zero, sub_self, zero_mul]
    exact tendsto_const_nhds
  | cons a m ih =>
    have ha : a.re ≠ 0 := hm a (Multiset.mem_cons_self a m)
    have hm' : ∀ b ∈ m, b.re ≠ 0 := fun b hb => hm b (Multiset.mem_cons_of_mem hb)
    have ih' := ih hm'
    have h_int :
        (fun R : ℝ => ∫ ω in (-R)..R, ((a ::ₘ m).map fun z => I / (I * ω - z)).sum) =
          fun R : ℝ =>
            (∫ ω in (-R)..R, I / (I * ω - a)) +
              (∫ ω in (-R)..R, (m.map fun z => I / (I * ω - z)).sum) := by
      funext R
      have h_eq : (fun ω : ℝ => ((a ::ₘ m).map fun z => I / (I * ω - z)).sum) =
          fun ω : ℝ => I / (I * ω - a) + (m.map fun z => I / (I * ω - z)).sum := by
        funext ω
        simp [Multiset.map_cons, Multiset.sum_cons]
      rw [h_eq]
      exact intervalIntegral.integral_add
        (intervalIntegrable_single_pole_imagAxis a ha (-R) R)
        (intervalIntegrable_sum_poles_imagAxis m hm' (-R) R)
    rw [h_int]
    rcases lt_or_gt_of_ne ha with hlt | hgt
    · have hnot : ¬ (0 < a.re) := not_lt.mpr hlt.le
      have hcard_l :
          ((a ::ₘ m).filter fun z : ℂ => z.re < 0).card =
            (m.filter fun z : ℂ => z.re < 0).card + 1 := by
        simp [Multiset.filter_cons_of_pos, hlt]
      have hcard_r :
          ((a ::ₘ m).filter fun z : ℂ => 0 < z.re).card =
            (m.filter fun z : ℂ => 0 < z.re).card := by
        simp [Multiset.filter_cons_of_neg, hnot]
      have hsum := (tendsto_integral_single_pole_imagAxis_neg a hlt).add ih'
      have hlim :
          (I * (Real.pi : ℂ)) +
            (((m.filter fun z : ℂ => z.re < 0).card : ℂ) -
              ((m.filter fun z : ℂ => 0 < z.re).card : ℂ)) * (I * Real.pi) =
          ((((a ::ₘ m).filter fun z : ℂ => z.re < 0).card : ℂ) -
            (((a ::ₘ m).filter fun z : ℂ => 0 < z.re).card : ℂ)) * (I * Real.pi) := by
        rw [hcard_l, hcard_r]
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
      have hsum := (tendsto_integral_single_pole_imagAxis_pos a hgt).add ih'
      have hlim :
          (-I * (Real.pi : ℂ)) +
            (((m.filter fun z : ℂ => z.re < 0).card : ℂ) -
              ((m.filter fun z : ℂ => 0 < z.re).card : ℂ)) * (I * Real.pi) =
          ((((a ::ₘ m).filter fun z : ℂ => z.re < 0).card : ℂ) -
            (((a ::ₘ m).filter fun z : ℂ => 0 < z.re).card : ℂ)) * (I * Real.pi) := by
        rw [hcard_l, hcard_r]
        push_cast
        ring
      rw [hlim] at hsum
      exact hsum

private lemma eventually_lt_all_norms (m : Multiset ℂ) :
    ∀ᶠ R : ℝ in atTop, ∀ a ∈ m, ‖a‖ < R := by
  induction m using Multiset.induction_on with
  | empty => exact Eventually.of_forall fun _ _ h => (Multiset.notMem_zero _ h).elim
  | cons a m ih =>
    refine ((eventually_gt_atTop ‖a‖).and ih).mono fun R ⟨ha, hm⟩ b hb => ?_
    rcases Multiset.mem_cons.mp hb with rfl | hb'
    · exact ha
    · exact hm b hb'

private lemma intervalIntegrable_sum_poles_semicircle (m : Multiset ℂ) {R : ℝ}
    (hR : ∀ a ∈ m, ‖a‖ < R) (u v : ℝ) :
    IntervalIntegrable
      (fun θ : ℝ =>
        (m.map fun a => (I * R * Complex.exp (I * θ)) / (R * Complex.exp (I * θ) - a)).sum)
      volume u v := by
  induction m using Multiset.induction_on with
  | empty => simp [intervalIntegrable_const]
  | cons a m ih =>
    have ha : ‖a‖ < R := hR a (Multiset.mem_cons_self a m)
    have hm' : ∀ b ∈ m, ‖b‖ < R := fun b hb => hR b (Multiset.mem_cons_of_mem hb)
    have h_eq :
        (fun θ : ℝ =>
          ((a ::ₘ m).map fun z =>
            (I * R * Complex.exp (I * θ)) / (R * Complex.exp (I * θ) - z)).sum) =
          fun θ : ℝ =>
            (I * R * Complex.exp (I * θ)) / (R * Complex.exp (I * θ) - a) +
              (m.map fun z =>
                (I * R * Complex.exp (I * θ)) / (R * Complex.exp (I * θ) - z)).sum := by
      funext θ
      simp [Multiset.map_cons, Multiset.sum_cons]
    rw [h_eq]
    exact (intervalIntegrable_single_pole_semicircle a ha u v).add (ih hm')

private lemma tendsto_integral_sum_poles_semicircle (m : Multiset ℂ) :
    Tendsto
      (fun R : ℝ =>
        ∫ θ in (Real.pi / 2)..(-Real.pi / 2),
          (m.map fun a =>
            (I * R * Complex.exp (I * θ)) / (R * Complex.exp (I * θ) - a)).sum)
      atTop (nhds ((m.card : ℂ) * (-I * Real.pi))) := by
  induction m using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.sum_zero, intervalIntegral.integral_zero,
      Multiset.card_zero, Nat.cast_zero, zero_mul]
    exact tendsto_const_nhds
  | cons a m ih =>
    have hsum := (tendsto_integral_single_pole_semicircle a).add ih
    have hlim : (-I * (Real.pi : ℂ)) + (m.card : ℂ) * (-I * Real.pi) =
        (((a ::ₘ m).card : ℂ)) * (-I * Real.pi) := by
      simp only [Multiset.card_cons]
      push_cast
      ring
    rw [hlim] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop ‖a‖, eventually_lt_all_norms m] with R ha hm
    have h_eq :
        (fun θ : ℝ =>
          ((a ::ₘ m).map fun z =>
            (I * R * Complex.exp (I * θ)) / (R * Complex.exp (I * θ) - z)).sum) =
          fun θ : ℝ =>
            (I * R * Complex.exp (I * θ)) / (R * Complex.exp (I * θ) - a) +
              (m.map fun z =>
                (I * R * Complex.exp (I * θ)) / (R * Complex.exp (I * θ) - z)).sum := by
      funext θ
      simp [Multiset.map_cons, Multiset.sum_cons]
    rw [h_eq]
    exact (intervalIntegral.integral_add
      (intervalIntegrable_single_pole_semicircle a ha (Real.pi / 2) (-Real.pi / 2))
      (intervalIntegrable_sum_poles_semicircle m hm (Real.pi / 2) (-Real.pi / 2))).symm

/-! ### Imaginary-Axis and Semicircle Contour Limits -/

private lemma nyquistImagIntegral_tendsto_raw (N D : Polynomial ℂ)
    (hD : NoImagAxisRoots D) (hC : NoImagAxisRoots (D + N)) :
    Tendsto (nyquistImagIntegral N D) atTop
      (nhds ((((lhpRootCount (D + N) : ℂ) - (rhpRootCount (D + N) : ℂ)) -
        ((lhpRootCount D : ℂ) - (rhpRootCount D : ℂ))) * (I * Real.pi))) := by
  have hD0 : D ≠ 0 := noImagAxisRoots_ne_zero hD
  have hC0 : D + N ≠ 0 := noImagAxisRoots_ne_zero hC
  have hmD : ∀ a ∈ D.roots, a.re ≠ 0 := fun a ha => re_ne_zero_of_mem_roots hD ha
  have hmC : ∀ a ∈ (D + N).roots, a.re ≠ 0 := fun a ha => re_ne_zero_of_mem_roots hC ha
  have h1 := tendsto_integral_sum_poles_imagAxis (D + N).roots hmC
  have h2 := tendsto_integral_sum_poles_imagAxis D.roots hmD
  have hdiff := h1.sub h2
  have hlim :
      (((lhpRootCount (D + N) : ℂ) - (rhpRootCount (D + N) : ℂ)) * (I * Real.pi)) -
        (((lhpRootCount D : ℂ) - (rhpRootCount D : ℂ)) * (I * Real.pi)) =
      (((lhpRootCount (D + N) : ℂ) - (rhpRootCount (D + N) : ℂ)) -
        ((lhpRootCount D : ℂ) - (rhpRootCount D : ℂ))) * (I * Real.pi) := by
    ring
  change Tendsto _ atTop (nhds (((lhpRootCount (D + N) : ℂ) - (rhpRootCount (D + N) : ℂ)) *
    (I * Real.pi))) at h1
  change Tendsto _ atTop (nhds (((lhpRootCount D : ℂ) - (rhpRootCount D : ℂ)) *
    (I * Real.pi))) at h2
  have hdiff' := h1.sub h2
  rw [hlim] at hdiff'
  refine hdiff'.congr fun R => ?_
  unfold nyquistImagIntegral
  have h_eq : nyquistIntegrand N D = fun ω : ℝ =>
      ((D + N).roots.map fun z => I / (I * ω - z)).sum -
        (D.roots.map fun p => I / (I * ω - p)).sum := by
    funext ω
    exact nyquistIntegrand_eq_sum_roots N D hD0 hC0 hD hC ω
  rw [h_eq]
  exact (intervalIntegral.integral_sub
    (intervalIntegrable_sum_poles_imagAxis (D + N).roots hmC (-R) R)
    (intervalIntegrable_sum_poles_imagAxis D.roots hmD (-R) R)).symm

private lemma nyquistSemiIntegral_tendsto_raw (N D : Polynomial ℂ)
    (hD0 : D ≠ 0) (hC0 : D + N ≠ 0) :
    Tendsto (nyquistSemiIntegral N D) atTop
      (nhds ((((D + N).roots.card : ℂ) - (D.roots.card : ℂ)) * (-I * Real.pi))) := by
  have h1 := tendsto_integral_sum_poles_semicircle (D + N).roots
  have h2 := tendsto_integral_sum_poles_semicircle D.roots
  have hdiff := h1.sub h2
  have hlim :
      ((D + N).roots.card : ℂ) * (-I * Real.pi) - (D.roots.card : ℂ) * (-I * Real.pi) =
        (((D + N).roots.card : ℂ) - (D.roots.card : ℂ)) * (-I * Real.pi) := by
    ring
  rw [hlim] at hdiff
  refine hdiff.congr' ?_
  obtain ⟨R₀, _, hR₀D, hR₀C⟩ := exists_radius_above_roots N D
  filter_upwards [eventually_ge_atTop R₀] with R hR
  have hR_D : ∀ a ∈ D.roots, ‖a‖ < R := fun a ha => lt_of_lt_of_le (hR₀D a ha) hR
  have hR_C : ∀ a ∈ (D + N).roots, ‖a‖ < R := fun a ha => lt_of_lt_of_le (hR₀C a ha) hR
  unfold nyquistSemiIntegral
  have h_eq : nyquistSemiIntegrand N D R = fun θ : ℝ =>
      ((D + N).roots.map fun z =>
        (I * R * Complex.exp (I * θ)) / (R * Complex.exp (I * θ) - z)).sum -
      (D.roots.map fun p =>
        (I * R * Complex.exp (I * θ)) / (R * Complex.exp (I * θ) - p)).sum := by
    funext θ
    exact nyquistSemiIntegrand_eq_sum_roots N D hD0 hC0 R θ
      (eval_ne_zero_on_circle_of_radius_gt D hD0 hR₀D hR θ)
      (eval_ne_zero_on_circle_of_radius_gt (D + N) hC0 hR₀C hR θ)
  rw [h_eq]
  exact (intervalIntegral.integral_sub
    (intervalIntegrable_sum_poles_semicircle (D + N).roots hR_C (Real.pi / 2) (-Real.pi / 2))
    (intervalIntegrable_sum_poles_semicircle D.roots hR_D (Real.pi / 2) (-Real.pi / 2))).symm

/-- **Rational Argument Principle on the Nyquist D-Contour:**
Without any properness assumption, as the contour radius `R → ∞`, the clockwise D-contour
winding integral converges to `Z - P`, the number of open right half-plane closed-loop roots
minus open right half-plane open-loop poles. -/
theorem nyquist_dContour_tendsto (N D : Polynomial ℂ)
    (hD : NoImagAxisRoots D) (hC : NoImagAxisRoots (D + N)) :
    Tendsto (nyquistDContourCW N D) atTop
      (nhds ((rhpRootCount (D + N) : ℂ) - (rhpRootCount D : ℂ))) := by
  have hD0 : D ≠ 0 := noImagAxisRoots_ne_zero hD
  have hC0 : D + N ≠ 0 := noImagAxisRoots_ne_zero hC
  have him := nyquistImagIntegral_tendsto_raw N D hD hC
  have hsemi := nyquistSemiIntegral_tendsto_raw N D hD0 hC0
  have hsum := him.add hsemi
  have hmul := tendsto_const_nhds (x := -(1 / (2 * Real.pi * I))).mul hsum
  have hcardD : D.roots.card = rhpRootCount D + lhpRootCount D := by
    rw [rhpRootCount_add_lhpRootCount hD0 hD, (IsAlgClosed.splits D).natDegree_eq_card_roots]
  have hcardC : (D + N).roots.card = rhpRootCount (D + N) + lhpRootCount (D + N) := by
    rw [rhpRootCount_add_lhpRootCount hC0 hC,
      (IsAlgClosed.splits (D + N)).natDegree_eq_card_roots]
  have h2piI : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  have hlim :
      -(1 / (2 * Real.pi * I)) *
        ((((lhpRootCount (D + N) : ℂ) - (rhpRootCount (D + N) : ℂ)) -
          ((lhpRootCount D : ℂ) - (rhpRootCount D : ℂ))) * (I * Real.pi) +
          (((D + N).roots.card : ℂ) - (D.roots.card : ℂ)) * (-I * Real.pi)) =
        (rhpRootCount (D + N) : ℂ) - (rhpRootCount D : ℂ) := by
    rw [hcardD, hcardC]
    push_cast
    field_simp [h2piI]
    ring
  rw [hlim] at hmul
  exact hmul

/-- For proper non-degenerate open-loop transfer functions (`deg (D + N) = deg D`),
the contribution of the right-half-plane semicircle tends to `0` as `R → ∞`. -/
theorem nyquist_semicircle_tendsto_zero (N D : Polynomial ℂ)
    (hProp : IsProperNonDegenerate N D)
    (hD : NoImagAxisRoots D) (hC : NoImagAxisRoots (D + N)) :
    Tendsto (nyquistSemiIntegral N D) atTop (nhds 0) := by
  have hD0 : D ≠ 0 := noImagAxisRoots_ne_zero hD
  have hC0 : D + N ≠ 0 := noImagAxisRoots_ne_zero hC
  have hsemi := nyquistSemiIntegral_tendsto_raw N D hD0 hC0
  have hcard : (D + N).roots.card = D.roots.card := by
    rw [← (IsAlgClosed.splits (D + N)).natDegree_eq_card_roots,
      ← (IsAlgClosed.splits D).natDegree_eq_card_roots, hProp.2.2]
  simpa [hcard] using hsemi

/-! ### Lebesgue Integrability and Exact Encirclement Count -/

private lemma integrable_sum_poles_sub_ref (m : Multiset ℂ) (hm : ∀ a ∈ m, a.re ≠ 0) :
    Integrable (fun ω : ℝ => (m.map fun a => I / (I * ω - a) - I / (I * ω - 1)).sum) volume := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    have ha : a.re ≠ 0 := hm a (Multiset.mem_cons_self a m)
    have hm' : ∀ b ∈ m, b.re ≠ 0 := fun b hb => hm b (Multiset.mem_cons_of_mem hb)
    have h_eq :
        (fun ω : ℝ => ((a ::ₘ m).map fun z => I / (I * ω - z) - I / (I * ω - 1)).sum) =
          fun ω : ℝ =>
            (I / (I * ω - a) - I / (I * ω - 1)) +
              (m.map fun z => I / (I * ω - z) - I / (I * ω - 1)).sum := by
      funext ω
      simp [Multiset.map_cons, Multiset.sum_cons]
    rw [h_eq]
    exact (integrable_pole_sub_ref a ha).add (ih hm')

private lemma multiset_sum_sub_const (m : Multiset ℂ) (f : ℂ → ℂ) (c : ℂ) :
    (m.map fun a => f a - c).sum = (m.map f).sum - (m.card : ℂ) * c := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]
    push_cast
    ring

/-- The Nyquist logarithmic-derivative integrand is Lebesgue integrable on `ℝ` whenever
`L(s) = N(s) / D(s)` is proper and non-degenerate and neither `D` nor `D + N` has imaginary-axis
roots. -/
theorem nyquistIntegrand_integrable (N D : Polynomial ℂ)
    (hProp : IsProperNonDegenerate N D)
    (hD : NoImagAxisRoots D) (hC : NoImagAxisRoots (D + N)) :
    Integrable (nyquistIntegrand N D) volume := by
  have hD0 : D ≠ 0 := noImagAxisRoots_ne_zero hD
  have hC0 : D + N ≠ 0 := noImagAxisRoots_ne_zero hC
  have hmD : ∀ a ∈ D.roots, a.re ≠ 0 := fun a ha => re_ne_zero_of_mem_roots hD ha
  have hmC : ∀ a ∈ (D + N).roots, a.re ≠ 0 := fun a ha => re_ne_zero_of_mem_roots hC ha
  have hcard : (D + N).roots.card = D.roots.card := by
    rw [← (IsAlgClosed.splits (D + N)).natDegree_eq_card_roots,
      ← (IsAlgClosed.splits D).natDegree_eq_card_roots, hProp.2.2]
  have h_eq : nyquistIntegrand N D = fun ω : ℝ =>
      ((D + N).roots.map fun z => I / (I * ω - z) - I / (I * ω - 1)).sum -
        (D.roots.map fun p => I / (I * ω - p) - I / (I * ω - 1)).sum := by
    funext ω
    rw [nyquistIntegrand_eq_sum_roots N D hD0 hC0 hD hC ω,
      multiset_sum_sub_const (D + N).roots (fun z => I / (I * ω - z)) (I / (I * ω - 1)),
      multiset_sum_sub_const D.roots (fun p => I / (I * ω - p)) (I / (I * ω - 1)),
      hcard]
    ring
  rw [h_eq]
  exact (integrable_sum_poles_sub_ref (D + N).roots hmC).sub
    (integrable_sum_poles_sub_ref D.roots hmD)

/-- **Nyquist Encirclement Formula (Counterclockwise):**
The net counterclockwise encirclements of `-1` by `ω ↦ L(i ω)` equals `P - Z`, i.e.
the number of open-loop RHP poles minus closed-loop RHP roots. -/
theorem nyquist_encirclement_formula (N D : Polynomial ℂ)
    (hProp : IsProperNonDegenerate N D)
    (hD : NoImagAxisRoots D) (hC : NoImagAxisRoots (D + N)) :
    nyquistEncirclementsCCW N D = (rhpRootCount D : ℂ) - (rhpRootCount (D + N) : ℂ) := by
  have hD0 : D ≠ 0 := noImagAxisRoots_ne_zero hD
  have hC0 : D + N ≠ 0 := noImagAxisRoots_ne_zero hC
  have hint := nyquistIntegrand_integrable N D hProp hD hC
  have htend_int : Tendsto (nyquistImagIntegral N D) atTop
      (nhds (∫ ω : ℝ, nyquistIntegrand N D ω)) :=
    intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
  have htend_lim := nyquistImagIntegral_tendsto_raw N D hD hC
  have heq := tendsto_nhds_unique htend_int htend_lim
  have hdeg_eq : rhpRootCount (D + N) + lhpRootCount (D + N) = rhpRootCount D + lhpRootCount D := by
    rw [rhpRootCount_add_lhpRootCount hC0 hC, rhpRootCount_add_lhpRootCount hD0 hD, hProp.2.2]
  have hlhp_eq : (lhpRootCount (D + N) : ℂ) - (lhpRootCount D : ℂ) =
      (rhpRootCount D : ℂ) - (rhpRootCount (D + N) : ℂ) := by
    have : (rhpRootCount (D + N) : ℂ) + (lhpRootCount (D + N) : ℂ) =
        (rhpRootCount D : ℂ) + (lhpRootCount D : ℂ) := by
      exact_mod_cast hdeg_eq
    linear_combination this
  have h2piI : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  unfold nyquistEncirclementsCCW
  rw [heq]
  have hsimp :
      ((lhpRootCount (D + N) : ℂ) - (rhpRootCount (D + N) : ℂ)) -
        ((lhpRootCount D : ℂ) - (rhpRootCount D : ℂ)) =
        2 * ((rhpRootCount D : ℂ) - (rhpRootCount (D + N) : ℂ)) := by
    linear_combination hlhp_eq
  rw [hsimp]
  field_simp [h2piI]

/-- **Nyquist Encirclement Formula (Clockwise):**
The net clockwise encirclements of `-1` by `ω ↦ L(i ω)` equals `Z - P`. -/
theorem nyquist_encirclement_formula_cw (N D : Polynomial ℂ)
    (hProp : IsProperNonDegenerate N D)
    (hD : NoImagAxisRoots D) (hC : NoImagAxisRoots (D + N)) :
    nyquistEncirclementsCW N D = (rhpRootCount (D + N) : ℂ) - (rhpRootCount D : ℂ) := by
  unfold nyquistEncirclementsCW
  rw [nyquist_encirclement_formula N D hProp hD hC]
  ring

/-! ### Topological Continuous Phase-Lift Formulation -/

private lemma multiset_prod_I_mul_sub_polar (m : Multiset ℂ) (hm : ∀ a ∈ m, a.re ≠ 0) (ω : ℝ) :
    (m.map fun a => I * ω - a).prod =
      ‖(m.map fun a => I * ω - a).prod‖ *
        Complex.exp (I * ((m.map fun a => factorPhase a ω).sum : ℝ)) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    have ha : a.re ≠ 0 := hm a (Multiset.mem_cons_self a m)
    have hm' : ∀ b ∈ m, b.re ≠ 0 := fun b hb => hm b (Multiset.mem_cons_of_mem hb)
    have hfac := I_mul_sub_eq_norm_mul_exp_factorPhase a ha ω
    have hih := ih hm'
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, Complex.norm_mul,
      Complex.ofReal_add, Complex.ofReal_mul]
    conv_lhs => rw [hfac, hih]
    rw [mul_add I, Complex.exp_add]
    ring

private lemma continuous_sum_factorPhase (m : Multiset ℂ) (hm : ∀ a ∈ m, a.re ≠ 0) :
    Continuous (fun ω : ℝ => (m.map fun a => factorPhase a ω).sum) := by
  induction m using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.sum_zero]
    exact continuous_const
  | cons a m ih =>
    have ha : a.re ≠ 0 := hm a (Multiset.mem_cons_self a m)
    have hm' : ∀ b ∈ m, b.re ≠ 0 := fun b hb => hm b (Multiset.mem_cons_of_mem hb)
    have h_eq : (fun ω : ℝ => ((a ::ₘ m).map fun z => factorPhase z ω).sum) =
        fun ω : ℝ => factorPhase a ω + (m.map fun z => factorPhase z ω).sum := by
      funext ω
      simp [Multiset.map_cons, Multiset.sum_cons]
    rw [h_eq]
    exact (factorPhase_continuous a ha).add (ih hm')

private lemma tendsto_sum_factorPhase_atTop (m : Multiset ℂ) (hm : ∀ a ∈ m, a.re ≠ 0) :
    Tendsto (fun ω : ℝ => (m.map fun a => factorPhase a ω).sum)
      atTop (nhds ((m.card : ℝ) * (Real.pi / 2))) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    have ha : a.re ≠ 0 := hm a (Multiset.mem_cons_self a m)
    have hm' : ∀ b ∈ m, b.re ≠ 0 := fun b hb => hm b (Multiset.mem_cons_of_mem hb)
    have h_eq : (fun ω : ℝ => ((a ::ₘ m).map fun z => factorPhase z ω).sum) =
        fun ω : ℝ => factorPhase a ω + (m.map fun z => factorPhase z ω).sum := by
      funext ω
      simp [Multiset.map_cons, Multiset.sum_cons]
    rw [h_eq]
    have htop : Tendsto (factorPhase a) atTop (nhds (Real.pi / 2)) := by
      rcases lt_or_gt_of_ne ha with hlt | hgt
      · exact tendsto_factorPhase_neg_atTop a hlt
      · exact tendsto_factorPhase_pos_atTop a hgt
    have hadd := htop.add (ih hm')
    have hlim : Real.pi / 2 + (m.card : ℝ) * (Real.pi / 2) =
        ((a ::ₘ m).card : ℝ) * (Real.pi / 2) := by
      simp only [Multiset.card_cons]
      push_cast
      ring
    rw [hlim] at hadd
    exact hadd

private lemma tendsto_sum_factorPhase_atBot (m : Multiset ℂ) (hm : ∀ a ∈ m, a.re ≠ 0) :
    Tendsto (fun ω : ℝ => (m.map fun a => factorPhase a ω).sum)
      atBot
      (nhds (((m.filter fun z : ℂ => 0 < z.re).card : ℝ) * (3 * Real.pi / 2) +
        ((m.filter fun z : ℂ => z.re < 0).card : ℝ) * (-Real.pi / 2))) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    have ha : a.re ≠ 0 := hm a (Multiset.mem_cons_self a m)
    have hm' : ∀ b ∈ m, b.re ≠ 0 := fun b hb => hm b (Multiset.mem_cons_of_mem hb)
    have ih' := ih hm'
    have h_eq : (fun ω : ℝ => ((a ::ₘ m).map fun z => factorPhase z ω).sum) =
        fun ω : ℝ => factorPhase a ω + (m.map fun z => factorPhase z ω).sum := by
      funext ω
      simp [Multiset.map_cons, Multiset.sum_cons]
    rw [h_eq]
    rcases lt_or_gt_of_ne ha with hlt | hgt
    · have hnot : ¬ (0 < a.re) := not_lt.mpr hlt.le
      have hbot := tendsto_factorPhase_neg_atBot a hlt
      have hadd := hbot.add ih'
      have hcard_r :
          ((a ::ₘ m).filter fun z : ℂ => 0 < z.re).card =
            (m.filter fun z : ℂ => 0 < z.re).card := by
        simp [Multiset.filter_cons_of_neg, hnot]
      have hcard_l :
          ((a ::ₘ m).filter fun z : ℂ => z.re < 0).card =
            (m.filter fun z : ℂ => z.re < 0).card + 1 := by
        simp [Multiset.filter_cons_of_pos, hlt]
      have hlim :
          (-Real.pi / 2) +
            (((m.filter fun z : ℂ => 0 < z.re).card : ℝ) * (3 * Real.pi / 2) +
              ((m.filter fun z : ℂ => z.re < 0).card : ℝ) * (-Real.pi / 2)) =
          (((a ::ₘ m).filter fun z : ℂ => 0 < z.re).card : ℝ) * (3 * Real.pi / 2) +
            (((a ::ₘ m).filter fun z : ℂ => z.re < 0).card : ℝ) * (-Real.pi / 2) := by
        rw [hcard_r, hcard_l]
        push_cast
        ring
      rw [hlim] at hadd
      exact hadd
    · have hnot : ¬ (a.re < 0) := not_lt.mpr hgt.le
      have hbot := tendsto_factorPhase_pos_atBot a hgt
      have hadd := hbot.add ih'
      have hcard_r :
          ((a ::ₘ m).filter fun z : ℂ => 0 < z.re).card =
            (m.filter fun z : ℂ => 0 < z.re).card + 1 := by
        simp [Multiset.filter_cons_of_pos, hgt]
      have hcard_l :
          ((a ::ₘ m).filter fun z : ℂ => z.re < 0).card =
            (m.filter fun z : ℂ => z.re < 0).card := by
        simp [Multiset.filter_cons_of_neg, hnot]
      have hlim :
          (3 * Real.pi / 2) +
            (((m.filter fun z : ℂ => 0 < z.re).card : ℝ) * (3 * Real.pi / 2) +
              ((m.filter fun z : ℂ => z.re < 0).card : ℝ) * (-Real.pi / 2)) =
          (((a ::ₘ m).filter fun z : ℂ => 0 < z.re).card : ℝ) * (3 * Real.pi / 2) +
            (((a ::ₘ m).filter fun z : ℂ => z.re < 0).card : ℝ) * (-Real.pi / 2) := by
        rw [hcard_r, hcard_l]
        push_cast
        ring
      rw [hlim] at hadd
      exact hadd

/-- **Topological Continuous Phase-Lift Nyquist Theorem:**
There exists a continuous real-valued phase lift `Φ : ℝ → ℝ` of `ω ↦ 1 + L(i ω)` whose
asymptotic phase change `Φ(+∞) - Φ(-∞)` equals `2 π (P - Z)`. -/
theorem nyquist_phase_lift (N D : Polynomial ℂ)
    (hProp : IsProperNonDegenerate N D)
    (hD : NoImagAxisRoots D) (hC : NoImagAxisRoots (D + N)) :
    ∃ (Φ : ℝ → ℝ) (Φ_pos Φ_neg : ℝ),
      Continuous Φ ∧
      (∀ ω : ℝ, returnDifference N D (I * ω) =
        ‖returnDifference N D (I * ω)‖ * Complex.exp (I * Φ ω)) ∧
      Tendsto Φ atTop (nhds Φ_pos) ∧
      Tendsto Φ atBot (nhds Φ_neg) ∧
      Φ_pos - Φ_neg = 2 * Real.pi * ((rhpRootCount D : ℝ) - (rhpRootCount (D + N) : ℝ)) := by
  have hD0 : D ≠ 0 := noImagAxisRoots_ne_zero hD
  have hC0 : D + N ≠ 0 := noImagAxisRoots_ne_zero hC
  have hmD : ∀ a ∈ D.roots, a.re ≠ 0 := fun a ha => re_ne_zero_of_mem_roots hD ha
  have hmC : ∀ a ∈ (D + N).roots, a.re ≠ 0 := fun a ha => re_ne_zero_of_mem_roots hC ha
  let c : ℂ := (D + N).leadingCoeff / D.leadingCoeff
  let θ₀ : ℝ := Complex.arg c
  let Φ : ℝ → ℝ := fun ω =>
    θ₀ + ((D + N).roots.map fun z => factorPhase z ω).sum -
      (D.roots.map fun p => factorPhase p ω).sum
  let Φ_pos : ℝ := θ₀ + ((D + N).roots.card : ℝ) * (Real.pi / 2) -
    (D.roots.card : ℝ) * (Real.pi / 2)
  let Φ_neg : ℝ := θ₀ +
    (((rhpRootCount (D + N) : ℝ) * (3 * Real.pi / 2) +
      (lhpRootCount (D + N) : ℝ) * (-Real.pi / 2)) -
     ((rhpRootCount D : ℝ) * (3 * Real.pi / 2) +
      (lhpRootCount D : ℝ) * (-Real.pi / 2)))
  refine ⟨Φ, Φ_pos, Φ_neg, ?_, ?_, ?_, ?_, ?_⟩
  · exact (continuous_const.add (continuous_sum_factorPhase (D + N).roots hmC)).sub
      (continuous_sum_factorPhase D.roots hmD)
  · intro ω
    have hret := returnDifference_eq_div (N := N) (D := D) (s := I * ω) (hD ω)
    have hfacC := poly_eq_C_leadingCoeff_mul_prod_roots (D + N) hC0
    have hfacD := poly_eq_C_leadingCoeff_mul_prod_roots D hD0
    have hevalC : (D + N).eval (I * ω) =
        (D + N).leadingCoeff * ((D + N).roots.map fun z => I * ω - z).prod := by
      conv_lhs => rw [hfacC]
      simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod,
        Multiset.map_map]
    have hevalD : D.eval (I * ω) =
        D.leadingCoeff * (D.roots.map fun p => I * ω - p).prod := by
      conv_lhs => rw [hfacD]
      simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod,
        Multiset.map_map]
    have hc_eq : c = ‖c‖ * Complex.exp (I * (θ₀ : ℂ)) := by
      rw [mul_comm I (θ₀ : ℂ)]
      exact (Complex.norm_mul_exp_arg_mul_I c).symm
    have hprodC := multiset_prod_I_mul_sub_polar (D + N).roots hmC ω
    have hprodD := multiset_prod_I_mul_sub_polar D.roots hmD ω
    have hDprod_ne : (D.roots.map fun p => I * ω - p).prod ≠ 0 := by
      intro hzero
      apply hD ω
      rw [hevalD, hzero, mul_zero]
    have hDnorm_ne : (‖(D.roots.map fun p => I * ω - p).prod‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hDprod_ne)
    have hDlc_ne : D.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hD0
    have hnorm_ret : ‖returnDifference N D (I * ω)‖ =
        ‖c‖ * ‖((D + N).roots.map fun z => I * ω - z).prod‖ /
          ‖(D.roots.map fun p => I * ω - p).prod‖ := by
      rw [hret, hevalC, hevalD, norm_div, norm_mul, norm_mul, norm_div]
      ring
    have hdiv_lc :
        ((D + N).leadingCoeff * ((D + N).roots.map fun z => I * ω - z).prod) /
          (D.leadingCoeff * (D.roots.map fun p => I * ω - p).prod) =
        c * ((D + N).roots.map fun z => I * ω - z).prod /
          (D.roots.map fun p => I * ω - p).prod := by
      dsimp [c]
      field_simp [hDlc_ne, hDprod_ne]
    conv_lhs => rw [hret, hevalC, hevalD, hdiv_lc, hc_eq, hprodC, hprodD]
    conv_rhs => rw [hnorm_ret]
    have hΦ_exp :
        Complex.exp (I * (Φ ω : ℂ)) =
          Complex.exp (I * (θ₀ : ℂ)) *
            Complex.exp (I * (((D + N).roots.map fun z => factorPhase z ω).sum : ℝ)) /
            Complex.exp (I * ((D.roots.map fun p => factorPhase p ω).sum : ℝ)) := by
      dsimp [Φ]
      push_cast
      rw [mul_sub, Complex.exp_sub, mul_add, Complex.exp_add]
    rw [hΦ_exp]
    have hexp_ne : Complex.exp (I * ((D.roots.map fun p => factorPhase p ω).sum : ℝ)) ≠ 0 :=
      Complex.exp_ne_zero _
    push_cast
    field_simp [hDnorm_ne, hexp_ne]
  · have htopC := tendsto_sum_factorPhase_atTop (D + N).roots hmC
    have htopD := tendsto_sum_factorPhase_atTop D.roots hmD
    exact (tendsto_const_nhds.add htopC).sub htopD
  · have hbotC := tendsto_sum_factorPhase_atBot (D + N).roots hmC
    have hbotD := tendsto_sum_factorPhase_atBot D.roots hmD
    have hsub := tendsto_const_nhds (x := θ₀).add (hbotC.sub hbotD)
    simpa only [Φ, Φ_neg, rhpRootCount, lhpRootCount, add_sub_assoc] using hsub
  · have hcardC : (D + N).roots.card = rhpRootCount (D + N) + lhpRootCount (D + N) := by
      rw [rhpRootCount_add_lhpRootCount hC0 hC,
        (IsAlgClosed.splits (D + N)).natDegree_eq_card_roots]
    have hcardD : D.roots.card = rhpRootCount D + lhpRootCount D := by
      rw [rhpRootCount_add_lhpRootCount hD0 hD, (IsAlgClosed.splits D).natDegree_eq_card_roots]
    have hdeg_eq :
        rhpRootCount (D + N) + lhpRootCount (D + N) = rhpRootCount D + lhpRootCount D := by
      rw [rhpRootCount_add_lhpRootCount hC0 hC, rhpRootCount_add_lhpRootCount hD0 hD, hProp.2.2]
    have hlhp_eq : (lhpRootCount (D + N) : ℝ) - (lhpRootCount D : ℝ) =
        (rhpRootCount D : ℝ) - (rhpRootCount (D + N) : ℝ) := by
      have : (rhpRootCount (D + N) : ℝ) + (lhpRootCount (D + N) : ℝ) =
          (rhpRootCount D : ℝ) + (lhpRootCount D : ℝ) := by
        exact_mod_cast hdeg_eq
      linarith
    dsimp [Φ_pos, Φ_neg]
    rw [hcardC, hcardD]
    push_cast
    linear_combination Real.pi * hlhp_eq

/-- Uniqueness of the asymptotic phase change for any continuous phase lift `Ψ` of
`ω ↦ 1 + L(i ω)`. -/
theorem nyquist_phase_lift_unique (N D : Polynomial ℂ)
    (hProp : IsProperNonDegenerate N D)
    (hD : NoImagAxisRoots D) (hC : NoImagAxisRoots (D + N))
    (Ψ : ℝ → ℝ) (Ψ_pos Ψ_neg : ℝ) (hΨc : Continuous Ψ)
    (hΨpolar : ∀ ω : ℝ, returnDifference N D (I * ω) =
      ‖returnDifference N D (I * ω)‖ * Complex.exp (I * Ψ ω))
    (hΨtop : Tendsto Ψ atTop (nhds Ψ_pos))
    (hΨbot : Tendsto Ψ atBot (nhds Ψ_neg)) :
    Ψ_pos - Ψ_neg = 2 * Real.pi * ((rhpRootCount D : ℝ) - (rhpRootCount (D + N) : ℝ)) := by
  obtain ⟨Φ, Φ_pos, Φ_neg, hΦc, hΦpolar, hΦtop, hΦbot, hΦdiff⟩ :=
    nyquist_phase_lift N D hProp hD hC
  have hret_ne : ∀ ω : ℝ, returnDifference N D (I * ω) ≠ 0 := by
    intro ω
    rw [returnDifference_eq_div (hD ω)]
    exact div_ne_zero (hC ω) (hD ω)
  obtain ⟨k, hk⟩ := continuous_phase_lift_unique
    (fun ω => returnDifference N D (I * ω)) hret_ne Ψ Φ hΨc hΦc hΨpolar hΦpolar
  have hdiff_eq : (fun ω : ℝ => Ψ ω - Φ ω) = fun _ => 2 * Real.pi * (k : ℝ) := by
    funext ω
    exact hk ω
  have ht1 : Tendsto (fun ω : ℝ => Ψ ω - Φ ω) atTop (nhds (Ψ_pos - Φ_pos)) := hΨtop.sub hΦtop
  have ht2 : Tendsto (fun ω : ℝ => Ψ ω - Φ ω) atBot (nhds (Ψ_neg - Φ_neg)) := hΨbot.sub hΦbot
  rw [hdiff_eq] at ht1 ht2
  have he1 : Ψ_pos - Φ_pos = 2 * Real.pi * (k : ℝ) :=
    tendsto_nhds_unique ht1 tendsto_const_nhds
  have he2 : Ψ_neg - Φ_neg = 2 * Real.pi * (k : ℝ) :=
    tendsto_nhds_unique ht2 tendsto_const_nhds
  linarith

/-! ### Main Nyquist Stability Criterion Theorems -/

/-- **Nyquist Stability Criterion (Counterclockwise Convention):**
Under properness (`deg (D + N) = deg D`) and no imaginary-axis poles/zeros of `1 + L`,
the closed-loop polynomial `D + N` is Hurwitz stable if and only if the Nyquist plot
`ω ↦ L(i ω)` encircles `-1` counterclockwise `P` times, where `P = rhpRootCount D`. -/
theorem nyquist_stability_criterion (N D : Polynomial ℂ)
    (hProp : IsProperNonDegenerate N D)
    (hD : NoImagAxisRoots D) (hC : NoImagAxisRoots (D + N)) :
    IsHurwitz (D + N) ↔ nyquistEncirclementsCCW N D = (rhpRootCount D : ℂ) := by
  have hC0 : D + N ≠ 0 := noImagAxisRoots_ne_zero hC
  rw [isHurwitz_iff_rhpRootCount_eq_zero hC0 hC, nyquist_encirclement_formula N D hProp hD hC]
  constructor
  · intro hZ
    simp [hZ]
  · intro heq
    have hZ0 : (rhpRootCount (D + N) : ℂ) = 0 := by
      linear_combination -heq
    exact_mod_cast hZ0

/-- **Nyquist Stability Criterion (Clockwise Convention):**
`D + N` is Hurwitz stable if and only if the Nyquist plot encircles `-1` clockwise
`-P` times (i.e. `P` counterclockwise encirclements). -/
theorem nyquist_stability_criterion_cw (N D : Polynomial ℂ)
    (hProp : IsProperNonDegenerate N D)
    (hD : NoImagAxisRoots D) (hC : NoImagAxisRoots (D + N)) :
    IsHurwitz (D + N) ↔ nyquistEncirclementsCW N D = -(rhpRootCount D : ℂ) := by
  rw [nyquist_stability_criterion N D hProp hD hC]
  unfold nyquistEncirclementsCW
  constructor
  · intro h
    rw [h]
  · intro h
    linear_combination -h

/-- **Strictly Proper Specialization** (`deg N < deg D`). -/
theorem nyquist_stability_criterion_strictlyProper (N D : Polynomial ℂ)
    (hD0 : D ≠ 0) (hdeg : N.natDegree < D.natDegree)
    (hD : NoImagAxisRoots D) (hC : NoImagAxisRoots (D + N)) :
    IsHurwitz (D + N) ↔ nyquistEncirclementsCCW N D = (rhpRootCount D : ℂ) :=
  nyquist_stability_criterion N D (strictlyProper_implies_properNonDegenerate hD0 hdeg) hD hC

/-- **Open-Loop Stable Specialization:**
If the open-loop plant `D` is Hurwitz stable, then the closed-loop system `D + N` is Hurwitz
stable if and only if the Nyquist plot makes `0` encirclements of `-1`. -/
theorem nyquist_stability_criterion_openLoopStable (N D : Polynomial ℂ)
    (hProp : IsProperNonDegenerate N D)
    (hHurwitzD : IsHurwitz D) (hC : NoImagAxisRoots (D + N)) :
    IsHurwitz (D + N) ↔ nyquistEncirclementsCW N D = 0 := by
  have hD : NoImagAxisRoots D := by
    intro ω hzero
    have hlt := hHurwitzD.2 (I * (ω : ℂ)) hzero
    simp at hlt
  have hrD : rhpRootCount D = 0 :=
    (isHurwitz_iff_rhpRootCount_eq_zero hHurwitzD.1 hD).mp hHurwitzD
  rw [nyquist_stability_criterion_cw N D hProp hD hC, hrD]
  simp

/-! ### Real Transfer Functions and Conjugate Symmetry -/

private lemma eval_map_algebraMap_conj (p : Polynomial ℝ) (s : ℂ) :
    starRingEnd ℂ ((p.map (algebraMap ℝ ℂ)).eval s) =
      (p.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ s) := by
  rw [Polynomial.eval_map, Polynomial.eval_map, Polynomial.hom_eval₂]
  have hcomp : (starRingEnd ℂ).comp (algebraMap ℝ ℂ) = algebraMap ℝ ℂ := by
    ext x
    simp
  rw [hcomp]

/-- Conjugate symmetry of the Nyquist curve for real rational transfer functions:
`L(-i ω) = conj (L(i ω))`. -/
theorem nyquistCurve_conj_symm (N D : Polynomial ℝ) (ω : ℝ) :
    nyquistCurve (N.map (algebraMap ℝ ℂ)) (D.map (algebraMap ℝ ℂ)) (-ω) =
      starRingEnd ℂ (nyquistCurve (N.map (algebraMap ℝ ℂ)) (D.map (algebraMap ℝ ℂ)) ω) := by
  unfold nyquistCurve evalTransfer
  have hconj_s : starRingEnd ℂ (I * (ω : ℂ)) = I * ((-ω : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [map_div₀, eval_map_algebraMap_conj, eval_map_algebraMap_conj, hconj_s]

/-- **Nyquist Stability Criterion for Real Transfer Functions** (`N D : Polynomial ℝ`). -/
theorem nyquist_stability_criterion_real (N D : Polynomial ℝ)
    (hProp : IsProperNonDegenerate (N.map (algebraMap ℝ ℂ)) (D.map (algebraMap ℝ ℂ)))
    (hD : NoImagAxisRoots (D.map (algebraMap ℝ ℂ)))
    (hC : NoImagAxisRoots ((D + N).map (algebraMap ℝ ℂ))) :
    IsHurwitz ((D + N).map (algebraMap ℝ ℂ)) ↔
      nyquistEncirclementsCCW (N.map (algebraMap ℝ ℂ)) (D.map (algebraMap ℝ ℂ)) =
        (rhpRootCount (D.map (algebraMap ℝ ℂ)) : ℂ) := by
  have hadd : (D + N).map (algebraMap ℝ ℂ) =
      D.map (algebraMap ℝ ℂ) + N.map (algebraMap ℝ ℂ) := Polynomial.map_add _
  rw [hadd] at hC ⊢
  exact nyquist_stability_criterion (N.map (algebraMap ℝ ℂ)) (D.map (algebraMap ℝ ℂ)) hProp hD hC

end Nyquist
