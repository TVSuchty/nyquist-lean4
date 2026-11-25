import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Core Definitions for the Nyquist Stability Criterion

This file defines the basic objects for rational transfer functions `L(s) = N(s) / D(s)`,
right/left half-plane root counts, Hurwitz stability, the Nyquist curve, the D-contour integrals,
and the winding number (encirclements of `-1`).
-/

namespace Nyquist

open Complex Polynomial MeasureTheory

/-- Open-loop rational transfer function `L(s) = N(s) / D(s)`. -/
noncomputable def evalTransfer (N D : Polynomial ℂ) (s : ℂ) : ℂ :=
  N.eval s / D.eval s

/-- Closed-loop characteristic polynomial `D(s) + N(s)` for unity negative feedback. -/
noncomputable def closedLoopPoly (N D : Polynomial ℂ) : Polynomial ℂ :=
  D + N

/-- Number of roots (counted with multiplicity) in the open right half-plane `{s | 0 < s.re}`. -/
noncomputable def rhpRootCount (p : Polynomial ℂ) : ℕ :=
  (p.roots.filter (fun z : ℂ => 0 < z.re)).card

/-- Number of roots (counted with multiplicity) in the open left half-plane `{s | s.re < 0}`. -/
noncomputable def lhpRootCount (p : Polynomial ℂ) : ℕ :=
  (p.roots.filter (fun z : ℂ => z.re < 0)).card

/-- Hurwitz stability: `p` is nonzero and all its roots lie in the open left half-plane. -/
def IsHurwitz (p : Polynomial ℂ) : Prop :=
  p ≠ 0 ∧ ∀ z : ℂ, p.IsRoot z → z.re < 0

/-- No roots on the imaginary axis `i ℝ`. -/
def NoImagAxisRoots (p : Polynomial ℂ) : Prop :=
  ∀ ω : ℝ, p.eval (I * ω) ≠ 0

/-- Proper and non-degenerate at `∞`: `D ≠ 0`, `D + N ≠ 0`, and `deg (D + N) = deg D`
(equivalently, `deg N ≤ deg D` and leading coefficients do not cancel). -/
def IsProperNonDegenerate (N D : Polynomial ℂ) : Prop :=
  D ≠ 0 ∧ D + N ≠ 0 ∧ (D + N).natDegree = D.natDegree

/-- The open-loop Nyquist plot `ω ↦ L(i ω)`. -/
noncomputable def nyquistCurve (N D : Polynomial ℂ) (ω : ℝ) : ℂ :=
  evalTransfer N D (I * ω)

/-- The return difference `F(s) = 1 + L(s)`. -/
noncomputable def returnDifference (N D : Polynomial ℂ) (s : ℂ) : ℂ :=
  1 + evalTransfer N D s

/-- Logarithmic-derivative integrand along the imaginary axis `s = i ω` for `1 + L(s)`. -/
noncomputable def nyquistIntegrand (N D : Polynomial ℂ) (ω : ℝ) : ℂ :=
  deriv (fun t : ℝ => returnDifference N D (I * t)) ω / returnDifference N D (I * ω)

/-- Counterclockwise encirclements of `-1` by the Nyquist curve `L(i ℝ)`
(i.e. of `0` by `1 + L(i ℝ)`). -/
noncomputable def nyquistEncirclementsCCW (N D : Polynomial ℂ) : ℂ :=
  (1 / (2 * Real.pi * I)) * ∫ ω : ℝ, nyquistIntegrand N D ω

/-- Clockwise encirclements of `-1` by the Nyquist curve `L(i ℝ)`. -/
noncomputable def nyquistEncirclementsCW (N D : Polynomial ℂ) : ℂ :=
  - nyquistEncirclementsCCW N D

/-- Logarithmic-derivative integral along the imaginary-axis segment `[-iR, iR]`. -/
noncomputable def nyquistImagIntegral (N D : Polynomial ℂ) (R : ℝ) : ℂ :=
  ∫ ω in (-R)..R, nyquistIntegrand N D ω

/-- Logarithmic-derivative integrand along the clockwise semicircle `θ ↦ R * exp (i θ)`. -/
noncomputable def nyquistSemiIntegrand (N D : Polynomial ℂ) (R : ℝ) (θ : ℝ) : ℂ :=
  deriv (fun t : ℝ => returnDifference N D (R * Complex.exp (I * t))) θ /
    returnDifference N D (R * Complex.exp (I * θ))

/-- Logarithmic-derivative integral along the clockwise right semicircle `θ ∈ [π/2, -π/2]`. -/
noncomputable def nyquistSemiIntegral (N D : Polynomial ℂ) (R : ℝ) : ℂ :=
  ∫ θ in (Real.pi / 2)..(-Real.pi / 2), nyquistSemiIntegrand N D R θ

/-- Total clockwise Nyquist D-contour winding integral of radius `R`. -/
noncomputable def nyquistDContourCW (N D : Polynomial ℂ) (R : ℝ) : ℂ :=
  -(1 / (2 * Real.pi * I)) * (nyquistImagIntegral N D R + nyquistSemiIntegral N D R)

lemma noImagAxisRoots_ne_zero {p : Polynomial ℂ} (hp : NoImagAxisRoots p) : p ≠ 0 := by
  intro h0
  have := hp 0
  simp [h0] at this

lemma re_ne_zero_of_mem_roots {p : Polynomial ℂ} (hImag : NoImagAxisRoots p) {z : ℂ}
    (hz : z ∈ p.roots) : z.re ≠ 0 := by
  intro hre
  have hp0 : p ≠ 0 := noImagAxisRoots_ne_zero hImag
  have heval : p.eval z = 0 := (mem_roots hp0).mp hz
  have hz_eq : z = I * (z.im : ℂ) := by
    apply Complex.ext <;> simp [hre]
  rw [hz_eq] at heval
  exact hImag z.im heval

lemma rhpRootCount_add_lhpRootCount {p : Polynomial ℂ} (_hp : p ≠ 0) (hImag : NoImagAxisRoots p) :
    rhpRootCount p + lhpRootCount p = p.natDegree := by
  unfold rhpRootCount lhpRootCount
  have hdisj :
      p.roots.filter (fun z : ℂ => z.re < 0) = p.roots.filter (fun z : ℂ => ¬ (0 < z.re)) := by
    refine Multiset.filter_congr fun z hz => ?_
    have hne : z.re ≠ 0 := re_ne_zero_of_mem_roots hImag hz
    constructor
    · intro hlt hgt
      linarith
    · intro hnot
      exact lt_of_le_of_ne (not_lt.mp hnot) hne
  rw [hdisj, ← Multiset.card_add, Multiset.filter_add_not]
  exact (IsAlgClosed.splits p).natDegree_eq_card_roots.symm

lemma isHurwitz_iff_rhpRootCount_eq_zero {p : Polynomial ℂ} (hp : p ≠ 0)
    (hImag : NoImagAxisRoots p) : IsHurwitz p ↔ rhpRootCount p = 0 := by
  constructor
  · rintro ⟨_, hroots⟩
    unfold rhpRootCount
    rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro z hz hpos
    have hlt := hroots z ((mem_roots hp).mp hz)
    linarith
  · intro hr
    refine ⟨hp, fun z hz => ?_⟩
    have hmem : z ∈ p.roots := (mem_roots hp).mpr hz
    have hne : z.re ≠ 0 := re_ne_zero_of_mem_roots hImag hmem
    by_contra hnot
    have hpos : 0 < z.re := lt_of_le_of_ne (not_lt.mp hnot) hne.symm
    have hmemf : z ∈ p.roots.filter (fun w : ℂ => 0 < w.re) :=
      Multiset.mem_filter.mpr ⟨hmem, hpos⟩
    have hnil : p.roots.filter (fun w : ℂ => 0 < w.re) = 0 :=
      Multiset.card_eq_zero.mp hr
    rw [hnil] at hmemf
    exact Multiset.notMem_zero z hmemf

lemma strictlyProper_implies_properNonDegenerate {N D : Polynomial ℂ}
    (hD : D ≠ 0) (hdeg : N.natDegree < D.natDegree) : IsProperNonDegenerate N D := by
  have hdeg_eq : (D + N).natDegree = D.natDegree :=
    Polynomial.natDegree_add_eq_left_of_natDegree_lt hdeg
  have hC0 : D + N ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg_eq
    omega
  exact ⟨hD, hC0, hdeg_eq⟩

lemma returnDifference_eq_div {N D : Polynomial ℂ} {s : ℂ} (hD : D.eval s ≠ 0) :
    returnDifference N D s = (D + N).eval s / D.eval s := by
  unfold returnDifference evalTransfer
  rw [Polynomial.eval_add]
  field_simp [hD]

end Nyquist
