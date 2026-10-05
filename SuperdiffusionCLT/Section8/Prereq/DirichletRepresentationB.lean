/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.DirichletRepresentation
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExitMeanValueLimit
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExitMeanValueCube
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExitMeanValueDecomposition
public import SuperdiffusionCLT.Section8.DivergenceForm.OnePointRealExtension
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.CruxUpperProcess

/-!
# Uniform bounds for the part resolvent on a ball

A classical supersolution of the unit forcing, built from a Gaussian centred outside the ball
at a boundary point, bounds every zero-trace solution of `lam u - ∇·(a∇u) = 1` on the ball by a
constant that does not depend on the shift.  Through the resolvent identity this makes the part
resolvent Lipschitz in the shift, uniformly in the (bounded) datum.

* `dirRep_uniform_bound_weak`: the shift-free bound for weak solutions;
* `dirRep_uniform_bound`: the bound for the part resolvent of the indicator of the ball;
* `dirRep_resolvent_le_mul`, `dirRep_resolvent_bound`: the bound for bounded data;
* `dirRep_resolvent_diff_le`: `|R_mu f - R_nu f| ≤ |nu - mu| M Bd²`;
* `dirRep_pos`, `dirRep_neg`, `dirRep_part_split`, `dirRep_abs_resolvent_le`: signed data;
* `dirRep_decomp`, `dirRep_decomp_signed`: the strong Markov decomposition at the exit time on the
  ball, `R_mu G = R^B_mu G + (discounted exit average of R_mu G)`, for continuous data vanishing at
  infinity.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory Set Filter Topology
open SuperdiffusionCLT.Section8.DivergenceForm
open SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.StoppedDirichlet
open MarkovProcess MarkovProcess.Semigroup MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d] {nu : ℝ} {k : Vec d → Mat d}

/-- **A uniform supersolution on the ball.**  There is a constant `Bd`, independent of the
shift, such that every zero-trace weak solution of `lam u - ∇·(a∇u) = 1` on the ball is at most
`Bd` almost everywhere. -/
theorem dirRep_uniform_bound_weak {ν : ℝ} (hν : 0 < ν) {k : Vec d → Mat d}
    (hk : ∀ i j, ContDiff ℝ 1 (fun x => k x i j)) (hskew : ∀ x i j, k x i j = -k x j i)
    {x₀ : Vec d} {r : ℝ} (hr : 0 < r) :
    ∃ Bd : ℝ, 0 ≤ Bd ∧ ∀ (lam : ℝ), 0 < lam → ∀ (u : H10Function (euclideanBall x₀ r)),
      IsScalarForcedWeakSolution (fun x => ν • (1 : Mat d) + k x) (euclideanBall x₀ r)
        (fun y => 1 - lam * u.toH1Function.toFun y) u.toH1Function →
      ∀ᵐ x ∂(volumeMeasureOn (euclideanBall x₀ r)), u.toH1Function.toFun x ≤ Bd := by
  have hV := SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
    x₀ hr
  have hcompact : IsCompact (Metric.closedBall x₀ r) := isCompact_closedBall x₀ r
  have hUR : euclideanBall x₀ r ⊆ Metric.closedBall x₀ r :=
    (euclideanBall_subset_metricBall hr).trans Metric.ball_subset_closedBall
  have hcont : Continuous (fun x => ∑ j, |ballBdry_colDiv k x j|) :=
    continuous_finsetSum _ fun j _ => continuous_abs.comp (ballBdry_continuous_colDiv hk j)
  obtain ⟨Kb, hKb⟩ := hcompact.exists_bound_of_continuousOn hcont.continuousOn
  set Y : ℝ := 4 * r with hY
  have hY0 : 0 ≤ Y := by positivity
  set μ : ℝ := (ν * d + |Kb| * Y + 1) / (2 * ν * r ^ 2) + 1 with hμ
  have hμ0 : 0 < μ := by positivity
  have hμbig : ν * (d : ℝ) + |Kb| * Y + 1 ≤ 2 * μ * ν * r ^ 2 := by
    have : 2 * μ * ν * r ^ 2 = (ν * d + |Kb| * Y + 1) + 2 * ν * r ^ 2 := by
      rw [hμ]; field_simp
    rw [this]
    have : 0 < 2 * ν * r ^ 2 := by positivity
    linarith only [this]
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  obtain ⟨i0⟩ : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  set p : Vec d := x₀ + (r • (Pi.single i0 1 : Vec d)) with hpdef
  have hp : euclideanSqDist p x₀ = r ^ 2 := by
    rw [ballBdry_euclideanSqDist_eq]
    have : ∀ j : Fin d, (p j - x₀ j) ^ 2 = if j = i0 then r ^ 2 else 0 := fun j => by
      by_cases hj : j = i0
      · subst hj; simp [hpdef]
      · simp [hpdef, hj]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  set e : Vec d := fun j => 2 * p j - x₀ j with he
  set M : ℝ := Real.exp (μ * Y ^ 2) / (2 * μ) with hM
  set c : ℝ := Real.exp (-μ * r ^ 2) with hc
  have hM0 : 0 ≤ M := by positivity
  have hsp : ballBdry_sq e p = r ^ 2 := by
    rw [ballBdry_sq_eq_euclideanSqDist, ballBdry_euclideanSqDist_eq, ← hp,
      ballBdry_euclideanSqDist_eq]
    exact Finset.sum_congr rfl fun j _ => by simp only [he]; ring
  have hψ0 : ∀ x ∈ euclideanBall x₀ r, 0 ≤ ballBdry_psi M μ c e x := fun x hx => by
    have hb := (ballBdry_dist_bounds hp hx).1
    unfold ballBdry_psi
    refine mul_nonneg hM0 (sub_nonneg.mpr ?_)
    unfold ballBdry_gauss
    exact Real.exp_le_exp.mpr (by nlinarith only [hb, hμ0])
  have hψfd : ∀ x, (fun j => fderiv ℝ (ballBdry_psi M μ c e) x (basisVec j)) =
      ballBdry_grad M μ e x := fun x => funext fun j => ballBdry_psi_apply_basis M μ c e x j
  have hfun : (fun x => matVecMul (ν • (1 : Mat d) + k x)
      (fun j => fderiv ℝ (ballBdry_psi M μ c e) x (basisVec j))) =
      ballBdry_flux ν k M μ e := funext fun x => by
    rw [hψfd x]; rfl
  have hle : ∀ x, ballBdry_psi M μ c e x ≤ M := fun x => by
    unfold ballBdry_psi
    have h1 : c ≤ 1 := by
      rw [hc]
      exact Real.exp_le_one_iff.mpr (by nlinarith only [hμ0, sq_nonneg r])
    have h2 : 0 < ballBdry_gauss μ e x := Real.exp_pos _
    nlinarith only [h1, h2, hM0]
  refine ⟨M, hM0, fun lam hlam u hu => ?_⟩
  have hcomp := ballBdry_compare hV hν hk hskew hlam u hu
      (ballBdry_contDiff_psi M μ c e (n := 1)) hψ0 hr.le hUR (by
        intro i
        have h := ballBdry_contDiff_flux ν hk M μ e i
        rw [← hfun] at h
        exact h) (by
        intro x hx
        rw [hfun]
        have hb := ballBdry_dist_bounds hp hx
        refine ballBdry_neg_div_flux_ge ν hk hskew hμ0 hν hY0 hμbig e x hb.1 hb.2 ?_
        have := hKb x (hUR hx)
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans (this.trans (le_abs_self _)))
  filter_upwards [hcomp] with x hx
  exact hx.trans (hle x)


variable (D : FieldInputData d nu k)

/-- The part resolvent of the indicator of the ball is bounded uniformly in the shift. -/
theorem dirRep_uniform_bound (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    ∃ Bd : ℝ, 0 ≤ Bd ∧ ∀ (mu : PositiveShift) (y : Vec d),
      D.analyticData.partC0Resolvent
        (SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
          x₀ hr) mu (ballExit_datum (euclideanBall x₀ r))
        (ballExit_measurable_datum (isOpen_euclideanBall x₀ r)) (ballExit_abs_datum_le _) y ≤ Bd := by
  obtain ⟨Bd, hBd0, hBd⟩ := dirRep_uniform_bound_weak D.nu_pos (fun i j => D.contDiff_entry i j)
    (ballBdry_skew_entry D) (x₀ := x₀) hr
  refine ⟨Bd, hBd0, fun mu y => ?_⟩
  have hV := SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
    x₀ hr
  set A := D.analyticData with hA
  have hf := ballExit_measurable_datum (d := d) (V := euclideanBall x₀ r) hV.isOpen
  have hfD := ballExit_abs_datum_le (d := d) (euclideanBall x₀ r)
  set w₀ := A.partC0Resolvent hV mu _ hf hfD with hw₀
  have hrep : w₀ =ᵐ[volumeMeasureOn (euclideanBall x₀ r)] ZeroTraceSobolev.toL2
      (alphaShiftedSolution A.a (show (0 : ℝ) < ((mu : MarkovProcess.Semigroup.PositiveShift) : ℝ) from mu.property)
        A.hnu (partEllipticity A hV) (ballExit_datumL2 hV)) := by
    filter_upwards [A.partC0Resolvent_ae hV mu _ hf hfD] with y hy
    exact hy
  obtain ⟨u, hwu, hsol⟩ := ballExit_exists_h10_solution A hV mu hrep
  by_cases hy : y ∈ euclideanBall x₀ r
  · refine le_of_ae_le_of_continuousOn hV.isOpen (A.continuousOn_partC0Resolvent hV mu _ hf hfD)
      continuousOn_const ?_ y hy
    filter_upwards [hwu, hBd mu.1 mu.property u hsol] with z h1 h2
    exact h1.trans_le h2
  · rw [hw₀, A.partC0Resolvent_of_notMem hV mu _ hf hfD hy]
    exact hBd0


/-- The ball as an open bounded convex domain. -/
abbrev dirRep_ball (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    IsOpenBoundedConvexDomain (euclideanBall x₀ r) :=
  SuperdiffusionCLT.Section8.Common.Regularity.Ported.isOpenBoundedConvexDomain_euclideanBall
    x₀ hr

/-- The part resolvent of a bounded nonnegative datum is at most the bound times the part
resolvent of the indicator of the ball. -/
theorem dirRep_resolvent_le_mul (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {M : ℝ}
    (hfM : ∀ y, |f y| ≤ M) (y : Vec d) :
    D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) mu f hf hfM y ≤
      M * D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) mu (ballExit_datum (euclideanBall x₀ r))
        (ballExit_measurable_datum (isOpen_euclideanBall x₀ r)) (ballExit_abs_datum_le _) y := by
  set A := D.analyticData with hA
  set B := euclideanBall x₀ r with hB
  have hV := dirRep_ball x₀ hr
  have h1 := ballExit_measurable_datum (d := d) (V := B) hV.isOpen
  have h1D := ballExit_abs_datum_le (d := d) B
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hfM 0)
  have hcM : ∀ y, |M * ballExit_datum B y| ≤ |M| * 1 := fun y => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (h1D y) (abs_nonneg M)
  have hsm : Measurable fun y => M * ballExit_datum B y := h1.const_smul M
  have hf' : Measurable (B.indicator f) := hf.indicator hV.isOpen.measurableSet
  have hf'M : ∀ y, |B.indicator f y| ≤ M := fun y => by
    by_cases hy : y ∈ B
    · rw [Set.indicator_of_mem hy]; exact hfM y
    · rw [Set.indicator_of_notMem hy, abs_zero]; exact hM0
  have hle : A.partC0Resolvent hV mu f hf hfM y ≤
      A.partC0Resolvent hV mu (fun y => M * ballExit_datum B y) hsm hcM y := by
    refine (A.partC0Resolvent_eq_of_eqOn hV mu hf hf' hfM hf'M
      (fun y hy => (Set.indicator_of_mem hy f).symm) y).le.trans ?_
    refine A.partC0Resolvent_mono hV mu hf' hsm hf'M hcM (fun y => ?_) y
    by_cases hy : y ∈ B
    · rw [Set.indicator_of_mem hy, ballExit_datum_of_mem hy, mul_one]
      exact (le_abs_self _).trans (hfM y)
    · rw [Set.indicator_of_notMem hy]
      unfold ballExit_datum
      rw [Set.indicator_of_notMem hy, mul_zero]
  exact hle.trans (A.partC0Resolvent_smul hV mu M h1 h1D hcM y).le

/-- **A uniform bound for the part resolvent.**  `0 ≤ R_mu f ≤ M Bd`, with `Bd` independent of the
shift and of the datum. -/
theorem dirRep_resolvent_bound (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    ∃ Bd : ℝ, 0 ≤ Bd ∧ ∀ (mu : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f)
      {M : ℝ} (hfM : ∀ y, |f y| ≤ M) (y : Vec d),
      D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) mu f hf hfM y ≤ M * Bd := by
  obtain ⟨Bd, hBd0, hBd⟩ := dirRep_uniform_bound D x₀ hr
  refine ⟨Bd, hBd0, fun mu f hf M hfM y => ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hfM 0)
  exact (dirRep_resolvent_le_mul D x₀ hr mu hf hfM y).trans
    (mul_le_mul_of_nonneg_left (hBd mu y) hM0)


/-- **The part resolvent is Lipschitz in the shift, uniformly in the datum bound.**  By the
resolvent identity, `R_mu f - R_nu f = (nu - mu) R_nu R_mu f`, and `R_nu` of a function bounded
by `M Bd` is at most `M Bd²`. -/
theorem dirRep_resolvent_diff_le (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    ∃ Bd : ℝ, 0 ≤ Bd ∧ ∀ (mu nu : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f)
      {M : ℝ} (hfM : ∀ y, |f y| ≤ M), (∀ y, 0 ≤ f y) → ∀ (y : Vec d),
      |D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) mu f hf hfM y -
          D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) nu f hf hfM y| ≤
        |(nu : ℝ) - (mu : ℝ)| * (M * Bd * Bd) := by
  obtain ⟨Bd, hBd0, hBd⟩ := dirRep_resolvent_bound D x₀ hr
  refine ⟨Bd, hBd0, fun mu nu f hf M hfM hf0 y => ?_⟩
  set A := D.analyticData with hA
  have hV := dirRep_ball x₀ hr
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hfM 0)
  set g := A.partC0Resolvent hV mu f hf hfM with hg
  have hgm : Measurable g := A.measurable_partC0Resolvent hV mu f hf hfM
  have hg0 : ∀ z, 0 ≤ g z := fun z => A.partC0Resolvent_nonneg hV mu f hf hf0 hfM z
  have hgle : ∀ z, g z ≤ M * Bd := fun z => hBd mu hf hfM z
  have hgC : ∀ z, |g z| ≤ M * Bd := fun z => by
    rw [abs_of_nonneg (hg0 z)]; exact hgle z
  have hid := A.partC0Resolvent_resolvent_identity hV mu nu hf hM0 hfM y
  have hswap : A.partC0Resolvent hV nu g hgm (D := M / (mu : ℝ))
      (A.abs_partC0Resolvent_le hV mu hf hM0 hfM) y =
      A.partC0Resolvent hV nu g hgm hgC y :=
    A.partC0Resolvent_eq_of_eqOn hV nu hgm hgm _ hgC (Set.eqOn_refl _ _) y
  rw [hswap] at hid
  have h0 : 0 ≤ A.partC0Resolvent hV nu g hgm hgC y :=
    A.partC0Resolvent_nonneg hV nu g hgm hg0 hgC y
  have h1 : A.partC0Resolvent hV nu g hgm hgC y ≤ (M * Bd) * Bd := hBd nu hgm hgC y
  have hdiff : g y - A.partC0Resolvent hV nu f hf hfM y =
      ((nu : ℝ) - (mu : ℝ)) * A.partC0Resolvent hV nu g hgm hgC y := by
    linarith only [hid]
  rw [hdiff, abs_mul, abs_of_nonneg h0]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)


/-- The positive part of a bounded measurable datum. -/
def dirRep_pos (f : Vec d → ℝ) : Vec d → ℝ := fun z => max (f z) 0

/-- The negative part of a bounded measurable datum. -/
def dirRep_neg (f : Vec d → ℝ) : Vec d → ℝ := fun z => max (-f z) 0

omit [NeZero d] in
theorem dirRep_pos_nonneg (f : Vec d → ℝ) (z : Vec d) : 0 ≤ dirRep_pos f z := le_max_right _ _

omit [NeZero d] in
theorem dirRep_neg_nonneg (f : Vec d → ℝ) (z : Vec d) : 0 ≤ dirRep_neg f z := le_max_right _ _

omit [NeZero d] in
theorem dirRep_pos_sub_neg (f : Vec d → ℝ) (z : Vec d) : dirRep_pos f z - dirRep_neg f z = f z := by
  unfold dirRep_pos dirRep_neg
  rcases le_total (f z) 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith only [h])]; ring
  · rw [max_eq_left h, max_eq_right (by linarith only [h])]; ring

omit [NeZero d] in
theorem dirRep_pos_measurable {f : Vec d → ℝ} (hf : Measurable f) : Measurable (dirRep_pos f) :=
  hf.max measurable_const

omit [NeZero d] in
theorem dirRep_neg_measurable {f : Vec d → ℝ} (hf : Measurable f) : Measurable (dirRep_neg f) :=
  hf.neg.max measurable_const

omit [NeZero d] in
theorem dirRep_abs_pos_le {f : Vec d → ℝ} {M : ℝ} (hfM : ∀ y, |f y| ≤ M) (z : Vec d) :
    |dirRep_pos f z| ≤ M := by
  rw [abs_of_nonneg (dirRep_pos_nonneg f z)]
  exact max_le ((le_abs_self _).trans (hfM z)) ((abs_nonneg _).trans (hfM z))

omit [NeZero d] in
theorem dirRep_abs_neg_le {f : Vec d → ℝ} {M : ℝ} (hfM : ∀ y, |f y| ≤ M) (z : Vec d) :
    |dirRep_neg f z| ≤ M := by
  rw [abs_of_nonneg (dirRep_neg_nonneg f z)]
  exact max_le (neg_le_abs _ |>.trans (hfM z)) ((abs_nonneg _).trans (hfM z))


/-- The part resolvent of a bounded measurable datum is the difference of the part resolvents of
its positive and negative parts. -/
theorem dirRep_part_split (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) {M : ℝ} (hfM : ∀ y, |f y| ≤ M) (y : Vec d) :
    D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) mu f hf hfM y =
      D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) mu (dirRep_pos f)
        (dirRep_pos_measurable hf) (dirRep_abs_pos_le hfM) y -
      D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) mu (dirRep_neg f)
        (dirRep_neg_measurable hf) (dirRep_abs_neg_le hfM) y := by
  have hV := dirRep_ball x₀ hr
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hfM 0)
  have hcb : ∀ z, |(-1 : ℝ) * dirRep_neg f z| ≤ |(-1 : ℝ)| * M := fun z => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (dirRep_abs_neg_le hfM z) (abs_nonneg _)
  have hsum : ∀ z, |dirRep_pos f z + (-1 : ℝ) * dirRep_neg f z| ≤ M + |(-1 : ℝ)| * M := fun z =>
    (abs_add_le _ _).trans (add_le_add (dirRep_abs_pos_le hfM z) (hcb z))
  have hmeas : Measurable fun z => dirRep_pos f z + (-1 : ℝ) * dirRep_neg f z :=
    (dirRep_pos_measurable hf).add ((dirRep_neg_measurable hf).const_smul (-1 : ℝ))
  have hlin : D.analyticData.partC0Resolvent hV mu
      (fun z => dirRep_pos f z + (-1 : ℝ) * dirRep_neg f z) hmeas hsum y =
      D.analyticData.partC0Resolvent hV mu (dirRep_pos f) (dirRep_pos_measurable hf)
        (dirRep_abs_pos_le hfM) y +
      (-1 : ℝ) * D.analyticData.partC0Resolvent hV mu (dirRep_neg f) (dirRep_neg_measurable hf)
        (dirRep_abs_neg_le hfM) y :=
    D.analyticData.partC0Resolvent_add_const_mul hV mu (-1 : ℝ) (dirRep_pos_measurable hf)
      (dirRep_neg_measurable hf) (dirRep_abs_pos_le hfM) (dirRep_abs_neg_le hfM) hmeas hsum y
  have hswap : D.analyticData.partC0Resolvent hV mu f hf hfM y =
      D.analyticData.partC0Resolvent hV mu (fun z => dirRep_pos f z + (-1 : ℝ) * dirRep_neg f z)
        hmeas hsum y :=
    D.analyticData.partC0Resolvent_eq_of_eqOn hV mu hf hmeas hfM hsum (fun z _ => by
      have := dirRep_pos_sub_neg f z
      show f z = dirRep_pos f z + (-1 : ℝ) * dirRep_neg f z
      linarith only [this]) y
  linarith only [hlin, hswap]


/-- **The exit decomposition at a positive shift on a ball for the marginal field.**  For a
nonnegative `C₀` datum `G`, the resolvent `R_mu G` at a point `y` of the ball is the part
resolvent of `G` plus the discounted exit average of `R_mu G`. -/
theorem dirRep_decomp (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (mu : PositiveShift)
    (G : C₀(Vec d, ℝ)) (hG0 : ∀ z, 0 ≤ G z) {y : Vec d} (hy : y ∈ euclideanBall x₀ r) :
    let hreg := D.logGrowthBounds.processInput.toOnePointRegular
    let := hreg.metricSpace
    let := hreg.completeSpace
    D.logGrowthBounds.resolvent.toContractiveResolvent.operator mu G y =
      D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) mu G G.continuous.measurable
          (D := ‖G‖) (fun z => by
            rw [← Real.norm_eq_abs, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
            exact BoundedContinuousFunction.norm_coe_le_norm G.toBCF z) y +
        discountedExitAverage D.logGrowthBounds.resolvent.onePointKernelSemigroup
          D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
          (((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall x₀ r) (mu : ℝ)
          (onePointRealExtension
            (fun z => D.logGrowthBounds.resolvent.toContractiveResolvent.operator mu G z))
          (y : OnePoint (Vec d)) := by
  intro hreg hm hc
  set B := euclideanBall x₀ r with hB
  have hV := dirRep_ball x₀ hr
  have hUopen : IsOpen (((↑) : Vec d → OnePoint (Vec d)) '' B) :=
    OnePoint.isOpen_image_coe.mpr hV.isOpen
  have hGbd : ∀ z, |G z| ≤ ‖G‖ := fun z => by
    rw [← Real.norm_eq_abs, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    exact BoundedContinuousFunction.norm_coe_le_norm G.toBCF z
  set q : Vec d → ℝ := fun z => D.logGrowthBounds.resolvent.toContractiveResolvent.operator mu G z with hqdef
  have hq0 : ∀ z, 0 ≤ q z := fun z => D.logGrowthBounds.resolvent.isPositive mu G hG0 z
  have hqmeas : Measurable q := (D.logGrowthBounds.resolvent.toContractiveResolvent.operator mu G).continuous.measurable
  have hqbd : ∀ z, |q z| ≤ ‖D.logGrowthBounds.resolvent.toContractiveResolvent.operator mu G‖ :=
    abs_apply_le_norm_zeroAtInfty _
  have hgmeas : Measurable fun z : Vec d => ENNReal.ofReal (G z) :=
    ENNReal.measurable_ofReal.comp G.continuous.measurable
  have hlive : Measurable (PositiveC0ContractiveResolvent.onePointLiveExtension
      (fun z => ENNReal.ofReal (G z))) :=
    PositiveC0ContractiveResolvent.measurable_onePointLiveExtension hgmeas
  have hres : ∀ z : OnePoint (Vec d),
      (∫⁻ path, ContinuousPath.pathResolvent (mu : ℝ)
        (PositiveC0ContractiveResolvent.onePointLiveExtension
          (fun w => ENNReal.ofReal (G w))) path
        ∂(IsConservative.continuousProcess D.logGrowthBounds.resolvent.onePointKernelSemigroup
          D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup z)) =
        (fun z => ENNReal.ofReal (onePointRealExtension q z)) z := by
    intro z
    rw [ofReal_onePointRealExtension_eq_onePointLiveExtension q]
    exact lintegral_pathResolvent_c0 D.logGrowthBounds.resolvent hreg mu G hG0 z
  have hdecomp := eq_killedResolvent_add_lintegralDiscountedExit
    D.logGrowthBounds.resolvent.onePointKernelSemigroup D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
    D.logGrowthBounds.resolvent.isFellerKernelSemigroup_onePointKernelSemigroup hreg.kolmogorovRegular
    hUopen (mu : ℝ) hlive hres (y : OnePoint (Vec d))
  let hP := dirRep_barrierData D x₀ hr mu G.continuous.measurable hG0 hGbd
  have hcrux := fieldExit_killedResolvent_eq_partResolvent D hP hy
  dsimp only at hcrux
  have hobs : ∀ z ∈ ((↑) : Vec d → OnePoint (Vec d)) '' B,
      PositiveC0ContractiveResolvent.onePointLiveExtension
          (fun w => ENNReal.ofReal (G w)) z =
        PositiveC0ContractiveResolvent.onePointLiveExtension
          (fun w => ENNReal.ofReal (hP.f w)) z := by
    rintro _ ⟨w, hw, rfl⟩
    rw [PositiveC0ContractiveResolvent.onePointLiveExtension_coe,
      PositiveC0ContractiveResolvent.onePointLiveExtension_coe]
    exact congrArg ENNReal.ofReal (Set.indicator_of_mem hw G).symm
  have hkilled := (killedResolvent_congr_of_eqOn _ _ _ _ (mu : ℝ) hobs (y : OnePoint (Vec d))).trans
    hcrux
  have hfin : lintegralDiscountedExit D.logGrowthBounds.resolvent.onePointKernelSemigroup
      D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
      (((↑) : Vec d → OnePoint (Vec d)) '' B) (mu : ℝ)
      (fun z => ENNReal.ofReal (onePointRealExtension q z)) (y : OnePoint (Vec d)) ≠ ⊤ := by
    refine lintegralDiscountedExit_ne_top D.logGrowthBounds.resolvent.onePointKernelSemigroup
      D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup mu.property.le
      (C := ENNReal.ofReal ‖D.logGrowthBounds.resolvent.toContractiveResolvent.operator mu G‖)
      ENNReal.ofReal_ne_top (fun z => ?_) _
    refine ENNReal.ofReal_le_ofReal ?_
    exact (le_abs_self _).trans (abs_onePointRealExtension_le (norm_nonneg _) hqbd z)
  have hnn : 0 ≤ hP.utilde y := D.analyticData.partC0Resolvent_nonneg (dirRep_ball x₀ hr) mu G
    G.continuous.measurable hG0 hGbd y
  have htoReal := congrArg ENNReal.toReal hdecomp
  rw [hkilled, ENNReal.toReal_add ENNReal.ofReal_ne_top hfin,
    ENNReal.toReal_ofReal hnn,
    toReal_lintegralDiscountedExit D.logGrowthBounds.resolvent.onePointKernelSemigroup
      D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup hUopen (mu : ℝ)
      (measurable_onePointRealExtension hqmeas)
      (onePointRealExtension_nonneg hq0),
    onePointRealExtension_coe, ENNReal.toReal_ofReal (hq0 y)] at htoReal
  exact htoReal


/-- The positive part of a `C₀` function. -/
def dirRep_posPart (G : C₀(Vec d, ℝ)) : C₀(Vec d, ℝ) :=
  ⟨⟨fun x => max (G x) 0, G.continuous.max continuous_const⟩, by
    simpa using G.zero_at_infty'.max (tendsto_const_nhds (x := (0 : ℝ)))⟩

omit [NeZero d] in
theorem dirRep_posPart_apply (G : C₀(Vec d, ℝ)) (x : Vec d) :
    dirRep_posPart G x = max (G x) 0 := rfl

omit [NeZero d] in
theorem dirRep_posPart_nonneg (G : C₀(Vec d, ℝ)) (x : Vec d) : 0 ≤ dirRep_posPart G x :=
  le_max_right _ _

omit [NeZero d] in
theorem dirRep_eq_posPart_sub (G : C₀(Vec d, ℝ)) :
    G = dirRep_posPart G - dirRep_posPart (-G) := by
  ext x
  simp only [ZeroAtInftyContinuousMap.sub_apply, dirRep_posPart_apply,
    ZeroAtInftyContinuousMap.neg_apply]
  rcases le_total (G x) 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith only [h])]; ring
  · rw [max_eq_left h, max_eq_right (by linarith only [h])]; ring


omit [NeZero d] in
/-- The bounded measurable datum of a `C₀` function. -/
theorem dirRep_c0_abs_le (G : C₀(Vec d, ℝ)) (z : Vec d) : |G z| ≤ ‖G‖ := by
  rw [← Real.norm_eq_abs, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact BoundedContinuousFunction.norm_coe_le_norm G.toBCF z

/-- **The exit decomposition at a positive shift on a ball, for a signed `C₀` datum.** -/
theorem dirRep_decomp_signed (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (mu : PositiveShift)
    (G : C₀(Vec d, ℝ)) {y : Vec d} (hy : y ∈ euclideanBall x₀ r) :
    let hreg := D.logGrowthBounds.processInput.toOnePointRegular
    let := hreg.metricSpace
    let := hreg.completeSpace
    D.logGrowthBounds.resolvent.toContractiveResolvent.operator mu G y =
      D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) mu G G.continuous.measurable
          (D := ‖G‖) (dirRep_c0_abs_le G) y +
        discountedExitAverage D.logGrowthBounds.resolvent.onePointKernelSemigroup
          D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
          (((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall x₀ r) (mu : ℝ)
          (onePointRealExtension
            (fun z => D.logGrowthBounds.resolvent.toContractiveResolvent.operator mu G z))
          (y : OnePoint (Vec d)) := by
  intro hreg hm hc
  have hV := dirRep_ball x₀ hr
  set Gp := dirRep_posPart G with hGp
  set Gn := dirRep_posPart (-G) with hGn
  have h1 := dirRep_decomp D x₀ hr mu Gp (dirRep_posPart_nonneg G) hy
  have h2 := dirRep_decomp D x₀ hr mu Gn (dirRep_posPart_nonneg (-G)) hy
  dsimp only at h1 h2
  have hGeq : G = Gp - Gn := dirRep_eq_posPart_sub G
  have hop : ∀ z, D.logGrowthBounds.resolvent.toContractiveResolvent.operator mu G z =
      D.logGrowthBounds.resolvent.toContractiveResolvent.operator mu Gp z -
        D.logGrowthBounds.resolvent.toContractiveResolvent.operator mu Gn z := fun z => by
    conv_lhs => rw [hGeq]
    rw [map_sub]; rfl
  have hpart : D.analyticData.partC0Resolvent hV mu G G.continuous.measurable
        (D := ‖G‖) (dirRep_c0_abs_le G) y =
      D.analyticData.partC0Resolvent hV mu Gp Gp.continuous.measurable
        (D := ‖Gp‖) (dirRep_c0_abs_le Gp) y -
      D.analyticData.partC0Resolvent hV mu Gn Gn.continuous.measurable
        (D := ‖Gn‖) (dirRep_c0_abs_le Gn) y := by
    have hcb : ∀ z, |(-1 : ℝ) * Gn z| ≤ |(-1 : ℝ)| * ‖Gn‖ := fun z => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (dirRep_c0_abs_le Gn z) (abs_nonneg _)
    have hsum : ∀ z, |Gp z + (-1 : ℝ) * Gn z| ≤ ‖Gp‖ + |(-1 : ℝ)| * ‖Gn‖ := fun z =>
      (abs_add_le _ _).trans (add_le_add (dirRep_c0_abs_le Gp z) (hcb z))
    have hmeas : Measurable fun z => Gp z + (-1 : ℝ) * Gn z :=
      Gp.continuous.measurable.add (Gn.continuous.measurable.const_smul (-1 : ℝ))
    have hlin : D.analyticData.partC0Resolvent hV mu (fun z => Gp z + (-1 : ℝ) * Gn z) hmeas hsum y =
        D.analyticData.partC0Resolvent hV mu Gp Gp.continuous.measurable
          (D := ‖Gp‖) (dirRep_c0_abs_le Gp) y +
        (-1 : ℝ) * D.analyticData.partC0Resolvent hV mu Gn Gn.continuous.measurable
          (D := ‖Gn‖) (dirRep_c0_abs_le Gn) y :=
      D.analyticData.partC0Resolvent_add_const_mul hV mu (-1 : ℝ)
        Gp.continuous.measurable Gn.continuous.measurable (dirRep_c0_abs_le Gp)
        (dirRep_c0_abs_le Gn) hmeas hsum y
    have hswap : D.analyticData.partC0Resolvent hV mu G G.continuous.measurable
        (D := ‖G‖) (dirRep_c0_abs_le G) y =
        D.analyticData.partC0Resolvent hV mu (fun z => Gp z + (-1 : ℝ) * Gn z) hmeas hsum y :=
      D.analyticData.partC0Resolvent_eq_of_eqOn hV mu G.continuous.measurable hmeas
      (dirRep_c0_abs_le G) hsum (fun z _ => by
        have := congrArg (fun H : C₀(Vec d, ℝ) => H z) hGeq
        simp only [ZeroAtInftyContinuousMap.sub_apply] at this
        show G z = Gp z + (-1 : ℝ) * Gn z
        linarith only [this]) y
    linarith only [hlin, hswap]
  have hdea : discountedExitAverage D.logGrowthBounds.resolvent.onePointKernelSemigroup
        D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall x₀ r) (mu : ℝ)
        (onePointRealExtension
          (fun z => D.logGrowthBounds.resolvent.toContractiveResolvent.operator mu G z))
        (y : OnePoint (Vec d)) =
      discountedExitAverage D.logGrowthBounds.resolvent.onePointKernelSemigroup
        D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall x₀ r) (mu : ℝ)
        (onePointRealExtension
          (fun z => D.logGrowthBounds.resolvent.toContractiveResolvent.operator mu Gp z))
        (y : OnePoint (Vec d)) -
      discountedExitAverage D.logGrowthBounds.resolvent.onePointKernelSemigroup
        D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall x₀ r) (mu : ℝ)
        (onePointRealExtension
          (fun z => D.logGrowthBounds.resolvent.toContractiveResolvent.operator mu Gn z))
        (y : OnePoint (Vec d)) := by
    have hUopen : IsOpen (((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall x₀ r) :=
      OnePoint.isOpen_image_coe.mpr hV.isOpen
    have hlin := discountedExitAverage_add_const_mul
      D.logGrowthBounds.resolvent.onePointKernelSemigroup
      D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup hUopen (mu : ℝ)
      mu.property.le
      (psi1 := onePointRealExtension
        (fun z => D.logGrowthBounds.resolvent.toContractiveResolvent.operator mu Gp z))
      (psi2 := onePointRealExtension
        (fun z => D.logGrowthBounds.resolvent.toContractiveResolvent.operator mu Gn z))
      (measurable_onePointRealExtension
        (D.logGrowthBounds.resolvent.toContractiveResolvent.operator mu Gp).continuous.measurable)
      (measurable_onePointRealExtension
        (D.logGrowthBounds.resolvent.toContractiveResolvent.operator mu Gn).continuous.measurable)
      (M1 := ‖D.logGrowthBounds.resolvent.toContractiveResolvent.operator mu Gp‖)
      (M2 := ‖D.logGrowthBounds.resolvent.toContractiveResolvent.operator mu Gn‖)
      (fun z => by
        rw [Real.norm_eq_abs]
        exact abs_onePointRealExtension_le (norm_nonneg _) (dirRep_c0_abs_le _) z)
      (fun z => by
        rw [Real.norm_eq_abs]
        exact abs_onePointRealExtension_le (norm_nonneg _) (dirRep_c0_abs_le _) z) (-1) (y : OnePoint (Vec d))
    have hfun : (onePointRealExtension
          (fun z => D.logGrowthBounds.resolvent.toContractiveResolvent.operator mu G z)) =
        fun z => onePointRealExtension
          (fun z => D.logGrowthBounds.resolvent.toContractiveResolvent.operator mu Gp z) z +
          (-1 : ℝ) * onePointRealExtension
            (fun z => D.logGrowthBounds.resolvent.toContractiveResolvent.operator mu Gn z) z := by
      funext z
      induction z using OnePoint.rec with
      | infty => simp
      | coe x => simp only [onePointRealExtension_coe, hop x]; ring
    rw [hfun, hlin]; ring
  rw [hop y, hpart, hdea]
  linarith only [h1, h2]



/-- The part resolvent of a bounded measurable datum of either sign is bounded uniformly in the
shift. -/
theorem dirRep_abs_resolvent_le (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    ∃ Bd : ℝ, 0 ≤ Bd ∧ ∀ (mu : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f) {M : ℝ}
      (hfM : ∀ y, |f y| ≤ M) (y : Vec d),
      |D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) mu f hf hfM y| ≤ M * Bd := by
  obtain ⟨Bd, hBd0, hBd⟩ := dirRep_resolvent_bound D x₀ hr
  refine ⟨Bd, hBd0, fun mu f hf M hfM y => ?_⟩
  have hsplit := dirRep_part_split D x₀ hr mu hf hfM y
  have h1 := hBd mu (dirRep_pos_measurable hf) (dirRep_abs_pos_le hfM) y
  have h2 := hBd mu (dirRep_neg_measurable hf) (dirRep_abs_neg_le hfM) y
  have h3 := D.analyticData.partC0Resolvent_nonneg (dirRep_ball x₀ hr) mu (dirRep_pos f)
    (dirRep_pos_measurable hf) (dirRep_pos_nonneg f) (dirRep_abs_pos_le hfM) y
  have h4 := D.analyticData.partC0Resolvent_nonneg (dirRep_ball x₀ hr) mu (dirRep_neg f)
    (dirRep_neg_measurable hf) (dirRep_neg_nonneg f) (dirRep_abs_neg_le hfM) y
  rw [hsplit, abs_le]
  constructor <;> linarith only [h1, h2, h3, h4]

end
end SuperdiffusionCLT.Section8
