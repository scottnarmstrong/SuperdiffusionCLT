/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.DirichletRepresentationB
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExitMeanValueIdentificationCarrier
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.StoppedDirichlet

/-!
# The vanishing-shift limit of the part resolvents and the occupation before exit

For a bounded nonnegative measurable datum `f`, the part resolvents of the ball at the shifts
`1 / (n + 1)` increase, differ by at most a multiple of the difference of the shifts, and so
converge uniformly to a continuous function `W` which vanishes off the ball.  By monotone
convergence of the killed resolvent of the compactified process, `W x` is the expected occupation
`E^x ∫₀^{T_B} f(X_s) ds` of the ball before the exit time, for every continuous-path law.  With
`f = 1` this is the expected exit time, finite and continuous in the starting point.

* `dirRep_resolvent_sub`, `dirRep_resolvent_antitone`: the resolvent identity with a bounded
  remainder, and monotonicity in the shift;
* `dirRep_limit`, `dirRep_limit_sandwich`, `dirRep_limit_continuous`: the limit and its uniform
  convergence;
* `dirRep_lintegral_limit`: the probabilistic identification;
* `dirRep_z`, `dirRep_z_cauchy`: the zero-trace Sobolev solutions of the shifted equations are
  Cauchy in `H¹₀`;
* `dirRep_z_tendsto_L2`: their scalar parts converge in `L²` to the class of the limit;
* `dirRep_h10_solution`, `dirRep_signed`: the limit is an `H¹₀` weak solution, for data of either
  sign, and is the limit as the real shift decreases to zero (`dirRep_tendsto_resolventAt`);
* `dirRep_expectedExitTime_eq`: the expected exit time of the compactified process is the torsion
  function; `dirRep_torsion`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization MeasureTheory Set Filter Topology
open SuperdiffusionCLT.Section8.DivergenceForm
open SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.StoppedDirichlet
open MarkovProcess MarkovProcess.Semigroup MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal ZeroAtInfty RealInnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d] {nu : ℝ} {k : Vec d → Mat d} (D : FieldInputData d nu k)

/-- The shifts `1 / (n + 1)`. -/
def dirRep_shift (n : ℕ) : PositiveShift := ⟨((n : ℝ) + 1)⁻¹, Set.mem_Ioi.mpr (by positivity)⟩

theorem dirRep_shift_coe (n : ℕ) : ((dirRep_shift n : PositiveShift) : ℝ) = ((n : ℝ) + 1)⁻¹ := rfl

/-- **The resolvent identity with a bounded remainder.**  For shifts `mu`, `nu` the difference of
the part resolvents is `(nu - mu)` times a number in `[0, M Bd²]`. -/
theorem dirRep_resolvent_sub (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    ∃ Bd : ℝ, 0 ≤ Bd ∧ ∀ (mu nu : PositiveShift) {f : Vec d → ℝ} (hf : Measurable f)
      {M : ℝ} (hfM : ∀ y, |f y| ≤ M), (∀ y, 0 ≤ f y) → ∀ (y : Vec d),
      ∃ c : ℝ, 0 ≤ c ∧ c ≤ M * Bd * Bd ∧
        D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) mu f hf hfM y -
          D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) nu f hf hfM y =
          ((nu : ℝ) - (mu : ℝ)) * c := by
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
  refine ⟨A.partC0Resolvent hV nu g hgm hgC y, A.partC0Resolvent_nonneg hV nu g hgm hg0 hgC y,
    hBd nu hgm hgC y, ?_⟩
  linarith only [hid]

/-- The part resolvent of a nonnegative datum increases as the shift decreases. -/
theorem dirRep_resolvent_antitone (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {mu lam : PositiveShift}
    (hmn : (mu : ℝ) ≤ (lam : ℝ)) {f : Vec d → ℝ} (hf : Measurable f)
    {M : ℝ} (hfM : ∀ y, |f y| ≤ M) (hf0 : ∀ y, 0 ≤ f y) (y : Vec d) :
    D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) lam f hf hfM y ≤
      D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) mu f hf hfM y := by
  obtain ⟨Bd, -, h⟩ := dirRep_resolvent_sub D x₀ hr
  obtain ⟨c, hc0, -, hc⟩ := h mu lam hf hfM hf0 y
  have : 0 ≤ ((lam : ℝ) - (mu : ℝ)) * c := mul_nonneg (by linarith only [hmn]) hc0
  linarith only [hc, this]


/-- The vanishing-shift limit of the part resolvents of `f`: their supremum over the shifts
`1 / (n + 1)`. -/
def dirRep_limit (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {f : Vec d → ℝ} (hf : Measurable f) {M : ℝ}
    (hfM : ∀ y, |f y| ≤ M) : Vec d → ℝ :=
  fun y => ⨆ n : ℕ, D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) (dirRep_shift n) f hf hfM y

/-- **Uniform convergence of the part resolvents as the shift tends to zero.**  There is a
constant `C` such that for every bounded nonnegative measurable datum `f`, the limit `W` of
the part resolvents satisfies `R_n f ≤ W ≤ R_n f + M C / (n + 1)` everywhere. -/
theorem dirRep_limit_sandwich (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {f : Vec d → ℝ} (hf : Measurable f) {M : ℝ} (hfM : ∀ y, |f y| ≤ M),
      (∀ y, 0 ≤ f y) → ∀ (n : ℕ) (y : Vec d),
      D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) (dirRep_shift n) f hf hfM y ≤
          dirRep_limit D x₀ hr hf hfM y ∧
        dirRep_limit D x₀ hr hf hfM y ≤
          D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) (dirRep_shift n) f hf hfM y +
            M * C * ((n : ℝ) + 1)⁻¹ := by
  obtain ⟨Bd, hBd0, hsub⟩ := dirRep_resolvent_sub D x₀ hr
  obtain ⟨Bd', hBd0', hBd'⟩ := dirRep_resolvent_bound D x₀ hr
  refine ⟨Bd * Bd, mul_nonneg hBd0 hBd0, fun {f} hf {M} hfM hf0 n y => ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hfM 0)
  set R : ℕ → ℝ := fun n => D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) (dirRep_shift n)
    f hf hfM y with hR
  have hbdd : BddAbove (Set.range R) := ⟨M * Bd', by
    rintro _ ⟨m, rfl⟩
    exact hBd' (dirRep_shift m) hf hfM y⟩
  refine ⟨le_ciSup hbdd n, ?_⟩
  refine ciSup_le fun m => ?_
  by_cases hmn : n ≤ m
  · obtain ⟨c, hc0, hc1, hc⟩ := hsub (dirRep_shift m) (dirRep_shift n) hf hfM hf0 y
    have hshift : ((dirRep_shift n : PositiveShift) : ℝ) - ((dirRep_shift m : PositiveShift) : ℝ) ≤
        ((n : ℝ) + 1)⁻¹ := by
      have : 0 ≤ ((dirRep_shift m : PositiveShift) : ℝ) := (dirRep_shift m).property.le
      linarith only [this, show ((dirRep_shift n : PositiveShift) : ℝ) = ((n : ℝ) + 1)⁻¹ from rfl]
    have hs0 : 0 ≤ ((dirRep_shift n : PositiveShift) : ℝ) - ((dirRep_shift m : PositiveShift) : ℝ) := by
      have : ((m : ℝ) + 1)⁻¹ ≤ ((n : ℝ) + 1)⁻¹ :=
        inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
      show 0 ≤ ((n : ℝ) + 1)⁻¹ - ((m : ℝ) + 1)⁻¹
      linarith only [this]
    have h1 : (((dirRep_shift n : PositiveShift) : ℝ) - ((dirRep_shift m : PositiveShift) : ℝ)) * c ≤
        ((n : ℝ) + 1)⁻¹ * (M * Bd * Bd) :=
      mul_le_mul hshift hc1 hc0 (by positivity)
    have : R m ≤ R n + ((n : ℝ) + 1)⁻¹ * (M * Bd * Bd) := by
      simp only [hR]
      linarith only [hc, h1]
    calc R m ≤ R n + ((n : ℝ) + 1)⁻¹ * (M * Bd * Bd) := this
      _ = R n + M * (Bd * Bd) * ((n : ℝ) + 1)⁻¹ := by ring
  · push Not at hmn
    have hmn' : m ≤ n := hmn.le
    have hanti := dirRep_resolvent_antitone D x₀ hr
      (mu := dirRep_shift n) (lam := dirRep_shift m)
      (by
        show ((n : ℝ) + 1)⁻¹ ≤ ((m : ℝ) + 1)⁻¹
        exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn' 1)) hf hfM hf0 y
    have hpos : 0 ≤ M * (Bd * Bd) * ((n : ℝ) + 1)⁻¹ := by positivity
    linarith only [hanti, hpos]


theorem dirRep_limit_off (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {f : Vec d → ℝ} (hf : Measurable f)
    {M : ℝ} (hfM : ∀ y, |f y| ≤ M) {y : Vec d} (hy : y ∉ euclideanBall x₀ r) :
    dirRep_limit D x₀ hr hf hfM y = 0 := by
  unfold dirRep_limit
  simp only [D.analyticData.partC0Resolvent_of_notMem (dirRep_ball x₀ hr) _ f hf hfM hy]
  exact ciSup_const

theorem dirRep_limit_nonneg (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {f : Vec d → ℝ}
    (hf : Measurable f) {M : ℝ} (hfM : ∀ y, |f y| ≤ M) (hf0 : ∀ y, 0 ≤ f y) (y : Vec d) :
    0 ≤ dirRep_limit D x₀ hr hf hfM y := by
  obtain ⟨C, hC0, hC⟩ := dirRep_limit_sandwich D x₀ hr
  exact (D.analyticData.partC0Resolvent_nonneg (dirRep_ball x₀ hr) (dirRep_shift 0) f hf hf0 hfM
    y).trans (hC hf hfM hf0 0 y).1

/-- **The limit of the part resolvents is continuous on the whole space.** -/
theorem dirRep_limit_continuous (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {f : Vec d → ℝ}
    (hf : Measurable f) {M : ℝ} (hfM : ∀ y, |f y| ≤ M) (hf0 : ∀ y, 0 ≤ f y) :
    Continuous (dirRep_limit D x₀ hr hf hfM) := by
  obtain ⟨C, hC0, hC⟩ := dirRep_limit_sandwich D x₀ hr
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hfM 0)
  have hunif : TendstoUniformly (fun n : ℕ => D.analyticData.partC0Resolvent (dirRep_ball x₀ hr)
      (dirRep_shift n) f hf hfM) (dirRep_limit D x₀ hr hf hfM) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (M * C / ε)
    filter_upwards [eventually_ge_atTop N] with n hn y
    obtain ⟨h1, h2⟩ := hC hf hfM hf0 n y
    rw [Real.dist_eq, abs_of_nonneg (by linarith only [h1])]
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hlt : M * C / ε < (n : ℝ) + 1 := by linarith only [hN, hNn]
    have hlt2 : M * C * ((n : ℝ) + 1)⁻¹ < ε := by
      rw [← div_eq_mul_inv, div_lt_iff₀ hpos]
      rw [div_lt_iff₀ hε] at hlt
      linarith only [hlt]
    linarith only [h2, hlt2]
  exact hunif.continuous (Eventually.of_forall fun n =>
    dirRep_resolvent_continuous D x₀ hr (dirRep_shift n) hf hf0 hfM).frequently


theorem dirRep_iSup_ofReal_eq (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {f : Vec d → ℝ}
    (hf : Measurable f) {M : ℝ} (hfM : ∀ y, |f y| ≤ M) (hf0 : ∀ y, 0 ≤ f y) (y : Vec d) :
    ⨆ n : ℕ, ENNReal.ofReal (D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) (dirRep_shift n)
        f hf hfM y) = ENNReal.ofReal (dirRep_limit D x₀ hr hf hfM y) := by
  obtain ⟨Bd', hBd0', hBd'⟩ := dirRep_resolvent_bound D x₀ hr
  set R : ℕ → ℝ := fun n => D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) (dirRep_shift n)
    f hf hfM y with hR
  have hmono : Monotone R := monotone_nat_of_le_succ fun n =>
    dirRep_resolvent_antitone D x₀ hr (mu := dirRep_shift (n + 1)) (lam := dirRep_shift n)
      (by
        show (((n + 1 : ℕ) : ℝ) + 1)⁻¹ ≤ ((n : ℝ) + 1)⁻¹
        exact inv_anti₀ (by positivity) (by push_cast; linarith only)) hf hfM hf0 y
  have hbdd : BddAbove (Set.range R) := ⟨M * Bd', by
    rintro _ ⟨m, rfl⟩
    exact hBd' (dirRep_shift m) hf hfM y⟩
  have h1 : Tendsto R atTop (𝓝 (⨆ n, R n)) := tendsto_atTop_ciSup hmono hbdd
  have h2 : Tendsto (fun n => ENNReal.ofReal (R n)) atTop (𝓝 (ENNReal.ofReal (⨆ n, R n))) :=
    ENNReal.tendsto_ofReal h1
  have hmono' : Monotone fun n => ENNReal.ofReal (R n) := fun a b hab =>
    ENNReal.ofReal_le_ofReal (hmono hab)
  exact tendsto_nhds_unique (tendsto_atTop_iSup hmono') h2

open SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.LiveRestriction in
/-- **The expected occupation of the ball before the exit time.**  For every continuous-path law
`Q` of the kernel semigroup of the marginal field, a bounded nonnegative measurable observable
`f` and a starting point `x` in the ball,
`E^x ∫₀^{T_B} f(X_s) ds` is the value at `x` of the vanishing-shift limit `W` of the part
resolvents.  With `f = 1` this is the expected exit time. -/
theorem dirRep_lintegral_limit (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {f : Vec d → ℝ}
    (hf : Measurable f) {M : ℝ} (hfM : ∀ y, |f y| ≤ M) (hf0 : ∀ y, 0 ≤ f y)
    {Q : Vec d → Measure (ContinuousPath (Vec d))}
    (hQ : IsContinuousPathLaw D.logGrowthBounds.resolvent.kernelSemigroup Q)
    {x : Vec d} (hx : x ∈ euclideanBall x₀ r) :
    ∫⁻ path, (∫⁻ t in Set.Ioi (0 : ℝ), {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) <
            ContinuousPath.exitTime (euclideanBall x₀ r) path}.indicator
          (fun t => ENNReal.ofReal (f (path (Real.toNNReal t)))) t) ∂(Q x) =
      ENNReal.ofReal (dirRep_limit D x₀ hr hf hfM x) := by
  have htr := dirRep_transfer D x₀ hr 0 hf hQ x
  dsimp only at htr
  let := D.logGrowthBounds.processInput.toOnePointRegular.metricSpace
  let := D.logGrowthBounds.processInput.toOnePointRegular.completeSpace
  have hV := dirRep_ball x₀ hr
  have hmeasF : Measurable (PositiveC0ContractiveResolvent.onePointLiveExtension
      (fun y => ENNReal.ofReal ((euclideanBall x₀ r).indicator f y))) :=
    PositiveC0ContractiveResolvent.measurable_onePointLiveExtension
      (ENNReal.measurable_ofReal.comp (hf.indicator hV.isOpen.measurableSet))
  have hiSup := IsConservative.killedResolvent_zero_eq_iSup
    D.logGrowthBounds.resolvent.onePointKernelSemigroup
    D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
    (((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall x₀ r)
    (OnePoint.isOpen_image_coe.mpr hV.isOpen) hmeasF (x : OnePoint (Vec d))
  have hterm : ∀ n : ℕ, IsConservative.killedResolvent
      D.logGrowthBounds.resolvent.onePointKernelSemigroup
      D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
      (((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall x₀ r)
      (OnePoint.isOpen_image_coe.mpr hV.isOpen) ((n : ℝ) + 1)⁻¹
      (PositiveC0ContractiveResolvent.onePointLiveExtension
          (fun y => ENNReal.ofReal ((euclideanBall x₀ r).indicator f y))) (x : OnePoint (Vec d)) =
      ENNReal.ofReal (D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) (dirRep_shift n)
        f hf hfM x) := by
    intro n
    have h1 := dirRep_transfer D x₀ hr ((n : ℝ) + 1)⁻¹ hf hQ x
    have h2 := dirRep_lintegral_resolvent D x₀ hr (dirRep_shift n) hf hf0 hfM hQ hx
    dsimp only at h1
    exact h1.trans h2
  simp only [hterm] at hiSup
  rw [dirRep_iSup_ofReal_eq D x₀ hr hf hfM hf0 x] at hiSup
  rw [← hiSup]
  refine Eq.trans ?_ htr.symm
  refine lintegral_congr fun path => ?_
  simp only [neg_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one, one_mul]

/-- The zero-trace Sobolev solution of the shifted equation at the `n`-th shift. -/
def dirRep_z (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {f : Vec d → ℝ} (hf : Measurable f) {M : ℝ}
    (hfM : ∀ y, |f y| ≤ M) (n : ℕ) : ZeroTraceSobolev (euclideanBall x₀ r) :=
  alphaShiftedSolution D.analyticData.a
    (show (0 : ℝ) < ((dirRep_shift n : PositiveShift) : ℝ) from (dirRep_shift n).property)
    D.analyticData.hnu (partEllipticity D.analyticData (dirRep_ball x₀ hr))
    (partDatumL2 (dirRep_ball x₀ hr) hf hfM)

theorem dirRep_z_toL2_ae (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {f : Vec d → ℝ} (hf : Measurable f)
    {M : ℝ} (hfM : ∀ y, |f y| ≤ M) (n : ℕ) :
    ⇑(ZeroTraceSobolev.toL2 (dirRep_z D x₀ hr hf hfM n)) =ᵐ[volumeMeasureOn (euclideanBall x₀ r)]
      D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) (dirRep_shift n) f hf hfM := by
  filter_upwards [D.analyticData.partC0Resolvent_ae (dirRep_ball x₀ hr) (dirRep_shift n) f hf hfM]
    with y hy
  exact hy.symm

/-- The weak equation of `dirRep_z` with the shift written out. -/
theorem dirRep_z_eq (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {f : Vec d → ℝ} (hf : Measurable f)
    {M : ℝ} (hfM : ∀ y, |f y| ≤ M) (n : ℕ) (v : ZeroTraceSobolev (euclideanBall x₀ r)) :
    ((dirRep_shift n : PositiveShift) : ℝ) *
        ⟪ZeroTraceSobolev.toL2 (dirRep_z D x₀ hr hf hfM n), ZeroTraceSobolev.toL2 v⟫ +
      shiftedBilin (partEllipticity D.analyticData (dirRep_ball x₀ hr)) 0
        (dirRep_z D x₀ hr hf hfM n) v =
      ⟪partDatumL2 (dirRep_ball x₀ hr) hf hfM, ZeroTraceSobolev.toL2 v⟫ := by
  have h := alphaShiftedSolution_isAlphaShiftedWeakSolution D.analyticData.a
    (show (0 : ℝ) < ((dirRep_shift n : PositiveShift) : ℝ) from (dirRep_shift n).property)
    D.analyticData.hnu (partEllipticity D.analyticData (dirRep_ball x₀ hr))
    (partDatumL2 (dirRep_ball x₀ hr) hf hfM) v
  rw [← coefficientPairing_gradient_eq_shiftedBilin]
  exact h


/-- The scalar parts of the shifted solutions are bounded in `L²`, and Lipschitz in the shift. -/
theorem dirRep_z_L2_bounds (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {f : Vec d → ℝ} (hf : Measurable f) {M : ℝ} (hfM : ∀ y, |f y| ≤ M),
      (∀ y, 0 ≤ f y) → ∀ n m : ℕ,
      ‖ZeroTraceSobolev.toL2 (dirRep_z D x₀ hr hf hfM n)‖ ≤ K * M ∧
      ‖ZeroTraceSobolev.toL2 (dirRep_z D x₀ hr hf hfM n) -
          ZeroTraceSobolev.toL2 (dirRep_z D x₀ hr hf hfM m)‖ ≤
        K * M * |((dirRep_shift n : PositiveShift) : ℝ) - ((dirRep_shift m : PositiveShift) : ℝ)| := by
  obtain ⟨Bd, hBd0, hBd⟩ := dirRep_resolvent_bound D x₀ hr
  obtain ⟨Bd2, hBd20, hBd2⟩ := dirRep_resolvent_diff_le D x₀ hr
  have hV := dirRep_ball x₀ hr
  have hfac := scalarL2Factor_nonneg (euclideanBall x₀ r)
  refine ⟨scalarL2Factor (euclideanBall x₀ r) * (Bd + Bd2 * Bd2),
    by positivity, fun {f} hf {M} hfM hf0 n m => ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hfM 0)
  constructor
  · refine (norm_scalarL2_le_of_ae_bound hV _ (mul_nonneg hM0 hBd0) ?_).trans ?_
    · filter_upwards [dirRep_z_toL2_ae D x₀ hr hf hfM n] with y hy
      rw [hy, abs_of_nonneg (D.analyticData.partC0Resolvent_nonneg _ _ f hf hf0 hfM y)]
      exact hBd _ hf hfM y
    · have : 0 ≤ M * (Bd2 * Bd2) := by positivity
      nlinarith only [hfac, mul_nonneg hM0 hBd0, this]
  · have hC : 0 ≤ |((dirRep_shift n : PositiveShift) : ℝ) - ((dirRep_shift m : PositiveShift) : ℝ)| *
        (M * Bd2 * Bd2) := by positivity
    refine (norm_scalarL2_le_of_ae_bound hV _ hC ?_).trans ?_
    · filter_upwards [dirRep_z_toL2_ae D x₀ hr hf hfM n, dirRep_z_toL2_ae D x₀ hr hf hfM m,
        Lp.coeFn_sub (ZeroTraceSobolev.toL2 (dirRep_z D x₀ hr hf hfM n))
          (ZeroTraceSobolev.toL2 (dirRep_z D x₀ hr hf hfM m))] with y h1 h2 h3
      rw [h3, Pi.sub_apply, h1, h2]
      exact (hBd2 (dirRep_shift n) (dirRep_shift m) hf hfM hf0 y).trans_eq (by rw [abs_sub_comm])
    · have h4 : 0 ≤ |((dirRep_shift n : PositiveShift) : ℝ) - ((dirRep_shift m : PositiveShift) : ℝ)| := abs_nonneg _
      nlinarith only [hfac, mul_nonneg h4 (mul_nonneg hM0 (mul_nonneg hBd20 hBd20)), mul_nonneg h4 (mul_nonneg hM0 hBd0), hC]


/-- **The energy of a difference of shifted solutions.**  The gradient energy of
`z_n - z_m` is controlled by the shifts, the `L²` bound and the `L²` size of the difference. -/
theorem dirRep_z_grad_le (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {f : Vec d → ℝ} (hf : Measurable f)
    {M : ℝ} (hfM : ∀ y, |f y| ≤ M) {Kb : ℝ} (n m : ℕ)
    (hn : ‖ZeroTraceSobolev.toL2 (dirRep_z D x₀ hr hf hfM n)‖ ≤ Kb)
    (hm : ‖ZeroTraceSobolev.toL2 (dirRep_z D x₀ hr hf hfM m)‖ ≤ Kb) :
    D.analyticData.nu *
        ‖ZeroTraceSobolev.gradient (dirRep_z D x₀ hr hf hfM n - dirRep_z D x₀ hr hf hfM m)‖ ^ 2 ≤
      (((dirRep_shift n : PositiveShift) : ℝ) + ((dirRep_shift m : PositiveShift) : ℝ)) * Kb *
        ‖ZeroTraceSobolev.toL2 (dirRep_z D x₀ hr hf hfM n) -
          ZeroTraceSobolev.toL2 (dirRep_z D x₀ hr hf hfM m)‖ := by
  set A := D.analyticData with hA
  have hEll := partEllipticity A (dirRep_ball x₀ hr)
  set zn := dirRep_z D x₀ hr hf hfM n with hzn
  set zm := dirRep_z D x₀ hr hf hfM m with hzm
  set e := zn - zm with he
  have hTe : ZeroTraceSobolev.toL2 e = ZeroTraceSobolev.toL2 zn - ZeroTraceSobolev.toL2 zm :=
    map_sub _ _ _
  have h1 := dirRep_z_eq D x₀ hr hf hfM n e
  have h2 := dirRep_z_eq D x₀ hr hf hfM m e
  have hB : shiftedBilin hEll 0 e e = shiftedBilin hEll 0 zn e - shiftedBilin hEll 0 zm e := by
    have hsub : shiftedBilin hEll 0 e = shiftedBilin hEll 0 zn - shiftedBilin hEll 0 zm :=
      map_sub _ _ _
    rw [hsub]; rfl
  have hcoer := mul_norm_gradient_sq_le_coefficientPairing hEll e
  rw [coefficientPairing_gradient_eq_shiftedBilin hEll e e] at hcoer
  set mn : ℝ := ((dirRep_shift n : PositiveShift) : ℝ) with hmn
  set mm : ℝ := ((dirRep_shift m : PositiveShift) : ℝ) with hmm
  have hmn0 : 0 ≤ mn := (dirRep_shift n).property.le
  have hmm0 : 0 ≤ mm := (dirRep_shift m).property.le
  have hrew : shiftedBilin hEll 0 e e = mm * ⟪ZeroTraceSobolev.toL2 zm, ZeroTraceSobolev.toL2 e⟫ -
      mn * ⟪ZeroTraceSobolev.toL2 zn, ZeroTraceSobolev.toL2 e⟫ := by
    rw [hB]; linarith only [h1, h2]
  have hi1 : |⟪ZeroTraceSobolev.toL2 zn, ZeroTraceSobolev.toL2 e⟫| ≤
      Kb * ‖ZeroTraceSobolev.toL2 e‖ := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul_of_nonneg_right hn (norm_nonneg _)
  have hi2 : |⟪ZeroTraceSobolev.toL2 zm, ZeroTraceSobolev.toL2 e⟫| ≤
      Kb * ‖ZeroTraceSobolev.toL2 e‖ := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul_of_nonneg_right hm (norm_nonneg _)
  have hb1 : mn * ⟪ZeroTraceSobolev.toL2 zn, ZeroTraceSobolev.toL2 e⟫ ≤
      mn * (Kb * ‖ZeroTraceSobolev.toL2 e‖) :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans hi1) hmn0
  have hb2 : mm * ⟪ZeroTraceSobolev.toL2 zm, ZeroTraceSobolev.toL2 e⟫ ≤
      mm * (Kb * ‖ZeroTraceSobolev.toL2 e‖) :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans hi2) hmm0
  have hb3 : -(mn * ⟪ZeroTraceSobolev.toL2 zn, ZeroTraceSobolev.toL2 e⟫) ≤
      mn * (Kb * ‖ZeroTraceSobolev.toL2 e‖) := by
    have := mul_le_mul_of_nonneg_left (neg_le_abs _ |>.trans hi1) hmn0
    linarith only [this]
  have key : A.nu * ‖ZeroTraceSobolev.gradient e‖ ^ 2 ≤
      (mn + mm) * Kb * ‖ZeroTraceSobolev.toL2 e‖ := by
    linarith only [hcoer, hrew, hb2, hb3]
  rw [hTe] at key
  exact key


/-- **The shifted solutions are Cauchy in `H¹₀`.** -/
theorem dirRep_z_cauchy (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {f : Vec d → ℝ} (hf : Measurable f)
    {M : ℝ} (hfM : ∀ y, |f y| ≤ M) (hf0 : ∀ y, 0 ≤ f y) :
    CauchySeq (dirRep_z D x₀ hr hf hfM) := by
  obtain ⟨K, hK0, hK⟩ := dirRep_z_L2_bounds D x₀ hr
  set A := D.analyticData with hA
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hfM 0)
  have hnu := A.hnu
  set c : ℝ := (K * M) ^ 2 * (1 + 2 / A.nu) with hc
  have hc0 : 0 ≤ c := by positivity
  refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => Real.sqrt c * (1 / ((N : ℝ) + 1))) ?_ ?_
  · intro n m N hn hm
    set s : ℝ := 1 / ((N : ℝ) + 1) with hs
    have hs0 : 0 < s := by positivity
    have hsh : ∀ j : ℕ, N ≤ j → ((dirRep_shift j : PositiveShift) : ℝ) ≤ s := fun j hj => by
      show ((j : ℝ) + 1)⁻¹ ≤ 1 / ((N : ℝ) + 1)
      rw [one_div]
      exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hj 1)
    have hshp : ∀ j : ℕ, 0 ≤ ((dirRep_shift j : PositiveShift) : ℝ) := fun j =>
      (dirRep_shift j).property.le
    have hdelta : |((dirRep_shift n : PositiveShift) : ℝ) - ((dirRep_shift m : PositiveShift) : ℝ)| ≤ s := by
      rw [abs_le]
      constructor <;> linarith only [hsh n hn, hsh m hm, hshp n, hshp m]
    obtain ⟨hKn, -⟩ := hK hf hfM hf0 n m
    obtain ⟨hKm, hKd⟩ := hK hf hfM hf0 m n
    obtain ⟨-, hKd'⟩ := hK hf hfM hf0 n m
    have hgrad := dirRep_z_grad_le D x₀ hr hf hfM n m hKn hKm
    have hKM : 0 ≤ K * M := mul_nonneg hK0 hM0
    have hTe : ‖ZeroTraceSobolev.toL2 (dirRep_z D x₀ hr hf hfM n) -
        ZeroTraceSobolev.toL2 (dirRep_z D x₀ hr hf hfM m)‖ ≤ K * M * s :=
      hKd'.trans (mul_le_mul_of_nonneg_left hdelta hKM)
    have hTe0 := norm_nonneg (ZeroTraceSobolev.toL2 (dirRep_z D x₀ hr hf hfM n) -
        ZeroTraceSobolev.toL2 (dirRep_z D x₀ hr hf hfM m))
    have hsum : ((dirRep_shift n : PositiveShift) : ℝ) + ((dirRep_shift m : PositiveShift) : ℝ) ≤ 2 * s := by
      linarith only [hsh n hn, hsh m hm]
    have hg1 : A.nu * ‖ZeroTraceSobolev.gradient (dirRep_z D x₀ hr hf hfM n - dirRep_z D x₀ hr hf hfM m)‖ ^ 2 ≤
        (2 * s) * (K * M) * (K * M * s) := by
      refine hgrad.trans ?_
      refine mul_le_mul (mul_le_mul_of_nonneg_right hsum hKM) hTe hTe0 (by positivity)
    have hnorm := ZeroTraceSobolev.norm_sq_eq (dirRep_z D x₀ hr hf hfM n - dirRep_z D x₀ hr hf hfM m)
    rw [map_sub] at hnorm
    have hsq : ‖dirRep_z D x₀ hr hf hfM n - dirRep_z D x₀ hr hf hfM m‖ ^ 2 ≤ c * s ^ 2 := by
      rw [hnorm]
      have h1 : ‖ZeroTraceSobolev.toL2 (dirRep_z D x₀ hr hf hfM n) -
          ZeroTraceSobolev.toL2 (dirRep_z D x₀ hr hf hfM m)‖ ^ 2 ≤ (K * M * s) ^ 2 :=
        pow_le_pow_left₀ hTe0 hTe 2
      have h2 : ‖ZeroTraceSobolev.gradient (dirRep_z D x₀ hr hf hfM n - dirRep_z D x₀ hr hf hfM m)‖ ^ 2 ≤
          (2 * s) * (K * M) * (K * M * s) / A.nu := by
        rw [le_div_iff₀ hnu]; linarith only [hg1]
      have h3 : (K * M * s) ^ 2 + (2 * s) * (K * M) * (K * M * s) / A.nu = c * s ^ 2 := by
        rw [hc]; field_simp
      linarith only [h1, h2, h3]
    rw [dist_eq_norm]
    have hle : ‖dirRep_z D x₀ hr hf hfM n - dirRep_z D x₀ hr hf hfM m‖ ≤ Real.sqrt (c * s ^ 2) :=
      Real.le_sqrt_of_sq_le hsq
    rw [Real.sqrt_mul hc0, Real.sqrt_sq hs0.le] at hle
    exact hle
  · have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.sqrt c)
    simpa using this


theorem dirRep_limit_bound (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    ∃ Bd : ℝ, 0 ≤ Bd ∧ ∀ {f : Vec d → ℝ} (hf : Measurable f) {M : ℝ} (hfM : ∀ y, |f y| ≤ M),
      (∀ y, 0 ≤ f y) → ∀ y, |dirRep_limit D x₀ hr hf hfM y| ≤ M * Bd := by
  obtain ⟨Bd, hBd0, hBd⟩ := dirRep_resolvent_bound D x₀ hr
  refine ⟨Bd, hBd0, fun {f} hf {M} hfM hf0 y => ?_⟩
  have h0 := dirRep_limit_nonneg D x₀ hr hf hfM hf0 y
  rw [abs_of_nonneg h0]
  exact ciSup_le fun n => hBd (dirRep_shift n) hf hfM y

/-- The scalar parts of the shifted solutions converge in `L²` to the class of the limit. -/
theorem dirRep_z_tendsto_L2 (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {f : Vec d → ℝ}
    (hf : Measurable f) {M : ℝ} (hfM : ∀ y, |f y| ≤ M) (hf0 : ∀ y, 0 ≤ f y)
    {B : ℝ} (hB : ∀ y, |dirRep_limit D x₀ hr hf hfM y| ≤ B) :
    Tendsto (fun n => ZeroTraceSobolev.toL2 (dirRep_z D x₀ hr hf hfM n)) atTop
      (𝓝 (boundedMeasurableToScalarL2 (dirRep_ball x₀ hr)
        ((dirRep_limit_continuous D x₀ hr hf hfM hf0).measurable.comp measurable_subtype_coe)
        (fun y => hB y))) := by
  obtain ⟨C, hC0, hC⟩ := dirRep_limit_sandwich D x₀ hr
  have hV := dirRep_ball x₀ hr
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hfM 0)
  have hfac := scalarL2Factor_nonneg (euclideanBall x₀ r)
  have hnorm : ∀ n : ℕ, ‖ZeroTraceSobolev.toL2 (dirRep_z D x₀ hr hf hfM n) -
      boundedMeasurableToScalarL2 hV
        ((dirRep_limit_continuous D x₀ hr hf hfM hf0).measurable.comp measurable_subtype_coe)
        (fun y => hB y)‖ ≤ scalarL2Factor (euclideanBall x₀ r) * (M * C * ((n : ℝ) + 1)⁻¹) := by
    intro n
    refine norm_scalarL2_le_of_ae_bound hV _ (by positivity) ?_
    filter_upwards [dirRep_z_toL2_ae D x₀ hr hf hfM n,
      boundedMeasurableToScalarL2_coeFn hV
        ((dirRep_limit_continuous D x₀ hr hf hfM hf0).measurable.comp measurable_subtype_coe)
        (fun y => hB y),
      Lp.coeFn_sub (ZeroTraceSobolev.toL2 (dirRep_z D x₀ hr hf hfM n))
        (boundedMeasurableToScalarL2 hV
          ((dirRep_limit_continuous D x₀ hr hf hfM hf0).measurable.comp measurable_subtype_coe)
          (fun y => hB y)),
      ae_restrict_mem hV.isOpen.measurableSet] with y h1 h2 h3 hy
    rw [h3, Pi.sub_apply, h1, h2, domainExtension_of_mem hy]
    obtain ⟨a1, a2⟩ := hC hf hfM hf0 n y
    change |_ - dirRep_limit D x₀ hr hf hfM y| ≤ _
    rw [abs_sub_comm, abs_of_nonneg (by linarith only [a1])]
    linarith only [a2]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) hnorm ?_
  have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
    (scalarL2Factor (euclideanBall x₀ r) * (M * C))
  simpa [one_div, mul_assoc] using this



/-- The part resolvent as a function of a real shift (zero for nonpositive shifts). -/
def dirRep_resolventAt (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {f : Vec d → ℝ} (hf : Measurable f)
    {M : ℝ} (hfM : ∀ y, |f y| ≤ M) (lam : ℝ) (y : Vec d) : ℝ :=
  if h : 0 < lam then
    D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) ⟨lam, Set.mem_Ioi.mpr h⟩ f hf hfM y
  else 0

/-- **The part resolvent converges to the limit as the real shift decreases to zero.** -/
theorem dirRep_tendsto_resolventAt (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {f : Vec d → ℝ}
    (hf : Measurable f) {M : ℝ} (hfM : ∀ y, |f y| ≤ M) (hf0 : ∀ y, 0 ≤ f y) (y : Vec d) :
    Tendsto (fun lam : ℝ => dirRep_resolventAt D x₀ hr hf hfM lam y) (𝓝[>] (0 : ℝ))
      (𝓝 (dirRep_limit D x₀ hr hf hfM y)) := by
  obtain ⟨C, hC0, hC⟩ := dirRep_limit_sandwich D x₀ hr
  obtain ⟨Bd, hBd0, hBd⟩ := dirRep_resolvent_diff_le D x₀ hr
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hfM 0)
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set K1 : ℝ := M * C with hK1
  set K2 : ℝ := M * Bd * Bd with hK2
  have hK1p : 0 ≤ K1 := by positivity
  have hK2p : 0 ≤ K2 := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt ((K1 + K2) * 2 / ε)
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hmu : ((n : ℝ) + 1)⁻¹ * (K1 + K2) < ε / 2 := by
    have hn' : (K1 + K2) * 2 / ε < (n : ℝ) + 1 := by linarith only [hn]
    rw [div_lt_iff₀ hε] at hn'
    rw [inv_mul_lt_iff₀ hpos]
    linarith only [hn']
  refine ⟨ε / (2 * (K2 + 1)), by positivity, fun lam hlam hd => ?_⟩
  have hlam0 : 0 < lam := hlam
  have hlt : lam < ε / (2 * (K2 + 1)) := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hlam0] at hd; exact hd
  simp only [dirRep_resolventAt, hlam0, ↓reduceDIte]
  obtain ⟨h1, h2⟩ := hC hf hfM hf0 n y
  have h3 := hBd ⟨lam, Set.mem_Ioi.mpr hlam0⟩ (dirRep_shift n) hf hfM hf0 y
  have hmu0 : ((dirRep_shift n : PositiveShift) : ℝ) = ((n : ℝ) + 1)⁻¹ := rfl
  have h4 : |((dirRep_shift n : PositiveShift) : ℝ) - lam| ≤ ((n : ℝ) + 1)⁻¹ + lam := by
    rw [hmu0, abs_le]; constructor <;> nlinarith only [hlam0, inv_pos.2 hpos]
  have h5 : |D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) ⟨lam, Set.mem_Ioi.mpr hlam0⟩ f hf hfM y -
      D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) (dirRep_shift n) f hf hfM y| ≤
      (((n : ℝ) + 1)⁻¹ + lam) * K2 :=
    h3.trans (mul_le_mul_of_nonneg_right h4 hK2p)
  rw [Real.dist_eq]
  have h6 : |dirRep_limit D x₀ hr hf hfM y - D.analyticData.partC0Resolvent (dirRep_ball x₀ hr)
      (dirRep_shift n) f hf hfM y| ≤ ((n : ℝ) + 1)⁻¹ * K1 := by
    rw [abs_of_nonneg (by linarith only [h1])]
    linarith only [h2, hK1]
  have h7 : lam * K2 < ε / 2 := by
    have : lam * (2 * (K2 + 1)) < ε := by
      rwa [lt_div_iff₀ (by positivity)] at hlt
    nlinarith only [this, hK2p, hlam0]
  have h8 := abs_sub_le (D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) ⟨lam, Set.mem_Ioi.mpr hlam0⟩ f hf hfM y)
    (D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) (dirRep_shift n) f hf hfM y)
    (dirRep_limit D x₀ hr hf hfM y)
  have h9 : |D.analyticData.partC0Resolvent (dirRep_ball x₀ hr) (dirRep_shift n) f hf hfM y -
      dirRep_limit D x₀ hr hf hfM y| ≤ ((n : ℝ) + 1)⁻¹ * K1 := by
    rwa [abs_sub_comm] at h6
  have h10 : ((n : ℝ) + 1)⁻¹ * K1 ≤ ((n : ℝ) + 1)⁻¹ * (K1 + K2) :=
    mul_le_mul_of_nonneg_left (by linarith only [hK2p]) (inv_pos.2 hpos).le
  have h11 : (((n : ℝ) + 1)⁻¹ + lam) * K2 = ((n : ℝ) + 1)⁻¹ * K2 + lam * K2 := by ring
  have h12 : ((n : ℝ) + 1)⁻¹ * K2 + ((n : ℝ) + 1)⁻¹ * K1 = ((n : ℝ) + 1)⁻¹ * (K1 + K2) := by ring
  linarith only [h8, h9, h5, h7, hmu, h11, h12]



/-- **The expected exit time of the compactified process from a ball is the torsion function.** -/
theorem dirRep_expectedExitTime_eq (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {y : Vec d}
    (hy : y ∈ euclideanBall x₀ r) :
    let hreg := D.logGrowthBounds.processInput.toOnePointRegular
    let := hreg.metricSpace
    let := hreg.completeSpace
    expectedExitTime D.logGrowthBounds.resolvent.onePointKernelSemigroup
        D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall x₀ r) (y : OnePoint (Vec d)) =
      ENNReal.ofReal (dirRep_limit D x₀ hr (f := fun _ : Vec d => (1 : ℝ)) measurable_const
        (M := 1) (fun _ => by simp) y) := by
  intro hreg hm hc
  have hV := dirRep_ball x₀ hr
  have hUopen : IsOpen (((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall x₀ r) :=
    OnePoint.isOpen_image_coe.mpr hV.isOpen
  set B := euclideanBall x₀ r with hB
  have hf : Measurable (fun _ : Vec d => (1 : ℝ)) := measurable_const
  have h1M : ∀ z : Vec d, |(fun _ : Vec d => (1 : ℝ)) z| ≤ 1 := fun z => by simp
  have hmeasF : Measurable (PositiveC0ContractiveResolvent.onePointLiveExtension
      (fun z => ENNReal.ofReal (B.indicator (fun _ : Vec d => (1 : ℝ)) z))) :=
    PositiveC0ContractiveResolvent.measurable_onePointLiveExtension
      (ENNReal.measurable_ofReal.comp (hf.indicator hV.isOpen.measurableSet))
  have hexp := IsConservative.lintegral_exitTime_eq_killedResolvent_zero
    D.logGrowthBounds.resolvent.onePointKernelSemigroup
    D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
    (((↑) : Vec d → OnePoint (Vec d)) '' B) hUopen (y : OnePoint (Vec d))
  have hcongr := killedResolvent_congr_of_eqOn
    D.logGrowthBounds.resolvent.onePointKernelSemigroup
    D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
    (((↑) : Vec d → OnePoint (Vec d)) '' B) hUopen 0
    (f := fun _ => (1 : ℝ≥0∞))
    (g := PositiveC0ContractiveResolvent.onePointLiveExtension
      (fun z => ENNReal.ofReal (B.indicator (fun _ : Vec d => (1 : ℝ)) z)))
    (fun z hz => by
      obtain ⟨w, hw, rfl⟩ := hz
      rw [PositiveC0ContractiveResolvent.onePointLiveExtension_coe, Set.indicator_of_mem hw,
        ENNReal.ofReal_one]) (y : OnePoint (Vec d))
  have hiSup := IsConservative.killedResolvent_zero_eq_iSup
    D.logGrowthBounds.resolvent.onePointKernelSemigroup
    D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
    (((↑) : Vec d → OnePoint (Vec d)) '' B) hUopen hmeasF (y : OnePoint (Vec d))
  have hterm : ∀ n : ℕ, IsConservative.killedResolvent
      D.logGrowthBounds.resolvent.onePointKernelSemigroup
      D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
      (((↑) : Vec d → OnePoint (Vec d)) '' B) hUopen ((n : ℝ) + 1)⁻¹
      (PositiveC0ContractiveResolvent.onePointLiveExtension
          (fun z => ENNReal.ofReal (B.indicator (fun _ : Vec d => (1 : ℝ)) z)))
        (y : OnePoint (Vec d)) =
      ENNReal.ofReal (D.analyticData.partC0Resolvent hV (dirRep_shift n) (fun _ => (1 : ℝ)) hf h1M y) := by
    intro n
    have hcrux := fieldExit_killedResolvent_eq_partResolvent D
      (dirRep_barrierData D x₀ hr (dirRep_shift n) hf (fun _ => zero_le_one) h1M) hy
    dsimp only at hcrux
    exact hcrux
  simp only [hterm] at hiSup
  rw [dirRep_iSup_ofReal_eq D x₀ hr hf h1M (fun _ => zero_le_one) y] at hiSup
  unfold expectedExitTime
  rw [hexp, hcongr, hiSup]

/-- **The expected exit time of the compactified process from a ball is finite.** -/
theorem dirRep_expectedExitTime_ne_top (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {y : Vec d}
    (hy : y ∈ euclideanBall x₀ r) :
    let hreg := D.logGrowthBounds.processInput.toOnePointRegular
    let := hreg.metricSpace
    let := hreg.completeSpace
    expectedExitTime D.logGrowthBounds.resolvent.onePointKernelSemigroup
        D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall x₀ r) (y : OnePoint (Vec d)) ≠ ⊤ := by
  intro hreg hm hc
  have h := dirRep_expectedExitTime_eq D x₀ hr hy
  dsimp only at h
  rw [h]
  exact ENNReal.ofReal_ne_top


/-- **The limit of the part resolvents is the zero-trace solution of the unshifted problem.**
For a bounded nonnegative measurable `f`, the vanishing-shift limit `W` of the part resolvents of
the ball agrees almost everywhere with an `H¹₀` function `u` which solves `-∇·(a∇u) = f` weakly. -/
theorem dirRep_h10_solution (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {f : Vec d → ℝ}
    (hf : Measurable f) {M : ℝ} (hfM : ∀ y, |f y| ≤ M) (hf0 : ∀ y, 0 ≤ f y) :
    ∃ u : H10Function (euclideanBall x₀ r),
      (∀ᵐ y ∂volumeMeasureOn (euclideanBall x₀ r),
        dirRep_limit D x₀ hr hf hfM y = u.toH1Function.toFun y) ∧
      IsScalarForcedWeakSolution D.analyticData.a (euclideanBall x₀ r) f u.toH1Function := by
  obtain ⟨Bd, hBd0, hBd⟩ := dirRep_limit_bound D x₀ hr
  have hB := hBd hf hfM hf0
  have hV := dirRep_ball x₀ hr
  set A := D.analyticData with hA
  have hEll := partEllipticity A hV
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete (dirRep_z_cauchy D x₀ hr hf hfM hf0)
  have hTz : Tendsto (fun n => ZeroTraceSobolev.toL2 (dirRep_z D x₀ hr hf hfM n)) atTop
      (𝓝 (ZeroTraceSobolev.toL2 z)) :=
    (ZeroTraceSobolev.toL2.continuous.tendsto z).comp hz
  have hwcl := dirRep_z_tendsto_L2 D x₀ hr hf hfM hf0 hB
  have hTeq := tendsto_nhds_unique hTz hwcl
  have hweak : ∀ v : ZeroTraceSobolev (euclideanBall x₀ r),
      shiftedBilin hEll 0 z v = ⟪partDatumL2 hV hf hfM, ZeroTraceSobolev.toL2 v⟫ := by
    intro v
    have hμ : Tendsto (fun n : ℕ => ((dirRep_shift n : PositiveShift) : ℝ)) atTop (𝓝 0) := by
      simpa [dirRep_shift_coe, one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hin : Tendsto (fun n => ⟪ZeroTraceSobolev.toL2 (dirRep_z D x₀ hr hf hfM n),
        ZeroTraceSobolev.toL2 v⟫) atTop (𝓝 ⟪ZeroTraceSobolev.toL2 z, ZeroTraceSobolev.toL2 v⟫) :=
      (continuous_id.inner continuous_const).tendsto _ |>.comp hTz
    have hbil : Tendsto (fun n => shiftedBilin hEll 0 (dirRep_z D x₀ hr hf hfM n) v) atTop
        (𝓝 (shiftedBilin hEll 0 z v)) :=
      (((shiftedBilin hEll 0).flip v).continuous.tendsto z).comp hz
    have hsum := (hμ.mul hin).add hbil
    have hconst : Tendsto (fun n : ℕ => ⟪partDatumL2 hV hf hfM, ZeroTraceSobolev.toL2 v⟫) atTop
        (𝓝 ⟪partDatumL2 hV hf hfM, ZeroTraceSobolev.toL2 v⟫) := tendsto_const_nhds
    have hlim := tendsto_nhds_unique hsum
      (hconst.congr fun n => (dirRep_z_eq D x₀ hr hf hfM n v).symm)
    rw [zero_mul, zero_add] at hlim
    exact hlim
  have hweakα : IsAlphaShiftedWeakSolution A.a (euclideanBall x₀ r) 0
      (partDatumL2 hV hf hfM) z := by
    intro v
    rw [coefficientPairing_gradient_eq_shiftedBilin hEll, hweak v, zero_mul, zero_add]
  obtain ⟨u, hu1, hu2⟩ := ZeroTraceSobolev.exists_h10Function hV z
  have hzu : ZeroTraceSobolev.ofH10Function u = z := by
    ext1
    · rw [ZeroTraceSobolev.toL2_ofH10Function, hu1]
    · rw [ZeroTraceSobolev.gradient_ofH10Function, hu2]
  rw [← hzu] at hweakα
  refine ⟨u, ?_, ?_⟩
  · filter_upwards [u.toH1Function.coeFn_toScalarL2,
      boundedMeasurableToScalarL2_coeFn hV
        ((dirRep_limit_continuous D x₀ hr hf hfM hf0).measurable.comp measurable_subtype_coe)
        (fun y => hB y), ae_restrict_mem hV.isOpen.measurableSet] with y h1 h2 hy
    have h4 := hu1.trans hTeq
    rw [← h1, h4, h2, domainExtension_of_mem hy]
    rfl
  · refine (isScalarForcedWeakSolution_sub_alpha_mul_of_isAlphaShiftedWeakSolution u
      hweakα).congr_datum ?_
    filter_upwards [boundedMeasurableToScalarL2_coeFn hV (hf.comp measurable_subtype_coe)
      (fun y => hfM y), ae_restrict_mem hV.isOpen.measurableSet] with y hy hyV
    have h3 : (partDatumL2 hV hf hfM) y = f y := by
      unfold partDatumL2
      rw [hy, domainExtension_of_mem hyV]; rfl
    rw [h3]; ring

/-- **The zero-trace solution for a signed bounded datum.**  For a bounded measurable `f` there is a
continuous `w`, vanishing off the ball, which is the `H¹₀` weak solution of `-∇·(a∇w) = f`, and
which is the limit of the part resolvents as the real shift decreases to zero. -/
theorem dirRep_signed (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {f : Vec d → ℝ}
    (hf : Measurable f) {M : ℝ} (hfM : ∀ y, |f y| ≤ M) :
    ∃ (w : Vec d → ℝ) (u : H10Function (euclideanBall x₀ r)), Continuous w ∧
      (∀ y, y ∉ euclideanBall x₀ r → w y = 0) ∧
      (∀ᵐ y ∂volumeMeasureOn (euclideanBall x₀ r), w y = u.toH1Function.toFun y) ∧
      IsScalarForcedWeakSolution D.analyticData.a (euclideanBall x₀ r) f u.toH1Function ∧
      ∀ y, Tendsto (fun lam : ℝ => dirRep_resolventAt D x₀ hr hf hfM lam y) (𝓝[>] (0 : ℝ))
        (𝓝 (w y)) := by
  have hp := dirRep_pos_measurable hf
  have hn := dirRep_neg_measurable hf
  have hpM := dirRep_abs_pos_le hfM
  have hnM := dirRep_abs_neg_le hfM
  obtain ⟨up, hup1, hup2⟩ := dirRep_h10_solution D x₀ hr hp hpM (dirRep_pos_nonneg f)
  obtain ⟨un, hun1, hun2⟩ := dirRep_h10_solution D x₀ hr hn hnM (dirRep_neg_nonneg f)
  have hV := dirRep_ball x₀ hr
  refine ⟨fun y => dirRep_limit D x₀ hr hp hpM y - dirRep_limit D x₀ hr hn hnM y, up - un,
    (dirRep_limit_continuous D x₀ hr hp hpM (dirRep_pos_nonneg f)).sub
      (dirRep_limit_continuous D x₀ hr hn hnM (dirRep_neg_nonneg f)),
    fun y hy => by
      simp only [dirRep_limit_off D x₀ hr hp hpM hy, dirRep_limit_off D x₀ hr hn hnM hy, sub_zero],
    ?_, ?_, fun y => ?_⟩
  · filter_upwards [hup1, hun1] with y h1 h2
    show _ = (up.toH1Function - un.toH1Function).toFun y
    rw [H1Function.sub_toFun]
    show _ = up.toFun y - un.toFun y
    rw [h1, h2]
  · have hs := (hup2.sub (partEllipticity D.analyticData hV) hun2)
    have hfun : (fun x => dirRep_pos f x - dirRep_neg f x) = f := funext (dirRep_pos_sub_neg f)
    rw [hfun] at hs
    exact hs
  · have h1 := dirRep_tendsto_resolventAt D x₀ hr hp hpM (dirRep_pos_nonneg f) y
    have h2 := dirRep_tendsto_resolventAt D x₀ hr hn hnM (dirRep_neg_nonneg f) y
    refine (h1.sub h2).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with lam hlam
    have hlam0 : (0 : ℝ) < lam := hlam
    simp only [dirRep_resolventAt, hlam0, ↓reduceDIte]
    exact (dirRep_part_split D x₀ hr ⟨lam, Set.mem_Ioi.mpr hlam0⟩ hf hfM y).symm

/-- The torsion function of the ball: the expected exit time. -/
def dirRep_torsion (x₀ : Vec d) {r : ℝ} (hr : 0 < r) : Vec d → ℝ :=
  dirRep_limit D x₀ hr (f := fun _ : Vec d => (1 : ℝ)) measurable_const (M := 1) (fun _ => by simp)

theorem dirRep_torsion_continuous (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    Continuous (dirRep_torsion D x₀ hr) :=
  dirRep_limit_continuous D x₀ hr measurable_const _ (fun _ => zero_le_one)

theorem dirRep_torsion_off (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {y : Vec d}
    (hy : y ∉ euclideanBall x₀ r) : dirRep_torsion D x₀ hr y = 0 :=
  dirRep_limit_off D x₀ hr measurable_const _ hy

theorem dirRep_torsion_nonneg (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (y : Vec d) :
    0 ≤ dirRep_torsion D x₀ hr y :=
  dirRep_limit_nonneg D x₀ hr measurable_const _ (fun _ => zero_le_one) y

end
end SuperdiffusionCLT.Section8
