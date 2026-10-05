/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.CrudeMomentsD

/-!
# The fourth moment of the marginal-field process at the origin, for times at most one

At the shift `mu = 1 / t ≥ 1` the displacement tail at the origin is the shift-uniform profile
provided the radius is above the cubic-log cutting radius and above the point where the
stretched-exponential envelope is at most one half.  The layer cake of `CrudeMomentsC` then gives
the fourth moment `C (1 + log (1 / t)) ^ 12 t ^ 2`, with a constant that depends only on the
logarithmic-growth bounds of the split datum.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory Set Filter
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section6
open SuperdiffusionCLT.Section8.DivergenceForm
open MarkovProcess MarkovProcess.Semigroup
open scoped ENNReal NNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ} [NeZero d] {A : WholeSpaceAnalyticData d} {Sp : WholeSpaceLocalizedSplitData A}

/-- **The displacement tail at the origin.**  Above the cutting radius and the one-half level of
the envelope, the transition law at time `1 / mu` started at the origin leaves the ball of radius
`11 r` with probability at most `2 e` times the shift-uniform profile. -/
theorem LogGrowthBounds.crudeMom_tail_at_origin
    (T : LogGrowthBounds Sp) (R : PositiveC0ContractiveResolvent (Vec d))
    (hcons : R.kernelSemigroup.IsConservative)
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R)
    {sstar : ℝ} (hs : ∀ s, sstar ≤ s → LogGrowthBounds.uniformEnvelope T s ≤ 1 / 2)
    (mu : PositiveShift) (hmu : 1 ≤ (mu : ℝ)) {t : ℝ≥0} (ht : (mu : ℝ) * (t : ℝ) = 1)
    {r : ℝ} (hr : 0 < r)
    (hrs : max (LogGrowthBounds.uniformCutoff T (mu : ℝ)) sstar < Real.sqrt (mu : ℝ) * r) :
    R.kernelSemigroup t 0 (Metric.ball (0 : Vec d) (11 * r))ᶜ ≤
      ENNReal.ofReal (2 * Real.exp 1 *
        LogGrowthBounds.uniformProfile T (mu : ℝ) (Real.sqrt (mu : ℝ) * r)) := by
  have hcutlt : LogGrowthBounds.uniformCutoff T (mu : ℝ) < Real.sqrt (mu : ℝ) * r :=
    lt_of_le_of_lt (le_max_left _ _) hrs
  have hslt : sstar < Real.sqrt (mu : ℝ) * r := lt_of_le_of_lt (le_max_right _ _) hrs
  have hprof : LogGrowthBounds.uniformProfile T (mu : ℝ) (Real.sqrt (mu : ℝ) * r) ≤ 1 / 2 := by
    unfold LogGrowthBounds.uniformProfile
    simp only [hcutlt, ↓reduceIte]
    exact hs _ hslt.le
  refine crudeMom_measure_compl_ball_le R hcons ht 0 hr
    (LogGrowthBounds.uniformProfile_nonneg T _ _) ?_ ?_
  · have h0 := LogGrowthBounds.crudeMom_liveTail T R hid mu hmu (0 : Vec d) hr
    rwa [crudeMom_amp_zero] at h0
  · intro y hy
    rw [dist_zero_right] at hy
    have hsub : Metric.ball (0 : Vec d) (2 * r) ⊆
        (Metric.ball y (fieldInput_exhaustionAmp y r))ᶜ := by
      intro z hz
      simp only [Metric.mem_ball, dist_zero_right, Set.mem_compl_iff, not_lt] at hz ⊢
      have hamp := crudeMom_amp_le_of_far hr hy
      have h1 : ‖y‖ - ‖z‖ ≤ ‖y - z‖ := norm_sub_norm_le y z
      rw [dist_comm, dist_eq_norm]
      linarith only [hamp, h1, hz]
    calc ENNReal.ofReal (mu : ℝ) *
          R.kernelSemigroup.resolventPotential (mu : ℝ) y (Metric.ball (0 : Vec d) (2 * r))
        ≤ ENNReal.ofReal (mu : ℝ) *
          R.kernelSemigroup.resolventPotential (mu : ℝ) y
            (Metric.ball y (fieldInput_exhaustionAmp y r))ᶜ := by
          gcongr
      _ ≤ ENNReal.ofReal (LogGrowthBounds.uniformProfile T (mu : ℝ)
            (Real.sqrt (mu : ℝ) * r)) :=
          LogGrowthBounds.crudeMom_liveTail T R hid mu hmu y hr
      _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hprof

/-- **The fourth moment at the origin for times at most one, with the explicit constant.** -/
theorem LogGrowthBounds.crudeMom_fourth_moment_le_one
    (T : LogGrowthBounds Sp) (R : PositiveC0ContractiveResolvent (Vec d))
    (hcons : R.kernelSemigroup.IsConservative)
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R)
    {sstar : ℝ} (hsstar : 0 ≤ sstar)
    (hs : ∀ s, sstar ≤ s → LogGrowthBounds.uniformEnvelope T s ≤ 1 / 2)
    {t : ℝ≥0} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∫⁻ z, edist z (0 : Vec d) ^ (4 : ℝ) ∂(R.kernelSemigroup t 0) ≤
      ENNReal.ofReal (14641 * (((LogGrowthBounds.uniformScale T *
        (1 + Real.log ((t : ℝ)⁻¹))) ^ 12 + sstar ^ 4 +
          8 * Real.exp 1 * LogGrowthBounds.uniformBudget T) * (t : ℝ) ^ 2)) := by
  have htpos : (0 : ℝ) < (t : ℝ) := ht0
  have ht1' : (t : ℝ) ≤ 1 := by exact_mod_cast ht1
  have hinv : (0 : ℝ) < (t : ℝ)⁻¹ := inv_pos.mpr htpos
  have hone : (1 : ℝ) ≤ (t : ℝ)⁻¹ := (one_le_inv₀ htpos).mpr ht1'
  let mu : PositiveShift := ⟨(t : ℝ)⁻¹, hinv⟩
  have hmu : 1 ≤ (mu : ℝ) := hone
  have hmut : (mu : ℝ) * (t : ℝ) = 1 := inv_mul_cancel₀ htpos.ne'
  have hsqrt : Real.sqrt (mu : ℝ) * Real.sqrt (t : ℝ) = 1 := by
    rw [← Real.sqrt_mul (by positivity), hmut, Real.sqrt_one]
  have hsqt : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr htpos
  set a : ℝ := max (LogGrowthBounds.uniformCutoff T (mu : ℝ)) sstar with ha
  have ha0 : 0 ≤ a := le_max_of_le_right hsstar
  have hcut1 : 1 ≤ LogGrowthBounds.uniformCutoff T (mu : ℝ) :=
    LogGrowthBounds.one_le_uniformCutoff T _
  have hapos : 0 < a := lt_of_lt_of_le zero_lt_one (hcut1.trans (le_max_left _ _))
  have hB0 := LogGrowthBounds.uniformBudget_nonneg T
  have he0 : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hlevel : ∀ s : ℝ, a < s →
      (R.kernelSemigroup t 0) {z | s < dist z 0 / (11 * Real.sqrt (t : ℝ))} ≤
        ENNReal.ofReal (2 * Real.exp 1 *
          LogGrowthBounds.uniformProfile T (mu : ℝ) s) := by
    intro s hsa
    have hs0 : 0 < s := hapos.trans hsa
    have hr : 0 < Real.sqrt (t : ℝ) * s := mul_pos hsqt hs0
    have hscale : Real.sqrt (mu : ℝ) * (Real.sqrt (t : ℝ) * s) = s := by
      rw [← mul_assoc, hsqrt, one_mul]
    have hrs : a < Real.sqrt (mu : ℝ) * (Real.sqrt (t : ℝ) * s) := by
      rw [hscale]; exact hsa
    have htail := LogGrowthBounds.crudeMom_tail_at_origin T R hcons hid hs mu hmu hmut hr hrs
    rw [hscale] at htail
    refine le_trans (measure_mono ?_) htail
    intro z hz
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Metric.mem_ball, dist_zero_right,
      not_lt] at hz ⊢
    rw [lt_div_iff₀ (by positivity)] at hz
    nlinarith only [hz, hsqt, hs0]
  have hint : ∫⁻ s in Set.Ioi a, ENNReal.ofReal
      ((2 * Real.exp 1 * LogGrowthBounds.uniformProfile T (mu : ℝ) s) * s ^ 3) ≤
      ENNReal.ofReal (2 * Real.exp 1 * LogGrowthBounds.uniformBudget T) := by
    have h2e : (0 : ℝ) ≤ 2 * Real.exp 1 := by positivity
    have hrw : ∀ s : ℝ, ENNReal.ofReal
        ((2 * Real.exp 1 * LogGrowthBounds.uniformProfile T (mu : ℝ) s) * s ^ 3) =
        ENNReal.ofReal (2 * Real.exp 1) *
          ENNReal.ofReal (LogGrowthBounds.uniformProfile T (mu : ℝ) s * s ^ 3) := by
      intro s
      rw [← ENNReal.ofReal_mul h2e, mul_assoc]
    simp only [hrw]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ENNReal.ofReal_mul h2e]
    gcongr
    calc ∫⁻ s in Set.Ioi a, ENNReal.ofReal
          (LogGrowthBounds.uniformProfile T (mu : ℝ) s * s ^ 3)
        ≤ ∫⁻ s in Set.Ioi (LogGrowthBounds.uniformCutoff T (mu : ℝ)), ENNReal.ofReal
          (LogGrowthBounds.uniformProfile T (mu : ℝ) s * s ^ 3) :=
          lintegral_mono_set (Set.Ioi_subset_Ioi (le_max_left _ _))
      _ ≤ ENNReal.ofReal (LogGrowthBounds.uniformBudget T) :=
          LogGrowthBounds.lintegral_uniformProfile_mul_cube_le T hmu
  have : IsProbabilityMeasure (R.kernelSemigroup t 0) := ⟨hcons t 0⟩
  have hcake := crudeMom_lintegral_edist_pow_le (nu := R.kernelSemigroup t 0)
    (le_of_eq measure_univ) (0 : Vec d) (c := 11 * Real.sqrt (t : ℝ)) (by positivity) ha0
    (by positivity : (0 : ℝ) ≤ 2 * Real.exp 1 * LogGrowthBounds.uniformBudget T)
    (psi := fun s ↦ 2 * Real.exp 1 * LogGrowthBounds.uniformProfile T (mu : ℝ) s)
    (fun s ↦ mul_nonneg (by positivity) (LogGrowthBounds.uniformProfile_nonneg T _ _))
    hlevel hint
  refine hcake.trans (ENNReal.ofReal_le_ofReal ?_)
  have hc4 : (11 * Real.sqrt (t : ℝ)) ^ 4 = 14641 * (t : ℝ) ^ 2 := by
    have : Real.sqrt (t : ℝ) ^ 4 = (t : ℝ) ^ 2 := by
      rw [show Real.sqrt (t : ℝ) ^ 4 = (Real.sqrt (t : ℝ) ^ 2) ^ 2 by ring,
        Real.sq_sqrt htpos.le]
    rw [mul_pow, this]
    norm_num
  have hcutpow : LogGrowthBounds.uniformCutoff T (mu : ℝ) ^ 4 =
      (LogGrowthBounds.uniformScale T * (1 + Real.log ((t : ℝ)⁻¹))) ^ 12 := by
    unfold LogGrowthBounds.uniformCutoff fieldInput_uniformShiftWeight
    rw [← pow_mul]
    have hmax : max (mu : ℝ) 1 = (t : ℝ)⁻¹ := max_eq_left hone
    rw [hmax]
  have ha4 : a ^ 4 ≤ LogGrowthBounds.uniformCutoff T (mu : ℝ) ^ 4 + sstar ^ 4 := by
    have h1 : (0 : ℝ) ≤ LogGrowthBounds.uniformCutoff T (mu : ℝ) ^ 4 := by positivity
    have h2 : (0 : ℝ) ≤ sstar ^ 4 := by positivity
    rcases le_total (LogGrowthBounds.uniformCutoff T (mu : ℝ)) sstar with h | h
    · rw [ha, max_eq_right h]; linarith only [h1]
    · rw [ha, max_eq_left h]; linarith only [h2]
  rw [hc4]
  have ht2 : (0 : ℝ) ≤ (t : ℝ) ^ 2 := by positivity
  have hbr : a ^ 4 + 4 * (2 * Real.exp 1 * LogGrowthBounds.uniformBudget T) ≤
      (LogGrowthBounds.uniformScale T * (1 + Real.log ((t : ℝ)⁻¹))) ^ 12 + sstar ^ 4 +
        8 * Real.exp 1 * LogGrowthBounds.uniformBudget T := by
    rw [hcutpow] at ha4
    linarith only [ha4]
  calc 14641 * (t : ℝ) ^ 2 * (a ^ 4 + 4 * (2 * Real.exp 1 * LogGrowthBounds.uniformBudget T))
      = 14641 * ((t : ℝ) ^ 2 *
          (a ^ 4 + 4 * (2 * Real.exp 1 * LogGrowthBounds.uniformBudget T))) := by ring
    _ ≤ 14641 * ((t : ℝ) ^ 2 * ((LogGrowthBounds.uniformScale T *
          (1 + Real.log ((t : ℝ)⁻¹))) ^ 12 + sstar ^ 4 +
            8 * Real.exp 1 * LogGrowthBounds.uniformBudget T)) := by
        gcongr
    _ = _ := by ring

/-- **The fourth moment at the origin for times at most one.**  There is a constant `M`, depending
only on the logarithmic-growth bounds, with
`∫ ‖y‖⁴ d(S t 0) ≤ M (1 + log (1 / t)) ^ 12 t ^ 2` for `0 < t ≤ 1`. -/
theorem LogGrowthBounds.crudeMom_exists_const
    (T : LogGrowthBounds Sp) (R : PositiveC0ContractiveResolvent (Vec d))
    (hcons : R.kernelSemigroup.IsConservative)
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ≥0, 0 < t → t ≤ 1 →
      ∫⁻ z, edist z (0 : Vec d) ^ (4 : ℝ) ∂(R.kernelSemigroup t 0) ≤
        ENNReal.ofReal (M * (1 + Real.log ((t : ℝ)⁻¹)) ^ 12 * (t : ℝ) ^ 2) := by
  obtain ⟨s1, hs1⟩ := Filter.eventually_atTop.1
    ((LogGrowthBounds.tendsto_uniformEnvelope_atTop T).eventually
      (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  have hs : ∀ s, max s1 0 ≤ s → LogGrowthBounds.uniformEnvelope T s ≤ 1 / 2 :=
    fun s h => hs1 s (le_trans (le_max_left _ _) h)
  have hB0 := LogGrowthBounds.uniformBudget_nonneg T
  refine ⟨14641 * (LogGrowthBounds.uniformScale T ^ 12 + max s1 0 ^ 4 +
    8 * Real.exp 1 * LogGrowthBounds.uniformBudget T), by positivity, fun t ht0 ht1 => ?_⟩
  refine (LogGrowthBounds.crudeMom_fourth_moment_le_one T R hcons hid (le_max_right _ _) hs
    ht0 ht1).trans (ENNReal.ofReal_le_ofReal ?_)
  have htpos : (0 : ℝ) < (t : ℝ) := ht0
  have hone : (1 : ℝ) ≤ (t : ℝ)⁻¹ := (one_le_inv₀ htpos).mpr (by exact_mod_cast ht1)
  have hw : 1 ≤ 1 + Real.log ((t : ℝ)⁻¹) := by
    have := Real.log_nonneg hone
    linarith only [this]
  have hw12 : 1 ≤ (1 + Real.log ((t : ℝ)⁻¹)) ^ 12 := one_le_pow₀ hw
  have hrest : (0 : ℝ) ≤ max s1 0 ^ 4 + 8 * Real.exp 1 * LogGrowthBounds.uniformBudget T := by
    positivity
  have ht2 : (0 : ℝ) ≤ (t : ℝ) ^ 2 := by positivity
  have hmul : (LogGrowthBounds.uniformScale T * (1 + Real.log ((t : ℝ)⁻¹))) ^ 12 =
      LogGrowthBounds.uniformScale T ^ 12 * (1 + Real.log ((t : ℝ)⁻¹)) ^ 12 := mul_pow _ _ _
  have hineq : (LogGrowthBounds.uniformScale T * (1 + Real.log ((t : ℝ)⁻¹))) ^ 12 +
      max s1 0 ^ 4 + 8 * Real.exp 1 * LogGrowthBounds.uniformBudget T ≤
      (LogGrowthBounds.uniformScale T ^ 12 + max s1 0 ^ 4 +
        8 * Real.exp 1 * LogGrowthBounds.uniformBudget T) *
        (1 + Real.log ((t : ℝ)⁻¹)) ^ 12 := by
    have h1 : max s1 0 ^ 4 + 8 * Real.exp 1 * LogGrowthBounds.uniformBudget T ≤
        (max s1 0 ^ 4 + 8 * Real.exp 1 * LogGrowthBounds.uniformBudget T) *
          (1 + Real.log ((t : ℝ)⁻¹)) ^ 12 := by
      calc _ = (max s1 0 ^ 4 + 8 * Real.exp 1 * LogGrowthBounds.uniformBudget T) * 1 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hw12 hrest
    rw [hmul]
    linarith only [h1]
  calc 14641 * (((LogGrowthBounds.uniformScale T * (1 + Real.log ((t : ℝ)⁻¹))) ^ 12 +
        max s1 0 ^ 4 + 8 * Real.exp 1 * LogGrowthBounds.uniformBudget T) * (t : ℝ) ^ 2)
      ≤ 14641 * (((LogGrowthBounds.uniformScale T ^ 12 + max s1 0 ^ 4 +
        8 * Real.exp 1 * LogGrowthBounds.uniformBudget T) *
          (1 + Real.log ((t : ℝ)⁻¹)) ^ 12) * (t : ℝ) ^ 2) := by
        gcongr
    _ = _ := by ring

/-- **The fourth moment at the origin of the marginal-field process, for times at most one.** -/
theorem fieldMoment_fourth_le_one {nu : ℝ} {k : Vec d → Mat d} (D : FieldInputData d nu k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ≥0, 0 < t → t ≤ 1 →
      ∫⁻ z, edist z (0 : Vec d) ^ (4 : ℝ) ∂(D.logGrowthBounds.resolvent.kernelSemigroup t 0) ≤
        ENNReal.ofReal (M * (1 + Real.log ((t : ℝ)⁻¹)) ^ 12 * (t : ℝ) ^ 2) :=
  D.logGrowthBounds.crudeMom_exists_const D.logGrowthBounds.resolvent
    D.logGrowthBounds.isConservative_kernelSemigroup
    D.logGrowthBounds.kernelResolventIdentifiesAnalyticMinimal

/-! ## Satisfiability witnesses -/

/-- The moment bound applies to the marginal field of the zero skew field, for which the process
is the heat flow. -/
example (hd : 2 ≤ d) :
    ∃ D : FieldInputData d 1 (fun _ : Vec d => (0 : Mat d)),
      ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ≥0, 0 < t → t ≤ 1 →
        ∫⁻ z, edist z (0 : Vec d) ^ (4 : ℝ) ∂(D.logGrowthBounds.resolvent.kernelSemigroup t 0) ≤
          ENNReal.ofReal (M * (1 + Real.log ((t : ℝ)⁻¹)) ^ 12 * (t : ℝ) ^ 2) := by
  let D : FieldInputData d 1 (fun _ : Vec d => (0 : Mat d)) :=
    { two_le := hd
      nu_pos := one_pos
      skew := fun _ => by simp [matTranspose]
      contDiff := contDiff_const
      gradConst := 0
      gradConst_nonneg := le_rfl
      grad_le := fun y => by simp }
  exact ⟨D, fieldMoment_fourth_le_one D⟩

/-- **Almost surely the marginal-field process has the fourth moment bound at the origin for
times at most one.** -/
theorem fieldMoment_ae_fourth_le_one {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      ∃ D : FieldInputData d nu (fullStreamRecentered omega),
        ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ≥0, 0 < t → t ≤ 1 →
          ∫⁻ z, edist z (0 : Vec d) ^ (4 : ℝ) ∂(D.logGrowthBounds.resolvent.kernelSemigroup t 0) ≤
            ENNReal.ofReal (M * (1 + Real.log ((t : ℝ)⁻¹)) ^ 12 * (t : ℝ) ^ 2) := by
  filter_upwards [fieldInput_ae_data hPrefix hJ3 hnu] with omega hD
  obtain ⟨D⟩ := hD
  exact ⟨D, fieldMoment_fourth_le_one D⟩

/-- The almost-sure statement holds for the Dirac zero law. -/
example (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∃ D : FieldInputData d nu (fullStreamRecentered omega),
        ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ≥0, 0 < t → t ≤ 1 →
          ∫⁻ z, edist z (0 : Vec d) ^ (4 : ℝ) ∂(D.logGrowthBounds.resolvent.kernelSemigroup t 0) ≤
            ENNReal.ofReal (M * (1 + Real.log ((t : ℝ)⁻¹)) ^ 12 * (t : ℝ) ^ 2) :=
  fieldMoment_ae_fourth_le_one
    (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw hd)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw hnu

/-! ## A general centre -/

/-- **The displacement tail at a general centre.**  With the working radius
`a = max r (2/3 (1 + |x|))`, above the cutting radius and the one-half level of the envelope the
transition law started at `x` leaves the ball of radius `11 a` with probability at most `2 e`
times the shift-uniform profile at `sqrt mu * r`. -/
theorem LogGrowthBounds.crudeMom_tail_at
    (T : LogGrowthBounds Sp) (R : PositiveC0ContractiveResolvent (Vec d))
    (hcons : R.kernelSemigroup.IsConservative)
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R)
    {sstar : ℝ} (hs : ∀ s, sstar ≤ s → LogGrowthBounds.uniformEnvelope T s ≤ 1 / 2)
    (mu : PositiveShift) (hmu : 1 ≤ (mu : ℝ)) {t : ℝ≥0} (ht : (mu : ℝ) * (t : ℝ) = 1)
    (x : Vec d) {r : ℝ} (hr : 0 < r)
    (hrs : max (LogGrowthBounds.uniformCutoff T (mu : ℝ)) sstar < Real.sqrt (mu : ℝ) * r) :
    R.kernelSemigroup t x (Metric.ball x (11 * max r (2 / 3 * (1 + ‖x‖))))ᶜ ≤
      ENNReal.ofReal (2 * Real.exp 1 *
        LogGrowthBounds.uniformProfile T (mu : ℝ) (Real.sqrt (mu : ℝ) * r)) := by
  have hcutlt : LogGrowthBounds.uniformCutoff T (mu : ℝ) < Real.sqrt (mu : ℝ) * r :=
    lt_of_le_of_lt (le_max_left _ _) hrs
  have hslt : sstar < Real.sqrt (mu : ℝ) * r := lt_of_le_of_lt (le_max_right _ _) hrs
  have hprof : LogGrowthBounds.uniformProfile T (mu : ℝ) (Real.sqrt (mu : ℝ) * r) ≤ 1 / 2 := by
    unfold LogGrowthBounds.uniformProfile
    simp only [hcutlt, ↓reduceIte]
    exact hs _ hslt.le
  have ha : 0 < max r (2 / 3 * (1 + ‖x‖)) := lt_of_lt_of_le hr (le_max_left _ _)
  refine crudeMom_measure_compl_ball_le R hcons ht x ha
    (LogGrowthBounds.uniformProfile_nonneg T _ _) ?_ ?_
  · have h0 := LogGrowthBounds.crudeMom_liveTail T R hid mu hmu x hr
    have hamp : fieldInput_exhaustionAmp x r ≤ max r (2 / 3 * (1 + ‖x‖)) := by
      unfold fieldInput_exhaustionAmp
      split_ifs
      · exact le_rfl
      · exact le_max_left _ _
    refine le_trans ?_ h0
    gcongr
  · intro y hy
    rw [dist_eq_norm] at hy
    have hsub : Metric.ball x (2 * max r (2 / 3 * (1 + ‖x‖))) ⊆
        (Metric.ball y (fieldInput_exhaustionAmp y r))ᶜ := by
      intro z hz
      simp only [Metric.mem_ball, dist_eq_norm, Set.mem_compl_iff, not_lt] at hz ⊢
      have hamp := crudeMom_amp_le_of_far_at hr hy
      have h1 := norm_sub_norm_le (y - x) (z - x)
      rw [sub_sub_sub_cancel_right] at h1
      rw [← norm_neg, neg_sub]
      linarith only [hamp, h1, hz]
    calc ENNReal.ofReal (mu : ℝ) *
          R.kernelSemigroup.resolventPotential (mu : ℝ) y
            (Metric.ball x (2 * max r (2 / 3 * (1 + ‖x‖))))
        ≤ ENNReal.ofReal (mu : ℝ) *
          R.kernelSemigroup.resolventPotential (mu : ℝ) y
            (Metric.ball y (fieldInput_exhaustionAmp y r))ᶜ := by
          gcongr
      _ ≤ ENNReal.ofReal (LogGrowthBounds.uniformProfile T (mu : ℝ)
            (Real.sqrt (mu : ℝ) * r)) :=
          LogGrowthBounds.crudeMom_liveTail T R hid mu hmu y hr
      _ ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hprof

/-- **The fourth moment at a general centre for times at most one.**  The bound has the
polynomial term `(2/3 (1 + |x|)) ^ 4` of the working radius and the logarithmic term of the
origin. -/
theorem LogGrowthBounds.crudeMom_fourth_moment_le_one_at
    (T : LogGrowthBounds Sp) (R : PositiveC0ContractiveResolvent (Vec d))
    (hcons : R.kernelSemigroup.IsConservative)
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R)
    {sstar : ℝ} (hsstar : 0 ≤ sstar)
    (hs : ∀ s, sstar ≤ s → LogGrowthBounds.uniformEnvelope T s ≤ 1 / 2)
    {t : ℝ≥0} (ht0 : 0 < t) (ht1 : t ≤ 1) (x : Vec d) :
    ∫⁻ z, edist z x ^ (4 : ℝ) ∂(R.kernelSemigroup t x) ≤
      ENNReal.ofReal (14641 * (((LogGrowthBounds.uniformScale T *
        (1 + Real.log ((t : ℝ)⁻¹))) ^ 12 + sstar ^ 4 +
          8 * Real.exp 1 * LogGrowthBounds.uniformBudget T) * (t : ℝ) ^ 2 +
            (2 / 3 * (1 + ‖x‖)) ^ 4)) := by
  have htpos : (0 : ℝ) < (t : ℝ) := ht0
  have ht1' : (t : ℝ) ≤ 1 := by exact_mod_cast ht1
  have hinv : (0 : ℝ) < (t : ℝ)⁻¹ := inv_pos.mpr htpos
  have hone : (1 : ℝ) ≤ (t : ℝ)⁻¹ := (one_le_inv₀ htpos).mpr ht1'
  let mu : PositiveShift := ⟨(t : ℝ)⁻¹, hinv⟩
  have hmu : 1 ≤ (mu : ℝ) := hone
  have hmut : (mu : ℝ) * (t : ℝ) = 1 := inv_mul_cancel₀ htpos.ne'
  have hsqrt : Real.sqrt (mu : ℝ) * Real.sqrt (t : ℝ) = 1 := by
    rw [← Real.sqrt_mul (by positivity), hmut, Real.sqrt_one]
  have hsqt : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr htpos
  set q : ℝ := 2 / 3 * (1 + ‖x‖) with hq
  have hq0 : 0 ≤ q := by positivity
  set b : ℝ := q / Real.sqrt (t : ℝ) with hb
  have hb0 : 0 ≤ b := by positivity
  set a1 : ℝ := max (LogGrowthBounds.uniformCutoff T (mu : ℝ)) sstar with ha1
  have ha10 : 0 ≤ a1 := le_max_of_le_right hsstar
  set a : ℝ := max a1 b with ha
  have ha0 : 0 ≤ a := le_max_of_le_left ha10
  have hcut1 : 1 ≤ LogGrowthBounds.uniformCutoff T (mu : ℝ) :=
    LogGrowthBounds.one_le_uniformCutoff T _
  have hapos : 0 < a := lt_of_lt_of_le zero_lt_one
    (hcut1.trans ((le_max_left _ _).trans (le_max_left _ _)))
  have hB0 := LogGrowthBounds.uniformBudget_nonneg T
  have hlevel : ∀ s : ℝ, a < s →
      (R.kernelSemigroup t x) {z | s < dist z x / (11 * Real.sqrt (t : ℝ))} ≤
        ENNReal.ofReal (2 * Real.exp 1 *
          LogGrowthBounds.uniformProfile T (mu : ℝ) s) := by
    intro s hsa
    have hs0 : 0 < s := hapos.trans hsa
    have hr : 0 < Real.sqrt (t : ℝ) * s := mul_pos hsqt hs0
    have hscale : Real.sqrt (mu : ℝ) * (Real.sqrt (t : ℝ) * s) = s := by
      rw [← mul_assoc, hsqrt, one_mul]
    have hrs : max (LogGrowthBounds.uniformCutoff T (mu : ℝ)) sstar <
        Real.sqrt (mu : ℝ) * (Real.sqrt (t : ℝ) * s) := by
      rw [hscale]
      exact lt_of_le_of_lt (le_max_left _ _) hsa
    have hbs : b < s := lt_of_le_of_lt (le_max_right _ _) hsa
    have hqr : q ≤ Real.sqrt (t : ℝ) * s := by
      have h1 : q / Real.sqrt (t : ℝ) < s := hbs
      rw [div_lt_iff₀ hsqt] at h1
      linarith only [h1, mul_comm s (Real.sqrt (t : ℝ))]
    have htail := LogGrowthBounds.crudeMom_tail_at T R hcons hid hs mu hmu hmut x hr hrs
    rw [hscale, max_eq_left hqr] at htail
    refine le_trans (measure_mono ?_) htail
    intro z hz
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Metric.mem_ball, not_lt] at hz ⊢
    rw [lt_div_iff₀ (by positivity)] at hz
    nlinarith only [hz, hsqt, hs0]
  have hint : ∫⁻ s in Set.Ioi a, ENNReal.ofReal
      ((2 * Real.exp 1 * LogGrowthBounds.uniformProfile T (mu : ℝ) s) * s ^ 3) ≤
      ENNReal.ofReal (2 * Real.exp 1 * LogGrowthBounds.uniformBudget T) := by
    have h2e : (0 : ℝ) ≤ 2 * Real.exp 1 := by positivity
    have hrw : ∀ s : ℝ, ENNReal.ofReal
        ((2 * Real.exp 1 * LogGrowthBounds.uniformProfile T (mu : ℝ) s) * s ^ 3) =
        ENNReal.ofReal (2 * Real.exp 1) *
          ENNReal.ofReal (LogGrowthBounds.uniformProfile T (mu : ℝ) s * s ^ 3) := by
      intro s
      rw [← ENNReal.ofReal_mul h2e, mul_assoc]
    simp only [hrw]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ENNReal.ofReal_mul h2e]
    gcongr
    calc ∫⁻ s in Set.Ioi a, ENNReal.ofReal
          (LogGrowthBounds.uniformProfile T (mu : ℝ) s * s ^ 3)
        ≤ ∫⁻ s in Set.Ioi (LogGrowthBounds.uniformCutoff T (mu : ℝ)), ENNReal.ofReal
          (LogGrowthBounds.uniformProfile T (mu : ℝ) s * s ^ 3) :=
          lintegral_mono_set (Set.Ioi_subset_Ioi
            ((le_max_left _ _).trans (le_max_left _ _)))
      _ ≤ ENNReal.ofReal (LogGrowthBounds.uniformBudget T) :=
          LogGrowthBounds.lintegral_uniformProfile_mul_cube_le T hmu
  have : IsProbabilityMeasure (R.kernelSemigroup t x) := ⟨hcons t x⟩
  have hcake := crudeMom_lintegral_edist_pow_le (nu := R.kernelSemigroup t x)
    (le_of_eq measure_univ) x (c := 11 * Real.sqrt (t : ℝ)) (by positivity) ha0
    (by positivity : (0 : ℝ) ≤ 2 * Real.exp 1 * LogGrowthBounds.uniformBudget T)
    (psi := fun s ↦ 2 * Real.exp 1 * LogGrowthBounds.uniformProfile T (mu : ℝ) s)
    (fun s ↦ mul_nonneg (by positivity) (LogGrowthBounds.uniformProfile_nonneg T _ _))
    hlevel hint
  refine hcake.trans (ENNReal.ofReal_le_ofReal ?_)
  have hc2 : (11 * Real.sqrt (t : ℝ)) ^ 2 = 121 * (t : ℝ) := by
    rw [mul_pow, Real.sq_sqrt htpos.le]; norm_num
  have hc4 : (11 * Real.sqrt (t : ℝ)) ^ 4 = 14641 * (t : ℝ) ^ 2 := by
    rw [show (11 * Real.sqrt (t : ℝ)) ^ 4 = ((11 * Real.sqrt (t : ℝ)) ^ 2) ^ 2 by ring, hc2]
    ring
  have hcb : (11 * Real.sqrt (t : ℝ)) * b = 11 * q := by
    rw [hb]; field_simp
  have hcutpow : LogGrowthBounds.uniformCutoff T (mu : ℝ) ^ 4 =
      (LogGrowthBounds.uniformScale T * (1 + Real.log ((t : ℝ)⁻¹))) ^ 12 := by
    unfold LogGrowthBounds.uniformCutoff fieldInput_uniformShiftWeight
    rw [← pow_mul]
    have hmax : max (mu : ℝ) 1 = (t : ℝ)⁻¹ := max_eq_left hone
    rw [hmax]
  have ha1p : a1 ^ 4 ≤ LogGrowthBounds.uniformCutoff T (mu : ℝ) ^ 4 + sstar ^ 4 := by
    have h1 : (0 : ℝ) ≤ LogGrowthBounds.uniformCutoff T (mu : ℝ) ^ 4 := by positivity
    have h2 : (0 : ℝ) ≤ sstar ^ 4 := by positivity
    rcases le_total (LogGrowthBounds.uniformCutoff T (mu : ℝ)) sstar with h | h
    · rw [ha1, max_eq_right h]; linarith only [h1]
    · rw [ha1, max_eq_left h]; linarith only [h2]
  have hap : a ^ 4 ≤ a1 ^ 4 + b ^ 4 := by
    have h1 : (0 : ℝ) ≤ a1 ^ 4 := by positivity
    have h2 : (0 : ℝ) ≤ b ^ 4 := by positivity
    rcases le_total a1 b with h | h
    · rw [ha, max_eq_right h]; linarith only [h1]
    · rw [ha, max_eq_left h]; linarith only [h2]
  have hc40 : (0 : ℝ) ≤ 14641 * (t : ℝ) ^ 2 := by positivity
  rw [hc4]
  have hbpow : 14641 * (t : ℝ) ^ 2 * b ^ 4 = 14641 * q ^ 4 := by
    have h1 : ((11 * Real.sqrt (t : ℝ)) * b) ^ 4 = (11 * q) ^ 4 := by rw [hcb]
    rw [mul_pow, hc4] at h1
    rw [h1]; ring
  calc 14641 * (t : ℝ) ^ 2 * (a ^ 4 + 4 * (2 * Real.exp 1 * LogGrowthBounds.uniformBudget T))
      ≤ 14641 * (t : ℝ) ^ 2 * ((LogGrowthBounds.uniformScale T *
          (1 + Real.log ((t : ℝ)⁻¹))) ^ 12 + sstar ^ 4 + b ^ 4 +
            8 * Real.exp 1 * LogGrowthBounds.uniformBudget T) := by
        refine mul_le_mul_of_nonneg_left ?_ hc40
        rw [hcutpow] at ha1p
        linarith only [ha1p, hap]
    _ = 14641 * (((LogGrowthBounds.uniformScale T *
        (1 + Real.log ((t : ℝ)⁻¹))) ^ 12 + sstar ^ 4 +
          8 * Real.exp 1 * LogGrowthBounds.uniformBudget T) * (t : ℝ) ^ 2 +
            (2 / 3 * (1 + ‖x‖)) ^ 4) := by
        have : 14641 * (t : ℝ) ^ 2 * b ^ 4 = 14641 * (2 / 3 * (1 + ‖x‖)) ^ 4 := hbpow
        linarith only [this]

/-! ## All times, qualitatively -/

omit [NeZero d] in
private theorem crudeMom_fourth_split (u v : ℝ) :
    (u + v) ^ 4 ≤ 8 * (u ^ 4 + v ^ 4) := by
  have h2 : (u + v) ^ 2 ≤ 2 * (u ^ 2 + v ^ 2) := by
    nlinarith only [sq_nonneg (u - v)]
  have h3 : ((u + v) ^ 2) ^ 2 ≤ (2 * (u ^ 2 + v ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) h2 2
  have h4 : (2 * (u ^ 2 + v ^ 2)) ^ 2 ≤ 8 * (u ^ 4 + v ^ 4) := by
    nlinarith only [sq_nonneg (u ^ 2 - v ^ 2)]
  calc (u + v) ^ 4 = ((u + v) ^ 2) ^ 2 := by ring
    _ ≤ _ := h3.trans h4

omit [NeZero d] in
private theorem crudeMom_measurable_weight :
    Measurable fun y : Vec d => ENNReal.ofReal ((1 + ‖y‖) ^ 4) :=
  ENNReal.measurable_ofReal.comp (by fun_prop)

/-- **The polynomial moment bound at one time.**  For each time in `(0, 1]` the fourth weighted
moment of the transition law started at `x` is at most a constant times `(1 + |x|) ^ 4`. -/
theorem LogGrowthBounds.crudeMom_exists_poly
    (T : LogGrowthBounds Sp) (R : PositiveC0ContractiveResolvent (Vec d))
    (hcons : R.kernelSemigroup.IsConservative)
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R) {t : ℝ≥0} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vec d,
      ∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ 4) ∂(R.kernelSemigroup t x) ≤
        ENNReal.ofReal (C * (1 + ‖x‖) ^ 4) := by
  obtain ⟨s1, hs1⟩ := Filter.eventually_atTop.1
    ((LogGrowthBounds.tendsto_uniformEnvelope_atTop T).eventually
      (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  have hs : ∀ s, max s1 0 ≤ s → LogGrowthBounds.uniformEnvelope T s ≤ 1 / 2 :=
    fun s h => hs1 s (le_trans (le_max_left _ _) h)
  have hB0 := LogGrowthBounds.uniformBudget_nonneg T
  set X : ℝ := ((LogGrowthBounds.uniformScale T * (1 + Real.log ((t : ℝ)⁻¹))) ^ 12 +
    max s1 0 ^ 4 + 8 * Real.exp 1 * LogGrowthBounds.uniformBudget T) with hX
  have hX0 : 0 ≤ X := by positivity
  refine ⟨8 + 8 * (14641 * (X * (t : ℝ) ^ 2 + 1)), by positivity, fun x => ?_⟩
  have hmom := LogGrowthBounds.crudeMom_fourth_moment_le_one_at T R hcons hid
    (le_max_right s1 0) hs ht0 ht1 x
  have hn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hw1 : (1 : ℝ) ≤ (1 + ‖x‖) ^ 4 := one_le_pow₀ (by linarith only [hn])
  have : IsProbabilityMeasure (R.kernelSemigroup t x) := ⟨hcons t x⟩
  have hpt : ∀ y : Vec d, ENNReal.ofReal ((1 + ‖y‖) ^ 4) ≤
      ENNReal.ofReal (8 * (1 + ‖x‖) ^ 4) + ENNReal.ofReal 8 * edist y x ^ (4 : ℝ) := by
    intro y
    have h1 : 1 + ‖y‖ ≤ (1 + ‖x‖) + ‖y - x‖ := by
      have := norm_le_norm_add_norm_sub' y x
      linarith only [this]
    have h2 : (1 + ‖y‖) ^ 4 ≤ 8 * ((1 + ‖x‖) ^ 4 + ‖y - x‖ ^ 4) :=
      (pow_le_pow_left₀ (by positivity) h1 4).trans
        (crudeMom_fourth_split _ _)
    have he : edist y x ^ (4 : ℝ) = ENNReal.ofReal (‖y - x‖ ^ 4) := by
      rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num),
        show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, dist_eq_norm]
    rw [he, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
      (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith only [h2]
  calc ∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ 4) ∂(R.kernelSemigroup t x)
      ≤ ∫⁻ y, (ENNReal.ofReal (8 * (1 + ‖x‖) ^ 4) +
          ENNReal.ofReal 8 * edist y x ^ (4 : ℝ)) ∂(R.kernelSemigroup t x) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (8 * (1 + ‖x‖) ^ 4) +
          ENNReal.ofReal 8 * ∫⁻ y, edist y x ^ (4 : ℝ) ∂(R.kernelSemigroup t x) := by
        rw [lintegral_add_left measurable_const, lintegral_const,
          measure_univ, mul_one, lintegral_const_mul']
        exact ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (8 * (1 + ‖x‖) ^ 4) + ENNReal.ofReal 8 *
          ENNReal.ofReal (14641 * (X * (t : ℝ) ^ 2 + (2 / 3 * (1 + ‖x‖)) ^ 4)) := by
        gcongr
    _ = ENNReal.ofReal (8 * (1 + ‖x‖) ^ 4 +
          8 * (14641 * (X * (t : ℝ) ^ 2 + (2 / 3 * (1 + ‖x‖)) ^ 4))) := by
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hq : (2 / 3 * (1 + ‖x‖)) ^ 4 ≤ (1 + ‖x‖) ^ 4 := by
          rw [mul_pow]
          have : (2 / 3 : ℝ) ^ 4 ≤ 1 := by norm_num
          nlinarith only [this, hw1]
        have hXt : X * (t : ℝ) ^ 2 ≤ X * (t : ℝ) ^ 2 * (1 + ‖x‖) ^ 4 := by
          have : 0 ≤ X * (t : ℝ) ^ 2 := by positivity
          nlinarith only [this, hw1]
        nlinarith only [hq, hXt, hw1]

/-- **Finite fourth weighted moments at every time.**  Chapman--Kolmogorov and the polynomial
bound at times at most one give, for the process started at the origin, a finite integral of
`(1 + |y|) ^ 4` at every time. -/
theorem LogGrowthBounds.crudeMom_lintegral_weight_lt_top
    (T : LogGrowthBounds Sp) (R : PositiveC0ContractiveResolvent (Vec d))
    (hcons : R.kernelSemigroup.IsConservative)
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R) (t : ℝ≥0) :
    ∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ 4) ∂(R.kernelSemigroup t 0) < ⊤ := by
  have hstep : ∀ u s : ℝ≥0, 0 < s → s ≤ 1 →
      ∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ 4) ∂(R.kernelSemigroup u 0) < ⊤ →
      ∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ 4) ∂(R.kernelSemigroup (u + s) 0) < ⊤ := by
    intro u s hs0 hs1 hu
    obtain ⟨C, hC0, hC⟩ := LogGrowthBounds.crudeMom_exists_poly T R hcons hid hs0 hs1
    rw [R.kernelSemigroup.lintegral_add u s 0 crudeMom_measurable_weight]
    calc ∫⁻ y, ∫⁻ z, ENNReal.ofReal ((1 + ‖z‖) ^ 4) ∂(R.kernelSemigroup s y)
          ∂(R.kernelSemigroup u 0)
        ≤ ∫⁻ y, ENNReal.ofReal C * ENNReal.ofReal ((1 + ‖y‖) ^ 4) ∂(R.kernelSemigroup u 0) := by
          refine lintegral_mono fun y => ?_
          refine (hC y).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_mul hC0]
      _ = ENNReal.ofReal C *
          ∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ 4) ∂(R.kernelSemigroup u 0) :=
          lintegral_const_mul _ crudeMom_measurable_weight
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hu
  have hzero : ∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ 4) ∂(R.kernelSemigroup 0 0) < ⊤ := by
    have h0 : R.kernelSemigroup 0 (0 : Vec d) = Measure.dirac 0 := by
      rw [R.kernelSemigroup.zero]
      rfl
    rw [h0, lintegral_dirac' _ crudeMom_measurable_weight]
    exact ENNReal.ofReal_lt_top
  have hall : ∀ n : ℕ, ∀ u : ℝ≥0, u ≤ n →
      ∫⁻ y, ENNReal.ofReal ((1 + ‖y‖) ^ 4) ∂(R.kernelSemigroup u 0) < ⊤ := by
    intro n
    induction n with
    | zero =>
        intro u hu
        have : u = 0 := by
          simpa only [Nat.cast_zero, nonpos_iff_eq_zero] using hu
        rw [this]
        exact hzero
    | succ n ih =>
        intro u hu
        by_cases h1 : u ≤ 1
        · rcases eq_zero_or_pos u with h0 | hpos
          · rw [h0]
            exact hzero
          · have := hstep 0 u hpos h1 hzero
            rwa [zero_add] at this
        · replace h1 := not_le.mp h1
          have hle : (1 : ℝ≥0) ≤ u := h1.le
          have hu' : u - 1 ≤ n := by
            have : u ≤ (n : ℝ≥0) + 1 := by exact_mod_cast hu
            exact tsub_le_iff_right.2 this
          have := hstep (u - 1) 1 one_pos le_rfl (ih (u - 1) hu')
          rwa [tsub_add_cancel_of_le hle] at this
  obtain ⟨n, hn⟩ := exists_nat_ge t
  exact hall n t hn

omit [NeZero d] in
private theorem crudeMom_vecNormSq_le (y : Vec d) :
    vecNormSq y ≤ (d : ℝ) * (1 + ‖y‖) ^ 4 := by
  have hn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
  have hcoord : ∀ i : Fin d, y i * y i ≤ ‖y‖ ^ 2 := fun i => by
    have h := norm_le_pi_norm y i
    rw [Real.norm_eq_abs] at h
    have h2 : |y i| ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs] at h2
    linarith only [h2, sq (y i)]
  have hsum : vecNormSq y ≤ (d : ℝ) * ‖y‖ ^ 2 := by
    unfold vecNormSq vecDot
    calc ∑ i, y i * y i ≤ ∑ _i : Fin d, ‖y‖ ^ 2 := Finset.sum_le_sum fun i _ => hcoord i
      _ = (d : ℝ) * ‖y‖ ^ 2 := by simp
  have h2 : ‖y‖ ^ 2 ≤ (1 + ‖y‖) ^ 4 := by
    have h1 : ‖y‖ ^ 2 ≤ (1 + ‖y‖) ^ 2 := pow_le_pow_left₀ hn (by linarith only) 2
    have h3 : (1 + ‖y‖) ^ 2 ≤ ((1 + ‖y‖) ^ 2) ^ 2 :=
      le_self_pow₀ (by nlinarith only [hn]) (by norm_num)
    calc ‖y‖ ^ 2 ≤ (1 + ‖y‖) ^ 2 := h1
      _ ≤ ((1 + ‖y‖) ^ 2) ^ 2 := h3
      _ = (1 + ‖y‖) ^ 4 := by ring
  calc vecNormSq y ≤ (d : ℝ) * ‖y‖ ^ 2 := hsum
    _ ≤ (d : ℝ) * (1 + ‖y‖) ^ 4 :=
        mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg d)

/-- **Integrability of the squared length at every time.**  The squared Euclidean length is
integrable under the transition law started at the origin, at every time. -/
theorem LogGrowthBounds.crudeMom_integrable_vecNormSq
    (T : LogGrowthBounds Sp) (R : PositiveC0ContractiveResolvent (Vec d))
    (hcons : R.kernelSemigroup.IsConservative)
    (hid : A.KernelResolventIdentifiesAnalyticMinimal R) (t : ℝ≥0) :
    Integrable (fun y : Vec d => vecNormSq y) (R.kernelSemigroup t 0) := by
  have hcont : Continuous fun y : Vec d => vecNormSq y := by
    unfold vecNormSq vecDot
    fun_prop
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  have hfin := LogGrowthBounds.crudeMom_lintegral_weight_lt_top T R hcons hid t
  have hnn : ∀ y : Vec d, 0 ≤ vecNormSq y := fun y => by
    unfold vecNormSq vecDot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hconst : ∫⁻ y, ENNReal.ofReal (d : ℝ) * ENNReal.ofReal ((1 + ‖y‖) ^ 4)
      ∂(R.kernelSemigroup t 0) < ⊤ := by
    rw [lintegral_const_mul _ crudeMom_measurable_weight]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  have hbound : ∫⁻ y, ‖vecNormSq y‖ₑ ∂(R.kernelSemigroup t 0) ≤
      ∫⁻ y, ENNReal.ofReal (d : ℝ) * ENNReal.ofReal ((1 + ‖y‖) ^ 4)
        ∂(R.kernelSemigroup t 0) := by
    refine lintegral_mono fun y => ?_
    rw [Real.enorm_eq_ofReal (hnn y), ← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
    exact ENNReal.ofReal_le_ofReal (crudeMom_vecNormSq_le y)
  exact lt_of_le_of_lt hbound hconst

/-- **The squared length of the marginal-field process is integrable at every time.** -/
theorem fieldMoment_integrable_vecNormSq {nu : ℝ} {k : Vec d → Mat d} (D : FieldInputData d nu k)
    (t : ℝ≥0) :
    Integrable (fun y : Vec d => vecNormSq y)
      (D.logGrowthBounds.resolvent.kernelSemigroup t 0) :=
  D.logGrowthBounds.crudeMom_integrable_vecNormSq D.logGrowthBounds.resolvent
    D.logGrowthBounds.isConservative_kernelSemigroup
    D.logGrowthBounds.kernelResolventIdentifiesAnalyticMinimal t

/-- The integrability holds for the Dirac zero law, at every time. -/
example (hd : 2 ≤ d) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∃ D : FieldInputData d nu (fullStreamRecentered omega), ∀ t : ℝ≥0,
        Integrable (fun y : Vec d => vecNormSq y)
          (D.logGrowthBounds.resolvent.kernelSemigroup t 0) := by
  filter_upwards [fieldInput_ae_data
    (SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw hd)
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw hnu] with omega hD
  obtain ⟨D⟩ := hD
  exact ⟨D, fieldMoment_integrable_vecNormSq D⟩

end

end SuperdiffusionCLT.Section8
