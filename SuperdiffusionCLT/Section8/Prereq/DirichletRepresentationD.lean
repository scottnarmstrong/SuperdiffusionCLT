/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.DirichletRepresentationC
public import SuperdiffusionCLT.Section8.Prereq.ProcessUniquenessC
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.ExitMeanValueLimit
public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusionApi
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.StoppedDirichletHarmonic

/-!
# Stochastic representation of the zero-trace Dirichlet problem on a ball

For the process of `∇·(ν Id + k)∇` started at `x` in a Euclidean ball `B` and a bounded
nonnegative measurable observable `f`,

  `E^x ∫₀^{T_B} f(X_s) ds = w(x)`,

where `w` is continuous on the whole space, vanishes off `B`, and is the `H¹₀(B)` weak solution of
`-∇·(a∇w) = f`.  The case `f = 1` is the expected exit time, finite and equal to the torsion
function.  Both hold for every continuous-path law `Q` of the kernel semigroup of the process
input, and, almost surely for the marginal field `fullCoefficientRecentered nu omega`, for every
conservative divergence-form Feller semigroup and every continuous-path law of it.

* `dirRep_zero_trace`, `dirRep_mean_exit`: the deterministic statements;
* `dirRep_ae_spec_eq`, `dirRep_ae_mean_exit`: the almost-sure statements.

For a boundary datum `b` of class `C²` with compact support (affine and quadratic data are
`b = χ ℓ`, `b = χ |x|²` with a cutoff `χ` equal to one near the closed ball):

* `dirRep_hasExitMeanValueOn`: the solution `b + w` of the Dirichlet problem with trace `b`, `w`
  the zero-trace solution of `-∇·(a∇w) = ∇·(a∇b)`, is reproduced by the exit position of the
  compactified process (the form of `HasExitMeanValueOn`, as on translated cubes);
* `dirRep_boundary`: `E^y[(b + w)(X_{T_B})] = b(y) + w(y)` on paths of `ℝ^d`;
* `dirRep_stopped`: the finite-horizon form, with the torsion correction;
* `dirRep_ae_boundary`: the almost-sure form for every specification semigroup and every
  continuous-path law.
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

/-- The time integral of the survival indicator is the exit time. -/
theorem dirRep_lintegral_survival (tau : ℝ≥0∞) :
    ∫⁻ t in Set.Ioi (0 : ℝ), {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau}.indicator
      (fun _ => ENNReal.ofReal (1 : ℝ)) t = tau := by
  have hS : MeasurableSet {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau} :=
    measurableSet_lt (measurable_coe_nnreal_ennreal.comp measurable_real_toNNReal)
      measurable_const
  rw [lintegral_indicator hS, setLIntegral_const, ENNReal.ofReal_one, one_mul,
    Measure.restrict_apply hS, ContinuousPath.survivalSet tau]
  by_cases htop : tau = ⊤
  · rw [ite_eq_left_iff.mpr (fun h => absurd htop h), htop, Real.volume_Ioi]
  · rw [ite_eq_right_iff.mpr (fun h => absurd h htop), Real.volume_Ioo, sub_zero,
      ENNReal.ofReal_toReal htop]

/-- **The expected occupation before the exit time is the zero-trace solution.**  For a bounded
nonnegative measurable `f`, there is a continuous function `w`, vanishing off the ball, which is
the `H¹₀(B)` weak solution of `-∇·(a∇w) = f` and satisfies, for every continuous-path law of the
kernel semigroup and every starting point `x` in the ball,
`E^x ∫₀^{T_B} f(X_s) ds = w(x)`. -/
theorem dirRep_zero_trace (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {f : Vec d → ℝ}
    (hf : Measurable f) {M : ℝ} (hfM : ∀ y, |f y| ≤ M) (hf0 : ∀ y, 0 ≤ f y) :
    ∃ (w : Vec d → ℝ) (u : H10Function (euclideanBall x₀ r)), Continuous w ∧
      (∀ y, y ∉ euclideanBall x₀ r → w y = 0) ∧ (∀ y, 0 ≤ w y) ∧
      (∀ᵐ y ∂volumeMeasureOn (euclideanBall x₀ r), w y = u.toH1Function.toFun y) ∧
      IsScalarForcedWeakSolution D.analyticData.a (euclideanBall x₀ r) f u.toH1Function ∧
      ∀ {Q : Vec d → Measure (ContinuousPath (Vec d))},
        IsContinuousPathLaw D.logGrowthBounds.resolvent.kernelSemigroup Q →
        ∀ {x : Vec d}, x ∈ euclideanBall x₀ r →
        ∫⁻ path, (∫⁻ t in Set.Ioi (0 : ℝ), {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) <
            ContinuousPath.exitTime (euclideanBall x₀ r) path}.indicator
          (fun t => ENNReal.ofReal (f (path (Real.toNNReal t)))) t) ∂(Q x) =
          ENNReal.ofReal (w x) := by
  obtain ⟨u, hu1, hu2⟩ := dirRep_h10_solution D x₀ hr hf hfM hf0
  exact ⟨dirRep_limit D x₀ hr hf hfM, u, dirRep_limit_continuous D x₀ hr hf hfM hf0,
    fun y hy => dirRep_limit_off D x₀ hr hf hfM hy,
    dirRep_limit_nonneg D x₀ hr hf hfM hf0, hu1, hu2,
    fun {Q} hQ {x} hx => dirRep_lintegral_limit D x₀ hr hf hfM hf0 hQ hx⟩

/-- **The expected exit time from a ball.**  There is a continuous function `w`, vanishing off the
ball, which is the `H¹₀(B)` weak solution of `-∇·(a∇w) = 1`, such that for every continuous-path
law of the kernel semigroup and every starting point `x` in the ball, `E^x[T_B] = w(x)`; in
particular the expected exit time is finite. -/
theorem dirRep_mean_exit (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    ∃ (w : Vec d → ℝ) (u : H10Function (euclideanBall x₀ r)), Continuous w ∧
      (∀ y, y ∉ euclideanBall x₀ r → w y = 0) ∧ (∀ y, 0 ≤ w y) ∧
      (∀ᵐ y ∂volumeMeasureOn (euclideanBall x₀ r), w y = u.toH1Function.toFun y) ∧
      IsScalarForcedWeakSolution D.analyticData.a (euclideanBall x₀ r) (fun _ => 1)
        u.toH1Function ∧
      ∀ {Q : Vec d → Measure (ContinuousPath (Vec d))},
        IsContinuousPathLaw D.logGrowthBounds.resolvent.kernelSemigroup Q →
        ∀ {x : Vec d}, x ∈ euclideanBall x₀ r →
        ∫⁻ path, ContinuousPath.exitTime (euclideanBall x₀ r) path ∂(Q x) =
          ENNReal.ofReal (w x) := by
  obtain ⟨w, u, hc, hoff, hnn, hwu, hsol, hQ⟩ := dirRep_zero_trace D x₀ hr
    (f := fun _ => (1 : ℝ)) measurable_const (M := 1) (fun _ => by simp) (fun _ => zero_le_one)
  refine ⟨w, u, hc, hoff, hnn, hwu, hsol, fun {Q} hQ' {x} hx => ?_⟩
  rw [← hQ hQ' hx]
  refine lintegral_congr fun path => ?_
  exact (dirRep_lintegral_survival _).symm

open ProbabilityTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section6
open scoped Matrix.Norms.Elementwise

/-- **Every specification semigroup of the marginal field is the kernel semigroup of the process
input.**  Almost surely, the data of `FieldInputData` exist, and every divergence-form Feller
semigroup is the kernel semigroup of their resolvent. -/
theorem dirRep_ae_spec_eq {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      ∃ D : FieldInputData d nu (fullStreamRecentered omega),
        D.analyticData.a = fullCoefficientRecentered nu omega ∧
        ∀ S : SubMarkovKernelSemigroup (Vec d),
          IsDivergenceFormFeller (fullCoefficientRecentered nu omega) S →
            S = D.logGrowthBounds.resolvent.kernelSemigroup := by
  filter_upwards [fieldInput_ae_data hPrefix hJ3 hnu,
    fieldReg_ae_contDiff_two_fullStreamRecentered hJ3] with omega hD hreg
  obtain ⟨D⟩ := hD
  refine ⟨D, rfl, fun S hS => ?_⟩
  have h2 : ContDiff ℝ 2 (fullCoefficientRecentered nu omega) := contDiff_const.add hreg
  have ha : ∀ i j, ContDiff ℝ 2 fun y ↦ D.analyticData.a y i j := fun i j ↦
    contDiff_pi.1 (contDiff_pi.1 h2 i) j
  exact procUniq_kernelSemigroup_eq (fullCoefficientRecentered nu omega)
    D.logGrowthBounds.resolvent
    (fun mu g hg hc => procUniq_hreg D.analyticData ha
      D.logGrowthBounds.kernelResolventIdentifiesAnalyticMinimal mu g hg hc) hS

/-- **Almost surely: the expected exit time from a ball is finite and is the torsion function.**
Almost every sample of the marginal field has the following property.  For every ball `B` there
is a continuous `w`, vanishing off `B`, which is the `H¹₀(B)` weak solution of `-∇·(a∇w) = 1`, and
for every conservative divergence-form Feller semigroup `S` and continuous-path law `Q` of `S`,
`E^x[T_B] = w(x)` for `x` in `B`. -/
theorem dirRep_ae_mean_exit {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      ∀ (x₀ : Vec d) {r : ℝ}, 0 < r →
      ∃ (w : Vec d → ℝ) (u : H10Function (euclideanBall x₀ r)), Continuous w ∧
        (∀ y, y ∉ euclideanBall x₀ r → w y = 0) ∧ (∀ y, 0 ≤ w y) ∧
        (∀ᵐ y ∂volumeMeasureOn (euclideanBall x₀ r), w y = u.toH1Function.toFun y) ∧
        IsScalarForcedWeakSolution (fullCoefficientRecentered nu omega) (euclideanBall x₀ r)
          (fun _ => 1) u.toH1Function ∧
        ∀ (S : SubMarkovKernelSemigroup (Vec d))
          (Q : Vec d → Measure (ContinuousPath (Vec d))),
          IsDivergenceFormFeller (fullCoefficientRecentered nu omega) S →
          IsContinuousPathLaw S Q → ∀ {x : Vec d}, x ∈ euclideanBall x₀ r →
          ∫⁻ path, ContinuousPath.exitTime (euclideanBall x₀ r) path ∂(Q x) =
            ENNReal.ofReal (w x) := by
  filter_upwards [dirRep_ae_spec_eq (d := d) hPrefix hJ3 hnu] with omega hω
  obtain ⟨D, hDa, hS⟩ := hω
  intro x₀ r hr
  obtain ⟨w, u, hc, hoff, hnn, hwu, hsol, hQ⟩ := dirRep_mean_exit D x₀ hr
  refine ⟨w, u, hc, hoff, hnn, hwu, hDa ▸ hsol, fun S Q hS' hQ' {x} hx => ?_⟩
  have hSeq := hS S hS'
  subst hSeq
  exact hQ hQ' hx

/-! ## Satisfiability witnesses -/

/-- The statements are met for the law concentrated on the zero shell sequence (the constant field
`ν Id`): a conservative divergence-form Feller semigroup with a continuous-path law exists, and the
conclusions of the almost-sure theorems hold for it. -/
example (hd : 2 ≤ d) (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      (∃ (S : SubMarkovKernelSemigroup (Vec d)) (Q : Vec d → Measure (ContinuousPath (Vec d))),
        IsDivergenceFormFeller (fullCoefficientRecentered nu omega) S ∧ IsContinuousPathLaw S Q) ∧
      ∀ (x₀ : Vec d) {r : ℝ}, 0 < r →
      ∃ (w : Vec d → ℝ) (u : H10Function (euclideanBall x₀ r)), Continuous w ∧
        (∀ y, y ∉ euclideanBall x₀ r → w y = 0) ∧ (∀ y, 0 ≤ w y) ∧
        (∀ᵐ y ∂volumeMeasureOn (euclideanBall x₀ r), w y = u.toH1Function.toFun y) ∧
        IsScalarForcedWeakSolution (fullCoefficientRecentered nu omega) (euclideanBall x₀ r)
          (fun _ => 1) u.toH1Function ∧
        ∀ (S : SubMarkovKernelSemigroup (Vec d))
          (Q : Vec d → Measure (ContinuousPath (Vec d))),
          IsDivergenceFormFeller (fullCoefficientRecentered nu omega) S →
          IsContinuousPathLaw S Q → ∀ {x : Vec d}, x ∈ euclideanBall x₀ r →
          ∫⁻ path, ContinuousPath.exitTime (euclideanBall x₀ r) path ∂(Q x) =
            ENNReal.ofReal (w x) := by
  have hP := SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw (d := d) hd
  have hJ := SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw (d := d)
  filter_upwards [domId_ae_exists_process hP hJ hnu, dirRep_ae_mean_exit hP hJ hnu] with omega h1 h2
  obtain ⟨S, Q, hS, hQ⟩ := h1
  exact ⟨⟨S, Q, hS, hQ⟩, h2⟩

omit [NeZero d] in
theorem dirRep_divForm_eq_zero_of_notMem {a : CoeffField d} {b : Vec d → ℝ} {z : Vec d}
    (hz : z ∉ tsupport b) : divForm 1 a b z = 0 := by
  have h : b =ᶠ[𝓝 z] fun _ => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.mp hz
  rw [divForm_congr_of_eventuallyEq 1 (a := a) (a' := a) Filter.EventuallyEq.rfl h]
  simp [divForm]

theorem dirRep_entries_contDiff : ∀ i j, ContDiff ℝ 1 fun y => D.analyticData.a y i j := fun i j => by
  have h : (fun y => D.analyticData.a y i j) = fun y => (nu • (1 : Mat d)) i j + k y i j := by
    funext y; rfl
  rw [h]
  exact contDiff_const.add (D.contDiff_entry i j)

/-- **The exit mean-value property on a ball.**  For a boundary datum `b` of class `C²` with compact
support, there is a continuous `w`, vanishing off the ball, which is the `H¹₀` weak solution of
`-∇·(a∇w) = ∇·(a∇b)` (so that `b + w` is the `H¹` solution with trace `b`), such that the
compactified process started at any point of the ball reproduces `b + w` through its exit
position. -/
theorem dirRep_hasExitMeanValueOn (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {b : Vec d → ℝ}
    (hb : ContDiff ℝ 2 b) (hbc : HasCompactSupport b) :
    ∃ (w : Vec d → ℝ) (u : H10Function (euclideanBall x₀ r)), Continuous w ∧
      (∀ y, y ∉ euclideanBall x₀ r → w y = 0) ∧
      (∀ᵐ y ∂volumeMeasureOn (euclideanBall x₀ r), w y = u.toH1Function.toFun y) ∧
      IsScalarForcedWeakSolution D.analyticData.a (euclideanBall x₀ r)
        (divForm 1 D.analyticData.a b) u.toH1Function ∧
      let hreg := D.logGrowthBounds.processInput.toOnePointRegular
      let := hreg.metricSpace
      let := hreg.completeSpace
      HasExitMeanValueOn D.logGrowthBounds.resolvent.onePointKernelSemigroup
        D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall x₀ r)
        (onePointRealExtension (fun z => b z + w z)) := by
  have ha := dirRep_entries_contDiff D
  have hV := dirRep_ball x₀ hr
  set A := D.analyticData with hA
  let bC : C₀(Vec d, ℝ) := ⟨⟨b, hb.continuous⟩, hbc.is_zero_at_infty⟩
  have hvc : Continuous (divForm 1 A.a b) := domId_divForm_continuous ha hb
  have hvs : HasCompactSupport (divForm 1 A.a b) :=
    HasCompactSupport.intro hbc (fun z hz => dirRep_divForm_eq_zero_of_notMem hz)
  let vC : C₀(Vec d, ℝ) := ⟨⟨divForm 1 A.a b, hvc⟩, hvs.is_zero_at_infty⟩
  have hbM : ∀ z, |b z| ≤ ‖bC‖ := dirRep_c0_abs_le bC
  have hvM : ∀ z, |divForm 1 A.a b z| ≤ ‖vC‖ := dirRep_c0_abs_le vC
  have hbm : Measurable b := hb.continuous.measurable
  obtain ⟨w, u, hwc, hwoff, hwu, hsol, hlim⟩ := dirRep_signed D x₀ hr hvc.measurable hvM
  obtain ⟨Bd, hBd0, hBd⟩ := dirRep_abs_resolvent_le D x₀ hr
  refine ⟨w, u, hwc, hwoff, hwu, hsol, ?_⟩
  intro hreg hm hc
  have hUopen : IsOpen (((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall x₀ r) :=
    OnePoint.isOpen_image_coe.mpr hV.isOpen
  refine hasExitMeanValueOn_of_tendsto_discountedExitAverage
    D.logGrowthBounds.resolvent.onePointKernelSemigroup
    D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup hreg.kolmogorovRegular
    hUopen (psi := onePointRealExtension b) (measurable_onePointRealExtension hbm)
    (M := ‖bC‖) (fun z => by
      rw [Real.norm_eq_abs]; exact abs_onePointRealExtension_le (norm_nonneg _) hbM z)
    (fun y' hy' => by
      obtain ⟨z, hz, rfl⟩ := hy'
      exact dirRep_expectedExitTime_ne_top D x₀ hr hz)
    (mu := 1) one_pos
    (val := fun lam => onePointRealExtension (fun z => b z - lam *
      dirRep_resolventAt D x₀ hr hbm hbM lam z +
      dirRep_resolventAt D x₀ hr hvc.measurable hvM lam z))
    (h := onePointRealExtension (fun z => b z + w z)) ?_ ?_ ?_
  · intro lam hlam y' hy'
    obtain ⟨z, hz, rfl⟩ := hy'
    have hlam0 : 0 < lam := hlam.1
    set m : PositiveShift := ⟨lam, Set.mem_Ioi.mpr hlam0⟩ with hm'
    let F : C₀(Vec d, ℝ) := (m : ℝ) • bC - vC
    have hop : D.logGrowthBounds.resolvent.toContractiveResolvent.operator m F = bC :=
      domId_operator_eq A ha D.logGrowthBounds.kernelResolventIdentifiesAnalyticMinimal m bC vC hb
        (fun x => rfl)
    have hE := dirRep_decomp_signed D x₀ hr m F hz
    dsimp only at hE
    simp only [hop] at hE
    have hFfun : ∀ z', F z' = lam * b z' + (-1 : ℝ) * divForm 1 A.a b z' := fun z' => by
      show (m : ℝ) * b z' - divForm 1 A.a b z' = _
      show lam * b z' - divForm 1 A.a b z' = _
      ring
    have hlb : ∀ z', |lam * b z'| ≤ |lam| * ‖bC‖ := fun z' => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hbM z') (abs_nonneg _)
    have hcb : ∀ z', |(-1 : ℝ) * divForm 1 A.a b z'| ≤ |(-1 : ℝ)| * ‖vC‖ := fun z' => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hvM z') (abs_nonneg _)
    have hsum : ∀ z', |lam * b z' + (-1 : ℝ) * divForm 1 A.a b z'| ≤
        |lam| * ‖bC‖ + |(-1 : ℝ)| * ‖vC‖ := fun z' =>
      (abs_add_le _ _).trans (add_le_add (hlb z') (hcb z'))
    have hmeas : Measurable fun z' => lam * b z' + (-1 : ℝ) * divForm 1 A.a b z' :=
      (hbm.const_smul lam).add (hvc.measurable.const_smul (-1 : ℝ))
    have hlin : A.partC0Resolvent hV m (fun z' => lam * b z' + (-1 : ℝ) * divForm 1 A.a b z')
        hmeas hsum z =
        A.partC0Resolvent hV m (fun z' => lam * b z') (hbm.const_smul lam) hlb z +
        (-1 : ℝ) * A.partC0Resolvent hV m (divForm 1 A.a b) hvc.measurable hvM z :=
      A.partC0Resolvent_add_const_mul hV m (-1 : ℝ) (hbm.const_smul lam) hvc.measurable hlb hvM
        hmeas hsum z
    have hsm : A.partC0Resolvent hV m (fun z' => lam * b z') (hbm.const_smul lam) hlb z =
        lam * A.partC0Resolvent hV m b hbm hbM z :=
      A.partC0Resolvent_smul hV m lam hbm hbM hlb z
    have hswap : A.partC0Resolvent hV m F F.continuous.measurable (D := ‖F‖)
        (dirRep_c0_abs_le F) z =
        A.partC0Resolvent hV m (fun z' => lam * b z' + (-1 : ℝ) * divForm 1 A.a b z')
          hmeas hsum z :=
      A.partC0Resolvent_eq_of_eqOn hV m F.continuous.measurable hmeas (dirRep_c0_abs_le F) hsum
        (fun z' _ => hFfun z') z
    have hRb : dirRep_resolventAt D x₀ hr hbm hbM lam z =
        A.partC0Resolvent hV m b hbm hbM z := by
      simp only [dirRep_resolventAt, hlam0, ↓reduceDIte]
      rfl
    have hRv : dirRep_resolventAt D x₀ hr hvc.measurable hvM lam z =
        A.partC0Resolvent hV m (divForm 1 A.a b) hvc.measurable hvM z := by
      simp only [dirRep_resolventAt, hlam0, ↓reduceDIte]
      rfl
    show _ = b z - lam * dirRep_resolventAt D x₀ hr hbm hbM lam z +
      dirRep_resolventAt D x₀ hr hvc.measurable hvM lam z
    rw [hRb, hRv]
    replace hE : b z = A.partC0Resolvent hV m F F.continuous.measurable (D := ‖F‖)
        (dirRep_c0_abs_le F) z +
      discountedExitAverage D.logGrowthBounds.resolvent.onePointKernelSemigroup
        D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall x₀ r) lam (onePointRealExtension b)
        (z : OnePoint (Vec d)) := hE
    rw [hswap, hlin, hsm] at hE
    have key : discountedExitAverage D.logGrowthBounds.resolvent.onePointKernelSemigroup
        D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
        (((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall x₀ r) lam (onePointRealExtension b)
        (z : OnePoint (Vec d)) = b z - lam * A.partC0Resolvent hV m b hbm hbM z +
          A.partC0Resolvent hV m (divForm 1 A.a b) hvc.measurable hvM z := by
      linarith only [hE]
    exact key
  · intro y' hy'
    induction y' using OnePoint.rec with
    | infty => simp
    | coe z =>
      have hzB : z ∉ euclideanBall x₀ r := fun hzB => hy' ⟨z, hzB, rfl⟩
      show b z + w z = b z
      rw [hwoff z hzB, add_zero]
  · intro y' hy'
    obtain ⟨z, hz, rfl⟩ := hy'
    show Tendsto (fun lam : ℝ => b z - lam * dirRep_resolventAt D x₀ hr hbm hbM lam z +
      dirRep_resolventAt D x₀ hr hvc.measurable hvM lam z) (𝓝[>] (0 : ℝ)) (𝓝 (b z + w z))
    have h1 : Tendsto (fun lam : ℝ => lam * dirRep_resolventAt D x₀ hr hbm hbM lam z)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hid : Tendsto (fun lam : ℝ => lam) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        (tendsto_id (x := 𝓝 (0 : ℝ))).mono_left nhdsWithin_le_nhds
      refine squeeze_zero_norm' (a := fun lam : ℝ => lam * (‖bC‖ * Bd)) ?_ (by
        simpa using hid.mul_const (‖bC‖ * Bd))
      filter_upwards [self_mem_nhdsWithin] with lam hlam
      have hlam0 : (0 : ℝ) < lam := hlam
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos hlam0]
      refine mul_le_mul_of_nonneg_left ?_ hlam0.le
      simp only [dirRep_resolventAt, hlam0, ↓reduceDIte]
      rw [Real.norm_eq_abs]
      exact hBd _ hbm hbM z
    have h2 := (tendsto_const_nhds (x := b z)).sub h1
    have h3 := h2.add (hlim z)
    simpa using h3

open SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.LiveRestriction in
/-- **Boundary values by exit position.**  For a boundary datum `b` of class `C²` with compact
support, there is a continuous `w`, vanishing off the ball, which is the `H¹₀` weak solution of
`-∇·(a∇w) = ∇·(a∇b)`, such that for every continuous-path law `Q` of the kernel semigroup and
every starting point `y` in the ball, `E^y[(b + w)(X_{T_B})] = b(y) + w(y)`.  Thus `b + w` is the
solution of the Dirichlet problem with boundary values `b` and zero right-hand side, represented
by the process. -/
theorem dirRep_boundary (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {b : Vec d → ℝ}
    (hb : ContDiff ℝ 2 b) (hbc : HasCompactSupport b) :
    ∃ (w : Vec d → ℝ) (u : H10Function (euclideanBall x₀ r)), Continuous w ∧
      (∀ y, y ∉ euclideanBall x₀ r → w y = 0) ∧
      (∀ᵐ y ∂volumeMeasureOn (euclideanBall x₀ r), w y = u.toH1Function.toFun y) ∧
      IsScalarForcedWeakSolution D.analyticData.a (euclideanBall x₀ r)
        (divForm 1 D.analyticData.a b) u.toH1Function ∧
      ∀ {Q : Vec d → Measure (ContinuousPath (Vec d))},
        IsContinuousPathLaw D.logGrowthBounds.resolvent.kernelSemigroup Q →
        ∀ {y : Vec d}, y ∈ euclideanBall x₀ r →
        ∫ path, (b + w) (path ((ContinuousPath.exitTime (euclideanBall x₀ r) path).toNNReal))
          ∂(Q y) = b y + w y := by
  obtain ⟨w, u, hwc, hwoff, hwu, hsol, hME⟩ := dirRep_hasExitMeanValueOn D x₀ hr hb hbc
  refine ⟨w, u, hwc, hwoff, hwu, hsol, fun {Q} hQ {y} hy => ?_⟩
  have hmap := ballExit_map_pathPostcomp_eq D hQ y
  have hME' := hME (y : OnePoint (Vec d)) ⟨y, hy, rfl⟩
  let := D.logGrowthBounds.processInput.toOnePointRegular.metricSpace
  let := D.logGrowthBounds.processInput.toOnePointRegular.completeSpace
  have hemb : MeasurableEmbedding (pathPostcomp (liveEmbedding (Vec d))) :=
    (continuous_pathPostcomp (liveEmbedding (Vec d))).measurableEmbedding
      (procConstr_injective_pathPostcomp OnePoint.isOpenEmbedding_coe.isEmbedding)
  dsimp only at hmap hME'
  have hpt : ∀ path : ContinuousPath (Vec d),
      onePointRealExtension (fun z => b z + w z)
        (exitPosition (((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall x₀ r)
          (pathPostcomp (liveEmbedding (Vec d)) path)) =
      (b + w) (path ((ContinuousPath.exitTime (euclideanBall x₀ r) path).toNNReal)) := by
    intro path
    have hexit : ContinuousPath.exitTime (((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall x₀ r)
        (pathPostcomp (liveEmbedding (Vec d)) path) =
        ContinuousPath.exitTime (euclideanBall x₀ r) path :=
      exitTime_image_pathPostcomp (liveEmbedding (Vec d)) injective_liveCoe _ path
    unfold exitPosition
    erw [hexit]
    rfl
  have hint := hemb.integral_map (fun ω' : ContinuousPath (OnePoint (Vec d)) =>
    onePointRealExtension (fun z => b z + w z)
      (exitPosition (((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall x₀ r) ω')) (μ := Q y)
  rw [hmap] at hint
  have hcongr : ∫ path, (b + w) (path ((ContinuousPath.exitTime (euclideanBall x₀ r) path).toNNReal))
      ∂(Q y) = ∫ path, onePointRealExtension (fun z => b z + w z)
        (exitPosition (((↑) : Vec d → OnePoint (Vec d)) '' euclideanBall x₀ r)
          (pathPostcomp (liveEmbedding (Vec d)) path)) ∂(Q y) :=
    integral_congr_ae (Filter.Eventually.of_forall fun path => (hpt path).symm)
  rw [hcongr]
  exact hint.symm.trans hME'

open SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.LiveRestriction in
/-- **The stopped identity at a deterministic horizon.**  For a boundary datum `b` of class `C²`
with compact support, with `w` as in `dirRep_boundary` and `τ` the torsion function of the ball,
every continuous-path law `Q` of the kernel semigroup, every starting point `y` in the ball, every
horizon `t` and every `σ`,
`E^y[(b + w - σ τ)(X_{t ∧ T_B})] = (b + w - σ τ)(y) + σ E^y[t ∧ T_B]`.
For `σ = 0` this says that `b + w` is a martingale up to the exit time, in expectation; for
`σ = 1` it is the finite-horizon identity used with the quadratic datum. -/
theorem dirRep_stopped (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {b : Vec d → ℝ}
    (hb : ContDiff ℝ 2 b) (hbc : HasCompactSupport b) :
    ∃ (w : Vec d → ℝ) (u : H10Function (euclideanBall x₀ r)), Continuous w ∧
      (∀ y, y ∉ euclideanBall x₀ r → w y = 0) ∧
      (∀ᵐ y ∂volumeMeasureOn (euclideanBall x₀ r), w y = u.toH1Function.toFun y) ∧
      IsScalarForcedWeakSolution D.analyticData.a (euclideanBall x₀ r)
        (divForm 1 D.analyticData.a b) u.toH1Function ∧
      ∀ {Q : Vec d → Measure (ContinuousPath (Vec d))},
        IsContinuousPathLaw D.logGrowthBounds.resolvent.kernelSemigroup Q →
        ∀ {y : Vec d}, y ∈ euclideanBall x₀ r → ∀ (t : NNReal) (σ : ℝ),
        ∫ path, (fun z => b z + w z - σ * dirRep_torsion D x₀ hr z)
            (path (ContinuousPath.exitTimeTrunc (euclideanBall x₀ r) t path)) ∂(Q y) =
          (b y + w y - σ * dirRep_torsion D x₀ hr y) +
            σ * ∫ path, ((ContinuousPath.exitTimeTrunc (euclideanBall x₀ r) t path : NNReal) : ℝ)
              ∂(Q y) := by
  obtain ⟨w, u, hwc, hwoff, hwu, hsol, hME⟩ := dirRep_hasExitMeanValueOn D x₀ hr hb hbc
  refine ⟨w, u, hwc, hwoff, hwu, hsol, fun {Q} hQ {y} hy t σ => ?_⟩
  have hmap := ballExit_map_pathPostcomp_eq D hQ y
  let := D.logGrowthBounds.processInput.toOnePointRegular.metricSpace
  let := D.logGrowthBounds.processInput.toOnePointRegular.completeSpace
  have hemb : MeasurableEmbedding (pathPostcomp (liveEmbedding (Vec d))) :=
    (continuous_pathPostcomp (liveEmbedding (Vec d))).measurableEmbedding
      (procConstr_injective_pathPostcomp OnePoint.isOpenEmbedding_coe.isEmbedding)
  dsimp only at hmap hME
  have hV := dirRep_ball x₀ hr
  set B := euclideanBall x₀ r with hB
  have hUopen : IsOpen (((↑) : Vec d → OnePoint (Vec d)) '' B) :=
    OnePoint.isOpen_image_coe.mpr hV.isOpen
  have hUR : B ⊆ Metric.closedBall x₀ r :=
    (euclideanBall_subset_metricBall hr).trans Metric.ball_subset_closedBall
  have hwsupp : HasCompactSupport w :=
    HasCompactSupport.intro (isCompact_closedBall x₀ r) fun z hz =>
      hwoff z (fun hzB => hz (hUR hzB))
  obtain ⟨Cb, hCb⟩ := hbc.exists_bound_of_continuous hb.continuous
  obtain ⟨Cw, hCw⟩ := hwsupp.exists_bound_of_continuous hwc
  have hCh : ∀ y' : OnePoint (Vec d),
      ‖onePointRealExtension (fun z => b z + w z) y'‖ ≤ Cb + Cw := by
    intro y'
    induction y' using OnePoint.rec with
    | infty =>
      simp only [onePointRealExtension_infty, norm_zero]
      exact add_nonneg ((norm_nonneg _).trans (hCb 0)) ((norm_nonneg _).trans (hCw 0))
    | coe z =>
      simp only [onePointRealExtension_coe]
      exact (norm_add_le _ _).trans (add_le_add (hCb z) (hCw z))
  have hhm : Measurable (onePointRealExtension (fun z => b z + w z)) :=
    measurable_onePointRealExtension (hb.continuous.measurable.add hwc.measurable)
  have hwfin := dirRep_expectedExitTime_ne_top D x₀ hr hy
  dsimp only at hwfin
  have hKol := D.logGrowthBounds.processInput.toOnePointRegular.kolmogorovRegular
  have hu : ∀ y' : OnePoint (Vec d),
      onePointRealExtension (fun z => b z + w z - σ * dirRep_torsion D x₀ hr z) y' =
        onePointRealExtension (fun z => b z + w z) y' - σ *
          (expectedExitTime D.logGrowthBounds.resolvent.onePointKernelSemigroup
            D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
            (((↑) : Vec d → OnePoint (Vec d)) '' B) y').toReal := by
    intro y'
    induction y' using OnePoint.rec with
    | infty =>
      have h0 : expectedExitTime D.logGrowthBounds.resolvent.onePointKernelSemigroup
          D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
          (((↑) : Vec d → OnePoint (Vec d)) '' B) OnePoint.infty = 0 :=
        expectedExitTime_eq_zero_of_notMem
          D.logGrowthBounds.resolvent.onePointKernelSemigroup
          D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup hKol
          (U := ((↑) : Vec d → OnePoint (Vec d)) '' B) (y := OnePoint.infty)
          OnePoint.infty_notMem_image_coe
      rw [h0]; simp
    | coe z =>
      by_cases hz : z ∈ B
      · have h1 := dirRep_expectedExitTime_eq D x₀ hr hz
        dsimp only at h1
        rw [h1]
        change _ = _ - σ * (ENNReal.ofReal (dirRep_torsion D x₀ hr z)).toReal
        rw [ENNReal.toReal_ofReal (dirRep_torsion_nonneg D x₀ hr z)]
        simp only [onePointRealExtension_coe]
      · have hzU : (z : OnePoint (Vec d)) ∉ ((↑) : Vec d → OnePoint (Vec d)) '' B := fun h => by
          obtain ⟨z', hz', hzz'⟩ := h
          exact hz (by rwa [← OnePoint.coe_injective hzz'])
        have h0 : expectedExitTime D.logGrowthBounds.resolvent.onePointKernelSemigroup
            D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
            (((↑) : Vec d → OnePoint (Vec d)) '' B) (z : OnePoint (Vec d)) = 0 :=
          expectedExitTime_eq_zero_of_notMem
            D.logGrowthBounds.resolvent.onePointKernelSemigroup
            D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup hKol hzU
        rw [h0]
        simp only [onePointRealExtension_coe, ENNReal.toReal_zero, mul_zero, sub_zero,
          dirRep_torsion_off D x₀ hr hz]
  have hmain := integral_eval_exitTimeTrunc_eq_add_of_hasExitMeanValueOn
    D.logGrowthBounds.resolvent.onePointKernelSemigroup
    D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
    D.logGrowthBounds.resolvent.isFellerKernelSemigroup_onePointKernelSemigroup hKol hUopen hhm
    (Cb + Cw) hCh hME σ hu t (x := (y : OnePoint (Vec d))) ⟨y, hy, rfl⟩ hwfin
  have htrunc : ∀ path : ContinuousPath (Vec d),
      ContinuousPath.exitTimeTrunc (((↑) : Vec d → OnePoint (Vec d)) '' B) t
        (pathPostcomp (liveEmbedding (Vec d)) path) = ContinuousPath.exitTimeTrunc B t path := by
    intro path
    have hexit : ContinuousPath.exitTime (((↑) : Vec d → OnePoint (Vec d)) '' B)
        (pathPostcomp (liveEmbedding (Vec d)) path) = ContinuousPath.exitTime B path :=
      exitTime_image_pathPostcomp (liveEmbedding (Vec d)) injective_liveCoe _ path
    apply ENNReal.coe_injective
    rw [ContinuousPath.coe_exitTimeTrunc_ennreal, ContinuousPath.coe_exitTimeTrunc_ennreal]
    exact congrArg (fun e => min e (t : ℝ≥0∞)) hexit
  set uf : Vec d → ℝ := fun z => b z + w z - σ * dirRep_torsion D x₀ hr z with huf
  have hF : ∀ path : ContinuousPath (Vec d),
      onePointRealExtension uf
        ((pathPostcomp (liveEmbedding (Vec d)) path)
          (ContinuousPath.exitTimeTrunc (((↑) : Vec d → OnePoint (Vec d)) '' B) t
            (pathPostcomp (liveEmbedding (Vec d)) path))) =
      uf (path (ContinuousPath.exitTimeTrunc B t path)) := by
    intro path
    rw [htrunc path, pathPostcomp_apply]
    rfl
  have hI1 : ∫ path, uf (path (ContinuousPath.exitTimeTrunc B t path)) ∂(Q y) =
      ∫ ω', onePointRealExtension uf
        (ω' (ContinuousPath.exitTimeTrunc (((↑) : Vec d → OnePoint (Vec d)) '' B) t ω'))
        ∂(IsConservative.continuousProcess D.logGrowthBounds.resolvent.onePointKernelSemigroup
          D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
          (y : OnePoint (Vec d))) := by
    have hint := hemb.integral_map (fun ω' : ContinuousPath (OnePoint (Vec d)) =>
      onePointRealExtension uf
        (ω' (ContinuousPath.exitTimeTrunc (((↑) : Vec d → OnePoint (Vec d)) '' B) t ω')))
      (μ := Q y)
    rw [hmap] at hint
    refine Eq.trans ?_ hint.symm
    exact integral_congr_ae (Filter.Eventually.of_forall fun path => (hF path).symm)
  have hI2 : ∫ path, ((ContinuousPath.exitTimeTrunc B t path : NNReal) : ℝ) ∂(Q y) =
      ∫ ω', ((ContinuousPath.exitTimeTrunc (((↑) : Vec d → OnePoint (Vec d)) '' B) t ω' :
          NNReal) : ℝ)
        ∂(IsConservative.continuousProcess D.logGrowthBounds.resolvent.onePointKernelSemigroup
          D.logGrowthBounds.resolvent.isConservative_onePointKernelSemigroup
          (y : OnePoint (Vec d))) := by
    have hint := hemb.integral_map (fun ω' : ContinuousPath (OnePoint (Vec d)) =>
      ((ContinuousPath.exitTimeTrunc (((↑) : Vec d → OnePoint (Vec d)) '' B) t ω' : NNReal) : ℝ))
      (μ := Q y)
    rw [hmap] at hint
    refine Eq.trans ?_ hint.symm
    exact integral_congr_ae (Filter.Eventually.of_forall fun path => congrArg (fun e : NNReal => (e : ℝ)) (htrunc path).symm)
  rw [hI1, hI2]
  exact hmain

omit [NeZero d] in
/-- Boundary data of the admissible class exist: a smooth compactly supported bump equal to one at
the origin. -/
theorem dirRep_exists_boundaryDatum :
    ∃ b : Vec d → ℝ, ContDiff ℝ 2 b ∧ HasCompactSupport b ∧ b 0 = 1 := by
  let φ : ContDiffBump (0 : Vec d) := ⟨1, 2, one_pos, one_lt_two⟩
  exact ⟨φ, φ.contDiff, φ.hasCompactSupport,
    φ.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)⟩

/-- **Almost surely: boundary values by exit position, for every specification semigroup and
every continuous-path law.**  Almost every sample of the marginal field has the following
property.  For every ball `B` and every boundary datum `b` of class `C²` with compact support there
is a continuous `w`, vanishing off `B`, which is the `H¹₀(B)` weak solution of
`-∇·(a∇w) = ∇·(a∇b)` for `a = fullCoefficientRecentered nu omega`, and for every conservative
divergence-form Feller semigroup `S` and continuous-path law `Q` of `S`,
`E^y[(b + w)(X_{T_B})] = b(y) + w(y)` for `y` in `B`. -/
theorem dirRep_ae_boundary {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      ∀ (x₀ : Vec d) {r : ℝ} {b : Vec d → ℝ}, 0 < r → ContDiff ℝ 2 b → HasCompactSupport b →
      ∃ (w : Vec d → ℝ) (u : H10Function (euclideanBall x₀ r)), Continuous w ∧
        (∀ y, y ∉ euclideanBall x₀ r → w y = 0) ∧
        (∀ᵐ y ∂volumeMeasureOn (euclideanBall x₀ r), w y = u.toH1Function.toFun y) ∧
        IsScalarForcedWeakSolution (fullCoefficientRecentered nu omega) (euclideanBall x₀ r)
          (divForm 1 (fullCoefficientRecentered nu omega) b) u.toH1Function ∧
        ∀ (S : SubMarkovKernelSemigroup (Vec d))
          (Q : Vec d → Measure (ContinuousPath (Vec d))),
          IsDivergenceFormFeller (fullCoefficientRecentered nu omega) S →
          IsContinuousPathLaw S Q → ∀ {y : Vec d}, y ∈ euclideanBall x₀ r →
          ∫ path, (b + w) (path ((ContinuousPath.exitTime (euclideanBall x₀ r) path).toNNReal))
            ∂(Q y) = b y + w y := by
  filter_upwards [dirRep_ae_spec_eq (d := d) hPrefix hJ3 hnu] with omega hω
  obtain ⟨D, hDa, hS⟩ := hω
  intro x₀ r b hr hb hbc
  obtain ⟨w, u, hc, hoff, hwu, hsol, hQ⟩ := dirRep_boundary D x₀ hr hb hbc
  refine ⟨w, u, hc, hoff, hwu, hDa ▸ hsol, fun S Q hS' hQ' {y} hy => ?_⟩
  have hSeq := hS S hS'
  subst hSeq
  exact hQ hQ' hy

/-! ## Satisfiability witnesses -/

/-- The hypotheses of the boundary theorems are met, and the conclusion is not vacuous: for the
law concentrated on the zero shell sequence there is a conservative divergence-form Feller
semigroup with a continuous-path law, a nonzero admissible datum `b` (with `b 0 = 1`) exists, and
the boundary identity holds for the unit ball and every such semigroup and law. -/
example (hd : 2 ≤ d) (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      (∃ (S : SubMarkovKernelSemigroup (Vec d)) (Q : Vec d → Measure (ContinuousPath (Vec d))),
        IsDivergenceFormFeller (fullCoefficientRecentered nu omega) S ∧ IsContinuousPathLaw S Q) ∧
      ∃ b : Vec d → ℝ, ContDiff ℝ 2 b ∧ HasCompactSupport b ∧ b 0 = 1 ∧
      ∃ (w : Vec d → ℝ) (u : H10Function (euclideanBall (0 : Vec d) 1)), Continuous w ∧
        (∀ y, y ∉ euclideanBall (0 : Vec d) 1 → w y = 0) ∧
        (∀ᵐ y ∂volumeMeasureOn (euclideanBall (0 : Vec d) 1), w y = u.toH1Function.toFun y) ∧
        IsScalarForcedWeakSolution (fullCoefficientRecentered nu omega) (euclideanBall (0 : Vec d) 1)
          (divForm 1 (fullCoefficientRecentered nu omega) b) u.toH1Function ∧
        ∀ (S : SubMarkovKernelSemigroup (Vec d))
          (Q : Vec d → Measure (ContinuousPath (Vec d))),
          IsDivergenceFormFeller (fullCoefficientRecentered nu omega) S →
          IsContinuousPathLaw S Q → ∀ {y : Vec d}, y ∈ euclideanBall (0 : Vec d) 1 →
          ∫ path, (b + w) (path ((ContinuousPath.exitTime (euclideanBall (0 : Vec d) 1)
            path).toNNReal)) ∂(Q y) = b y + w y := by
  have hP := SuperdiffusionCLT.Assumptions.ShellLaw.shellLawPrefix_diracZeroLaw (d := d) hd
  have hJ := SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw (d := d)
  filter_upwards [domId_ae_exists_process hP hJ hnu, dirRep_ae_boundary hP hJ hnu] with omega h1 h2
  obtain ⟨S, Q, hS, hQ⟩ := h1
  obtain ⟨b, hb, hbc, hb0⟩ := dirRep_exists_boundaryDatum (d := d)
  exact ⟨⟨S, Q, hS, hQ⟩, b, hb, hbc, hb0, h2 (0 : Vec d) one_pos hb hbc⟩

end
end SuperdiffusionCLT.Section8
