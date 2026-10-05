/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.FieldProcessInputE
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.CruxGeneralDomainTail
public import SuperdiffusionCLT.Section8.DivergenceForm.WholeSpace.PenalizedNormalizedTail

/-!
# Fixed-collar localized penalization tails for the marginal field

The collar used by exterior penalization is fixed once the killed cube is
fixed.  Hence the point-dependent algebraic amplitude and decay rate of the
localized tail, which have polynomial and logarithmic envelopes by the
logarithmic-growth bounds, have finite uniform bounds on that collar.  This
produces a single positive-rate log-subexponential error which tends to zero
as the penalization mass grows.  The comparison uses the localized split-skew
tail and has no global small-contrast input.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.DivergenceForm

open Filter Homogenization MeasureTheory Set Topology
open SuperdiffusionCLT.Section8.Common.Regularity.Ported
open MarkovProcess.Semigroup
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- A coefficient-generic comparison driven by a localized tail bound which is
uniform on the fixed collar.  No small-contrast datum is assumed. -/
theorem analyticPenalizedCube_le_next_add_localizedTail_of_subset
    (L : WholeSpaceLocalizedSplitData A) (tailError : ℝ)
    (htailError : 0 ≤ tailError) {V : Set (Vec d)} (hV : IsOpen V)
    (v : ℕ) (hVcube : V ⊆ wholeSpaceCube d v) (n k : ℕ) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, |f x| ≤ 1)
    (hfsupp : ∀ᵐ x ∂volume, x ∉ V → f x = 0)
    (htailUniform : ∀ y ∈ wholeSpaceCube d (v + 1),
      L.tail ⟨(mu : ℝ) + n, Set.mem_Ioi.mpr
        (add_pos_of_pos_of_nonneg mu.property (Nat.cast_nonneg n))⟩ y 1 ≤ tailError)
    {x : Vec d} (hx : x ∈ wholeSpaceCube d v) :
    A.analyticPenalizedCubeResolvent hV n mu f hf hf1 (k + (v + 2)) x ≤
      A.analyticPenalizedCubeResolvent hV n mu f hf hf1 (v + 1) x +
        tailError / (mu : ℝ) := by
  let m := v + 1
  let outer := k + (v + 2)
  let U := wholeSpaceCube d m
  let W := wholeSpaceCube d outer
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
  let hW := isOpenBoundedConvexDomain_wholeSpaceCube d outer
  have hmouter : m ≤ outer := by
    dsimp only [m, outer]
    omega
  have hUW : U ⊆ W := wholeSpaceCube_mono hmouter
  let q := wholeSpacePenalizationPotential V n
  let zU := A.penalizedCubeResolventH10 hV n mu hf hf1 m
  let zW := A.penalizedCubeResolventH10 hV n mu hf hf1 outer
  let u0 : H1Function U := zW.toH1Function.restrict hU.isOpen hUW
  let uRep : Vec d → ℝ := U.indicator
    (A.analyticPenalizedCubeResolvent hV n mu f hf hf1 outer)
  let wRep : Vec d → ℝ := U.indicator
    (A.analyticPenalizedCubeResolvent hV n mu f hf hf1 m)
  have hzWae := A.penalizedCubeResolventH10_ae_eq hV n mu hf hf1 outer
  have huRepAe : uRep =ᵐ[volumeMeasureOn U] u0.toFun := by
    filter_upwards [ae_restrict_mem hU.isOpen.measurableSet,
      ae_restrict_of_ae_restrict_of_subset hUW hzWae] with y hyU hy
    simpa only [uRep, Set.indicator_of_mem hyU, u0, H1Function.restrict] using hy.symm
  have hzUae := A.penalizedCubeResolventH10_ae_eq hV n mu hf hf1 m
  have hwRepAe : wRep =ᵐ[volumeMeasureOn U] zU.toH1Function.toFun := by
    filter_upwards [ae_restrict_mem hU.isOpen.measurableSet, hzUae]
      with y hyU hy
    simpa only [wRep, Set.indicator_of_mem hyU] using hy.symm
  let u := h1FunctionWithAeRepresentative u0 uRep huRepAe
  let w := h1FunctionWithAeRepresentative zU.toH1Function wRep hwRepAe
  let FW : ScalarL2 W := boundedMeasurableToScalarL2 hW
    (hf.comp measurable_subtype_coe) (fun y ↦ hf1 y)
  let FU : ScalarL2 U := boundedMeasurableToScalarL2 hU
    (hf.comp measurable_subtype_coe) (fun y ↦ hf1 y)
  have hzWsol := A.penalizedCubeResolventH10_isScalarForcedWeakSolution
    hV n mu hf hf1 outer
  have hzWres := hzWsol.restrictToOpen hW.isOpen hU.isOpen hUW
  have hFWae := ae_restrict_of_ae_restrict_of_subset hUW
    (boundedMeasurableToScalarL2_wholeSpaceCube_ae_eq hf hf1 outer)
  have hsourceW : (fun y ↦ f y - ((mu : ℝ) + q y) * uRep y) =ᵐ[
      volumeMeasureOn U]
      fun y ↦ FW y - ((mu : ℝ) + q y) * u0.toFun y := by
    filter_upwards [hFWae, huRepAe] with y hFy huy
    rw [hFy, huy]
  have husol : IsScalarForcedWeakSolution A.a U
      (fun y ↦ f y - ((mu : ℝ) + q y) * u.toFun y) u := by
    refine hzWres.withAeRepresentative
      (g' := fun y ↦ f y - ((mu : ℝ) + q y) * uRep y)
      uRep huRepAe ?_
    exact hsourceW
  have hzUsol := A.penalizedCubeResolventH10_isScalarForcedWeakSolution
    hV n mu hf hf1 m
  have hFUae := boundedMeasurableToScalarL2_wholeSpaceCube_ae_eq hf hf1 m
  have hsourceU : (fun y ↦ f y - ((mu : ℝ) + q y) * wRep y) =ᵐ[
      volumeMeasureOn U]
      fun y ↦ FU y - ((mu : ℝ) + q y) * zU.toH1Function.toFun y := by
    filter_upwards [hFUae, hwRepAe] with y hFy hwy
    rw [hFy, hwy]
  have hwsol : IsScalarForcedWeakSolution A.a U
      (fun y ↦ f y - ((mu : ℝ) + q y) * w.toFun y) w := by
    refine hzUsol.withAeRepresentative
      (g' := fun y ↦ f y - ((mu : ℝ) + q y) * wRep y)
      wRep hwRepAe ?_
    simpa only [q, FU, zU, U, hU] using hsourceU
  have hdiff := isScalarForcedWeakSolution_sub_same_potential
    (A.cubeEllipticity m) q f u w husol hwsol
  let eps := tailError / (mu : ℝ)
  have heps : 0 ≤ eps := div_nonneg htailError mu.property.le
  have hucont : ContinuousOn u.toFun U := by
    change ContinuousOn uRep U
    refine ((A.continuousOn_analyticPenalizedCubeResolvent hV n mu hf hf1
      outer).mono hUW).congr ?_
    intro y hy
    simpa only [uRep] using Set.indicator_of_mem hy
      (A.analyticPenalizedCubeResolvent hV n mu f hf hf1 outer)
  have hwcont : ContinuousOn w.toFun U := by
    change ContinuousOn wRep U
    refine (A.continuousOn_analyticPenalizedCubeResolvent hV n mu hf hf1
      m).congr ?_
    intro y hy
    simpa only [wRep] using Set.indicator_of_mem hy
      (A.analyticPenalizedCubeResolvent hV n mu f hf hf1 m)
  have hcollar : ∀ y, y ∉ interchangeCollar d v →
      u.toFun y ≤ w.toFun y + eps := by
    intro y hyK
    change uRep y ≤ wRep y + eps
    by_cases hyU : y ∈ U
    · have hballU : euclideanBall y 1 ⊆ W :=
        (unitBall_subset_wholeSpaceCube_succ (d := d) hyU).trans
          (wholeSpaceCube_mono (by dsimp only [m, outer]; omega))
      have htailLocal := A.mul_abs_analyticPenalizedCubeResolvent_le_localizedTail L
        hV n mu hf hf1 hfsupp outer (by norm_num) hballU
        (disjoint_unitBall_of_subset_wholeSpaceCube hVcube hyK)
      have htail := htailLocal.trans (htailUniform y hyU)
      have habs : |A.analyticPenalizedCubeResolvent hV n mu f hf hf1
          outer y| ≤ eps := by
        apply (le_div_iff₀ mu.property).2
        simpa only [eps, mul_one, one_mul, mul_comm] using htail
      have hinner0 := A.analyticPenalizedCubeResolvent_nonneg hV n mu hf
        hf0 hf1 m y
      simp only [uRep, wRep, Set.indicator_of_mem hyU]
      exact (le_abs_self _).trans (habs.trans (le_add_of_nonneg_left hinner0))
    · simp only [uRep, wRep, Set.indicator_of_notMem hyU, zero_add]
      exact heps
  have hle := le_add_of_homogeneous_difference_boundary hU mu.property heps
    (A.cubeEllipticity m)
    (Filter.Eventually.of_forall fun y ↦
      wholeSpacePenalizationPotential_nonneg V n y)
    u w hucont hwcont hdiff (isCompact_interchangeCollar d v)
    (interchangeCollar_subset_wholeSpaceCube_succ d v) hcollar x
    (interchangeCollar_subset_wholeSpaceCube_succ d v
      (wholeSpaceCube_subset_interchangeCollar d v hx))
  have hxU : x ∈ U := interchangeCollar_subset_wholeSpaceCube_succ d v
    (wholeSpaceCube_subset_interchangeCollar d v hx)
  change uRep x ≤ wRep x + eps at hle
  simpa only [uRep, wRep, Set.indicator_of_mem hxU, m, outer, eps, U] using hle

end WholeSpaceAnalyticData

end

end SuperdiffusionCLT.Section8.DivergenceForm



namespace SuperdiffusionCLT.Section8

open Filter Homogenization MeasureTheory Set Topology
open SuperdiffusionCLT.Section8.DivergenceForm MarkovProcess.Semigroup
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d] {A : WholeSpaceAnalyticData d} {Sp : WholeSpaceLocalizedSplitData A}

/-- A uniform ambient-norm bound on the next exhaustion cube. -/
def fieldFixedCollarNormBound (v : ℕ) : ℝ := (3 : ℝ) ^ (v + 1)

theorem fieldFixedCollarNormBound_nonneg (v : ℕ) :
    0 ≤ fieldFixedCollarNormBound v := by
  unfold fieldFixedCollarNormBound
  positivity

omit [NeZero d] in
theorem norm_le_fieldFixedCollarNormBound {v : ℕ} {x : Vec d}
    (hx : x ∈ wholeSpaceCube d (v + 1)) :
    ‖x‖ ≤ fieldFixedCollarNormBound v := by
  rw [pi_norm_le_iff_of_nonneg (fieldFixedCollarNormBound_nonneg v)]
  intro i
  rw [Real.norm_eq_abs]
  simpa only [fieldFixedCollarNormBound] using
    (abs_lt.mpr (mem_wholeSpaceCube_iff.mp hx i)).le

namespace LogGrowthBounds

/-- A uniform amplitude for localized tails whose centers lie in the next
exhaustion cube. -/
def fixedCollarTailAmplitude (T : LogGrowthBounds Sp) (v : ℕ) : ℝ :=
  amplitudeConst T *
    (1 + fieldFixedCollarNormBound v) ^ amplitudeExponent T

/-- A uniform positive decay rate for localized tails whose centers lie in
the next exhaustion cube. -/
def fixedCollarTailRate (T : LogGrowthBounds Sp) (v : ℕ) : ℝ :=
  decayConst T / (1 + Real.log (1 + fieldFixedCollarNormBound v))

/-- The uniform fixed-collar error profile. -/
def fixedCollarTailProfile (T : LogGrowthBounds Sp) (v : ℕ) : ℝ → ℝ :=
  logSubexponentialProfile (fixedCollarTailAmplitude T v)
    (fixedCollarTailRate T v) (d + 1)

theorem fixedCollarTailAmplitude_nonneg (T : LogGrowthBounds Sp) (v : ℕ) :
    0 ≤ fixedCollarTailAmplitude T v := by
  unfold fixedCollarTailAmplitude
  have hbase : 0 ≤ 1 + fieldFixedCollarNormBound v := by
    exact add_nonneg zero_le_one (fieldFixedCollarNormBound_nonneg v)
  exact mul_nonneg (amplitudeConst_nonneg T)
    (Real.rpow_nonneg hbase _)

theorem fixedCollarTailRate_pos (T : LogGrowthBounds Sp) (v : ℕ) :
    0 < fixedCollarTailRate T v := by
  unfold fixedCollarTailRate
  apply div_pos (decayConst_pos T)
  have hlog := Real.log_nonneg (show
    1 ≤ 1 + fieldFixedCollarNormBound v by
      exact le_add_of_nonneg_right (fieldFixedCollarNormBound_nonneg v))
  linarith only [hlog]

/-- On the next exhaustion cube the pointwise localized profile is bounded
by the fixed-collar profile. -/
theorem tailProfile_le_fixedCollar
    (T : LogGrowthBounds Sp) (v : ℕ)
    {x : Vec d} (hx : x ∈ wholeSpaceCube d (v + 1)) (s : ℝ) :
    tailProfile Sp x s ≤ fixedCollarTailProfile T v s := by
  let qx : ℝ := 1 + ‖x‖
  let Q : ℝ := 1 + fieldFixedCollarNormBound v
  have hq : 0 < qx := by unfold qx; positivity
  have hQ : 0 < Q := by
    unfold Q
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (fieldFixedCollarNormBound_nonneg v)
  have hqQ : qx ≤ Q := by
    unfold qx Q
    simpa only [add_comm] using
      add_le_add_left (norm_le_fieldFixedCollarNormBound hx) 1
  have hp : 0 ≤ amplitudeExponent T := by
    unfold amplitudeExponent
    exact add_nonneg zero_le_one
      (mul_nonneg (Nat.cast_nonneg d) T.expo_pos.le)
  have hpow : qx ^ amplitudeExponent T ≤ Q ^ amplitudeExponent T :=
    Real.rpow_le_rpow hq.le hqQ hp
  have hamp : algebraicAmplitude Sp x ≤ fixedCollarTailAmplitude T v := by
    calc
      algebraicAmplitude Sp x ≤ amplitudeConst T * qx ^ amplitudeExponent T :=
        algebraicAmplitude_le T x
      _ ≤ amplitudeConst T * Q ^ amplitudeExponent T :=
        mul_le_mul_of_nonneg_left hpow (amplitudeConst_nonneg T)
      _ = fixedCollarTailAmplitude T v := rfl
  have hlog : Real.log qx ≤ Real.log Q :=
    Real.strictMonoOn_log.monotoneOn hq hQ hqQ
  have hdenx : 0 < 1 + Real.log qx := by
    have := Real.log_nonneg (show 1 ≤ qx by
      unfold qx
      exact le_add_of_nonneg_right (norm_nonneg x))
    linarith only [this]
  have hrate0 : fixedCollarTailRate T v ≤ decayConst T / (1 + Real.log qx) := by
    change decayConst T / (1 + Real.log Q) ≤ decayConst T / (1 + Real.log qx)
    exact div_le_div_of_nonneg_left (decayConst_pos T).le
      hdenx (by simpa only [add_comm] using add_le_add_left hlog 1)
  have hrate : fixedCollarTailRate T v ≤ decayRate Sp x :=
    hrate0.trans (decayRate_ge T x)
  have hs0 : 0 ≤ max s 0 := le_max_right _ _
  have hdenS : 0 < 1 + Real.log (1 + max s 0) := by
    have hlogS := Real.log_nonneg
      (le_add_of_nonneg_right (show 0 ≤ max s 0 from hs0))
    linarith only [hlogS]
  have hexp : Real.exp
      (-decayRate Sp x * max s 0 /
        (1 + Real.log (1 + max s 0))) ≤
      Real.exp (-fixedCollarTailRate T v * max s 0 /
        (1 + Real.log (1 + max s 0))) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_right hrate hs0
    have hneg : -decayRate Sp x * max s 0 ≤
        -fixedCollarTailRate T v * max s 0 := by
      simpa only [neg_mul] using neg_le_neg hmul
    exact div_le_div_of_nonneg_right hneg hdenS.le
  unfold tailProfile fixedCollarTailProfile logSubexponentialProfile
  have hpoly : 0 ≤ (1 + max s 0) ^ (d + 1) := pow_nonneg (by positivity) _
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right hamp hpoly) hexp (Real.exp_pos _).le
    (mul_nonneg (fixedCollarTailAmplitude_nonneg T v) hpoly)

end LogGrowthBounds

private theorem logWeight_le_five_mul_sqrt_cruxField {s : ℝ} (hs : 1 ≤ s) :
    1 + Real.log (1 + s) ≤ 5 * Real.sqrt s := by
  have hs0 : 0 ≤ s := zero_le_one.trans hs
  have hsqrt1 : 1 ≤ Real.sqrt s := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hs
  have hlog := Real.log_le_rpow_div (show 0 ≤ 1 + s by positivity)
    (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [← Real.sqrt_eq_rpow] at hlog
  have hsqrt : Real.sqrt (1 + s) ≤ 2 * Real.sqrt s := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt hs0]
      nlinarith only [hs]
  have hlog' : Real.log (1 + s) ≤ 4 * Real.sqrt s := by
    calc
      Real.log (1 + s) ≤ Real.sqrt (1 + s) / (1 / 2 : ℝ) := hlog
      _ = 2 * Real.sqrt (1 + s) := by ring
      _ ≤ 4 * Real.sqrt s := by linarith only [hsqrt]
  linarith only [hlog', hsqrt1]

/-- Every positive-rate fixed-collar profile tends to zero at infinity. -/
theorem LogGrowthBounds.tendsto_fixedCollarTailProfile_atTop
    (T : LogGrowthBounds Sp) (v : ℕ) :
    Tendsto (LogGrowthBounds.fixedCollarTailProfile T v) atTop (nhds 0) := by
  let C := LogGrowthBounds.fixedCollarTailAmplitude T v
  let c := LogGrowthBounds.fixedCollarTailRate T v
  let n := d + 1
  have hC : 0 ≤ C := LogGrowthBounds.fixedCollarTailAmplitude_nonneg T v
  have hc : 0 < c := LogGrowthBounds.fixedCollarTailRate_pos T v
  have hsqrtTop : Tendsto Real.sqrt atTop atTop := by
    simpa only [← Real.sqrt_eq_rpow] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2))
  have hbase := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((2 * n : ℕ) : ℝ) (c / 5) (div_pos hc (by norm_num))
  have hcomp := hbase.comp hsqrtTop
  have hmajor : Tendsto (fun s : ℝ ↦
      (C * 2 ^ n) *
        ((Real.sqrt s) ^ (2 * n) * Real.exp (-(c / 5) * Real.sqrt s)))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, Real.rpow_natCast, mul_zero] using hcomp.const_mul (C * 2 ^ n)
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    exact logSubexponentialProfile_nonneg hC c n s
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hs0 : 0 ≤ s := zero_le_one.trans hs
    have hpoly : (1 + s) ^ n ≤ (2 * s) ^ n :=
      pow_le_pow_left₀ (by positivity) (by linarith only [hs]) n
    have hratio : Real.sqrt s / 5 ≤ s / (1 + Real.log (1 + s)) := by
      have hden : 0 < 1 + Real.log (1 + s) := by
        have := Real.log_nonneg (by linarith only [hs] : 1 ≤ 1 + s)
        linarith only [this]
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 5) hden]
      simpa only [mul_comm] using (show
          Real.sqrt s * (1 + Real.log (1 + s)) ≤ 5 * s by
        calc
          Real.sqrt s * (1 + Real.log (1 + s)) ≤
              Real.sqrt s * (5 * Real.sqrt s) :=
            mul_le_mul_of_nonneg_left (logWeight_le_five_mul_sqrt_cruxField hs)
              (Real.sqrt_nonneg s)
          _ = 5 * s := by rw [show Real.sqrt s * (5 * Real.sqrt s) =
              5 * Real.sqrt s ^ 2 by ring, Real.sq_sqrt hs0])
    have hexp : Real.exp (-c * s / (1 + Real.log (1 + s))) ≤
        Real.exp (-(c / 5) * Real.sqrt s) := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hratio hc.le
      calc
        -c * s / (1 + Real.log (1 + s)) =
            -(c * (s / (1 + Real.log (1 + s)))) := by ring
        _ ≤ -(c * (Real.sqrt s / 5)) := neg_le_neg hmul
        _ = -(c / 5) * Real.sqrt s := by ring
    have hsqrtPow : (Real.sqrt s) ^ (2 * n) = s ^ n := by
      rw [pow_mul, Real.sq_sqrt hs0]
    change logSubexponentialProfile C c n s ≤
      (C * 2 ^ n) *
        ((Real.sqrt s) ^ (2 * n) * Real.exp (-(c / 5) * Real.sqrt s))
    unfold logSubexponentialProfile
    rw [max_eq_left hs0]
    calc
      C * (1 + s) ^ n * Real.exp (-c * s / (1 + Real.log (1 + s))) ≤
          C * (2 * s) ^ n * Real.exp (-(c / 5) * Real.sqrt s) := by
        gcongr
      _ = (C * 2 ^ n) *
          ((Real.sqrt s) ^ (2 * n) * Real.exp (-(c / 5) * Real.sqrt s)) := by
        rw [mul_pow, hsqrtPow]
        ring


end

end SuperdiffusionCLT.Section8


namespace SuperdiffusionCLT.Section8

open Filter Homogenization MeasureTheory Set Topology
open SuperdiffusionCLT.Section8.DivergenceForm MarkovProcess.Semigroup
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d] {A : WholeSpaceAnalyticData d} {Sp : WholeSpaceLocalizedSplitData A}

namespace LogGrowthBounds

/-- At sufficiently large penalization mass, the localized tail on a unit ball centered in the
fixed collar is controlled by one uniform profile. -/
theorem tail_unit_le_fixedCollar
    (T : LogGrowthBounds Sp) (v n : ℕ)
    (mu : PositiveShift) {y : Vec d} (hy : y ∈ wholeSpaceCube d (v + 1))
    (hsqrt : 1 < Real.sqrt ((mu : ℝ) + n)) :
    Sp.tail
        ⟨(mu : ℝ) + n, Set.mem_Ioi.mpr
          (add_pos_of_pos_of_nonneg mu.property (Nat.cast_nonneg n))⟩ y 1 ≤
      fixedCollarTailProfile T v (Real.sqrt ((mu : ℝ) + n)) := by
  let mass : ℝ := (mu : ℝ) + n
  have hmass0 : 0 < mass :=
    add_pos_of_pos_of_nonneg mu.property (Nat.cast_nonneg n)
  let massShift : PositiveShift := ⟨mass, Set.mem_Ioi.mpr hmass0⟩
  have hmassOne : 1 ≤ mass := by
    have hsquare := Real.sq_sqrt hmass0.le
    nlinarith only [hsqrt, hsquare]
  have hsqrt0 : Real.sqrt mass ≠ 0 := (Real.sqrt_pos.2 hmass0).ne'
  have hpoint := tail_le_profile T massShift y hmassOne hsqrt
  have hscaled : Sp.tail massShift y 1 ≤ tailProfile Sp y (Real.sqrt mass) := by
    change Sp.tail massShift y (Real.sqrt mass / Real.sqrt mass) ≤
      tailProfile Sp y (Real.sqrt mass) at hpoint
    rw [div_self hsqrt0] at hpoint
    exact hpoint
  exact hscaled.trans (tailProfile_le_fixedCollar T v hy (Real.sqrt mass))

/-- The far-cube penalized resolvent is bounded by the next-cube resolvent plus the fixed-collar
localized tail. -/
theorem analyticPenalizedCube_le_next_add_fixedCollarTail_of_subset
    (T : LogGrowthBounds Sp)
    {V : Set (Vec d)} (hV : IsOpen V) (v : ℕ)
    (hVcube : V ⊆ wholeSpaceCube d v) (n k : ℕ) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, |f x| ≤ 1)
    (hfsupp : ∀ᵐ x ∂volume, x ∉ V → f x = 0)
    (hsqrt : 1 < Real.sqrt ((mu : ℝ) + n))
    {x : Vec d} (hx : x ∈ wholeSpaceCube d v) :
    A.analyticPenalizedCubeResolvent
        hV n mu f hf hf1 (k + (v + 2)) x ≤
      A.analyticPenalizedCubeResolvent
          hV n mu f hf hf1 (v + 1) x +
        fixedCollarTailProfile T v (Real.sqrt ((mu : ℝ) + n)) /
          (mu : ℝ) :=
  A.analyticPenalizedCube_le_next_add_localizedTail_of_subset Sp
    (fixedCollarTailProfile T v (Real.sqrt ((mu : ℝ) + n)))
    (logSubexponentialProfile_nonneg
      (fixedCollarTailAmplitude_nonneg T v)
      (fixedCollarTailRate T v) (d + 1) _)
    hV v hVcube n k mu hf hf0 hf1 hfsupp
    (fun _ hy ↦ tail_unit_le_fixedCollar T v n mu hy hsqrt) hx

/-- Passing the fixed-collar comparison to the exhaustion supremum. -/
theorem toReal_analyticPenalizedResolvent_le_next_add_fixedCollarTail_of_subset
    (T : LogGrowthBounds Sp)
    {V : Set (Vec d)} (hV : IsOpen V) (v : ℕ)
    (hVcube : V ⊆ wholeSpaceCube d v) (n : ℕ) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, |f x| ≤ 1)
    (hfsupp : ∀ᵐ x ∂volume, x ∉ V → f x = 0)
    (hsqrt : 1 < Real.sqrt ((mu : ℝ) + n))
    {x : Vec d} (hx : x ∈ wholeSpaceCube d v) :
    (A.analyticPenalizedResolvent
      hV n mu f hf hf1 x).toReal ≤
      A.analyticPenalizedCubeResolvent
          hV n mu f hf hf1 (v + 1) x +
        fixedCollarTailProfile T v (Real.sqrt ((mu : ℝ) + n)) /
          (mu : ℝ) := by
  have ht := A.tendsto_analyticPenalizedCubeResolvent hV n mu hf hf0
    (by norm_num) hf1 x
  have houter := ht.comp (Filter.tendsto_add_atTop_nat (v + 2))
  exact le_of_tendsto' houter fun k ↦
    analyticPenalizedCube_le_next_add_fixedCollarTail_of_subset
      T hV v hVcube n k mu hf hf0 hf1 hfsupp hsqrt hx

end LogGrowthBounds

end

end SuperdiffusionCLT.Section8
