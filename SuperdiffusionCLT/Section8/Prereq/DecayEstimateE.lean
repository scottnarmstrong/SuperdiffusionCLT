/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.DecayEstimateD
public import SuperdiffusionCLT.Section8.Prereq.SuperdiffusivePoincare
public import SuperdiffusionCLT.Section7.Root.HolderRootB
public import SuperdiffusionCLT.Section8.Common.ExcessDecay.EquationRestrictionZeroExtension
public import SuperdiffusionCLT.Section7.Prereq.WellPosed

@[expose] public section

namespace SuperdiffusionCLT.Section8

noncomputable section

/-!
# Geometry of the decay estimate: balls and annuli

The open Euclidean annulus `{a² < |x|² < b²}`, the scaling `volume (B_r) = r^d volume (B_1)`, and the
lower bound `|B_b \ B_{b/4}| ≥ |B_b| / 2` used to normalise `L²` norms on the annuli of the dual
argument.
-/

section

open Homogenization MeasureTheory SuperdiffusionCLT.Section6
open scoped Pointwise ENNReal

variable {d : ℕ}

/-- The open Euclidean annulus `a < |x| < b`. -/
def decayEst_ann (a b : ℝ) : Set (Vec d) := {x | a ^ 2 < vecNormSq x ∧ vecNormSq x < b ^ 2}

theorem decayEst_ann_isOpen (a b : ℝ) : IsOpen (decayEst_ann (d := d) a b) :=
  (isOpen_lt continuous_const continuous_vecNormSq).inter
    (isOpen_lt continuous_vecNormSq continuous_const)

theorem decayEst_ann_measurable (a b : ℝ) : MeasurableSet (decayEst_ann (d := d) a b) :=
  (decayEst_ann_isOpen a b).measurableSet

theorem decayEst_ann_subset (a b : ℝ) : decayEst_ann (d := d) a b ⊆ euclidBall b :=
  fun _ hx => hx.2

theorem decayEst_ann_disjoint {a b : ℝ} {x : Vec d} (hx : x ∈ euclidBall a) :
    x ∉ decayEst_ann a b := fun h => by
  have h1 := h.1
  have h2 : vecNormSq x < a ^ 2 := hx
  linarith only [h1, h2]

/-- Dilates of Euclidean balls. -/
theorem decayEst_euclidBall_smul {t : ℝ} (ht : 0 < t) (r : ℝ) :
    t • euclidBall (d := d) r = euclidBall (t * r) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne', mem_euclidBall, mem_euclidBall, vecNormSq_smul]
  have h1 : t ^ 2 * (t⁻¹) ^ 2 = 1 := by field_simp
  have h2 : (t⁻¹) ^ 2 > 0 := by positivity
  constructor
  · intro h
    have := mul_lt_mul_of_pos_left h (by positivity : 0 < t ^ 2)
    calc vecNormSq x = t ^ 2 * ((t⁻¹) ^ 2 * vecNormSq x) := by
          rw [← mul_assoc, h1, one_mul]
      _ < t ^ 2 * r ^ 2 := this
      _ = (t * r) ^ 2 := by ring
  · intro h
    have h3 : (t⁻¹) ^ 2 * vecNormSq x < (t⁻¹) ^ 2 * (t * r) ^ 2 :=
      mul_lt_mul_of_pos_left h h2
    calc (t⁻¹) ^ 2 * vecNormSq x < (t⁻¹) ^ 2 * (t * r) ^ 2 := h3
      _ = r ^ 2 := by field_simp

/-- `|B_r| = r^d |B_1|`. -/
theorem decayEst_vol_ball {r : ℝ} (hr : 0 < r) :
    volume (euclidBall (d := d) r) = ENNReal.ofReal (r ^ d) * volume (euclidBall (d := d) 1) := by
  have h := decayEst_euclidBall_smul (d := d) hr 1
  rw [mul_one] at h
  rw [← h, MeasureTheory.Measure.addHaar_smul]
  simp [abs_of_pos hr]

theorem decayEst_volT_ball {r : ℝ} (hr : 0 < r) [NeZero d] :
    (volume (euclidBall (d := d) r)).toReal =
      r ^ d * (volume (euclidBall (d := d) 1)).toReal := by
  rw [decayEst_vol_ball hr, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

theorem decayEst_volT_ball_pos {r : ℝ} (hr : 0 < r) [NeZero d] :
    0 < (volume (euclidBall (d := d) r)).toReal :=
  ENNReal.toReal_pos (volume_euclidBall_ne_zero hr) (volume_euclidBall_ne_top hr)

/-- The annulus `{b/4 < |x| < b}` has at least half the volume of `B_b`. -/
theorem decayEst_vol_ann_ge [NeZero d] {b : ℝ} (hb : 0 < b) :
    (volume (euclidBall (d := d) b)).toReal / 2 ≤
      (volume (decayEst_ann (d := d) (b / 4) b)).toReal := by
  have hsub : euclidBall (d := d) b \ euclidBall (b / 2) ⊆ decayEst_ann (b / 4) b := by
    intro x hx
    refine ⟨?_, hx.1⟩
    have h1 : ¬ vecNormSq x < (b / 2) ^ 2 := hx.2
    have h2 : (b / 2) ^ 2 ≤ vecNormSq x := not_lt.1 h1
    have h3 : (b / 4) ^ 2 < (b / 2) ^ 2 := by nlinarith only [hb]
    linarith only [h2, h3]
  have hle : euclidBall (d := d) (b / 2) ⊆ euclidBall b := euclidBall_mono (by positivity) (by linarith only [hb])
  have hdiff : volume (euclidBall (d := d) b \ euclidBall (b / 2)) =
      volume (euclidBall (d := d) b) - volume (euclidBall (d := d) (b / 2)) :=
    measure_sdiff hle (measurableSet_euclidBall _).nullMeasurableSet
      (volume_euclidBall_ne_top (by linarith only [hb]))
  have hfin : volume (decayEst_ann (d := d) (b / 4) b) ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_euclidBall_ne_top hb) (measure_mono (decayEst_ann_subset _ _))
  have h1 := ENNReal.toReal_mono hfin (measure_mono hsub)
  rw [hdiff, ENNReal.toReal_sub_of_le (measure_mono hle) (volume_euclidBall_ne_top hb)] at h1
  rw [decayEst_volT_ball hb, decayEst_volT_ball (by linarith only [hb] : 0 < b / 2)] at h1
  rw [decayEst_volT_ball hb]
  have hω := (decayEst_volT_ball_pos (d := d) one_pos)
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have hpow : (b / 2) ^ d ≤ b ^ d / 2 := by
    rw [div_pow]
    have h2d : (2 : ℝ) ≤ 2 ^ d := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) (NeZero.one_le)
    have hbd : 0 < b ^ d := by positivity
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [h2d, hbd]
  have : b ^ d * (volume (euclidBall (d := d) 1)).toReal / 2 ≤
      b ^ d * (volume (euclidBall (d := d) 1)).toReal -
        (b / 2) ^ d * (volume (euclidBall (d := d) 1)).toReal := by
    nlinarith only [hpow, hω]
  linarith only [this, h1]

end

/-!
# Weak-solution API for the decay estimate

Restriction of a weak solution to an open subset, the `H¹₀` representative of a Dirichlet solution
with zero datum, and the real form of the normalised `L²` norm.
-/

section

open Homogenization MeasureTheory SuperdiffusionCLT.Section6 SuperdiffusionCLT.Section7
open SuperdiffusionCLT.Section8.Common.ExcessDecay
open scoped Pointwise ENNReal

variable {d : ℕ}

/-- Pairing a function against a zero-extended test function. -/
theorem decayEst_ext_integral {V U : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ U)
    (G : Vec d → ℝ) (φ : H10Function V) :
    ∫ x in U, G x * (h10ExtendToSuperset φ hV hVU).toH1Function.toFun x =
      ∫ x in V, G x * φ.toH1Function.toFun x := by
  have h : (fun x => G x * (h10ExtendToSuperset φ hV hVU).toH1Function.toFun x) =
      V.indicator (fun x => G x * φ.toH1Function.toFun x) := by
    funext x
    rw [h10ExtendToSuperset_toFun]
    by_cases hx : x ∈ V
    · simp only [h10ZeroExtension_of_mem φ hx, Set.indicator_of_mem hx]
    · simp only [h10ZeroExtension_of_not_mem φ hx, Set.indicator_of_notMem hx, mul_zero]
  rw [h, MeasureTheory.integral_indicator hV, Measure.restrict_restrict hV,
    Set.inter_eq_left.mpr hVU]

/-- Pairing a vector field against the gradient of a zero-extended test function. -/
theorem decayEst_ext_integral_grad {V U : Set (Vec d)} (hV : MeasurableSet V) (hVU : V ⊆ U)
    (F : Vec d → Vec d) (φ : H10Function V) :
    ∫ x in U, vecDot (F x) ((h10ExtendToSuperset φ hV hVU).toH1Function.grad x) =
      ∫ x in V, vecDot (F x) (φ.toH1Function.grad x) := by
  have h : (fun x => vecDot (F x) ((h10ExtendToSuperset φ hV hVU).toH1Function.grad x)) =
      V.indicator (fun x => vecDot (F x) (φ.toH1Function.grad x)) := by
    funext x
    rw [h10ExtendToSuperset_grad]
    by_cases hx : x ∈ V
    · simp only [h10ZeroExtensionGrad_of_mem φ hx, Set.indicator_of_mem hx]
    · simp only [h10ZeroExtensionGrad_of_not_mem φ hx, Set.indicator_of_notMem hx,
        vecDot_zero_right]
  rw [h, MeasureTheory.integral_indicator hV, Measure.restrict_restrict hV,
    Set.inter_eq_left.mpr hVU]

/-- **Restriction of a weak solution** to an open subset. -/
theorem decayEst_weak_restrict {a : CoeffField d} {U V : Set (Vec d)} {u : H1Function U}
    {f : Vec d → ℝ} {g : Vec d → Vec d} (hV : IsOpen V) (hVU : V ⊆ U)
    (hu : IsWeakSolutionOn a U u f g) :
    IsWeakSolutionOn a V (u.restrict hV hVU) f g := by
  intro φ
  have h := hu (h10ExtendToSuperset φ hV.measurableSet hVU)
  rw [decayEst_ext_integral_grad hV.measurableSet hVU, decayEst_ext_integral hV.measurableSet hVU,
    decayEst_ext_integral_grad hV.measurableSet hVU] at h
  exact h

/-- A weak solution is unchanged when the equation data agree on the set. -/
theorem decayEst_weak_congr_rhs {a : CoeffField d} {U : Set (Vec d)} {u : H1Function U}
    {f f' : Vec d → ℝ} {g : Vec d → Vec d} (hU : MeasurableSet U)
    (hff : ∀ x ∈ U, f x = f' x) (hu : IsWeakSolutionOn a U u f g) :
    IsWeakSolutionOn a U u f' g := by
  intro φ
  have h := hu φ
  have : ∫ x in U, f x * φ.toH1Function.toFun x = ∫ x in U, f' x * φ.toH1Function.toFun x := by
    refine setIntegral_congr_fun hU fun x hx => ?_
    simp only [hff x hx]
  rw [← this]
  exact h

/-- The `H¹₀` representative of a Dirichlet solution with zero datum. -/
theorem decayEst_h10_of_dirichlet {a : CoeffField d} {U : Set (Vec d)} (hU : IsOpen U)
    {f : Vec d → ℝ} {u : H1Function U} (hu : IsDirichletSolution a U f 0 u) :
    ∃ w : H10Function U, w.toH1Function.toFun = u.toFun ∧
      IsWeakSolutionOn a U w.toH1Function f (fun _ => 0) := by
  obtain ⟨hw, ⟨w, hwv⟩⟩ := hu
  have hwu : w.toH1Function.toFun = u.toFun := by
    rw [hwv]; funext x; simp [H1Function.zero_toFun]
  refine ⟨w, hwu, ?_⟩
  have hg := w0_grad_ae_of_toFun_eq hU w.toH1Function u hwu
  intro φ
  have h := hw φ
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards [hg] with x hx
  rw [hx]

end

/-!
# Real forms of the normalised norms

The `lpBar` and `eLpNorm` outputs of the large-scale Hölder estimate and of the superdiffusive
Poincaré inequality, rewritten as inequalities between square roots of integrals.
-/

section

open Homogenization MeasureTheory SuperdiffusionCLT.Section6 SuperdiffusionCLT.Section7
open scoped Pointwise ENNReal

variable {d : ℕ}

/-- The normalised `L²` norm of a square integrable function, as a square root of an integral. -/
theorem decayEst_lpBar_real {S : Set (Vec d)} (hS : volume S ≠ ⊤) (hv : 0 < (volume S).toReal)
    {F : Vec d → ℝ} (hF : MemLp F 2 (volume.restrict S)) :
    lpBar S 2 F =
      ENNReal.ofReal (Real.sqrt ((∫ x in S, F x ^ 2) / (volume S).toReal)) := by
  rw [rc_lpBar_two_eq S F hF.aestronglyMeasurable,
    hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have e0 : (volume S)⁻¹ = ENNReal.ofReal (((volume S).toReal)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hv, ENNReal.ofReal_toReal hS]
  have e1 : (volume S)⁻¹ ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (((volume S).toReal)⁻¹ ^ (1 / 2 : ℝ)) := by
    rw [e0, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  have hint : ∫ x in S, ‖F x‖ ^ (2 : ℝ≥0∞).toReal = ∫ x in S, F x ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards with x
    simp only [Real.norm_eq_abs, ENNReal.toReal_ofNat]
    rw [Real.rpow_two, sq_abs]
  rw [e1, ← ENNReal.ofReal_mul (by positivity), hint]
  congr 1
  simp only [ENNReal.toReal_ofNat]
  rw [Real.sqrt_eq_rpow, div_eq_inv_mul (∫ x in S, F x ^ 2),
    Real.mul_rpow (by positivity) (integral_nonneg fun x => by positivity)]
  norm_num

/-- The Euclidean norm of the gradient of an `H¹` function is square integrable. -/
theorem decayEst_memLp_eucNorm_grad {U : Set (Vec d)} (u : H1Function U) :
    MemLp (fun x => eucNorm (u.grad x)) 2 (volume.restrict U) := by
  have hmeas : AEStronglyMeasurable (fun x => eucNorm (u.grad x)) (volume.restrict U) := by
    have hg : AEStronglyMeasurable (fun x => vecNormSq (u.grad x)) (volume.restrict U) := by
      unfold vecNormSq vecDot
      exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
        (u.gradMemL2 i).aestronglyMeasurable.mul (u.gradMemL2 i).aestronglyMeasurable
    exact Real.continuous_sqrt.comp_aestronglyMeasurable hg
  rw [memLp_two_iff_integrable_sq hmeas]
  have : Integrable (fun x => vecNormSq (u.grad x)) (volume.restrict U) := by
    unfold vecNormSq vecDot
    refine integrable_finsetSum _ fun i _ => ?_
    have := (u.gradMemL2 i).integrable_sq
    simpa [sq] using this
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  show vecNormSq (u.grad x) = eucNorm (u.grad x) ^ 2
  unfold eucNorm
  rw [Real.sq_sqrt]
  unfold vecNormSq vecDot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

theorem decayEst_integral_eucNorm_sq {U : Set (Vec d)} (u : H1Function U) :
    ∫ x in U, eucNorm (u.grad x) ^ 2 = ∫ x in U, vecNormSq (u.grad x) := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show eucNorm (u.grad x) ^ 2 = vecNormSq (u.grad x)
  unfold eucNorm
  rw [Real.sq_sqrt]
  unfold vecNormSq vecDot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- **Real form of the Poincaré inequality** on a set `S` of positive finite volume. -/
theorem decayEst_poincare_real {S : Set (Vec d)} (hS : volume S ≠ ⊤)
    (hv : 0 < (volume S).toReal) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (w : H1Function S)
    {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict S))
    (hP : lpBar S 2 (fun x => w.toFun x - ⨍ z in S, w.toFun z) ≤
      ENNReal.ofReal α * lpBar S 2 (fun x => eucNorm (w.grad x)) +
        ENNReal.ofReal β * lpBar S 2 f) :
    Real.sqrt (∫ x in S, (w.toFun x - h1_avg S w.toFun) ^ 2) ≤
      α * Real.sqrt (∫ x in S, vecNormSq (w.grad x)) + β * Real.sqrt (∫ x in S, f x ^ 2) := by
  have hw : MemLp w.toFun 2 (volume.restrict S) := w.memL2
  have hfin := h1_finite_restrict hS
  have hF : MemLp (fun x => w.toFun x - h1_avg S w.toFun) 2 (volume.restrict S) :=
    hw.sub (memLp_const _)
  rw [hr_avg_eq, decayEst_lpBar_real hS hv hF, decayEst_lpBar_real hS hv
    (decayEst_memLp_eucNorm_grad w), decayEst_lpBar_real hS hv hf,
    decayEst_integral_eucNorm_sq w] at hP
  set V := (volume S).toReal with hV
  set I1 := ∫ x in S, (w.toFun x - h1_avg S w.toFun) ^ 2 with hI1
  set I2 := ∫ x in S, vecNormSq (w.grad x) with hI2
  set I3 := ∫ x in S, f x ^ 2 with hI3
  have hI1' : 0 ≤ I1 := integral_nonneg fun x => sq_nonneg _
  have hI3' : 0 ≤ I3 := integral_nonneg fun x => sq_nonneg _
  have hI2' : 0 ≤ I2 := by
    rw [hI2, ← decayEst_integral_eucNorm_sq w]
    exact integral_nonneg fun x => sq_nonneg _
  rw [← ENNReal.ofReal_mul hα, ← ENNReal.ofReal_mul hβ, ← ENNReal.ofReal_add
    (by positivity) (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hP
  have hsV : 0 < Real.sqrt V := Real.sqrt_pos.2 hv
  have e1 : Real.sqrt (I1 / V) = Real.sqrt I1 / Real.sqrt V := Real.sqrt_div hI1' V
  have e2 : Real.sqrt (I2 / V) = Real.sqrt I2 / Real.sqrt V := Real.sqrt_div hI2' V
  have e3 : Real.sqrt (I3 / V) = Real.sqrt I3 / Real.sqrt V := Real.sqrt_div hI3' V
  rw [e1, e2, e3] at hP
  have : Real.sqrt I1 / Real.sqrt V ≤
      (α * Real.sqrt I2 + β * Real.sqrt I3) / Real.sqrt V := by
    calc Real.sqrt I1 / Real.sqrt V ≤ α * (Real.sqrt I2 / Real.sqrt V) +
          β * (Real.sqrt I3 / Real.sqrt V) := hP
      _ = _ := by ring
  exact (div_le_div_iff_of_pos_right hsV).1 this

end

/-!
# Real form of the large-scale Hölder estimate

The output of `large_scale_holder` on balls `B_ρ ⊆ B_a` for a solution with a right-hand side
vanishing on `B_a`, as an inequality between square roots of integrals.
-/

section

open Homogenization MeasureTheory SuperdiffusionCLT.Section6 SuperdiffusionCLT.Section7
open scoped Pointwise ENNReal

variable {d : ℕ}

/-- An essential supremum bound in `ℝ≥0∞` gives an almost everywhere bound. -/
theorem decayEst_ae_le_of_eLpNorm_top {μ : Measure (Vec d)} {F : Vec d → ℝ}
    (hF : AEStronglyMeasurable F μ) {M : ℝ} (hM : 0 ≤ M)
    (h : eLpNorm F ⊤ μ ≤ ENNReal.ofReal M) : ∀ᵐ x ∂μ, |F x| ≤ M := by
  have h1 := ae_le_eLpNormEssSup (f := F) (μ := μ)
  rw [← eLpNorm_exponent_top hF] at h1
  filter_upwards [h1] with x hx
  have h2 : ‖F x‖ₑ ≤ ENNReal.ofReal M := hx.trans h
  rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff hM] at h2
  rwa [Real.norm_eq_abs] at h2

/-- **Real form of the Hölder estimate.** -/
theorem decayEst_holder_real [NeZero d] {ρ a : ℝ} (hρ : 0 < ρ) (hρa : ρ ≤ a)
    (w : H1Function (euclidBall (d := d) a)) {f : Vec d → ℝ}
    (hf0 : ∀ x ∈ euclidBall (d := d) a, f x = 0) {Cc κ : ℝ} (hCc : 0 ≤ Cc)
    (hH : eLpNorm (fun x => w.toFun x - ∫ y, w.toFun y ∂ballMeasure (d := d) ρ) ⊤
        (volume.restrict (euclidBall ρ)) ≤
      ENNReal.ofReal Cc *
        (ballL2 a (fun x => w.toFun x - ∫ y, w.toFun y ∂ballMeasure (d := d) a) +
          ENNReal.ofReal κ * eLpNorm f ⊤ (volume.restrict (euclidBall (d := d) a)))) :
    Real.sqrt (∫ x in euclidBall (d := d) ρ,
        (w.toFun x - h1_avg (euclidBall ρ) w.toFun) ^ 2) ≤
      Cc * Real.sqrt ((volume (euclidBall (d := d) ρ)).toReal /
          (volume (euclidBall (d := d) a)).toReal) *
        Real.sqrt (∫ x in euclidBall (d := d) a, (w.toFun x - h1_avg (euclidBall a) w.toFun) ^ 2) := by
  have ha : 0 < a := lt_of_lt_of_le hρ hρa
  have hf : eLpNorm f ⊤ (volume.restrict (euclidBall (d := d) a)) = 0 := by
    have : f =ᵐ[volume.restrict (euclidBall (d := d) a)] 0 :=
      (ae_restrict_iff' (measurableSet_euclidBall a)).2
        (Filter.Eventually.of_forall fun x hx => hf0 x hx)
    rw [eLpNorm_congr_ae this]
    exact eLpNorm_zero
  rw [hf, mul_zero, add_zero, hr_ballL2_osc ha w.memL2, ← ENNReal.ofReal_mul hCc] at hH
  simp only [hr_ballAvg] at hH
  set V := (volume (euclidBall (d := d) a)).toReal with hV
  set Vρ := (volume (euclidBall (d := d) ρ)).toReal with hVρ
  have hVpos : 0 < V := decayEst_volT_ball_pos ha
  have hVρpos : 0 < Vρ := decayEst_volT_ball_pos hρ
  have hl2 : 0 ≤ h1_l2 (euclidBall a) w.toFun := Real.sqrt_nonneg _
  have hmeas : AEStronglyMeasurable (fun x => w.toFun x - h1_avg (euclidBall ρ) w.toFun)
      (volume.restrict (euclidBall (d := d) ρ)) := by
    have h1 : AEStronglyMeasurable w.toFun (volume.restrict (euclidBall (d := d) ρ)) :=
      w.memL2.aestronglyMeasurable.mono_measure
        (Measure.restrict_mono (euclidBall_mono hρ.le hρa) le_rfl)
    exact h1.sub aestronglyMeasurable_const
  have hae := decayEst_ae_le_of_eLpNorm_top hmeas (by positivity) hH
  have hfin := h1_finite_restrict (volume_euclidBall_ne_top (d := d) hρ)
  set M := Cc * h1_l2 (euclidBall a) w.toFun with hM
  have hint : ∫ x in euclidBall (d := d) ρ, (w.toFun x - h1_avg (euclidBall ρ) w.toFun) ^ 2 ≤
      M ^ 2 * Vρ := by
    have h1 : ∫ x in euclidBall (d := d) ρ, (w.toFun x - h1_avg (euclidBall ρ) w.toFun) ^ 2 ≤
        ∫ x in euclidBall (d := d) ρ, M ^ 2 := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
        (integrable_const _) ?_
      filter_upwards [hae] with x hx
      exact sq_le_sq' (abs_le.1 hx).1 (abs_le.1 hx).2
    rwa [setIntegral_const, smul_eq_mul, Measure.real, mul_comm] at h1
  have hsq := Real.sqrt_le_sqrt hint
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)] at hsq
  refine hsq.trans (le_of_eq ?_)
  have hIa : 0 ≤ ∫ x in euclidBall (d := d) a, (w.toFun x - h1_avg (euclidBall a) w.toFun) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  rw [hM]
  unfold h1_l2
  rw [Real.sqrt_div hIa V, Real.sqrt_div hVρpos.le V]
  ring

end

end

end SuperdiffusionCLT.Section8
