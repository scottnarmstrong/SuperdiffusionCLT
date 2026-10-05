/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.DtExpK
public import SuperdiffusionCLT.Section8.Root.DtExpJ

/-!
# The quenched moments at a good sample and a good time

At a fixed sample with a good process input, a good scale and a good time, the moment of order two
and the mean of the transition law at the origin satisfy the printed bound, from the homogenization
estimate, the exit estimate and the crude fourth moment.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory MarkovProcess
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section6
open SuperdiffusionCLT.Section7
open SuperdiffusionCLT.Section8.Common.Regularity.Ported
open scoped Matrix.Norms.Elementwise ENNReal NNReal Pointwise

variable {d : ℕ}

/-- The component of the mean is the mean of the component. -/
theorem dtExp_integral_apply {ν : Measure (Vec d)} [IsProbabilityMeasure ν]
    (h : Integrable (fun y : Vec d => vecNormSq y) ν) (i : Fin d) :
    (∫ y, y ∂ν) i = ∫ y, y i ∂ν := by
  have hint : Integrable (fun y : Vec d => y) ν := by
    refine ((integrable_const (1 : ℝ)).add h).mono' aestronglyMeasurable_id
      (Filter.Eventually.of_forall fun y => ?_)
    have h0 := dtExp_vecNormSq_nonneg y
    have h1 : ‖y‖ ≤ Real.sqrt (vecNormSq y) := by
      rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
      intro i
      rw [Real.norm_eq_abs]
      exact dtExp_abs_coord_le y i
    have h2 : Real.sqrt (vecNormSq y) ≤ 1 + vecNormSq y := by
      have := Real.sqrt_le_sqrt (show vecNormSq y ≤ (1 + vecNormSq y) ^ 2 by nlinarith only [h0])
      rwa [Real.sqrt_sq (by linarith only [h0])] at this
    simp only [Pi.add_apply]
    exact h1.trans h2
  have := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).integral_comp_comm hint
  simpa using this.symm

/-- The scale `ε = r[t]⁻¹`, `r[t] = (t (log t)^{(1+α)/2})^{1/2}` (`e.rtnaught.def`). -/
noncomputable def dtExp_eps (t α : ℝ) : ℝ := (Real.sqrt (t * Real.log t ^ ((1 + α) / 2)))⁻¹

/-- **The quenched moments at a good sample and a good time.** -/
theorem dtExp_good [NeZero d] {nu cStar α C0 cE Mc C K : ℝ} {omega : ShellSeq d}
    (D : FieldInputData d nu (fullStreamRecentered omega))
    (ha : ∀ i j, ContDiff ℝ 1 fun y => fullCoefficientRecentered nu omega y i j)
    (hc : 0 < cStar) (hα0 : 0 < α) (hα1 : α < 1) (hC0 : 1 ≤ C0) (hcE : 0 < cE)
    {t : ℝ} (ht : 10 ≤ t)
    (hrt : ∀ (f : Vec d → ℝ) (g u uhom : H1Function (euclideanBall (0 : Vec d) 1)),
      IsDirichletSolution (fun x => opScale cStar (dtExp_eps t α) •
        epField nu omega (dtExp_eps t α) x) (euclideanBall (0 : Vec d) 1)
        (fun x => f x - 0 * u.toFun x) g u →
      IsDirichletSolution (fun _ => (1 / 2 : ℝ) • (1 : Mat d)) (euclideanBall (0 : Vec d) 1)
        (fun x => f x - 0 * uhom.toFun x) g uhom →
      eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤
          (volume.restrict (euclideanBall (0 : Vec d) 1)) ≤
        ENNReal.ofReal (4 * (C0 * |Real.log (dtExp_eps t α)| ^ (-α))) *
          (eLpNorm (fun x => eucNorm (g.grad x)) ⊤ (volume.restrict (euclideanBall (0 : Vec d) 1)) +
            eLpNorm (fun x => f x - 0 * u.toFun x) ⊤
              (volume.restrict (euclideanBall (0 : Vec d) 1))))
    {Q : Vec d → Measure (ContinuousPath (Vec d))}
    (hQ : IsContinuousPathLaw D.logGrowthBounds.resolvent.kernelSemigroup Q)
    (hex : ∀ t0 : ℝ, 0 < t0 → t0 ≤ 1 →
      Q ((dtExp_eps t α)⁻¹ • (0 : Vec d))
        {w | ContinuousPath.exitTime {y : Vec d | vecNormSq ((dtExp_eps t α) • y) < 1} w ≤
          ENNReal.ofReal (timeScale cStar (dtExp_eps t α) * t0)} ≤
        2 * ENNReal.ofReal (Real.exp (-(cE * min (t0 ^ (-(1 / 2 : ℝ)))
          (|Real.log (dtExp_eps t α)| ^ (α / 6))))))
    (hK27 : 27 ≤ K) (hKt : K ≤ Real.sqrt t)
    (hg : ∀ x : Vec d, matrixOperatorNorm (fullStreamRecentered omega x) ^ 2 ≤
      C * Real.log (K ^ 2 + vecNormSq x) ^ ((2 : ℝ) * (1 + 1)))
    (hMc : crudeMomL_const d nu (Real.sqrt (max C 0))
        (D.freezingAmplitude (smallContrastThreshold d (1 / 2 : ℝ))) 2 ≤ Mc)
    (hLc : Real.sqrt (8 * cStar) ≤ Real.log t ^ (α / 6))
    (hp1 : 2 * Real.exp (-(cE / 2 * Real.log t ^ (α / 6))) ≤ 1)
    (hap : d * Real.sqrt Mc * (2 * Real.log t) ^ 8 *
      Real.sqrt (2 * Real.exp (-(cE / 2 * Real.log t ^ (α / 6)))) ≤ 1)
    (hLp : Real.log t * (2 * Real.exp (-(cE / 2 * Real.log t ^ (α / 6)))) ≤ 1) :
    Integrable (fun y : Vec d => vecNormSq y)
        (D.logGrowthBounds.resolvent.kernelSemigroup t.toNNReal 0) ∧
      |(1 / t) * (∫ y, vecNormSq y ∂(D.logGrowthBounds.resolvent.kernelSemigroup t.toNNReal 0)) -
          2 * (d : ℝ) * Real.sqrt cStar * Real.sqrt (Real.log t)| +
        (1 / t) * vecNormSq (∫ y, y ∂(D.logGrowthBounds.resolvent.kernelSemigroup t.toNNReal 0)) ≤
      (16 * (2 + d) * C0 + 2 + 2 * d * Real.sqrt (2 * cStar) + 4 * d * Real.sqrt cStar +
        d * (16 * C0 + 2) ^ 2) * Real.log t ^ ((1 - α) / 2) := by
  obtain ⟨hL, hΛ1, hΛL⟩ := dtExp_scale_facts ht hα0 hα1
  obtain ⟨hε0, hε2, hεhalf, hv1, hv2, hop, hdiff⟩ : 0 < dtExp_eps t α ∧
      dtExp_eps t α ^ 2 * (t * Real.log t ^ ((1 + α) / 2)) = 1 ∧ dtExp_eps t α ≤ 1 / 2 ∧
      Real.log t / 2 ≤ |Real.log (dtExp_eps t α)| ∧ |Real.log (dtExp_eps t α)| ≤ Real.log t ∧
      opScale cStar (dtExp_eps t α) *
        (2 * Real.sqrt (2 * cStar * |Real.log (dtExp_eps t α)|)) = 1 ∧
      |2 * Real.sqrt (2 * cStar * |Real.log (dtExp_eps t α)|) -
        2 * Real.sqrt cStar * Real.sqrt (Real.log t)| ≤ 4 * Real.sqrt cStar :=
    dtExp_eps_facts ht hα0 hα1 hc
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  have ht0 : 0 < t := by linarith only [ht]
  set L := Real.log t with hLdef
  have hL0 : 0 < L := by linarith only [hL]
  have hε : 0 < dtExp_eps t α := hε0
  set ε := dtExp_eps t α with hεdef
  have hMc0 : 0 ≤ Mc := (crudeMomL_const_nonneg (d := d) nu (Real.sqrt (max C 0))
    (D.freezingAmplitude (smallContrastThreshold d (1 / 2 : ℝ))) 2).trans hMc
  have hκpos : 0 < 2 * Real.sqrt (2 * cStar * |Real.log ε|) := by
    have : 0 < |Real.log ε| := by linarith only [hv1, hL]
    have : 0 < Real.sqrt (2 * cStar * |Real.log ε|) := Real.sqrt_pos.2 (by positivity)
    linarith only [this]
  have hs : 0 < opScale cStar ε := by
    by_contra hneg
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.1 hneg) hκpos.le
    linarith only [this, hop]
  -- the homogenization constant
  have hE0 : 0 ≤ 8 * C0 * L ^ (-α) := by positivity
  have hEr : 4 * (C0 * |Real.log ε| ^ (-α)) ≤ 8 * C0 * L ^ (-α) := by
    have h1 : |Real.log ε| ^ (-α) ≤ (L / 2) ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hv1 (by linarith only [hα0])
    have h2 : (L / 2) ^ (-α) = L ^ (-α) * 2 ^ α := by
      rw [Real.div_rpow hL0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
    have h3 : (2 : ℝ) ^ α ≤ 2 := by
      calc (2 : ℝ) ^ α ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1.le
        _ = 2 := Real.rpow_one 2
    have h4 : 0 ≤ L ^ (-α) := Real.rpow_nonneg hL0.le _
    have : |Real.log ε| ^ (-α) ≤ 2 * L ^ (-α) := by
      calc |Real.log ε| ^ (-α) ≤ L ^ (-α) * 2 ^ α := h2 ▸ h1
        _ ≤ L ^ (-α) * 2 := by gcongr
        _ = 2 * L ^ (-α) := mul_comm _ _
    nlinarith only [this, hC0]
  have hA := dtExp_hA (nu := nu) (cStar := cStar) (omega := omega) hε hEr hrt
  -- the exit probability
  have hex' : ∀ t0 : ℝ, 0 < t0 → t0 ≤ 1 →
      (Q 0) {w | ContinuousPath.exitTime {y : Vec d | vecNormSq (ε • y) < 1} w ≤
        ENNReal.ofReal (timeScale cStar ε * t0)} ≤
      2 * ENNReal.ofReal (Real.exp (-(cE * min (t0 ^ (-(1 / 2 : ℝ)))
        (|Real.log ε| ^ (α / 6))))) := by
    intro t0 h0 h1
    have := hex t0 h0 h1
    simpa using this
  have hprob : IsProbabilityMeasure (Q 0) := (hQ 0).1
  have hpb := dtExp_p_bound (μ := Q 0) ht hα0 hα1 hc hcE.le hLc hex'
  set p := (Q 0).real {w | ContinuousPath.exitTime (euclideanBall (0 : Vec d) ε⁻¹) w ≤
    (t.toNNReal : ℝ≥0∞)} with hpdef
  set p0 := 2 * Real.exp (-(cE / 2 * L ^ (α / 6))) with hp0def
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hpp0 : p ≤ p0 := hpb
  have hp0nn : 0 ≤ p0 := by positivity
  -- the fourth moment
  have h4 := dtExp_fourth_bound D hK27 hg ht hKt
  set B4 : ℝ := Mc * (2 * L) ^ 16 * t ^ 2 with hB4def
  have hB4 : 0 ≤ B4 := by positivity
  have h4' : ∫⁻ z, edist z (0 : Vec d) ^ (4 : ℝ) ∂(D.logGrowthBounds.resolvent.kernelSemigroup
      t.toNNReal 0) ≤ ENNReal.ofReal B4 :=
    h4.trans (ENNReal.ofReal_le_ofReal (by rw [hB4def]; gcongr))
  obtain ⟨hint, hm2, hI, hII⟩ := dtExp_det D rfl ha hε hs hE0 hA hQ t.toNNReal hB4 h4'
  have hcoe : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht0.le
  rw [hcoe] at hI
  refine ⟨hint, ?_⟩
  -- the numerics
  set a : ℝ := d * Real.sqrt Mc * (2 * L) ^ 8 with hadef
  have hsq : Real.sqrt ((d : ℝ) ^ 2 * B4) = a * t := by
    have : (d : ℝ) ^ 2 * B4 = (a * t) ^ 2 := by
      rw [hadef, hB4def]
      have h1 : Real.sqrt Mc ^ 2 = Mc := Real.sq_sqrt hMc0
      calc (d : ℝ) ^ 2 * (Mc * (2 * L) ^ 16 * t ^ 2) =
          (d : ℝ) ^ 2 * (Real.sqrt Mc ^ 2) * ((2 * L) ^ 8) ^ 2 * t ^ 2 := by rw [h1]; ring
        _ = _ := by ring
    rw [this, Real.sqrt_sq (by positivity)]
  rw [hsq] at hI hII
  have hap' : a * Real.sqrt p ≤ 1 :=
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hpp0) (by positivity)).trans hap
  have hLp' : L * p ≤ 1 := (mul_le_mul_of_nonneg_left hpp0 hL0.le).trans hLp
  have hp1' : p ≤ 1 := hpp0.trans hp1
  have hmean : ∀ i : Fin d, |(∫ y, y ∂(D.logGrowthBounds.resolvent.kernelSemigroup t.toNNReal 0)) i| ≤
      2 * (8 * C0 * L ^ (-α)) * ε⁻¹ + (Real.sqrt (a * t) * Real.sqrt p + ε⁻¹ * p) := by
    intro i
    have : IsProbabilityMeasure (D.logGrowthBounds.resolvent.kernelSemigroup t.toNNReal 0) :=
      ⟨D.logGrowthBounds.isConservative_kernelSemigroup _ 0⟩
    rw [dtExp_integral_apply hint i]
    exact hII i
  have hnum := dtExp_numerics (d := d) hd1 (t := t) (α := α) (c := cStar) (C0 := C0)
    (E0 := 8 * C0 * L ^ (-α)) (a := a) (p := p)
    (m2 := ∫ y, vecNormSq y ∂(D.logGrowthBounds.resolvent.kernelSemigroup t.toNNReal 0))
    (∫ y, y ∂(D.logGrowthBounds.resolvent.kernelSemigroup t.toNNReal 0))
    ht hα0 hα1 hc hC0 le_rfl (by positivity) hp0 hp1' hap' hLp' hI hmean
  rw [one_div_mul_eq_div, one_div_mul_eq_div]
  exact hnum

end SuperdiffusionCLT.Section8
