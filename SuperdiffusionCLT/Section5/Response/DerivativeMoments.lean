/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Response.GammaMoments
public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellDerivLargeCube
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementPthMoment

/-!
# Stationary `L⁸` moments of the shell derivatives on a large cube

The second display of the proof of `lem.response` bounds
`E‖∇ j_r‖_{L̲⁸(cu_K)}⁸` for the shells `r ≤ K` by stationarity. Here the derivative size
`D_k(ω, x) = ‖∇ (ω k)(x)‖` is jointly measurable in `(x, ω)`, so by Tonelli the expectation of the
normalized `L̲⁸(cu_K)` norm to the eighth power is the cube average of `E D_k(·, x)⁸`, and for each
`x` the variable `D_k(·, x)` is dominated by the translated natural-cube envelope
(`translatedShellDerivSupBound k x`), whose `Γ₂` amplitude is `3^{-k}` by `J3` and stationarity.
This avoids the union bound over sub-cubes, so the amplitude carries no factor of `K`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open MeasureTheory Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open scoped ENNReal Matrix.Norms.Elementwise

variable {d : ℕ}

/-! ## Minkowski for finite sums in `ℝ≥0∞` -/

/-- Minkowski's inequality in `L^p(μ)` for a finite sum of measurable `ℝ≥0∞`-valued functions. -/
theorem lintegral_rpow_finsetSum_le {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) (f : ι → Ω → ℝ≥0∞) (hf : ∀ i ∈ s, Measurable (f i)) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ ω, (∑ i ∈ s, f i ω) ^ p ∂μ) ^ (1 / p) ≤
      ∑ i ∈ s, (∫⁻ ω, (f i ω) ^ p ∂μ) ^ (1 / p) := by
  classical
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  induction s using Finset.induction_on with
  | empty =>
      simp [ENNReal.zero_rpow_of_pos hp0]
      exact hp0
  | insert a t hat ih =>
      have hsum : Measurable (fun ω => ∑ i ∈ t, f i ω) :=
        Finset.measurable_sum _ fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hfa : Measurable (f a) := hf a (Finset.mem_insert_self a t)
      have h1 := ENNReal.lintegral_Lp_add_le (μ := μ) (f := f a) (g := fun ω => ∑ i ∈ t, f i ω)
        hfa.aemeasurable hsum.aemeasurable hp
      simp only [Pi.add_apply] at h1
      simp only [Finset.sum_insert hat]
      exact h1.trans (add_le_add le_rfl (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-! ## The eighth power of an `L⁸` norm -/

/-- `‖f‖_{L⁸}⁸ = ∫ ‖f‖⁸`. -/
theorem eLpNorm_eight_pow {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (f : α → E) (hf : AEStronglyMeasurable f μ) :
    (eLpNorm f 8 μ) ^ (8 : ℕ) = ∫⁻ x, ‖f x‖ₑ ^ (8 : ℕ) ∂μ := by
  have hq : (8 : ℝ≥0∞) ≠ 0 := by norm_num
  have hqt : (8 : ℝ≥0∞) ≠ ⊤ := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq hqt hf]
  have h8 : (8 : ℝ≥0∞).toReal = ((8 : ℕ) : ℝ) := by norm_num
  rw [h8, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  have : (1 / ((8 : ℕ) : ℝ)) * ((8 : ℕ) : ℝ) = 1 := by norm_num
  rw [this, ENNReal.rpow_one]
  exact lintegral_congr fun x => ENNReal.rpow_natCast _ _

/-! ## Joint measurability of the derivative size -/

/-- The exact induced norm of the stored derivative of shell `k` of `omega` at `x`. -/
noncomputable def shellDerivSize (k : ℕ) (omega : ShellSeq d) (x : Vec d) : ℝ :=
  ShellField.matrixDerivativeNorm (ShellField.deriv (omega k) x)

theorem shellDerivSize_nonneg (k : ℕ) (omega : ShellSeq d) (x : Vec d) :
    0 ≤ shellDerivSize k omega x :=
  ShellField.matrixDerivativeNorm_nonneg _

theorem continuous_shellDerivSize (k : ℕ) (omega : ShellSeq d) :
    Continuous (shellDerivSize k omega) :=
  ShellField.matrixDerivativeNorm_continuous.comp (ShellField.deriv (omega k)).continuous

theorem measurable_shellDerivSize_uncurry (k : ℕ) :
    Measurable (Function.uncurry fun (x : Vec d) (omega : ShellSeq d) =>
      shellDerivSize k omega x) :=
  measurable_uncurry_of_continuous_of_measurable
    (fun omega => continuous_shellDerivSize k omega)
    (fun x => (ShellField.matrixDerivativeNorm_continuous.comp
      (ShellField.continuous_eval_deriv x)).measurable.comp
        (ShellField.measurable_shellCoordinate k))

/-! ## The expectation of the normalized `L⁸` norm of the derivative size -/

/-- For every point `x`, the derivative size of shell `k` at `x` has `L⁸(P)` norm at most
`2 · 3^{-k}`, by `J3` and stationarity. -/
theorem lintegral_shellDerivSize_pow_le {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (k : ℕ) (x : Vec d) :
    ∫⁻ omega, ENNReal.ofReal (shellDerivSize k omega x) ^ (8 : ℕ) ∂P.toMeasure ≤
      ENNReal.ofReal (2 * ((3 : ℝ) ^ k)⁻¹) ^ (8 : ℕ) := by
  have hS := (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
    (translatedShellDerivSupBound_nonneg k x)).1
    (isBigOWith_gammaSigma_translatedShellDerivSupBound hPrefix hJ3 k x)
  have hA : (0 : ℝ) < ((3 : ℝ) ^ k)⁻¹ := by positivity
  have h8 := eLpNorm_eight_le_of_isBigO_gammaSigma_two hA
    (measurable_translatedShellDerivSupBound k x) hS
  have hx0 : x - x ∈ cubeSet (originCube d (k : ℤ)) := by
    rw [sub_self]
    exact openCubeSet_subset_cubeSet _ (zero_mem_openCubeSet_originCube k)
  calc ∫⁻ omega, ENNReal.ofReal (shellDerivSize k omega x) ^ (8 : ℕ) ∂P.toMeasure
      ≤ ∫⁻ omega, ‖translatedShellDerivSupBound k x omega‖ₑ ^ (8 : ℕ) ∂P.toMeasure := by
        refine lintegral_mono fun omega => ?_
        rw [Real.enorm_eq_ofReal (translatedShellDerivSupBound_nonneg k x omega)]
        exact pow_le_pow_left₀ bot_le (ENNReal.ofReal_le_ofReal
          (matrixDerivativeNorm_deriv_le_translatedShellDerivSupBound omega k x hx0)) 8
    _ = (eLpNorm (translatedShellDerivSupBound k x) 8 P.toMeasure) ^ (8 : ℕ) :=
        (eLpNorm_eight_pow _
          (measurable_translatedShellDerivSupBound k x).aestronglyMeasurable).symm
    _ ≤ ENNReal.ofReal (2 * ((3 : ℝ) ^ k)⁻¹) ^ (8 : ℕ) := pow_le_pow_left₀ bot_le h8 8

/-- `E[‖D_k‖_{L̲⁸(Q)}⁸] ≤ (2 · 3^{-k})⁸` on every triadic cube `Q`. -/
theorem lintegral_cubeLpENorm_shellDerivSize_pow_le {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (k : ℕ) (Q : TriadicCube d) :
    ∫⁻ omega, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8
        (shellDerivSize k omega)) ^ (8 : ℕ) ∂P.toMeasure ≤
      ENNReal.ofReal (2 * ((3 : ℝ) ^ k)⁻¹) ^ (8 : ℕ) := by
  have : IsProbabilityMeasure (normalizedCubeMeasure Q) := ⟨normalizedCubeMeasure_apply_univ Q⟩
  have hpt : ∀ omega, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8
      (shellDerivSize k omega)) ^ (8 : ℕ) =
      ∫⁻ x, ENNReal.ofReal (shellDerivSize k omega x) ^ (8 : ℕ) ∂normalizedCubeMeasure Q := by
    intro omega
    rw [SuperdiffusionCLT.Section2.Norms.cubeLpENorm,
      eLpNorm_eight_pow _ (continuous_shellDerivSize k omega).aestronglyMeasurable]
    exact lintegral_congr fun x => by
      rw [Real.enorm_eq_ofReal (shellDerivSize_nonneg k omega x)]
  simp_rw [hpt]
  have hmeas : Measurable (Function.uncurry fun (omega : ShellSeq d) (x : Vec d) =>
      ENNReal.ofReal (shellDerivSize k omega x) ^ (8 : ℕ)) := by
    have h := (measurable_shellDerivSize_uncurry (d := d) k).comp measurable_swap
    exact (ENNReal.measurable_ofReal.comp h).pow_const 8
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  calc ∫⁻ x, ∫⁻ omega, ENNReal.ofReal (shellDerivSize k omega x) ^ (8 : ℕ) ∂P.toMeasure
        ∂normalizedCubeMeasure Q
      ≤ ∫⁻ _x, ENNReal.ofReal (2 * ((3 : ℝ) ^ k)⁻¹) ^ (8 : ℕ) ∂normalizedCubeMeasure Q :=
        lintegral_mono fun x => lintegral_shellDerivSize_pow_le hPrefix hJ3 k x
    _ = ENNReal.ofReal (2 * ((3 : ℝ) ^ k)⁻¹) ^ (8 : ℕ) := by simp

end SuperdiffusionCLT.Section5
