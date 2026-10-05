/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1InputsC

/-!
# The shells above the cube scale, and the honest first display of Step 1

`RHSTerm1Inputs` states the first display of Step 1 of `l.RHS.term1` through
three carried hypotheses, two of which are stated in shapes that the available
estimates cannot deliver:

* its `hDerivHigh` compares the annealed second moment of
  `‖∇(k_{L'} − k_ℓ)‖_{L^∞(cu_m)}` with the annealed second moment of
  `‖∇(k_m − k_ℓ)‖_{L^∞(cu_m)}`.  That is a **ratio** of two lintegrals, and no
  shell law bounds the second one from below, so no comparison constant
  can be produced.  What the shell estimates do give is the **absolute**
  estimate on the shells above the cube scale, and that is what this file
  proves.
* its `hMoment` asks for `E[‖a_ℓ‖⁴_{L^∞(cu_ℓ)}]^{1/2} ≤ Ca (1+ℓ)^{3/2}` with a
  scale-free `Ca`.  The true size is `(1+ℓ)²`
  (`RHSTerm1InputsC.sqrt_fourth_moment_coeffCubeLinftyENorm_le` at `L = m = ℓ`),
  and that is the size used here.

## The shells above the cube scale

For `r ≤ k` the half-open cube `cu_r` is contained in `cu_k`, so the shell
`omega k` is controlled on `cu_r` by the **single-cube** envelope
`shellDerivLargeCubeSupBound k k`, whose `Γ₂` amplitude is `C 3^{-k}`
with **no** union-bound factor: the sub-cube family of `cu_k` at scale `k` is
the singleton `{cu_k}`.  Summing the finite `Γ₂` triangle over the shells
`(a, b]` gives `shellDerivHighSumSupBound a b` at the amplitude `C 3^{-a}`,
and hence the annealed second moment

`E[‖∇(k_b − k_a)‖²_{L^∞(cu_r)}]^{1/2} ≤ C 3^{-a}`  for `r ≤ a ≤ b`.

At `a = ℓ`, `b = L'`, `r = n` this is the last factor of the printed chain in the
proof of `l.RHS.term1`, which the print reads on the translate `z + cu_n` of the
**small** cube and not on `cu_m`; at `a = m`, `b = L'`, `r = m` it is the
absolute estimate on the shells `(m, L']` alone.  The union-bound factor
`√(1 + (m − ℓ))` of the large-cube estimate is exactly the price of moving that factor onto the
large cube `cu_m`;
on the small cube it is absent, and the closing arithmetic of the display then
runs at the printed size `ℓ²` with the honest `(1+ℓ)²` coefficient moment.

## References

The paper: `e.nabla.kmn.Linfty`, and the printed chain in the proof of
`l.RHS.term1` (including the `a_ℓ` moment).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The half-open cubes are nested -/

/-- The half-open natural cubes are nested: `cu_r ⊆ cu_k` for `r ≤ k`. -/
theorem cubeSet_originCube_subset_of_le {r k : ℕ} (hrk : r ≤ k) :
    cubeSet (originCube d (r : ℤ)) ⊆ cubeSet (originCube d (k : ℤ)) := by
  intro x hx
  have hpow : (3 : ℝ) ^ ((r : ℤ)) ≤ (3 : ℝ) ^ ((k : ℤ)) := by
    refine zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) ?_
    exact_mod_cast hrk
  rw [mem_cubeSet_originCube_iff] at hx ⊢
  intro i
  obtain ⟨hlo, hhi⟩ := hx i
  constructor
  · linarith only [hlo, hpow]
  · linarith only [hhi, hpow]

/-! ## The envelope of the shells above the cube scale -/

/-- The finite sum, over the shell interval `(a, b]`, of the **single-cube**
derivative envelopes `shellDerivLargeCubeSupBound k k`.  Each summand is the
scale-`k` derivative control of the shell `omega k` on `cu_k` itself, so it
carries the derivative scale `3^{-k}` with no union-bound factor. -/
def shellDerivHighSumSupBound (a b : ℕ) (omega : ShellSeq d) : ℝ :=
  ∑ k ∈ Finset.Ioc a b, shellDerivLargeCubeSupBound k k omega

theorem shellDerivHighSumSupBound_nonneg (a b : ℕ) (omega : ShellSeq d) :
    0 ≤ shellDerivHighSumSupBound a b omega :=
  Finset.sum_nonneg fun k _ => shellDerivLargeCubeSupBound_nonneg k k omega

theorem measurable_shellDerivHighSumSupBound (a b : ℕ) :
    Measurable (shellDerivHighSumSupBound a b : ShellSeq d → ℝ) :=
  Finset.measurable_sum _ fun k _ => measurable_shellDerivLargeCubeSupBound k k

/-- At every point of the half-open cube `cu_r` the exact induced norm of the
reconstructed derivative `∇(k_b − k_a) = ∑_{k ∈ (a,b]} ∇ j_k` is bounded by the
envelope, for every shell interval `(a, b]` **above** the cube scale. -/
theorem matrixDerivativeNorm_le_shellDerivHighSumSupBound
    (omega : ShellSeq d) {a b r : ℕ} (hra : r ≤ a) {x : Vec d}
    (hx : x ∈ cubeSet (originCube d (r : ℤ))) :
    ShellField.matrixDerivativeNorm
        (∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x) ≤
      shellDerivHighSumSupBound a b omega := by
  refine (matrixDerivativeNorm_finset_sum_le (Finset.Ioc a b)
    (fun k => ShellField.deriv (omega k) x)).trans ?_
  refine Finset.sum_le_sum fun k hk => ?_
  have hrk : r ≤ k := le_trans hra (le_of_lt (Finset.mem_Ioc.mp hk).1)
  exact matrixDerivativeNorm_deriv_le_shellDerivLargeCubeSupBound omega
    (le_refl k) (cubeSet_originCube_subset_of_le (d := d) hrk hx)

/-! ## The `Γ₂` tail of the high-shell envelope -/

/-- **The `Γ₂` tail of the high-shell envelope.**  The finite `Γ₂` triangle over
the shells `(a, b]` at the amplitudes `shellDerivLargeCubeConst d · 3^{-k}`,
summed by the geometric tail estimate `∑_{k ∈ (a,b]} 3^{-k} ≤ 3^{-a}`.  Unlike
`isBigOWith_gammaSigma_shellDerivLargeCubeSumSupBound` there is **no**
union-bound factor: every summand is read on its own cube `cu_k`, whose
scale-`k` sub-cube family is the singleton `{cu_k}`. -/
theorem isBigOWith_gammaSigma_shellDerivHighSumSupBound
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {a b : ℕ}
    (hab : a ≤ b) :
    IsBigOWith P.toMeasure (gammaSigma 2) (shellDerivHighSumSupBound a b)
      (shellDerivLargeCubeSumConst d * ((3 : ℝ) ^ a)⁻¹) := by
  have hconstpos : 0 < shellDerivLargeCubeConst d :=
    shellDerivLargeCubeConst_pos hPrefix
  rcases lt_or_eq_of_le hab with hlt | heq
  · have hsNonempty : (Finset.Ioc a b).Nonempty :=
      ⟨b + 1 - 1, by simp only [Finset.mem_Ioc]; omega⟩
    have hone : ∀ k : ℕ, Real.sqrt (1 + ((k - k : ℕ) : ℝ)) = 1 := by
      intro k
      rw [Nat.sub_self, Nat.cast_zero, add_zero, Real.sqrt_one]
    have hAkpos : ∀ k ∈ Finset.Ioc a b,
        0 < shellDerivLargeCubeConst d * ((3 : ℝ) ^ k)⁻¹ := by
      intro k _
      have hrpow : 0 < ((3 : ℝ) ^ k)⁻¹ :=
        inv_pos.2 (pow_pos (by norm_num : (0 : ℝ) < 3) k)
      exact mul_pos hconstpos hrpow
    have hbigO : ∀ k ∈ Finset.Ioc a b,
        IsBigO P.toMeasure (gammaSigma 2)
          (fun omega : ShellSeq d => shellDerivLargeCubeSupBound k k omega)
          (shellDerivLargeCubeConst d * ((3 : ℝ) ^ k)⁻¹) := by
      intro k _
      have hbase := isBigOWith_gammaSigma_shellDerivLargeCubeSupBound hPrefix hJ3
        (le_refl k)
      rw [hone k, mul_one] at hbase
      exact (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
        (shellDerivLargeCubeSupBound_nonneg k k)).mp hbase
    have hsum : IsBigO P.toMeasure (gammaSigma 2)
        (fun omega : ShellSeq d => shellDerivHighSumSupBound a b omega)
        (gammaTriangleConst 2 * ∑ k ∈ Finset.Ioc a b,
          shellDerivLargeCubeConst d * ((3 : ℝ) ^ k)⁻¹) :=
      isBigO_finset_sum_of_isBigO_gammaSigma
        (μ := P.toMeasure) (s := Finset.Ioc a b)
        (X := fun k omega => shellDerivLargeCubeSupBound k k omega)
        (a := fun k => shellDerivLargeCubeConst d * ((3 : ℝ) ^ k)⁻¹)
        (σ := 2) (by norm_num) hsNonempty hAkpos hbigO
        (fun k _ => measurable_shellDerivLargeCubeSupBound k k)
    have hcore : (∑ k ∈ Finset.Ioc a b, ((3 : ℝ) ^ k)⁻¹) ≤ ((3 : ℝ) ^ a)⁻¹ :=
      SuperdiffusionCLT.Probability.sum_Ioc_inv_pow_three_le hab
    have hstep : (∑ k ∈ Finset.Ioc a b,
          shellDerivLargeCubeConst d * ((3 : ℝ) ^ k)⁻¹) ≤
        shellDerivLargeCubeConst d * ((3 : ℝ) ^ a)⁻¹ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hcore hconstpos.le
    have hampl : gammaTriangleConst 2 * ∑ k ∈ Finset.Ioc a b,
          shellDerivLargeCubeConst d * ((3 : ℝ) ^ k)⁻¹ ≤
        shellDerivLargeCubeSumConst d * ((3 : ℝ) ^ a)⁻¹ := by
      refine le_trans (mul_le_mul_of_nonneg_left hstep
        gammaTriangleConst_pos.le) ?_
      rw [shellDerivLargeCubeSumConst, mul_assoc]
    have hfrom : IsBigOWith P.toMeasure (gammaSigma 2)
        (shellDerivHighSumSupBound a b)
        (gammaTriangleConst 2 * ∑ k ∈ Finset.Ioc a b,
          shellDerivLargeCubeConst d * ((3 : ℝ) ^ k)⁻¹) :=
      (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
        (shellDerivHighSumSupBound_nonneg a b)).mpr hsum
    exact hfrom.mono_scale hampl
  · have hIoc : Finset.Ioc a b = ∅ := by
      rw [heq]; exact Finset.Ioc_self b
    have hpoint : ∀ omega : ShellSeq d,
        shellDerivHighSumSupBound a b omega ≤ 0 := by
      intro omega
      rw [shellDerivHighSumSupBound, hIoc, Finset.sum_empty]
    have htarget : 0 ≤ shellDerivLargeCubeSumConst d * ((3 : ℝ) ^ a)⁻¹ :=
      mul_nonneg (shellDerivLargeCubeSumConst_pos hPrefix).le (by positivity)
    intro t ht
    have hAt : 0 ≤ shellDerivLargeCubeSumConst d * ((3 : ℝ) ^ a)⁻¹ * t :=
      mul_nonneg htarget (le_trans zero_le_one ht)
    have hempty : upperTailEvent (shellDerivHighSumSupBound a b)
        (shellDerivLargeCubeSumConst d * ((3 : ℝ) ^ a)⁻¹ * t) =
        (∅ : Set (ShellSeq d)) := by
      ext omega
      simp only [mem_upperTailEvent, Set.mem_empty_iff_false, iff_false, not_lt]
      linarith only [hpoint omega, hAt]
    rw [hempty, MeasureTheory.measureReal_empty, gammaSigma_inv]
    exact Real.exp_nonneg _

/-! ## The annealed second moment on a cube below the shells -/

/-- On the cube `cu_r` the derivative norm of the shells `(a, b]` **above** the
cube scale is dominated by the high-shell envelope. -/
theorem shellDerivCubeLinftyENorm_le_ofReal_high (omega : ShellSeq d)
    {a b r : ℕ} (hra : r ≤ a) :
    shellDerivCubeLinftyENorm a b r omega ≤
      ENNReal.ofReal (shellDerivHighSumSupBound a b omega) := by
  have hae : ∀ᵐ x ∂normalizedCubeMeasure (originCube d (r : ℤ)),
      ‖(fun x : Vec d => ShellField.matrixDerivativeNorm
        (∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x)) x‖ₑ ≤
        ENNReal.ofReal (shellDerivHighSumSupBound a b omega) := by
    have hmem : ∀ᵐ x ∂normalizedCubeMeasure (originCube d (r : ℤ)),
        x ∈ cubeSet (originCube d (r : ℤ)) :=
      MeasureTheory.Measure.ae_smul_measure
        (MeasureTheory.ae_restrict_mem (measurableSet_cubeSet _)) _
    refine hmem.mono fun x hx => ?_
    rw [← ofReal_norm, Real.norm_eq_abs,
      abs_of_nonneg (ShellField.matrixDerivativeNorm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal
      (matrixDerivativeNorm_le_shellDerivHighSumSupBound omega hra hx)
  have hbnd := MeasureTheory.eLpNorm_le_of_ae_enorm_bound
    (μ := normalizedCubeMeasure (originCube d (r : ℤ))) (p := ∞)
    (f := fun x : Vec d => ShellField.matrixDerivativeNorm
      (∑ k ∈ Finset.Ioc a b, ShellField.deriv (omega k) x))
    ((ShellField.matrixDerivativeNorm_continuous.comp
      (continuous_finsetSum _ fun k _ => (ShellField.deriv (omega k)).continuous)).aestronglyMeasurable) hae
  simpa only [shellDerivCubeLinftyENorm, Section2.Norms.cubeLpENorm,
    normalizedCubeMeasure_apply_univ (originCube d (r : ℤ)),
    ENNReal.toReal_top, inv_zero, ENNReal.rpow_zero, smul_eq_mul,
    mul_one] using hbnd

/-- **`e.nabla.kmn.Linfty` below the shells**: for a cube scale `r`
**at or below** the lowest shell `a`, the annealed second moment of
`‖∇(k_b − k_a)‖_{L^∞(cu_r)}` is bounded by `C 3^{-a}`, with no union-bound
factor.

This is the honest absolute estimate on the shells above the cube scale.  At
`r = n`, `a = ℓ`, `b = L'` it is the last factor of the printed chain
as the print reads it, on the small cube; at `r = a = m`, `b = L'`
it is the absolute estimate on the shells `(m, L']` alone. -/
theorem sqrt_second_moment_shellDerivCubeLinftyENorm_high_le
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P)
    {a b r : ℕ} (hab : a ≤ b) (hra : r ≤ a) :
    (∫⁻ omega : ShellSeq d,
        (shellDerivCubeLinftyENorm a b r omega) ^ (2 : ℕ) ∂P.toMeasure : ℝ≥0∞) ^
        ((1 : ℝ) / 2) ≤
      ENNReal.ofReal (shellDerivLargeCubeMomentConst d * ((3 : ℝ) ^ a)⁻¹) := by
  set Z : ShellSeq d → ℝ := shellDerivHighSumSupBound a b with hZ
  set A : ℝ := shellDerivLargeCubeSumConst d * ((3 : ℝ) ^ a)⁻¹ with hAdef
  have hApos : 0 < A :=
    mul_pos (shellDerivLargeCubeSumConst_pos hPrefix)
      (inv_pos.2 (pow_pos (by norm_num : (0 : ℝ) < 3) a))
  have habsZ : ∀ omega : ShellSeq d, |Z omega| = Z omega := fun omega =>
    abs_of_nonneg (shellDerivHighSumSupBound_nonneg a b omega)
  have hbigO : IsBigO P.toMeasure (gammaSigma 2) Z A := by
    show IsBigOWith P.toMeasure (gammaSigma 2) (fun omega => |Z omega|) A
    simpa only [habsZ] using
      isBigOWith_gammaSigma_shellDerivHighSumSupBound hPrefix hJ3 hab
  have hZmeas : AEMeasurable Z P.toMeasure :=
    (measurable_shellDerivHighSumSupBound a b).aemeasurable
  have hint : MeasureTheory.Integrable
      (fun omega : ShellSeq d => |Z omega| ^ (((2 : ℕ) : ℝ))) P.toMeasure :=
    SuperdiffusionCLT.Probability.integrable_abs_rpow_of_isBigO_gammaSigma_two
      hApos hZmeas hbigO 2
  have hmom := SuperdiffusionCLT.Probability.abs_moment_le_of_isBigO_gammaSigma_two
    hApos hZmeas hbigO 2
  have hptr : ∀ omega : ShellSeq d,
      (shellDerivCubeLinftyENorm a b r omega) ^ (2 : ℕ) ≤
        ENNReal.ofReal (|Z omega| ^ (((2 : ℕ) : ℝ))) := by
    intro omega
    have habs : ENNReal.ofReal (Z omega) ≤ ENNReal.ofReal |Z omega| :=
      ENNReal.ofReal_le_ofReal (le_abs_self _)
    calc (shellDerivCubeLinftyENorm a b r omega) ^ (2 : ℕ)
        ≤ (ENNReal.ofReal |Z omega|) ^ (2 : ℕ) :=
          pow_le_pow_left'
            (le_trans (shellDerivCubeLinftyENorm_le_ofReal_high omega hra) habs) 2
      _ = ENNReal.ofReal (|Z omega| ^ (2 : ℕ)) :=
          (ENNReal.ofReal_pow (abs_nonneg _) 2).symm
      _ = ENNReal.ofReal (|Z omega| ^ (((2 : ℕ) : ℝ))) := by rw [Real.rpow_natCast]
  have hlint : (∫⁻ omega : ShellSeq d,
      (shellDerivCubeLinftyENorm a b r omega) ^ (2 : ℕ) ∂P.toMeasure) ≤
      ENNReal.ofReal (A ^ (((2 : ℕ) : ℝ)) * (1 + Real.Gamma (((2 : ℕ) : ℝ) / 2 + 1))) := by
    calc (∫⁻ omega : ShellSeq d,
        (shellDerivCubeLinftyENorm a b r omega) ^ (2 : ℕ) ∂P.toMeasure)
        ≤ ∫⁻ omega : ShellSeq d,
            ENNReal.ofReal (|Z omega| ^ (((2 : ℕ) : ℝ))) ∂P.toMeasure :=
          lintegral_mono hptr
      _ = ENNReal.ofReal (∫ omega : ShellSeq d, |Z omega| ^ (((2 : ℕ) : ℝ)) ∂P.toMeasure) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
            (Filter.Eventually.of_forall fun omega =>
              Real.rpow_nonneg (abs_nonneg _) _)).symm
      _ ≤ ENNReal.ofReal (A ^ (((2 : ℕ) : ℝ)) *
            (1 + Real.Gamma (((2 : ℕ) : ℝ) / 2 + 1))) := ENNReal.ofReal_le_ofReal hmom
  have hsqrt : Real.sqrt (A ^ (((2 : ℕ) : ℝ)) * (1 + Real.Gamma (((2 : ℕ) : ℝ) / 2 + 1))) =
      shellDerivLargeCubeMomentConst d * ((3 : ℝ) ^ a)⁻¹ := by
    have hG : (0 : ℝ) < Real.Gamma 2 := Real.Gamma_pos_of_pos (by norm_num)
    rw [Real.rpow_natCast, show (((2 : ℕ) : ℝ)) / 2 + 1 = 2 by norm_num,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (le_of_lt hApos), hAdef,
      shellDerivLargeCubeMomentConst]
    ring
  have hGnn : (0 : ℝ) ≤ A ^ (((2 : ℕ) : ℝ)) * (1 + Real.Gamma (((2 : ℕ) : ℝ) / 2 + 1)) := by
    have hG : (0 : ℝ) < Real.Gamma (((2 : ℕ) : ℝ) / 2 + 1) := by
      refine Real.Gamma_pos_of_pos ?_
      norm_num
    have h1 : (0 : ℝ) ≤ A ^ (((2 : ℕ) : ℝ)) := Real.rpow_nonneg (le_of_lt hApos) _
    exact mul_nonneg h1 (by linarith only [hG])
  calc (∫⁻ omega : ShellSeq d,
      (shellDerivCubeLinftyENorm a b r omega) ^ (2 : ℕ) ∂P.toMeasure) ^ ((1 : ℝ) / 2)
      ≤ (ENNReal.ofReal (A ^ (((2 : ℕ) : ℝ)) *
          (1 + Real.Gamma (((2 : ℕ) : ℝ) / 2 + 1)))) ^ ((1 : ℝ) / 2) :=
        ENNReal.rpow_le_rpow hlint (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt (A ^ (((2 : ℕ) : ℝ)) *
          (1 + Real.Gamma (((2 : ℕ) : ℝ) / 2 + 1)))) := by
        rw [Real.sqrt_eq_rpow,
          ENNReal.ofReal_rpow_of_nonneg hGnn (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)]
    _ = ENNReal.ofReal (shellDerivLargeCubeMomentConst d * ((3 : ℝ) ^ a)⁻¹) := by
        rw [hsqrt]

/-! ## The honest first display of Step 1 -/

/-- The explicit constant of the honest first display of Step 1: the product of
the three input constants and the factor `4` of `(1 + ℓ)² ≤ 4 ℓ²`. -/
def fluxL2HighMomentConst (Cloc Ca Chigh : ℝ) : ℝ :=
  max 1 (Cloc * Ca * Chigh * 4)

theorem one_le_fluxL2HighMomentConst (Cloc Ca Chigh : ℝ) :
    1 ≤ fluxL2HighMomentConst Cloc Ca Chigh :=
  le_max_left _ _

/-! ## The first display of Step 1 from the localization line alone -/

/-- The constant `Chigh` of the high-shell bound. -/
def shellDerivHighBridgeConst (d : ℕ) : ℝ :=
  max 1 (shellDerivLargeCubeMomentConst d)

theorem one_le_shellDerivHighBridgeConst (d : ℕ) :
    1 ≤ shellDerivHighBridgeConst d :=
  le_max_left _ _

/-- **`hDerivHigh` of the honest display, discharged.**  The absolute annealed
second moment of `‖∇(k_{L'} − k_ℓ)‖_{L^∞(cu_n)}`, at the amplitude `C 3^{-ℓ}`
with no union-bound factor, from
`sqrt_second_moment_shellDerivCubeLinftyENorm_high_le`.  The shells `(ℓ, L']`
contain the shells `(m, L']` above the cube scale `m`, and the same bound at
`r = a = m`, `b = L'` gives those alone at the amplitude `C 3^{-m}`. -/
theorem deriv_high_bridge {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (S : ScaleSelection)
    (hSorder : ScalesOrdering S) :
    (∫⁻ omega : ShellSeq d,
        (shellDerivCubeLinftyENorm S.ell S.LPrime S.n omega) ^ (2 : ℕ)
      ∂P.toMeasure : ℝ≥0∞) ^ ((1 : ℝ) / 2) ≤
      ENNReal.ofReal (shellDerivHighBridgeConst d * ((3 : ℝ) ^ S.ell)⁻¹) := by
  have hab : S.ell ≤ S.LPrime :=
    le_of_lt (lt_trans (lt_trans hSorder.ell_lt_ellPrime hSorder.ellPrime_lt_m)
      hSorder.m_lt_LPrime)
  have hbase := sqrt_second_moment_shellDerivCubeLinftyENorm_high_le hPrefix hJ3
    hab (le_of_lt hSorder.n_lt_ell)
  refine le_trans hbase (ENNReal.ofReal_le_ofReal ?_)
  have hinv : (0 : ℝ) ≤ ((3 : ℝ) ^ S.ell)⁻¹ := by positivity
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) hinv

/-! ## Step 1 of `l.RHS.term1` from the localization line alone -/

end

end SuperdiffusionCLT.Section3.Terms
