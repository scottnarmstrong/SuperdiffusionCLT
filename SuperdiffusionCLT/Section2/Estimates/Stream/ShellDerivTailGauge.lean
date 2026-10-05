/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Carriers.ShellDerivLinftyNorm
public import SuperdiffusionCLT.Section2.Estimates.Stream.DerivativeConcentration
public import SuperdiffusionCLT.Probability.GammaSigmaTsum
public import SuperdiffusionCLT.Probability.OrliczTriangle

/-!
# The infinite tail of the shell derivative norms

The middle term of the printed smallness `e.kbounds.minscale.form` is

`3^m ‖∇ k - ∇ k_m‖_{L∞(cu_m)} ≤ 3^m ∑_{k > m} ‖∇ j_k‖_{L∞(cu_m)}`,

and the same quantity controls the shells above `m` in the coarse-average
display `e.bounding.something.that.is.more.complicated.than.it.seems`, where the printed
proof bounds the difference of two averages of `k_M - k_m` by the oscillation of
that field on `cu_m`.

`shellDerivTailGauge` is exactly that weighted tail. Its `Γ₂` amplitude does
**not** depend on the scale `m`: the shell derivative norm on `cu_m` is
dominated by the natural cube norm at the shell's own scale `k > m`
(`ShellField.shellCubeDerivNorm_mono`), whose `Γ₂` amplitude is `3^{-k}` by
J3, and the resulting weights `3^{m-k}` sum geometrically to `1/2` over
`k > m`.

The series is read through `ℝ≥0∞`, so that the carrier is measurable with no
summability hypothesis; on the divergent branch both the extended-real series
and the real series degenerate to the same junk value, which is what
`shellDerivTailGauge_eq_tsum` records. Almost-sure convergence itself is the
guard event of
`SuperdiffusionCLT.Section2.Cutoff.ae_forall_summable_shellDerivLinftyNorm_originCube`.

## Main definitions

* `shellDerivTailENorm`, `shellDerivTailGauge`: the weighted tail of the shell
  derivative norms on `cu_m`, as an extended-real series and as its real
  value.
* `streamDerivTailConst`: the explicit amplitude of the tail.

## Main results

* `shellDerivTailGauge_eq_tsum`: the gauge is the printed real series.
* `isBigO_gammaSigma_shellDerivTailGauge`: the `Γ₂` tail of the gauge, at an
  amplitude uniform in `m`.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section2
namespace Estimates
namespace Stream

open Homogenization MeasureTheory
open Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Carriers
open scoped ENNReal
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}
variable {P : ProbabilityMeasure (ℕ → ShellField d)}

/-! ## A nonnegative series read through `ℝ≥0∞` -/

/-! ## The infinite derivative tail -/

/-- The weighted tail `3^m ∑_{k > m} ‖∇ j_k‖_{L∞(cu_m)}` of the shell
derivative norms, as an extended-real series. -/
def shellDerivTailENorm (m : ℕ) (omega : ℕ → ShellField d) : ℝ≥0∞ :=
  ENNReal.ofReal ((3 : ℝ) ^ m) *
    ∑' k : ℕ,
      ENNReal.ofReal
        (shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ)))
          (omega (m + 1 + k)))

/-- The weighted tail `3^m ∑_{k > m} ‖∇ j_k‖_{L∞(cu_m)}` as a real random
variable: the real value of `shellDerivTailENorm`. -/
def shellDerivTailGauge (m : ℕ) (omega : ℕ → ShellField d) : ℝ :=
  (shellDerivTailENorm m omega).toReal

theorem shellDerivTailENorm_ne_top_iff (m : ℕ) (omega : ℕ → ShellField d) :
    shellDerivTailENorm m omega ≠ ⊤ ↔
      Summable fun k : ℕ =>
        shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ)))
          (omega (m + 1 + k)) := by
  have hpow : ENNReal.ofReal ((3 : ℝ) ^ m) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  constructor
  · intro hne
    have hser : (∑' k : ℕ, ENNReal.ofReal
        (shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ)))
          (omega (m + 1 + k)))) ≠ ⊤ := by
      intro htop
      exact hne (by rw [shellDerivTailENorm, htop, ENNReal.mul_top hpow])
    have h := ENNReal.summable_toReal hser
    simpa only [ENNReal.toReal_ofReal
      (shellDerivLinftyNorm_nonneg _ _)] using h
  · intro hsum
    rw [shellDerivTailENorm, ← ENNReal.ofReal_tsum_of_nonneg
      (fun k => shellDerivLinftyNorm_nonneg _ _) hsum, ← ENNReal.ofReal_mul
      (by positivity)]
    exact ENNReal.ofReal_ne_top

/-- **The gauge is the printed real series.** -/
theorem shellDerivTailGauge_eq_tsum (m : ℕ) (omega : ℕ → ShellField d) :
    shellDerivTailGauge m omega =
      (3 : ℝ) ^ m *
        ∑' k : ℕ,
          shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ)))
            (omega (m + 1 + k)) := by
  by_cases hsum : Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (m : ℤ)))
        (omega (m + 1 + k))
  · have hne := (shellDerivTailENorm_ne_top_iff m omega).2 hsum
    rw [shellDerivTailGauge, shellDerivTailENorm,
      ← ENNReal.ofReal_tsum_of_nonneg
        (fun k => shellDerivLinftyNorm_nonneg _ _) hsum,
      ← ENNReal.ofReal_mul (by positivity),
      ENNReal.toReal_ofReal
        (mul_nonneg (by positivity) (tsum_nonneg fun k =>
          shellDerivLinftyNorm_nonneg _ _))]
  · have htop : shellDerivTailENorm m omega = ⊤ := by
      by_contra hne
      exact hsum ((shellDerivTailENorm_ne_top_iff m omega).1 hne)
    rw [shellDerivTailGauge, htop, ENNReal.toReal_top,
      tsum_eq_zero_of_not_summable hsum, mul_zero]

theorem shellDerivTailGauge_nonneg (m : ℕ) (omega : ℕ → ShellField d) :
    0 ≤ shellDerivTailGauge m omega :=
  ENNReal.toReal_nonneg

theorem measurable_shellDerivTailENorm (m : ℕ) :
    Measurable (shellDerivTailENorm (d := d) m) := by
  refine measurable_const.mul (Measurable.tsum fun k => ?_)
  refine ENNReal.measurable_ofReal.comp ?_
  simp only [shellDerivLinftyNorm_openCubeSet]
  exact measurable_shellCubeDerivNorm_coordinate m (m + 1 + k)

theorem measurable_shellDerivTailGauge (m : ℕ) :
    Measurable (shellDerivTailGauge (d := d) m) :=
  (measurable_shellDerivTailENorm m).ennreal_toReal

/-! ## The `Γ₂` tail of the derivative tail gauge -/

/-- The explicit amplitude of the infinite derivative tail: the finite
triangle prefactor `16384` of `Probability/OrliczTriangle.lean` times the
geometric weight sum `∑_{k > m} 3^{m - k} = 1/2`, which does not depend on
`m`. -/
def streamDerivTailConst : ℝ := 8192

private theorem shellDerivTailWeight_eq (m k : ℕ) :
    (3 : ℝ) ^ m * (((3 : ℝ) ^ (m + 1 + k))⁻¹) =
      (3 : ℝ)⁻¹ * ((3 : ℝ)⁻¹) ^ k := by
  have h3 : (3 : ℝ) ^ (m + 1 + k) = (3 : ℝ) ^ m * (3 * (3 : ℝ) ^ k) := by
    rw [pow_add, pow_add, pow_one]
    ring
  have hm : ((3 : ℝ) ^ m) ≠ 0 := by positivity
  have hk : ((3 : ℝ) ^ k) ≠ 0 := by positivity
  rw [h3, mul_inv, mul_inv, ← mul_assoc, mul_inv_cancel₀ hm, one_mul,
    inv_pow]

private theorem summable_shellDerivTailWeight (m : ℕ) :
    Summable fun k : ℕ => (3 : ℝ) ^ m * (((3 : ℝ) ^ (m + 1 + k))⁻¹) := by
  simp only [shellDerivTailWeight_eq]
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

private theorem tsum_shellDerivTailWeight (m : ℕ) :
    ∑' k : ℕ, (3 : ℝ) ^ m * (((3 : ℝ) ^ (m + 1 + k))⁻¹) = 1 / 2 := by
  simp only [shellDerivTailWeight_eq]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/-- **The infinite form of the printed display `e.nabla.kmn.Linfty`.** Under
the J3 assumption, the weighted tail
`3^m ∑_{k > m} ‖∇ j_k‖_{L∞(cu_m)}` has a symmetric `Γ₂` tail at the amplitude
`streamDerivTailConst`, which does not depend on the scale `m`.

Each summand is dominated by the natural cube norm of its own shell,
`‖∇ j_{m+1+k}‖_{L∞(cu_m)} ≤ ‖∇ j_{m+1+k}‖_{L∞(cu_{m+1+k})}`, whose `Γ₂`
amplitude is `3^{-(m+1+k)}` by J3; after the weight `3^m` the amplitudes are
the geometric sequence `3^{-1-k}`, whose sum is `1/2`. The partial sums are
summed by the finite triangle inequality and the passage to the series is
`Probability.isBigO_gammaSigma_tsum_aux`, which needs no almost-sure
summability. -/
theorem isBigO_gammaSigma_shellDerivTailGauge (hJ3 : ShellLawJ3 d P) (m : ℕ) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (shellDerivTailGauge m) streamDerivTailConst := by
  classical
  set X : ℕ → (ℕ → ShellField d) → ℝ := fun k omega =>
    (3 : ℝ) ^ m * ShellField.shellCubeDerivNorm m (omega (m + 1 + k)) with hXdef
  set A : ℕ → ℝ := fun k => (3 : ℝ) ^ m * (((3 : ℝ) ^ (m + 1 + k))⁻¹) with hAdef
  have hApos : ∀ k : ℕ, 0 ≤ A k := by
    intro k
    rw [hAdef]
    positivity
  have hmeas : ∀ k : ℕ, Measurable (X k) := by
    intro k
    exact measurable_const.mul (measurable_shellCubeDerivNorm_coordinate m (m + 1 + k))
  have hX : ∀ k : ℕ,
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2) (X k) (A k) := by
    intro k
    have hmk : m ≤ m + 1 + k := by omega
    have hbase :
        IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
          (fun omega : ℕ → ShellField d =>
            ShellField.shellCubeDerivNorm m (omega (m + 1 + k)))
          (((3 : ℝ) ^ (m + 1 + k))⁻¹) :=
      (isBigOWith_gammaSigma_shellCubeDerivNorm_coordinate hJ3 (m + 1 + k)).of_le
        (fun omega => ShellField.shellCubeDerivNorm_mono hmk (omega (m + 1 + k)))
    have hscaled := hbase.const_mul (c := (3 : ℝ) ^ m) (by positivity)
    refine (SuperdiffusionCLT.Probability.isBigOWith_iff_isBigO_of_nonneg
      (mu := P.toMeasure) (Psi := IndependentSums.gammaSigma 2) (X := X k)
      (A := A k) ?_).1 hscaled
    intro omega
    rw [hXdef]
    have := ShellField.shellCubeDerivNorm_nonneg m (omega (m + 1 + k))
    positivity
  have hstep : ∀ s : Finset ℕ, s.Nonempty → (∀ i ∈ s, 0 < A i) →
      (∀ i ∈ s, IndependentSums.IsBigO P.toMeasure
        (IndependentSums.gammaSigma 2) (X i) (A i)) →
      (∀ i ∈ s, Measurable (X i)) →
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega => ∑ i ∈ s, X i omega) (16384 * ∑ i ∈ s, A i) := by
    intro s hs hsA hsX hsM
    exact SuperdiffusionCLT.Probability.isBigO_gammaSigma_finset_sum_of_one_le
      (mu := P.toMeasure) s (X := X) (a := A) (sigma := 2) (by norm_num) hs hsA hsX hsM
  have hpart : ∀ N : ℕ, IndependentSums.IsBigO P.toMeasure
      (IndependentSums.gammaSigma 2)
      (fun omega => ∑ k ∈ Finset.range N, X k omega)
      (16384 * ∑ k ∈ Finset.range N, A k) := by
    intro N
    exact SuperdiffusionCLT.Probability.isBigO_gammaSigma_range_sum
      (mu := P.toMeasure) (sigma := 2) (by norm_num) (by norm_num) hstep
      (fun k _ => hApos k) hmeas hX
  have htsum := SuperdiffusionCLT.Probability.isBigO_gammaSigma_tsum_aux
    (mu := P.toMeasure) (sigma := 2) (C := 16384) (by norm_num)
    (X := X) (A := A) (summable_shellDerivTailWeight m) hApos hpart
  rw [tsum_shellDerivTailWeight m] at htsum
  have hfun : (fun omega : ℕ → ShellField d => ∑' k : ℕ, X k omega) =
      shellDerivTailGauge (d := d) m := by
    funext omega
    rw [shellDerivTailGauge_eq_tsum, hXdef]
    simp only [shellDerivLinftyNorm_openCubeSet]
    exact tsum_mul_left
  rw [hfun] at htsum
  refine htsum.mono_scale ?_
  rw [streamDerivTailConst]
  norm_num
end

end Stream
end Estimates
end Section2
end SuperdiffusionCLT
