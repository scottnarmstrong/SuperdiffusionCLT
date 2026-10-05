/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.SmoothData
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The real trigonometric tight frame on a unit cell

On the cell `(-1/2, 1/2]^d` the functions `cos (2 π m · u)` and `sin (2 π m · u)`,
`m ∈ ℤ^d`, form a real tight frame: for continuous `f, g` supported in the open
cell,
`∑_m (c_cos_m f * c_cos_m g + c_sin_m f * c_sin_m g) = ∫ f g`.
This is Parseval's identity on the torus `UnitAddTorus (Fin d)` from Mathlib,
transported to `Vec d` and split into real and imaginary parts.

The index type is `(Fin d → ℤ) ⊕ (Fin d → ℤ)`, `inl m` for the cosine and `inr m`
for the sine of frequency `m`.

## Main definitions

* `cellPhase`, `cellTrig`: the phase `2 π m · u` and the real frame functions.
* `cellCoeff`: the frame coefficient `∫ u, cellTrig p u * f u`.
* `cellKernelCoeff`: the coefficient of the cell-localized kernel
  `u ↦ w u * ψ (x - c - u)`, i.e. of the white-noise cell with centre `c`.

## Main results

* `hasSum_cellCoeff_mul_cellCoeff`: the Parseval identity for general `f, g`.
* `hasSum_cellKernelCoeff_mul`: its specialization giving the covariance
  `∑_p c_p(x) c_p(x') = ∫ z, w (z - c) ^ 2 * ψ (x - z) * ψ (x' - z)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization Set Real MeasureTheory UnitAddTorus
open scoped Real ComplexConjugate

noncomputable section

variable {d : ℕ}

/-! ## Definitions -/

/-- The phase `2 π (m · u)` of the frequency-`m` plane wave. -/
def cellPhase (m : Fin d → ℤ) (u : Vec d) : ℝ := 2 * π * ∑ i, (m i : ℝ) * u i

/-- The real frame functions: `cos (cellPhase m ·)` for `inl m` and
`sin (cellPhase m ·)` for `inr m`. -/
def cellTrig : ((Fin d → ℤ) ⊕ (Fin d → ℤ)) → Vec d → ℝ
  | .inl m, u => Real.cos (cellPhase m u)
  | .inr m, u => Real.sin (cellPhase m u)

/-- The frame coefficient `∫ u, cellTrig p u * f u`. -/
def cellCoeff (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) (f : Vec d → ℝ) : ℝ :=
  ∫ u, cellTrig p u * f u

/-- The coefficient, at frame index `p`, of the cell kernel
`u ↦ w u * ψ (x - c - u)` for the cell centred at `c`. -/
def cellKernelCoeff (c x : Vec d) (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) : ℝ :=
  cellCoeff p fun u ↦ cellWeight d u * radialBump d (x - c - u)

theorem continuous_cellPhase (m : Fin d → ℤ) : Continuous (cellPhase m) :=
  continuous_const.mul
    (continuous_finsetSum _ fun i _ ↦ continuous_const.mul (continuous_apply i))

theorem continuous_cellTrig (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) : Continuous (cellTrig p) := by
  rcases p with m | m
  · exact Real.continuous_cos.comp (continuous_cellPhase m)
  · exact Real.continuous_sin.comp (continuous_cellPhase m)

theorem abs_cellTrig_le_one (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) (u : Vec d) :
    |cellTrig p u| ≤ 1 := by
  rcases p with m | m
  · exact Real.abs_cos_le_one _
  · exact Real.abs_sin_le_one _

/-- The support hypothesis shared by all functions on the cell: they vanish
unless every coordinate is in the open interval `(-1/2, 1/2)`. -/
theorem hasCompactSupport_of_cell {f : Vec d → ℝ}
    (hf0 : ∀ u, f u ≠ 0 → ∀ i, |u i| < 1 / 2) : HasCompactSupport f := by
  refine HasCompactSupport.intro (K := Set.pi Set.univ fun _ : Fin d ↦ Icc (-(1 / 2 : ℝ)) (1 / 2))
    (isCompact_univ_pi fun _ ↦ isCompact_Icc) fun y hy ↦ ?_
  by_contra hne
  refine hy fun i _ ↦ ?_
  have := hf0 y hne i
  exact ⟨by linarith only [(abs_lt.1 this).1], by linarith only [(abs_lt.1 this).2]⟩

theorem integrable_cellTrig_mul {f : Vec d → ℝ} (hf : Continuous f)
    (hf0 : ∀ u, f u ≠ 0 → ∀ i, |u i| < 1 / 2) (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) :
    Integrable (fun u ↦ cellTrig p u * f u) :=
  ((continuous_cellTrig p).mul hf).integrable_of_hasCompactSupport
    ((hasCompactSupport_of_cell hf0).mul_left)

/-! ## Transfer to the torus -/

/-- The unit circle carries the Haar probability measure, as in Mathlib's torus
Fourier file. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The point of the unit torus represented by `x`. -/
def torusPt (x : Vec d) : UnitAddTorus (Fin d) := fun i ↦ ((x i : ℝ) : UnitAddCircle)

/-- The representative in `(-1/2, 1/2]^d` of a point of the torus. -/
def cellLift (θ : UnitAddTorus (Fin d)) : Vec d :=
  fun i ↦ (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) (θ i) : ℝ)

theorem cellLift_torusPt {x : Vec d}
    (hx : ∀ i, x i ∈ Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)) : cellLift (torusPt x) = x := by
  funext i
  exact congrArg Subtype.val (AddCircle.equivIoc_coe_eq (hx i))

theorem measurable_cellLift : Measurable (cellLift (d := d)) := by
  refine Measurable.of_eval fun i ↦ ?_
  exact measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIoc (1 : ℝ) (-(1 / 2 : ℝ))).measurable.comp (measurable_pi_apply i))

/-- The function on the torus obtained from a function on the cell. -/
def cellG (f : Vec d → ℝ) (θ : UnitAddTorus (Fin d)) : ℂ := ((f (cellLift θ) : ℝ) : ℂ)

theorem mFourier_neg_torusPt (n : Fin d → ℤ) (x : Vec d) :
    mFourier (-n) (torusPt x) =
      ((Real.cos (cellPhase n x) : ℝ) : ℂ) - Complex.I * ((Real.sin (cellPhase n x) : ℝ) : ℂ) := by
  have h : mFourier (-n) (torusPt x) = Complex.exp (((-cellPhase n x : ℝ) : ℂ) * Complex.I) := by
    unfold mFourier torusPt
    simp only [ContinuousMap.coe_mk, Pi.neg_apply]
    simp_rw [fourier_coe_apply]
    rw [← Complex.exp_sum]
    congr 1
    unfold cellPhase
    push_cast
    simp only [neg_mul, Finset.mul_sum, Finset.sum_mul]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
    Real.sin_neg]
  push_cast
  ring

theorem mem_cellIoc {u : Vec d} (h : ∀ i, |u i| < 1 / 2) :
    ∀ i, u i ∈ Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) := fun i ↦ by
  have := abs_lt.1 (h i)
  exact ⟨by linarith only [this.1], by linarith only [this.2]⟩

theorem measurableSet_cellIoc :
    MeasurableSet {x : Vec d | ∀ i, x i ∈ Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)} :=
  MeasurableSet.univ_pi' fun _ ↦ measurableSet_Ioc

/-- The integral over the torus of a function lifted from the cell is the integral
over `Vec d`. -/
theorem integral_cellLift (h : Vec d → ℝ) (hh0 : ∀ u, h u ≠ 0 → ∀ i, |u i| < 1 / 2) :
    ∫ θ : UnitAddTorus (Fin d), ((h (cellLift θ) : ℝ) : ℂ) = ((∫ u, h u : ℝ) : ℂ) := by
  rw [integral_preimage (fun θ ↦ ((h (cellLift θ) : ℝ) : ℂ)) (fun _ ↦ -(1 / 2 : ℝ))]
  rw [← integral_complex_ofReal]
  have hK := measurableSet_cellIoc (d := d)
  calc ∫ x in {x : Vec d | ∀ i, x i ∈ Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)},
        ((h (cellLift fun i ↦ ((x i : ℝ) : UnitAddCircle)) : ℝ) : ℂ)
      = ∫ x in {x : Vec d | ∀ i, x i ∈ Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)},
        ((h x : ℝ) : ℂ) := by
        refine setIntegral_congr_fun hK fun x hx ↦ ?_
        have := cellLift_torusPt (d := d) hx
        exact congrArg (fun y ↦ ((h y : ℝ) : ℂ)) this
    _ = ∫ x, ((h x : ℝ) : ℂ) := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ ?_
        by_contra hne
        exact hx (mem_cellIoc (hh0 x (by
          intro h0; exact hne (by rw [h0]; simp))))

/-- The Fourier coefficients on the torus of a function lifted from the cell are the
cosine and sine coefficients. -/
theorem mFourierCoeff_cellG {f : Vec d → ℝ} (hf : Continuous f)
    (hf0 : ∀ u, f u ≠ 0 → ∀ i, |u i| < 1 / 2) (n : Fin d → ℤ) :
    mFourierCoeff (cellG f) n =
      ((cellCoeff (.inl n) f : ℝ) : ℂ) - Complex.I * ((cellCoeff (.inr n) f : ℝ) : ℂ) := by
  rw [mFourierCoeff_eq_integral (cellG f) n (fun _ ↦ -(1 / 2 : ℝ))]
  have hK := measurableSet_cellIoc (d := d)
  have hF : ∀ x : Vec d, ¬ (∀ i, x i ∈ Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)) →
      mFourier (-n) (torusPt x) • ((f x : ℝ) : ℂ) = 0 := by
    intro x hx
    have : f x = 0 := by
      by_contra hne
      exact hx (mem_cellIoc (hf0 x hne))
    rw [this]; simp
  change ∫ x in {x : Vec d | ∀ i, x i ∈ Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)},
      mFourier (-n) (torusPt x) • cellG f (torusPt x) = _
  have h1 : ∫ x in {x : Vec d | ∀ i, x i ∈ Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)},
      mFourier (-n) (torusPt x) • cellG f (torusPt x)
      = ∫ x in {x : Vec d | ∀ i, x i ∈ Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)},
      mFourier (-n) (torusPt x) • ((f x : ℝ) : ℂ) :=
    setIntegral_congr_fun hK fun x hx ↦ by
      have := cellLift_torusPt (d := d) hx
      simp only [cellG, this]
  have h2 : ∫ x in {x : Vec d | ∀ i, x i ∈ Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)},
      mFourier (-n) (torusPt x) • ((f x : ℝ) : ℂ)
      = ∫ x, mFourier (-n) (torusPt x) • ((f x : ℝ) : ℂ) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hF
  rw [h1, h2]
  have hpt : ∀ x : Vec d, mFourier (-n) (torusPt x) • ((f x : ℝ) : ℂ)
      = ((cellTrig (.inl n) x * f x : ℝ) : ℂ)
        - Complex.I * ((cellTrig (.inr n) x * f x : ℝ) : ℂ) := by
    intro x
    rw [mFourier_neg_torusPt, smul_eq_mul]
    simp only [cellTrig, Complex.ofReal_mul]
    ring
  simp_rw [hpt]
  rw [integral_sub, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal]
  · rfl
  · exact (integrable_cellTrig_mul hf hf0 _).ofReal
  · exact ((integrable_cellTrig_mul hf hf0 _).ofReal).const_mul _

theorem memLp_cellG {f : Vec d → ℝ} (hf : Continuous f)
    (hf0 : ∀ u, f u ≠ 0 → ∀ i, |u i| < 1 / 2) :
    MemLp (cellG f) 2 (volume : Measure (UnitAddTorus (Fin d))) := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support (hasCompactSupport_of_cell hf0)
  refine MemLp.of_bound (C := C)
    (Complex.measurable_ofReal.comp (hf.measurable.comp measurable_cellLift)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ ↦ ?_)
  simpa only [cellG, Complex.norm_real, Real.norm_eq_abs] using hC (cellLift θ)

/-- Parseval for the cosine and sine coefficients, summed frequency by frequency. -/
theorem hasSum_cellCoeff_pair {f g : Vec d → ℝ} (hf : Continuous f)
    (hf0 : ∀ u, f u ≠ 0 → ∀ i, |u i| < 1 / 2) (hg : Continuous g)
    (hg0 : ∀ u, g u ≠ 0 → ∀ i, |u i| < 1 / 2) :
    HasSum (fun n : Fin d → ℤ ↦ cellCoeff (.inl n) f * cellCoeff (.inl n) g
      + cellCoeff (.inr n) f * cellCoeff (.inr n) g) (∫ u, f u * g u) := by
  have hmf := memLp_cellG hf hf0
  have hmg := memLp_cellG hg hg0
  have h := hasSum_prod_mFourierCoeff (hmf.toLp (cellG f)) (hmg.toLp (cellG g))
  have hc : ∀ (h : Vec d → ℝ) (hm : MemLp (cellG h) 2 (volume : Measure (UnitAddTorus (Fin d)))),
      ∀ n, mFourierCoeff (hm.toLp (cellG h)) n = mFourierCoeff (cellG h) n := by
    intro h hm n
    refine integral_congr_ae ?_
    filter_upwards [hm.coeFn_toLp] with t ht
    rw [ht]
  have hI : ∫ t, conj ((hmf.toLp (cellG f)) t) * (hmg.toLp (cellG g)) t
      = ((∫ u, f u * g u : ℝ) : ℂ) := by
    rw [← integral_cellLift (fun u ↦ f u * g u) (fun u hu ↦ by
      by_cases hfu : f u = 0
      · exact absurd (by rw [hfu, zero_mul]) hu
      · exact hf0 u hfu)]
    refine integral_congr_ae ?_
    filter_upwards [hmf.coeFn_toLp, hmg.coeFn_toLp] with t ht1 ht2
    rw [ht1, ht2]
    simp [cellG, Complex.conj_ofReal]
  have h' : HasSum (fun n ↦ conj (mFourierCoeff (cellG f) n) * mFourierCoeff (cellG g) n)
      ((∫ u, f u * g u : ℝ) : ℂ) := by
    rw [← hI]; simpa only [hc] using h
  have hre := Complex.hasSum_re h'
  rw [Complex.ofReal_re] at hre
  refine hre.congr_fun fun n ↦ ?_
  rw [mFourierCoeff_cellG hf hf0, mFourierCoeff_cellG hg hg0]
  simp [Complex.mul_re]

/-- The cosine part of the pairing is absolutely summable. -/
theorem summable_cellCoeff_mul_inl {f g : Vec d → ℝ} (hf : Continuous f)
    (hf0 : ∀ u, f u ≠ 0 → ∀ i, |u i| < 1 / 2) (hg : Continuous g)
    (hg0 : ∀ u, g u ≠ 0 → ∀ i, |u i| < 1 / 2) :
    Summable (fun n : Fin d → ℤ ↦ cellCoeff (.inl n) f * cellCoeff (.inl n) g) := by
  have hff := (hasSum_cellCoeff_pair hf hf0 hf hf0).summable
  have hgg := (hasSum_cellCoeff_pair hg hg0 hg hg0).summable
  refine Summable.of_norm_bounded ((hff.add hgg).div_const 2) fun n ↦ ?_
  rw [Real.norm_eq_abs, abs_le]
  have := sq_nonneg (cellCoeff (.inr n) f)
  have := sq_nonneg (cellCoeff (.inr n) g)
  constructor <;>
    nlinarith only [sq_nonneg (cellCoeff (.inl n) f + cellCoeff (.inl n) g),
      sq_nonneg (cellCoeff (.inl n) f - cellCoeff (.inl n) g),
      sq_nonneg (cellCoeff (.inr n) f), sq_nonneg (cellCoeff (.inr n) g)]

/-- The sine part of the pairing is absolutely summable. -/
theorem summable_cellCoeff_mul_inr {f g : Vec d → ℝ} (hf : Continuous f)
    (hf0 : ∀ u, f u ≠ 0 → ∀ i, |u i| < 1 / 2) (hg : Continuous g)
    (hg0 : ∀ u, g u ≠ 0 → ∀ i, |u i| < 1 / 2) :
    Summable (fun n : Fin d → ℤ ↦ cellCoeff (.inr n) f * cellCoeff (.inr n) g) := by
  have hff := (hasSum_cellCoeff_pair hf hf0 hf hf0).summable
  have hgg := (hasSum_cellCoeff_pair hg hg0 hg hg0).summable
  refine Summable.of_norm_bounded ((hff.add hgg).div_const 2) fun n ↦ ?_
  rw [Real.norm_eq_abs, abs_le]
  constructor <;>
    nlinarith only [sq_nonneg (cellCoeff (.inr n) f + cellCoeff (.inr n) g),
      sq_nonneg (cellCoeff (.inr n) f - cellCoeff (.inr n) g),
      sq_nonneg (cellCoeff (.inl n) f), sq_nonneg (cellCoeff (.inl n) g)]

/-- **Parseval for the real trigonometric frame on the cell.** For continuous
`f, g` supported in the open cell `(-1/2, 1/2)^d`,
`∑_p cellCoeff p f * cellCoeff p g = ∫ f g`, the sum running over all cosine and
sine frequencies. -/
theorem hasSum_cellCoeff_mul_cellCoeff {f g : Vec d → ℝ} (hf : Continuous f)
    (hf0 : ∀ u, f u ≠ 0 → ∀ i, |u i| < 1 / 2) (hg : Continuous g)
    (hg0 : ∀ u, g u ≠ 0 → ∀ i, |u i| < 1 / 2) :
    HasSum (fun p : (Fin d → ℤ) ⊕ (Fin d → ℤ) ↦ cellCoeff p f * cellCoeff p g)
      (∫ u, f u * g u) := by
  have hu := summable_cellCoeff_mul_inl hf hf0 hg hg0
  have hv := summable_cellCoeff_mul_inr hf hf0 hg hg0
  have hab := hasSum_cellCoeff_pair hf hf0 hg hg0
  have heq : (∑' n, cellCoeff (.inl n) f * cellCoeff (.inl n) g)
      + (∑' n, cellCoeff (.inr n) f * cellCoeff (.inr n) g) = ∫ u, f u * g u :=
    ((hu.hasSum.add hv.hasSum).unique hab)
  have hs := HasSum.sum (f := fun p : (Fin d → ℤ) ⊕ (Fin d → ℤ) ↦
    cellCoeff p f * cellCoeff p g) hu.hasSum hv.hasSum
  rwa [heq] at hs

/-! ## The cell kernel of the white-noise construction -/

theorem continuous_cellKernel (c x : Vec d) :
    Continuous fun u : Vec d ↦ cellWeight d u * radialBump d (x - c - u) :=
  (cellWeight_contDiff.continuous).mul
    (radialBump_contDiff.continuous.comp (continuous_const.sub continuous_id))

theorem cellKernel_support {c x : Vec d} {u : Vec d}
    (h : cellWeight d u * radialBump d (x - c - u) ≠ 0) (i : Fin d) : |u i| < 1 / 2 :=
  abs_lt_half_of_cellWeight_ne_zero (left_ne_zero_of_mul h) i

/-- **Covariance of the cell kernels.** The frame coefficients of the kernel
`u ↦ w u * ψ (x - c - u)` satisfy
`∑_p c_p(x) c_p(x') = ∫ z, w (z - c) ^ 2 * (ψ (x - z) * ψ (x' - z))`. -/
theorem hasSum_cellKernelCoeff_mul (c x x' : Vec d) :
    HasSum (fun p : (Fin d → ℤ) ⊕ (Fin d → ℤ) ↦ cellKernelCoeff c x p * cellKernelCoeff c x' p)
      (∫ z, cellWeight d (z - c) ^ 2 * (radialBump d (x - z) * radialBump d (x' - z))) := by
  have h := hasSum_cellCoeff_mul_cellCoeff (continuous_cellKernel c x)
    (fun u hu i ↦ cellKernel_support hu i) (continuous_cellKernel c x')
    (fun u hu i ↦ cellKernel_support hu i)
  have hint : (∫ u, (cellWeight d u * radialBump d (x - c - u))
        * (cellWeight d u * radialBump d (x' - c - u)))
      = ∫ z, cellWeight d (z - c) ^ 2 * (radialBump d (x - z) * radialBump d (x' - z)) := by
    rw [← integral_add_right_eq_self
      (fun z : Vec d ↦ cellWeight d (z - c) ^ 2 * (radialBump d (x - z) * radialBump d (x' - z))) c]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
    have e1 : x - (u + c) = x - c - u := by abel
    have e2 : x' - (u + c) = x' - c - u := by abel
    have e3 : u + c - c = u := by abel
    simp only [e1, e2, e3]
    ring
  rw [← hint]
  exact h

/-- The covariance total of a cell kernel is strictly positive: the integrand is
continuous, nonnegative, compactly supported, and equal to `1` at the cell centre. -/
theorem cellKernel_integral_pos (c : Vec d) :
    0 < ∫ z, cellWeight d (z - c) ^ 2 * (radialBump d (c - z) * radialBump d (c - z)) := by
  have hw : HasCompactSupport fun z : Vec d ↦ cellWeight d (z - c) :=
    cellWeight_hasCompactSupport.comp_homeomorph (Homeomorph.subRight c)
  have hcs : HasCompactSupport fun z : Vec d ↦
      cellWeight d (z - c) ^ 2 * (radialBump d (c - z) * radialBump d (c - z)) := by
    refine HasCompactSupport.intro hw.isCompact fun z hz ↦ ?_
    have : cellWeight d (z - c) = 0 := by
      by_contra hne
      exact hz (subset_tsupport _ hne)
    rw [this]; ring
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := c) ?_ hcs
    (fun z ↦ mul_nonneg (sq_nonneg _) (mul_nonneg (radialBump_nonneg _) (radialBump_nonneg _)))
    (by simp)
  have hc1 : Continuous fun z : Vec d ↦ cellWeight d (z - c) :=
    cellWeight_contDiff.continuous.comp (continuous_id.sub continuous_const)
  have hc2 : Continuous fun z : Vec d ↦ radialBump d (c - z) :=
    radialBump_contDiff.continuous.comp (continuous_const.sub continuous_id)
  exact (hc1.pow 2).mul (hc2.mul hc2)

/-! ## Satisfiability witness -/

/-- The covariance identity is not vacuous: for `d = 2`, the kernel pairing at the
origin has strictly positive total mass. -/
example : ∃ t : ℝ, 0 < t ∧ HasSum (fun p : (Fin 2 → ℤ) ⊕ (Fin 2 → ℤ) ↦
    cellKernelCoeff (0 : Vec 2) 0 p * cellKernelCoeff 0 0 p) t := by
  refine ⟨_, ?_, hasSum_cellKernelCoeff_mul 0 0 0⟩
  simpa only [zero_sub, neg_neg] using cellKernel_integral_pos (0 : Vec 2)

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
