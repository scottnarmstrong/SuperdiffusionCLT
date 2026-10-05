/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Root.AnnealedDtD
public import SuperdiffusionCLT.Section8.Root.TheoremAAssemblyB
public import SuperdiffusionCLT.Section8.Prereq.SampleMeasurabilityE

/-!
# The annealed variance bound: the pointwise second moment bound with a polynomial constant
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8

open Homogenization Homogenization.Book.Ch02 MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section6
open SuperdiffusionCLT.Section8.Common.Regularity.Ported
open scoped Matrix.Norms.Elementwise ENNReal NNReal

noncomputable section

theorem annDt_vecNormSq_le {d : ℕ} (y : Vec d) : vecNormSq y ≤ (d : ℝ) * ‖y‖ ^ 2 := by
  unfold vecNormSq vecDot
  calc ∑ i, y i * y i ≤ ∑ _i : Fin d, ‖y‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := norm_le_pi_norm y i
        rw [Real.norm_eq_abs] at h
        calc y i * y i = |y i| ^ 2 := by rw [sq_abs, sq]
          _ ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = (d : ℝ) * ‖y‖ ^ 2 := by simp

/-- From the Sup-norm second moment to the Euclidean one. -/
theorem annDt_integral_vecNormSq_le {d : ℕ} {μ : Measure (Vec d)}
    (hint : Integrable (fun y => vecNormSq y) μ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∫⁻ z, edist z (0 : Vec d) ^ (2 : ℝ) ∂μ ≤ ENNReal.ofReal M) :
    ∫ y, vecNormSq y ∂μ ≤ (d : ℝ) * M := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hnn : 0 ≤ᵐ[μ] fun y : Vec d => vecNormSq y :=
    Filter.Eventually.of_forall fun y => by
      unfold vecNormSq vecDot; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h1 := ofReal_integral_eq_lintegral_ofReal hint hnn
  rw [← ENNReal.ofReal_le_ofReal_iff (mul_nonneg hd0 hM0), h1]
  calc ∫⁻ y, ENNReal.ofReal (vecNormSq y) ∂μ ≤
      ∫⁻ y, ENNReal.ofReal (d : ℝ) * edist y (0 : Vec d) ^ (2 : ℝ) ∂μ := by
        refine lintegral_mono fun y => ?_
        refine (ENNReal.ofReal_le_ofReal (annDt_vecNormSq_le y)).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul hd0, edist_zero_right, ENNReal.rpow_two,
          ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg y)]
    _ = ENNReal.ofReal (d : ℝ) * ∫⁻ y, edist y (0 : Vec d) ^ (2 : ℝ) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (d : ℝ) * ENNReal.ofReal M := by gcongr
    _ = ENNReal.ofReal ((d : ℝ) * M) := (ENNReal.ofReal_mul hd0).symm

/-- **The second moment, almost surely, with a polynomial constant in the gradient scale.** -/
theorem annDt_ae_second {d : ℕ} [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu)
    {C c4 : ℝ} (hc4 : ∀ G : ℝ, 0 ≤ G →
      crudeMomL_const d nu (Real.sqrt (max C 0))
        (min 1 (smallContrastThreshold d (1 / 2 : ℝ) * nu / (1 + 3 * ((d : ℝ) * G)))) 2 ≤
        c4 * (1 + G) ^ (8 * 2 * d))
    {Kfun : ShellSeq d → ℝ} (hK27 : ∀ omega, (27 : ℝ) ≤ Kfun omega)
    (hgrowth : ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ x : Vec d,
      matrixOperatorNorm (fullStreamRecentered omega x) ^ 2 ≤
        C * Real.log (Kfun omega ^ 2 + vecNormSq x) ^ (2 * (1 + (1 : ℝ))))
    {S : ShellSeq d → MarkovProcess.SubMarkovKernelSemigroup (Vec d)}
    (hS : ∀ᵐ omega : ShellSeq d ∂P.toMeasure,
      IsDivergenceFormFeller (fullCoefficientRecentered nu omega) (S omega)) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ t : ℝ≥0, 1 ≤ t →
      Integrable (fun y => vecNormSq y) (S omega t 0) ∧
      vecNormSq (∫ y, y ∂(S omega t 0)) ≤ ∫ y, vecNormSq y ∂(S omega t 0) ∧
      ∫ y, vecNormSq y ∂(S omega t 0) ≤
        (d : ℝ) * Real.sqrt c4 * (1 + gradScale_G omega) ^ (4 * 2 * d) *
          Real.log (Kfun omega ^ 2 + (t : ℝ)) ^ (4 * 2) * (t : ℝ) := by
  filter_upwards [hgrowth, thmA_link_data (nu := nu) hJ3, ae_contDiff_fullStreamRecentered hJ3,
    ae_fderiv_fullStreamRecentered hJ3, gradScale_ae_log_growth hPrefix hJ3, hS]
    with omega h1 hL h2 h3 hG hSo
  let D : FieldInputData d nu (fullStreamRecentered omega) :=
    { two_le := hPrefix.dimension
      nu_pos := hnu
      skew := fieldInput_matTranspose_recentered omega
      contDiff := h2
      gradConst := gradScale_G omega
      gradConst_nonneg := annDt_G_nonneg hPrefix omega
      grad_le := fun y => by rw [h3]; exact hG y }
  have hSD : S omega = D.logGrowthBounds.resolvent.kernelSemigroup := (hL D).2.2 _ hSo
  have hK2 : (2 : ℝ) ≤ Kfun omega := by linarith only [hK27 omega]
  have hceil : ⌈(1 : ℝ) + 1⌉₊ = 2 := by norm_num
  have hk := crudeMomL_opNorm_le hK2 h1
  rw [hceil] at hk
  intro t ht
  rw [hSD]
  have hprob : IsProbabilityMeasure (D.logGrowthBounds.resolvent.kernelSemigroup t 0) :=
    ⟨D.logGrowthBounds.isConservative_kernelSemigroup t 0⟩
  have hint := fieldMoment_integrable_vecNormSq D t
  refine ⟨hint, annDt_vecNormSq_integral_le hint, ?_⟩
  have hmom := fieldMoment_second_large D (Real.sqrt_nonneg _) hK2 (le_refl 2) hk ht
  have hGn := annDt_G_nonneg hPrefix omega
  have hconst := hc4 (gradScale_G omega) hGn
  have hamp : D.freezingAmplitude (smallContrastThreshold d (1 / 2 : ℝ)) =
      min 1 (smallContrastThreshold d (1 / 2 : ℝ) * nu / (1 + 3 * ((d : ℝ) * gradScale_G omega))) :=
    rfl
  rw [hamp] at hmom
  have hL1 : 0 ≤ Real.log (Kfun omega ^ 2 + (t : ℝ)) ^ (4 * 2) * (t : ℝ) := by
    have : 0 ≤ Real.log (Kfun omega ^ 2 + (t : ℝ)) :=
      zero_le_one.trans (crudeMomL_one_le_log hK2 (NNReal.coe_nonneg t))
    positivity
  have hsq : Real.sqrt (crudeMomL_const d nu (Real.sqrt (max C 0))
      (min 1 (smallContrastThreshold d (1 / 2 : ℝ) * nu / (1 + 3 * ((d : ℝ) * gradScale_G omega)))) 2)
      ≤ Real.sqrt c4 * (1 + gradScale_G omega) ^ (4 * 2 * d) := by
    refine (Real.sqrt_le_sqrt hconst).trans (le_of_eq ?_)
    have : (1 + gradScale_G omega) ^ (8 * 2 * d) =
        ((1 + gradScale_G omega) ^ (4 * 2 * d)) ^ 2 := by rw [← pow_mul]; ring_nf
    rw [this, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hM0 : 0 ≤ Real.sqrt (crudeMomL_const d nu (Real.sqrt (max C 0))
      (min 1 (smallContrastThreshold d (1 / 2 : ℝ) * nu / (1 + 3 * ((d : ℝ) * gradScale_G omega)))) 2) *
        Real.log (Kfun omega ^ 2 + (t : ℝ)) ^ (4 * 2) * (t : ℝ) := by
    have := Real.sqrt_nonneg (crudeMomL_const d nu (Real.sqrt (max C 0))
      (min 1 (smallContrastThreshold d (1 / 2 : ℝ) * nu / (1 + 3 * ((d : ℝ) * gradScale_G omega)))) 2)
    have : 0 ≤ Real.log (Kfun omega ^ 2 + (t : ℝ)) :=
      zero_le_one.trans (crudeMomL_one_le_log hK2 (NNReal.coe_nonneg t))
    positivity
  have h := annDt_integral_vecNormSq_le hint hM0 hmom
  refine h.trans ?_
  have hLn : 0 ≤ Real.log (Kfun omega ^ 2 + (t : ℝ)) :=
    zero_le_one.trans (crudeMomL_one_le_log hK2 (NNReal.coe_nonneg t))
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq
    (pow_nonneg hLn (4 * 2))) (NNReal.coe_nonneg t)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have := mul_le_mul_of_nonneg_left this hd0
  calc _ ≤ _ := this
    _ = _ := by ring

theorem annDt_one_le_log_ten {t : ℝ} (ht : 10 ≤ t) : 1 ≤ Real.log t := by
  have he : Real.exp 1 ≤ 10 := by
    have := Real.exp_one_lt_d9
    linarith only [this, ht]
  rw [Real.le_log_iff_exp_le (by linarith only [ht])]
  linarith only [he, ht]

theorem annDt_log_le {K t : ℝ} (hK : 27 ≤ K) (ht : 10 ≤ t) :
    Real.log (K ^ 2 + t) ≤ (2 * Real.log K + 1) * Real.log t := by
  have hL := annDt_one_le_log_ten ht
  have hK0 : 0 < K := by linarith only [hK]
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by linarith only [hK])
  have hK2 : 729 ≤ K ^ 2 := by nlinarith only [hK]
  have h0 := mul_nonneg (sub_nonneg.2 hK2) (sub_nonneg.2 ht)
  have h1 : K ^ 2 + t ≤ K ^ 2 * t := by nlinarith only [h0, hK2, ht]
  calc Real.log (K ^ 2 + t) ≤ Real.log (K ^ 2 * t) :=
        Real.log_le_log (by positivity) h1
    _ = 2 * Real.log K + Real.log t := by
        rw [Real.log_mul (by positivity) (by linarith only [ht]), Real.log_pow]; push_cast; ring
    _ ≤ _ := by nlinarith only [hL, hlogK]

/-- **The pointwise majorant of the deviation.**  Pure real analysis. -/
theorem annDt_Z_le {d : ℕ} {t K G X Y2 c4 cs L : ℝ} (hK : 27 ≤ K) (ht : 10 ≤ t) (hG : 0 ≤ G)
    (hY : 0 ≤ Y2) (hYX : Y2 ≤ X)
    (hX : X ≤ (d : ℝ) * Real.sqrt c4 * (1 + G) ^ (4 * 2 * d) *
      Real.log (K ^ 2 + t) ^ (4 * 2) * t) (hL : L = Real.log t) :
    |(1 / t) * X - 2 * (d : ℝ) * Real.sqrt cs * Real.sqrt L| + (1 / t) * Y2 ≤
      (2 * ((d : ℝ) * Real.sqrt c4) + 2 * (d : ℝ) * Real.sqrt cs) * L ^ 8 *
        ((1 + G) ^ (8 * d) * (2 * Real.log K + 1) ^ 8) := by
  have hL1 : 1 ≤ L := hL ▸ annDt_one_le_log_ten ht
  have ht0 : 0 < t := by linarith only [ht]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by linarith only [hK])
  have hlogK1 : 1 ≤ Real.log K := by
    rw [Real.le_log_iff_exp_le (by linarith only [hK])]
    have := Real.exp_one_lt_d9
    linarith only [this, hK]
  set v : ℝ := 2 * Real.log K + 1 with hv
  have hv1 : 1 ≤ v := by linarith only [hlogK]
  set a1 : ℝ := (d : ℝ) * Real.sqrt c4 with ha1
  have ha1n : 0 ≤ a1 := mul_nonneg hd0 (Real.sqrt_nonneg _)
  set P1 : ℝ := (1 + G) ^ (8 * d) with hP1
  have hP1' : 1 ≤ P1 := one_le_pow₀ (by linarith only [hG])
  have hlog := annDt_log_le hK ht
  rw [← hL] at hlog
  have hlog0 : 0 ≤ Real.log (K ^ 2 + t) :=
    Real.log_nonneg (by nlinarith only [hK, ht])
  have hXt : (1 / t) * X ≤ a1 * P1 * (v * L) ^ 8 := by
    have h1 : Real.log (K ^ 2 + t) ^ (4 * 2) ≤ (v * L) ^ 8 :=
      pow_le_pow_left₀ hlog0 hlog _
    have h3 : X / t ≤ a1 * P1 * (v * L) ^ 8 := by
      rw [div_le_iff₀ ht0]
      calc X ≤ a1 * P1 * Real.log (K ^ 2 + t) ^ (4 * 2) * t := hX
        _ ≤ a1 * P1 * (v * L) ^ 8 * t := by
          gcongr
    simpa [div_eq_inv_mul] using h3
  have hX0 : 0 ≤ (1 / t) * X := mul_nonneg (by positivity) (hY.trans hYX)
  have hYt : (1 / t) * Y2 ≤ (1 / t) * X := mul_le_mul_of_nonneg_left hYX (by positivity)
  have hm : 2 * (d : ℝ) * Real.sqrt cs * Real.sqrt L ≤ 2 * (d : ℝ) * Real.sqrt cs * L ^ 8 := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc Real.sqrt L ≤ L := by
          rw [Real.sqrt_le_left (by linarith only [hL1])]
          nlinarith only [hL1]
      _ ≤ L ^ 8 := by
          calc L = L ^ 1 := (pow_one L).symm
            _ ≤ L ^ 8 := pow_le_pow_right₀ hL1 (by norm_num)
  have hm0 : 0 ≤ 2 * (d : ℝ) * Real.sqrt cs * Real.sqrt L := by positivity
  have habs : |(1 / t) * X - 2 * (d : ℝ) * Real.sqrt cs * Real.sqrt L| ≤
      (1 / t) * X + 2 * (d : ℝ) * Real.sqrt cs * Real.sqrt L := by
    rw [abs_le]; constructor <;> linarith only [hX0, hm0]
  have hvL : (v * L) ^ 8 = v ^ 8 * L ^ 8 := mul_pow _ _ _
  have hvL8 : 1 ≤ v ^ 8 := one_le_pow₀ hv1
  have hL8 : 1 ≤ L ^ 8 := one_le_pow₀ hL1
  have hPV : 1 ≤ P1 * v ^ 8 := by nlinarith only [hP1', hvL8]
  rw [hvL] at hXt
  have hmain : 2 * (a1 * P1 * (v ^ 8 * L ^ 8)) + 2 * (d : ℝ) * Real.sqrt cs * L ^ 8 ≤
      (2 * a1 + 2 * (d : ℝ) * Real.sqrt cs) * L ^ 8 * (P1 * v ^ 8) := by
    have hq : 0 ≤ 2 * (d : ℝ) * Real.sqrt cs := by positivity
    have h1 : 2 * (d : ℝ) * Real.sqrt cs * L ^ 8 ≤
        2 * (d : ℝ) * Real.sqrt cs * L ^ 8 * (P1 * v ^ 8) := by
      have : 0 ≤ 2 * (d : ℝ) * Real.sqrt cs * L ^ 8 := by positivity
      nlinarith only [this, hPV]
    nlinarith only [h1]
  calc _ ≤ ((1 / t) * X + 2 * (d : ℝ) * Real.sqrt cs * Real.sqrt L) + (1 / t) * X := by
        linarith only [habs, hYt]
    _ ≤ 2 * (a1 * P1 * (v ^ 8 * L ^ 8)) + 2 * (d : ℝ) * Real.sqrt cs * L ^ 8 := by
        linarith only [hXt, hm]
    _ ≤ _ := hmain

/-! ## The moment of the majorant -/

variable {d : ℕ}

/-- The constant bounding the `2p`-th moment of the majorant. -/
def annDt_Mv (d : ℕ) (B : ℝ) (m : ℕ) : ℝ :=
  2 ^ (16 * d * m) * (1 + annDt_M (gradScale_rate d) 8 ((16 * d * m : ℕ) : ℝ)) +
    3 ^ (16 * m) * annDt_M (max B 1) 1 ((16 * m : ℕ) : ℝ)

theorem annDt_one_add_pow_le {G : ℝ} (hG : 0 ≤ G) (N : ℕ) :
    (1 + G) ^ N ≤ 2 ^ N * (1 + G ^ N) := by
  have h2N : 0 ≤ (2 : ℝ) ^ N := by positivity
  have hGN : 0 ≤ G ^ N := pow_nonneg hG N
  rcases le_total G 1 with h | h
  · have : (1 + G) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by linarith only [hG]) (by linarith only [h]) N
    nlinarith only [this, h2N, hGN]
  · have : (1 + G) ^ N ≤ (2 * G) ^ N :=
      pow_le_pow_left₀ (by linarith only [hG]) (by linarith only [h]) N
    rw [mul_pow] at this
    nlinarith only [this, h2N, hGN]

theorem annDt_pow_two_le (a b : ℝ) : a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith only [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b]

/-- **The `2p`-th moment of the majorant, with a constant independent of the law.** -/
theorem annDt_V_moment [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P)
    {Kfun : ShellSeq d → ℝ} (hKm : Measurable Kfun) (hK27 : ∀ omega, (27 : ℝ) ≤ Kfun omega)
    {B : ℝ} (hB : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma (2 * 1))
      (fun omega => Real.log (Kfun omega)) B) {p : ℝ} {m : ℕ} (hm : 2 * p ≤ m) (hp : 1 ≤ p) :
    ∫⁻ omega, ENNReal.ofReal (((1 + gradScale_G omega) ^ (8 * d) *
        (2 * Real.log (Kfun omega) + 1) ^ 8) ^ (2 * p)) ∂P.toMeasure ≤
      ENNReal.ofReal (annDt_Mv d B m) := by
  have hm2 : (2 : ℝ) ≤ m := by linarith only [hm, hp]
  have hm1 : 1 ≤ m := by
    have : (2 : ℕ) ≤ m := by exact_mod_cast hm2
    omega
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  set N1 : ℕ := 16 * d * m with hN1
  set N2 : ℕ := 16 * m with hN2
  have hN1p : (0 : ℝ) < ((N1 : ℕ) : ℝ) := by
    rw [hN1]; exact_mod_cast Nat.mul_pos (Nat.mul_pos (by norm_num) hd1) hm1
  have hN2p : (0 : ℝ) < ((N2 : ℕ) : ℝ) := by
    rw [hN2]; exact_mod_cast Nat.mul_pos (by norm_num) hm1
  have hGm := gradScale_measurable_G (d := d)
  have hlogm : Measurable fun omega => Real.log (Kfun omega) := Real.measurable_log.comp hKm
  have hlk : ∀ omega, 1 ≤ Real.log (Kfun omega) := fun omega => by
    rw [Real.le_log_iff_exp_le (by linarith only [hK27 omega])]
    have := Real.exp_one_lt_d9
    linarith only [this, hK27 omega]
  have hpt : ∀ omega, ENNReal.ofReal (((1 + gradScale_G omega) ^ (8 * d) *
        (2 * Real.log (Kfun omega) + 1) ^ 8) ^ (2 * p)) ≤
      ENNReal.ofReal (2 ^ N1) * (1 + ENNReal.ofReal (gradScale_G omega ^ ((N1 : ℕ) : ℝ))) +
      ENNReal.ofReal (3 ^ N2) * ENNReal.ofReal (Real.log (Kfun omega) ^ ((N2 : ℕ) : ℝ)) := by
    intro omega
    have hG := annDt_G_nonneg hPrefix omega
    set G := gradScale_G omega
    set lk := Real.log (Kfun omega)
    have hlk1 := hlk omega
    have hA : 1 ≤ (1 + G) ^ (8 * d) := one_le_pow₀ (by linarith only [hG])
    have hv : 1 ≤ (2 * lk + 1) ^ 8 := one_le_pow₀ (by linarith only [hlk1])
    have hV1 : 1 ≤ (1 + G) ^ (8 * d) * (2 * lk + 1) ^ 8 := by nlinarith only [hA, hv]
    have h1 : ((1 + G) ^ (8 * d) * (2 * lk + 1) ^ 8) ^ (2 * p) ≤
        ((1 + G) ^ (8 * d) * (2 * lk + 1) ^ 8) ^ ((m : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hV1 hm
    rw [Real.rpow_natCast, mul_pow, ← pow_mul, ← pow_mul] at h1
    have h2 := annDt_pow_two_le ((1 + G) ^ (8 * d * m)) ((2 * lk + 1) ^ (8 * m))
    rw [← pow_mul, ← pow_mul] at h2
    have h3 : (1 + G) ^ (8 * d * m * 2) = (1 + G) ^ N1 := by rw [hN1]; ring_nf
    have h4 : (2 * lk + 1) ^ (8 * m * 2) = (2 * lk + 1) ^ N2 := by rw [hN2]; ring_nf
    rw [h3, h4] at h2
    have h5 := annDt_one_add_pow_le hG N1
    have h6 : (2 * lk + 1) ^ N2 ≤ 3 ^ N2 * lk ^ N2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith only [hlk1]) (by linarith only [hlk1]) _
    have hsum : ((1 + G) ^ (8 * d) * (2 * lk + 1) ^ 8) ^ (2 * p) ≤
        2 ^ N1 * (1 + G ^ N1) + 3 ^ N2 * lk ^ N2 := by
      have h7 : (2 : ℝ) ^ N1 * (1 + G ^ N1) ≥ (1 + G) ^ N1 := h5
      have h8 : (1 + G) ^ N1 + (2 * lk + 1) ^ N2 ≤
          2 ^ N1 * (1 + G ^ N1) + 3 ^ N2 * lk ^ N2 := add_le_add h7 h6
      linarith only [h1, h2, h8]
    have hG1 : 0 ≤ G ^ N1 := pow_nonneg hG N1
    have hl2 : 0 ≤ lk ^ N2 := pow_nonneg (by linarith only [hlk1]) N2
    calc _ ≤ ENNReal.ofReal (2 ^ N1 * (1 + G ^ N1) + 3 ^ N2 * lk ^ N2) :=
          ENNReal.ofReal_le_ofReal hsum
      _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_add zero_le_one hG1, ENNReal.ofReal_one, Real.rpow_natCast,
            Real.rpow_natCast]
  have hG1m : Measurable fun omega => ENNReal.ofReal (gradScale_G omega ^ ((N1 : ℕ) : ℝ)) :=
    (hGm.pow_const _).ennreal_ofReal
  have hl2m : Measurable fun omega => ENNReal.ofReal (Real.log (Kfun omega) ^ ((N2 : ℕ) : ℝ)) :=
    (hlogm.pow_const _).ennreal_ofReal
  have hMG := annDt_G_moment hPrefix hJ3 hN1p
  have hMK := annDt_logK_moment (μ := P.toMeasure) hKm hK27 hB hN2p
  have hMG0 : 0 ≤ annDt_M (gradScale_rate d) 8 ((N1 : ℕ) : ℝ) := ENNReal.toReal_nonneg
  have hMK0 : 0 ≤ annDt_M (max B 1) 1 ((N2 : ℕ) : ℝ) := ENNReal.toReal_nonneg
  calc _ ≤ ∫⁻ omega, (ENNReal.ofReal (2 ^ N1) *
          (1 + ENNReal.ofReal (gradScale_G omega ^ ((N1 : ℕ) : ℝ))) +
        ENNReal.ofReal (3 ^ N2) * ENNReal.ofReal (Real.log (Kfun omega) ^ ((N2 : ℕ) : ℝ)))
          ∂P.toMeasure := lintegral_mono hpt
    _ = ENNReal.ofReal (2 ^ N1) * (1 + ∫⁻ omega, ENNReal.ofReal
            (gradScale_G omega ^ ((N1 : ℕ) : ℝ)) ∂P.toMeasure) +
        ENNReal.ofReal (3 ^ N2) * ∫⁻ omega, ENNReal.ofReal
            (Real.log (Kfun omega) ^ ((N2 : ℕ) : ℝ)) ∂P.toMeasure := by
        have e1 : ∫⁻ omega, (1 + ENNReal.ofReal (gradScale_G omega ^ ((N1 : ℕ) : ℝ))) ∂P.toMeasure =
            1 + ∫⁻ omega, ENNReal.ofReal (gradScale_G omega ^ ((N1 : ℕ) : ℝ)) ∂P.toMeasure := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
        have hsm : Measurable fun omega => (1 : ℝ≥0∞) +
            ENNReal.ofReal (gradScale_G omega ^ ((N1 : ℕ) : ℝ)) := measurable_const.add hG1m
        have e2 := lintegral_const_mul (μ := P.toMeasure) (ENNReal.ofReal (2 ^ N1)) hsm
        rw [lintegral_add_left (hsm.const_mul _), e2, e1, lintegral_const_mul _ hl2m]
    _ ≤ ENNReal.ofReal (2 ^ N1) * (1 + ENNReal.ofReal (annDt_M (gradScale_rate d) 8
            ((N1 : ℕ) : ℝ))) +
        ENNReal.ofReal (3 ^ N2) * ENNReal.ofReal (annDt_M (max B 1) 1 ((N2 : ℕ) : ℝ)) := by
        gcongr
    _ = ENNReal.ofReal (annDt_Mv d B m) := by
        rw [annDt_Mv, ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_add zero_le_one hMG0, ENNReal.ofReal_one]

/-! ## The final arithmetic -/

theorem annDt_sqrt_exp (y : ℝ) : Real.sqrt (Real.exp y) = Real.exp (y / 2) := by
  rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
  congr 1; ring

/-- **The final arithmetic of the annealed bound.** -/
theorem annDt_arith {C L a p β Λ0 Mv M3 : ℝ} (hC : 1 ≤ C) (hL : 1 ≤ L) (ha : 0 < a)
    (hp : 1 ≤ p) (hΛ0 : 0 ≤ Λ0)
    (hM3 : L ^ (8 * p) * Real.exp (-(C⁻¹ / 2 * L ^ β)) ≤ M3) :
    (C * L ^ a) ^ p + (Λ0 * L ^ 8) ^ p * Real.sqrt Mv *
        Real.sqrt (C * Real.exp (-(C⁻¹ * L ^ β))) ≤
      (((C ^ p + Λ0 ^ p * Real.sqrt Mv * Real.sqrt C * M3) ^ (1 / p)) * L ^ a) ^ p := by
  have hp0 : 0 < p := by linarith only [hp]
  have hL0 : 0 < L := by linarith only [hL]
  have hC0 : 0 < C := by linarith only [hC]
  have hLa1 : 1 ≤ L ^ a := Real.one_le_rpow hL ha.le
  have hLa0 : 0 ≤ L ^ a := by linarith only [hLa1]
  have h1 : (C * L ^ a) ^ p = C ^ p * (L ^ a) ^ p := Real.mul_rpow hC0.le hLa0
  have h2 : (Λ0 * L ^ 8) ^ p = Λ0 ^ p * L ^ (8 * p) := by
    rw [Real.mul_rpow hΛ0 (by positivity), ← Real.rpow_natCast L 8, ← Real.rpow_mul hL0.le]
    norm_num
  have h3 : Real.sqrt (C * Real.exp (-(C⁻¹ * L ^ β))) =
      Real.sqrt C * Real.exp (-(C⁻¹ / 2 * L ^ β)) := by
    rw [Real.sqrt_mul hC0.le, annDt_sqrt_exp]
    congr 2; ring
  set K1 : ℝ := Λ0 ^ p * Real.sqrt Mv * Real.sqrt C * M3 with hK1
  have hsecond : (Λ0 * L ^ 8) ^ p * Real.sqrt Mv * Real.sqrt (C * Real.exp (-(C⁻¹ * L ^ β))) ≤
      K1 := by
    rw [h2, h3]
    have hx : 0 ≤ Λ0 ^ p * Real.sqrt Mv * Real.sqrt C := by positivity
    calc Λ0 ^ p * L ^ (8 * p) * Real.sqrt Mv * (Real.sqrt C * Real.exp (-(C⁻¹ / 2 * L ^ β)))
        = (Λ0 ^ p * Real.sqrt Mv * Real.sqrt C) *
            (L ^ (8 * p) * Real.exp (-(C⁻¹ / 2 * L ^ β))) := by ring
      _ ≤ (Λ0 ^ p * Real.sqrt Mv * Real.sqrt C) * M3 := mul_le_mul_of_nonneg_left hM3 hx
      _ = K1 := by rw [hK1]
  have hLap : 1 ≤ (L ^ a) ^ p := Real.one_le_rpow hLa1 hp0.le
  have hK1nn : 0 ≤ K1 := by
    have : 0 ≤ M3 := le_trans (by positivity) hM3
    rw [hK1]; positivity
  have hCp : 0 ≤ C ^ p + K1 := by positivity
  have h4 : (((C ^ p + K1) ^ (1 / p)) * L ^ a) ^ p = (C ^ p + K1) * (L ^ a) ^ p := by
    rw [Real.mul_rpow (Real.rpow_nonneg hCp _) hLa0, ← Real.rpow_mul hCp,
      one_div, inv_mul_cancel₀ hp0.ne', Real.rpow_one]
  rw [h1, h4]
  nlinarith only [hsecond, hLap, hK1nn]

/-! ## The annealed clause -/

/-- **The annealed moment clause of Theorem A** (`e.annealed.Dt`), from the quenched clause
`hDtQ` (`e.Dt.exp`): the statement is exactly the hypothesis `hAnn` of `thmA_of_parts`. -/
theorem annDt_clause (d : ℕ) [NeZero d]
    (hDtQ : ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ cStar : ℝ, 0 < cStar →
        ∀ K : ℝ,
          ∀ δ β : ℝ, 0 < δ → δ < 1 / 4 → 0 < β → β < 4 * δ →
            ∃ C : ℝ, 1 ≤ C ∧
              ∀ (P : MeasureTheory.ProbabilityMeasure
                    (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                    hPrefix hJ2 hJ3 →
                ∃ S : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
                    MarkovProcess.SubMarkovKernelSemigroup (Homogenization.Vec d),
                  (∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                    SuperdiffusionCLT.Section8.IsDivergenceFormFeller
                      (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                      (S omega)) ∧
                  ∀ t : ℝ, 10 ≤ t →
                    (∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                      MeasureTheory.Integrable (fun y => Homogenization.vecNormSq y)
                        ((S omega) t.toNNReal (0 : Homogenization.Vec d))) ∧
                    P.toMeasure
                        {omega |
                          C * Real.log t ^ ((1 : ℝ) / 4 + δ) <
                            |(1 / t) * (∫ y, Homogenization.vecNormSq y
                                  ∂((S omega) t.toNNReal (0 : Homogenization.Vec d))) -
                                2 * (d : ℝ) * Real.sqrt cStar * Real.sqrt (Real.log t)| +
                              (1 / t) * Homogenization.vecNormSq
                                (∫ y, y ∂((S omega) t.toNNReal (0 : Homogenization.Vec d)))} ≤
                      ENNReal.ofReal (C * Real.exp (-(C⁻¹ * Real.log t ^ β)))) :
    ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ cStar : ℝ, 0 < cStar →
        ∀ K : ℝ,
          ∀ δ β : ℝ, 0 < δ → δ < 1 / 4 → 0 < β → β < 4 * δ →
              ∀ p : ℝ, 1 ≤ p →
                ∃ Cp : ℝ, 1 ≤ Cp ∧
                  ∀ (P : MeasureTheory.ProbabilityMeasure
                        (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
                    (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
                    (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
                    (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
                    SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar K
                        hPrefix hJ2 hJ3 →
                      ∃ S : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
                          MarkovProcess.SubMarkovKernelSemigroup (Homogenization.Vec d),
                        (∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
                          SuperdiffusionCLT.Section8.IsDivergenceFormFeller
                            (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
                            (S omega)) ∧
                      ∀ t : ℝ, 10 ≤ t →
                        AEMeasurable
                            (fun omega => ∫ y, Homogenization.vecNormSq y
                              ∂((S omega) t.toNNReal (0 : Homogenization.Vec d))) P.toMeasure ∧
                          AEMeasurable
                            (fun omega =>
                              ∫ y, y ∂((S omega) t.toNNReal (0 : Homogenization.Vec d)))
                            P.toMeasure ∧
                          (∫⁻ omega,
                              ENNReal.ofReal
                                (|(1 / t) * (∫ y, Homogenization.vecNormSq y
                                        ∂((S omega) t.toNNReal (0 : Homogenization.Vec d))) -
                                      2 * (d : ℝ) * Real.sqrt cStar * Real.sqrt (Real.log t)| ^ p +
                                  ((1 / t) * Homogenization.vecNormSq
                                    (∫ y, y ∂((S omega) t.toNNReal
                                      (0 : Homogenization.Vec d)))) ^ p)
                              ∂P.toMeasure) ^ (1 / p) ≤
                            ENNReal.ofReal (Cp * Real.log t ^ ((1 : ℝ) / 4 + δ)) := by

  intro nu hnu hnu1 cStar hc K δ β hδ0 hδ1 hβ0 hβ1 p hp
  obtain ⟨C, hC1, hCP⟩ := hDtQ nu hnu hnu1 cStar hc K δ β hδ0 hδ1 hβ0 hβ1
  obtain ⟨Cg, B, hscale⟩ := annDt_scale_uniform (d := d)
  obtain ⟨c4, hc4one, hc4⟩ := annDt_const_le (d := d) (nu := nu) (c0 := Real.sqrt (max Cg 0))
    (δ0 := Common.Regularity.Ported.smallContrastThreshold d (1 / 2 : ℝ)) hnu
    (Real.sqrt_nonneg _) (fieldInput_smallContrastThreshold_half_pos d) 2
  set m : ℕ := ⌈2 * p⌉₊ with hm
  set Λ0 : ℝ := 2 * ((d : ℝ) * Real.sqrt c4) + 2 * (d : ℝ) * Real.sqrt cStar with hΛ0
  have hΛ0nn : 0 ≤ Λ0 := by positivity
  have hC0 : 0 < C := by linarith only [hC1]
  obtain ⟨M3, hM3nn, hM3⟩ := annDt_pow_exp_le (q := 8 * p) (κ := C⁻¹ / 2) (β := β)
    (by positivity) hβ0
  set Mv := annDt_Mv d B m with hMvdef
  have hMv0 : 0 ≤ Mv := by
    have h1 : 0 ≤ annDt_M (gradScale_rate d) 8 ((16 * d * m : ℕ) : ℝ) := ENNReal.toReal_nonneg
    have h2 : 0 ≤ annDt_M (max B 1) 1 ((16 * m : ℕ) : ℝ) := ENNReal.toReal_nonneg
    rw [hMvdef]; unfold annDt_Mv; positivity
  set K1 : ℝ := Λ0 ^ p * Real.sqrt Mv * Real.sqrt C * M3 with hK1
  set Cp : ℝ := max 1 ((C ^ p + K1) ^ (1 / p)) with hCp
  refine ⟨Cp, le_max_left _ _, ?_⟩
  intro P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  obtain ⟨A, R, hAR, -⟩ := sampleMeas_constructed hPrefix hJ3 hnu
  have hS : ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
      IsDivergenceFormFeller (SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega)
        ((R omega).kernelSemigroup) := by
    filter_upwards [hAR] with omega h
    exact h.2.2.2
  refine ⟨fun omega => (R omega).kernelSemigroup, hS, ?_⟩
  intro t ht
  have hAR' : ∀ᵐ omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d ∂P.toMeasure,
      (A omega).a = SuperdiffusionCLT.Section6.fullCoefficientRecentered nu omega ∧
        (A omega).nu = nu ∧ (A omega).KernelResolventIdentifiesAnalyticMinimal (R omega) := by
    filter_upwards [hAR] with omega h
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  have hvm : Measurable fun y : Homogenization.Vec d => Homogenization.vecNormSq y := by
    unfold Homogenization.vecNormSq Homogenization.vecDot
    exact Finset.measurable_sum _ fun i _ =>
      (measurable_pi_apply i).mul (measurable_pi_apply i)
  have hae1 := sampleMeas_aemeasurable_integral hJ3 hnu A R hAR' t.toNNReal 0 hvm
  have hae2 := sampleMeas_aemeasurable_integral hJ3 hnu A R hAR' t.toNNReal 0
    (φ := fun y : Homogenization.Vec d => y) measurable_id
  refine ⟨hae1, hae2, ?_⟩
  obtain ⟨SQ, hSQ, hQ⟩ := hCP P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5
  have htailQ := (hQ t ht).2
  have hEq := thmA_ae_eq hPrefix hJ3 hnu hSQ hS
  obtain ⟨Kfun, hKm, hK27, hKB, hgrowth⟩ := hscale hPrefix hJ1 hJ2 hJ3 hJ4
  have hsecond := annDt_ae_second hPrefix hJ3 hnu hc4 hK27 hgrowth hS
  have hL1 : 1 ≤ Real.log t := annDt_one_le_log_ten ht
  have ht0 : 0 < t := by linarith only [ht]
  have ht1 : (1 : ℝ≥0) ≤ t.toNNReal := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal t ht0.le]
    simpa using (by linarith only [ht] : (1 : ℝ) ≤ t)
  set Z : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ := fun omega =>
    |(1 / t) * (∫ y, Homogenization.vecNormSq y ∂((R omega).kernelSemigroup t.toNNReal 0)) -
        2 * (d : ℝ) * Real.sqrt cStar * Real.sqrt (Real.log t)| +
      (1 / t) * Homogenization.vecNormSq
        (∫ y, y ∂((R omega).kernelSemigroup t.toNNReal 0)) with hZ
  set V : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ := fun omega =>
    (1 + gradScale_G omega) ^ (8 * d) * (2 * Real.log (Kfun omega) + 1) ^ 8 with hVdef
  have hVm : Measurable V := by
    have hlogm : Measurable fun omega => Real.log (Kfun omega) := Real.measurable_log.comp hKm
    exact (((measurable_const.add gradScale_measurable_G).pow_const _)).mul
      (((measurable_const.mul hlogm).add_const _).pow_const _)
  have hV0 : ∀ omega, 0 ≤ V omega := fun omega => by
    have hG := annDt_G_nonneg hPrefix omega
    have hlk : 0 ≤ Real.log (Kfun omega) := Real.log_nonneg (by linarith only [hK27 omega])
    simp only [hVdef]; positivity
  have hZV : ∀ᵐ omega ∂P.toMeasure, Z omega ≤ (Λ0 * Real.log t ^ 8) * V omega := by
    filter_upwards [hsecond] with omega h
    obtain ⟨-, hJ, hbd⟩ := h t.toNNReal ht1
    rw [Real.coe_toNNReal t ht0.le] at hbd
    have := annDt_Z_le (d := d) (t := t) (K := Kfun omega) (G := gradScale_G omega)
      (cs := cStar) (c4 := c4) (L := Real.log t) (hK27 omega) ht (annDt_G_nonneg hPrefix omega)
      (by unfold Homogenization.vecNormSq Homogenization.vecDot
          exact Finset.sum_nonneg fun i _ => mul_self_nonneg _) hJ hbd rfl
    simpa only [hZ, hVdef, hΛ0, mul_assoc] using this
  have hZ0 : ∀ᵐ omega ∂P.toMeasure, 0 ≤ Z omega := Filter.Eventually.of_forall fun omega => by
    have : 0 ≤ Homogenization.vecNormSq (∫ y, y ∂((R omega).kernelSemigroup t.toNNReal 0)) := by
      unfold Homogenization.vecNormSq Homogenization.vecDot
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    simp only [hZ]; positivity
  have hF : ∀ omega, ENNReal.ofReal
      (|(1 / t) * (∫ y, Homogenization.vecNormSq y ∂((R omega).kernelSemigroup t.toNNReal 0)) -
            2 * (d : ℝ) * Real.sqrt cStar * Real.sqrt (Real.log t)| ^ p +
        ((1 / t) * Homogenization.vecNormSq
          (∫ y, y ∂((R omega).kernelSemigroup t.toNNReal 0))) ^ p) ≤
      ENNReal.ofReal (Z omega ^ p) := fun omega => by
    refine ENNReal.ofReal_le_ofReal (Real.add_rpow_le_rpow_add (abs_nonneg _) ?_ hp)
    have : 0 ≤ Homogenization.vecNormSq (∫ y, y ∂((R omega).kernelSemigroup t.toNNReal 0)) := by
      unfold Homogenization.vecNormSq Homogenization.vecDot
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    positivity
  have hMvint := annDt_V_moment hPrefix hJ3 hKm hK27 hKB (Nat.le_ceil (2 * p)) hp
  have htail : P.toMeasure {omega | C * Real.log t ^ ((1 : ℝ) / 4 + δ) < Z omega} ≤
      ENNReal.ofReal (C * Real.exp (-(C⁻¹ * Real.log t ^ β))) := by
    refine le_trans (le_of_eq ?_) htailQ
    refine measure_congr ?_
    filter_upwards [hEq] with omega h
    simp only [hZ, h]
  have hsplit := annDt_split (μ := P.toMeasure) (p := p)
    (θ := C * Real.log t ^ ((1 : ℝ) / 4 + δ)) (Λ := Λ0 * Real.log t ^ 8)
    (τ := C * Real.exp (-(C⁻¹ * Real.log t ^ β))) (Mv := Mv) (Z := Z) (V := V)
    (F := fun omega => ENNReal.ofReal
      (|(1 / t) * (∫ y, Homogenization.vecNormSq y ∂((R omega).kernelSemigroup t.toNNReal 0)) -
            2 * (d : ℝ) * Real.sqrt cStar * Real.sqrt (Real.log t)| ^ p +
        ((1 / t) * Homogenization.vecNormSq
          (∫ y, y ∂((R omega).kernelSemigroup t.toNNReal 0))) ^ p))
    hp (by positivity) (by positivity) (by positivity) hMv0 (Filter.Eventually.of_forall hF) hZ0
    hZV hVm hV0 hMvint htail
  have hArith := annDt_arith (C := C) (L := Real.log t) (a := (1 : ℝ) / 4 + δ) (p := p) (β := β)
    (Λ0 := Λ0) (Mv := Mv) (M3 := M3) hC1 hL1 (by linarith only [hδ0]) hp hΛ0nn (hM3 _ hL1)
  have hCpmono : (((C ^ p + K1) ^ (1 / p)) * Real.log t ^ ((1 : ℝ) / 4 + δ)) ^ p ≤
      (Cp * Real.log t ^ ((1 : ℝ) / 4 + δ)) ^ p := by
    refine Real.rpow_le_rpow (by positivity) ?_ (by linarith only [hp])
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hfin := hsplit.trans (ENNReal.ofReal_le_ofReal (hArith.trans hCpmono))
  have hp0 : 0 < p := by linarith only [hp]
  calc _ ≤ (ENNReal.ofReal ((Cp * Real.log t ^ ((1 : ℝ) / 4 + δ)) ^ p)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hfin (by positivity)
    _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), ← Real.rpow_mul
          (by positivity), mul_one_div_cancel hp0.ne', Real.rpow_one]

end

end SuperdiffusionCLT.Section8
