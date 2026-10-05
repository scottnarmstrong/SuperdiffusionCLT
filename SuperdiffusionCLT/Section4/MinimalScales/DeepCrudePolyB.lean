/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section4.MinimalScales.DeepCrudePoly
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinfty
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolumeBelow
public import SuperdiffusionCLT.Frozen.Section4.LNaught
public import SuperdiffusionCLT.Assumptions.ShellLaw.J5Consequences

/-!
# srootD4: the polynomial crude bound for the deep-scale response

The squared deep-scale response of `srootE_field` against `σ • 1` is dominated, uniformly in the
cutoff and in the deep scale, by `srootD4_R d nu σ (srootD4_T m ω)`. Here the random envelope
`srootD4_T m` is shown to have a `Γ₂` tail at amplitude `cT (1 + m)²`, the diffusivity `σ` is
sandwiched by the envelope scalars, and the threshold `lNaught` at `alpha = 1/2` is shown to
dominate `nu⁻⁴` up to a universal constant. The resulting bound is a `Γ_{1/2}` tail at amplitude
`A0 (1 + m)^10`, and not the `Γ₁` tail at amplitude `A0 (1 + m)^p` for small `p` that a flat or
square-root growth law would give: the ellipticity ratio `Lam` of the cutoff field is quadratic
in the stream envelope, so the response majorant is quartic in a `Γ₂` variable.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section4.MinimalScales

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Probability

/-- The amplitude constant of the envelope `srootD4_T`. -/
noncomputable def srootD4_cT (d : ℕ) : ℝ :=
  max 1 (IndependentSums.gammaTriangleConst 2 *
    (131072 * shellValueLargeCubeConst d + 8192 * Real.sqrt d))

section Envelope

variable {d : ℕ} [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}

omit [NeZero d] in
theorem measurable_srootD4_T (m : ℕ) : Measurable (srootD4_T (d := d) m) := by
  unfold srootD4_T
  exact ((Finset.measurable_sum _ fun l _ => measurable_shellValueLargeCubeSupBound l (m + 1)).const_mul
    2).add ((measurable_shellDerivTailGauge (m + 1)).const_mul _)

omit [NeZero d] in
theorem srootD4_T_nonneg (m : ℕ) (omega : ShellSeq d) : 0 ≤ srootD4_T m omega := by
  unfold srootD4_T
  have h1 : 0 ≤ ∑ l ∈ Finset.range (m + 2), shellValueLargeCubeSupBound l (m + 1) omega :=
    Finset.sum_nonneg fun l _ => shellValueLargeCubeSupBound_nonneg _ _ _
  have h2 : 0 ≤ shellDerivTailGauge (m + 1) omega := shellDerivTailGauge_nonneg _ _
  positivity

/-- The envelope `T` has a `Γ₂` tail at a polynomial amplitude. -/
theorem srootD4_T_isBigO (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (m : ℕ) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
      (srootD4_T m) (srootD4_cT d * (1 + (m : ℝ)) ^ 2) := by
  have hCv : 0 < shellValueLargeCubeConst d := shellValueLargeCubeConst_pos hPrefix
  have hdpos : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d))
  have htri : 0 < IndependentSums.gammaTriangleConst 2 := IndependentSums.gammaTriangleConst_pos
  set a : ℝ := shellValueLargeCubeConst d * Real.sqrt ((m : ℝ) + 2) with ha
  have ha0 : 0 < a := mul_pos hCv (Real.sqrt_pos.2 (by positivity))
  have hV : ∀ l ∈ Finset.range (m + 2),
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 2)
        (fun omega : ShellSeq d => shellValueLargeCubeSupBound l (m + 1) omega) a := by
    intro l hl
    have hlm : l ≤ m + 1 := by simp only [Finset.mem_range] at hl; omega
    have h := isBigOWith_gammaSigma_shellValueLargeCubeSupBound hPrefix hJ3 (k := l) (m := m + 1) hlm
    refine (isBigOWith_iff_isBigO_of_nonneg (fun omega => shellValueLargeCubeSupBound_nonneg _ _ _)).1 ?_
    refine h.mono_scale ?_
    rw [ha]
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hCv.le
    have : ((m + 1 - l : ℕ) : ℝ) ≤ (m : ℝ) + 1 := by
      have : m + 1 - l ≤ m + 1 := Nat.sub_le _ _
      exact_mod_cast this
    linarith only [this]
  have hsumV := isBigO_gammaSigma_finset_sum_of_one_le (mu := P.toMeasure) (Finset.range (m + 2))
    (X := fun l (omega : ShellSeq d) => shellValueLargeCubeSupBound l (m + 1) omega)
    (a := fun _ => a) (sigma := 2) (by norm_num) (by simp)
    (fun _ _ => ha0) hV (fun l _ => measurable_shellValueLargeCubeSupBound l (m + 1))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsumV
  have hsumV2 := hsumV.const_mul (c := 2) (by norm_num)
  have hG := (isBigO_gammaSigma_shellDerivTailGauge (P := P) hJ3 (m + 1)).const_mul
    (c := Real.sqrt d) hdpos.le
  have hA : 0 < 2 * (16384 * (((m + 2 : ℕ) : ℝ) * a)) := by positivity
  have hB : 0 < Real.sqrt d * streamDerivTailConst := by
    have : 0 < streamDerivTailConst := by unfold streamDerivTailConst; norm_num
    positivity
  have hadd := isBigO_gammaSigma_add_of_isBigO (mu := P.toMeasure) (sigma := 2) (by norm_num) hA hB
    hsumV2 hG
    (((Finset.measurable_sum _ fun l _ => measurable_shellValueLargeCubeSupBound l (m + 1))).const_mul 2)
    ((measurable_shellDerivTailGauge (m + 1)).const_mul _)
  refine hadd.mono_scale ?_
  have hcT : IndependentSums.gammaTriangleConst 2 *
      (131072 * shellValueLargeCubeConst d + 8192 * Real.sqrt d) ≤ srootD4_cT d := le_max_right _ _
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hcT (by positivity))
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ htri.le
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hsq : Real.sqrt ((m : ℝ) + 2) ≤ (m : ℝ) + 2 := by
    refine Real.sqrt_le_iff.2 ⟨by linarith only [hm0], ?_⟩
    nlinarith only [hm0]
  have hcast : (((m + 2 : ℕ) : ℝ)) = (m : ℝ) + 2 := by push_cast; ring
  have h1 : ((m : ℝ) + 2) * Real.sqrt ((m : ℝ) + 2) ≤ 4 * (1 + (m : ℝ)) ^ 2 := by
    calc ((m : ℝ) + 2) * Real.sqrt ((m : ℝ) + 2) ≤ ((m : ℝ) + 2) * ((m : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hsq (by linarith only [hm0])
      _ ≤ 4 * (1 + (m : ℝ)) ^ 2 := by nlinarith only [hm0]
  have h2 : (1 : ℝ) ≤ (1 + (m : ℝ)) ^ 2 := by nlinarith only [hm0]
  have hconst : streamDerivTailConst = 8192 := rfl
  rw [hcast, hconst, ha]
  have e1 : 2 * (16384 * (((m : ℝ) + 2) * (shellValueLargeCubeConst d * Real.sqrt ((m : ℝ) + 2)))) =
      32768 * shellValueLargeCubeConst d * (((m : ℝ) + 2) * Real.sqrt ((m : ℝ) + 2)) := by ring
  have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 32768 * shellValueLargeCubeConst d)
  have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 8192 * Real.sqrt d)
  nlinarith only [h3, h4, e1]

end Envelope

section Sigma

variable {d : ℕ} [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}

/-- Two-sided envelope bounds on the infinite-volume diffusivity. -/
theorem srootD4_sigma_bounds {nu : ℝ} (hnu : 0 < nu) (m : ℕ) (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P) :
    0 < sigmaBarInfinite nu m P ∧
      (sigmaBarInfinite nu m P)⁻¹ ≤ 2 * cutoffEnvelopeConst d * nu⁻¹ ∧
      sigmaBarInfinite nu m P ≤ nu + 2 * cutoffEnvelopeConst d * nu⁻¹ * max 1 (m : ℝ) := by
  refine ⟨sigmaBarInfinite_pos hnu m hPrefix hJ2 hJ3 hJ4, ?_, ?_⟩
  · have h1 := sigmaBarStarInvLimit_le hnu m hPrefix hJ2 hJ3 hJ4 0
    have h2 := sigmaBarStarInvSeq_le_envelopeLowerScalar hnu m hPrefix hJ2 hJ3 hJ4 0
    rw [sigmaBarInfinite, inv_inv]
    exact h1.trans h2
  · have h1 := sigmaBarInfinite_le_sigmaBarUpperLimit hnu m hPrefix hJ2 hJ3 hJ4
    have h2 := sigmaBarUpperLimit_le hnu m hPrefix hJ2 hJ3 hJ4 0
    have h3 := sigmaBarSeq_le_envelopeUpperScalar hnu m hPrefix hJ2 hJ3 hJ4 0
    exact (h1.trans (h2.trans h3))

end Sigma

/-- A lower bound for `lNaught` at `alpha = 1/2` in terms of `nu⁻⁸`. -/
theorem srootD4_lNaught_ge_nu_inv {C M cStar nu K : ℝ} (hC : 1 ≤ C) (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hc : 0 < cStar) (hc2 : cStar ≤ 2) (hnu : 0 < nu) (hnu1 : nu ≤ 1) :
    (512 * Real.log 2 ^ 12) ^ 2 * (nu⁻¹) ^ 4 ≤
      SuperdiffusionCLT.Frozen.Section4.lNaught C M (1 / 2) cStar nu K := by
  unfold SuperdiffusionCLT.Frozen.Section4.lNaught
  have hrp : ∀ (x : ℝ) (n : ℕ), x ^ ((n : ℕ) : ℝ) = x ^ n := fun x n => Real.rpow_natCast x n
  have h12 : ∀ x : ℝ, x ^ (12 : ℝ) = x ^ 12 := fun x => by exact_mod_cast hrp x 12
  have h4 : ∀ x : ℝ, x ^ (4 : ℝ) = x ^ 4 := fun x => by exact_mod_cast hrp x 4
  have hcneg : (1 : ℝ) / 8 ≤ cStar ^ (-(3 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_nonpos hc hc2 (by norm_num : (-(3 : ℝ)) ≤ 0)
    have h2 : (2 : ℝ) ^ (-(3 : ℝ)) = 1 / 8 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      have h3 : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
      rw [h3, Real.rpow_natCast]
      norm_num
    rw [h2] at h
    exact h
  have hcneg0 : 0 ≤ cStar ^ (-(3 : ℝ)) := Real.rpow_nonneg hc.le _
  have hone : (1 - (1 / 2 : ℝ)) = 1 / 2 := by norm_num
  simp only [hone, h12, h4]
  have hA : (1 : ℝ) / 8 ≤ C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) := by
    have h1 : (1 : ℝ) ≤ C * (M + 1 + K) := by nlinarith only [hC, hM, hK]
    have := mul_le_mul h1 hcneg (by norm_num) (by linarith only [h1])
    linarith only [this]
  have hy : 0 ≤ (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 / 2)) := by
    have : 0 ≤ M + 1 + K := by linarith only [hM, hK]
    positivity
  have hlog : Real.log 2 ≤ Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 / 2))) :=
    Real.log_le_log (by norm_num) (by linarith only [hy])
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogp : Real.log 2 ^ 12 ≤
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 / 2))) ^ 12 :=
    pow_le_pow_left₀ hlog0.le hlog 12
  have hnu4 : 0 < nu ^ 4 := by positivity
  have hden : ((1 / 2 : ℝ) ^ 12 * nu ^ 4) = nu ^ 4 / 4096 := by ring
  set X : ℝ := C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / ((1 / 2 : ℝ) ^ 12 * nu ^ 4) *
      Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 / 2))) ^ 12 with hX
  have hXge : 512 * Real.log 2 ^ 12 * nu⁻¹ ^ 4 ≤ X := by
    rw [hX, hden]
    have e1 : C * (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu ^ 4 / 4096) =
        4096 * (C * (M + 1 + K) * cStar ^ (-(3 : ℝ))) * (nu⁻¹) ^ 4 := by
      field_simp
    rw [e1]
    have hnuinv4 : 0 ≤ (nu⁻¹) ^ 4 := by positivity
    have h1 : 512 * (nu⁻¹) ^ 4 ≤ 4096 * (C * (M + 1 + K) * cStar ^ (-(3 : ℝ))) * (nu⁻¹) ^ 4 := by
      have := mul_le_mul_of_nonneg_right hA hnuinv4
      nlinarith only [this]
    have hl0 : 0 ≤ Real.log 2 ^ 12 := by positivity
    calc 512 * Real.log 2 ^ 12 * nu⁻¹ ^ 4 = (512 * (nu⁻¹) ^ 4) * Real.log 2 ^ 12 := by ring
      _ ≤ (4096 * (C * (M + 1 + K) * cStar ^ (-(3 : ℝ))) * (nu⁻¹) ^ 4) * Real.log 2 ^ 12 :=
          mul_le_mul_of_nonneg_right h1 hl0
      _ ≤ (4096 * (C * (M + 1 + K) * cStar ^ (-(3 : ℝ))) * (nu⁻¹) ^ 4) *
            Real.log (2 + (M + 1 + K) * cStar ^ (-(3 : ℝ)) / (nu * (1 / 2))) ^ 12 :=
          mul_le_mul_of_nonneg_left hlogp (by positivity)
  have hXq : (512 * Real.log 2 ^ 12) * (nu⁻¹) ^ 4 ≥ 0 := by positivity
  have hone2 : (1 : ℝ) / (1 / 2) = 2 := by norm_num
  have hX2 : X ^ (2 : ℝ) = X ^ 2 := by exact_mod_cast hrp X 2
  have hnuinv : (1 : ℝ) ≤ (nu⁻¹) ^ 4 := by
    have : 1 ≤ nu⁻¹ := by rw [one_le_inv₀ hnu]; exact hnu1
    exact one_le_pow₀ this
  have key : (512 * Real.log 2 ^ 12) ^ 2 * (nu⁻¹) ^ 4 ≤ X ^ (2 : ℝ) := by
    rw [hX2]
    calc (512 * Real.log 2 ^ 12) ^ 2 * (nu⁻¹) ^ 4
        ≤ (512 * Real.log 2 ^ 12) ^ 2 * (nu⁻¹) ^ 4 * (nu⁻¹) ^ 4 := by
          have h0 : 0 ≤ (512 * Real.log 2 ^ 12) ^ 2 * (nu⁻¹) ^ 4 := by positivity
          nlinarith only [h0, hnuinv]
      _ = ((512 * Real.log 2 ^ 12) * (nu⁻¹) ^ 4) ^ 2 := by ring
      _ ≤ X ^ 2 := pow_le_pow_left₀ hXq hXge 2
  rw [hone2]
  exact key

/-- The deterministic polynomial majorant of the response bound. -/
theorem srootD4_R_le (d : ℕ) {nu σ T e1 c0 : ℝ} (m : ℕ) (hnu : 0 < nu) (hnu1 : nu ≤ 1)
    (hT : 0 ≤ T) (hσ : 0 < σ) (he1 : 0 ≤ e1) (hc0 : 0 < c0)
    (hσinv : σ⁻¹ ≤ e1 * nu⁻¹) (hσup : σ ≤ nu + e1 * nu⁻¹ * max 1 (m : ℝ))
    (hnuinv : c0 * (nu⁻¹) ^ 4 ≤ 1 + (m : ℝ)) :
    srootD4_R d nu σ T ≤
      (2 * (((d : ℝ) ^ 2 + 1) ^ 2 * e1 + 1 + e1) / c0) * (1 + (m : ℝ)) ^ 2 * (1 + T) ^ 4 := by
  unfold srootD4_R
  set v : ℝ := nu⁻¹ with hv
  have hv1 : 1 ≤ v := by rw [hv, one_le_inv₀ hnu]; exact hnu1
  have hv0 : 0 < v := lt_of_lt_of_le one_pos hv1
  have hnuv : nu * v = 1 := by rw [hv]; field_simp
  set W : ℝ := 1 + T with hW
  have hW1 : 1 ≤ W := by rw [hW]; linarith only [hT]
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  set D : ℝ := (d : ℝ) ^ 2 + 1 with hD
  have hD1 : 1 ≤ D := by rw [hD]; nlinarith only [sq_nonneg (d : ℝ)]
  -- Lam bound
  have hLam : ((d : ℝ) * (d : ℝ) * W ^ 2 + nu ^ 2) / nu ≤ v * (D * W ^ 2) := by
    have e1' : ((d : ℝ) * (d : ℝ) * W ^ 2 + nu ^ 2) / nu = v * ((d : ℝ) * (d : ℝ) * W ^ 2 + nu ^ 2) := by
      rw [hv]; field_simp
    rw [e1']
    refine mul_le_mul_of_nonneg_left ?_ hv0.le
    have hn2 : nu ^ 2 ≤ 1 := by nlinarith only [hnu, hnu1]
    have hW2 : 1 ≤ W ^ 2 := by nlinarith only [hW1]
    rw [hD]; nlinarith only [hn2, hW2, sq_nonneg (d : ℝ)]
  have hLam0 : 0 ≤ ((d : ℝ) * (d : ℝ) * W ^ 2 + nu ^ 2) / nu := by positivity
  have hLam2 : (((d : ℝ) * (d : ℝ) * W ^ 2 + nu ^ 2) / nu) ^ 2 ≤ v ^ 2 * D ^ 2 * W ^ 4 := by
    have := pow_le_pow_left₀ hLam0 hLam 2
    calc _ ≤ (v * (D * W ^ 2)) ^ 2 := this
      _ = v ^ 2 * D ^ 2 * W ^ 4 := by ring
  have hσ0 : 0 ≤ σ⁻¹ := inv_nonneg.2 hσ.le
  have hA : (((d : ℝ) * (d : ℝ) * W ^ 2 + nu ^ 2) / nu) ^ 2 * σ⁻¹ ≤ v ^ 2 * D ^ 2 * W ^ 4 * (e1 * v) :=
    mul_le_mul hLam2 hσinv hσ0 (by positivity)
  have hS : (((d : ℝ) * (d : ℝ) * W ^ 2 + nu ^ 2) / nu) ^ 2 * σ⁻¹ + σ ≤
      v ^ 2 * D ^ 2 * W ^ 4 * (e1 * v) + (nu + e1 * v * max 1 (m : ℝ)) := add_le_add hA hσup
  have hmax : max 1 (m : ℝ) ≤ 1 + (m : ℝ) := max_le (by linarith only [hm0]) (by linarith only [])
  have hm1 : (1 : ℝ) ≤ 1 + m := by linarith only [hm0]
  -- first reduction: R ≤ 2 v^4 (1+m) W^4 * cR'
  set cR : ℝ := 2 * (D ^ 2 * e1 + 1 + e1) with hcR
  have hv2 : v ^ 2 ≤ v ^ 4 := pow_le_pow_right₀ hv1 (by norm_num)
  have hv4 : 1 ≤ v ^ 4 := one_le_pow₀ hv1
  have hW4 : 1 ≤ W ^ 4 := one_le_pow₀ hW1
  have hstep : 2 * v * ((((d : ℝ) * (d : ℝ) * W ^ 2 + nu ^ 2) / nu) ^ 2 * σ⁻¹ + σ) ≤
      cR * v ^ 4 * (1 + (m : ℝ)) * W ^ 4 := by
    have h1 : 2 * v * ((((d : ℝ) * (d : ℝ) * W ^ 2 + nu ^ 2) / nu) ^ 2 * σ⁻¹ + σ) ≤
        2 * v * (v ^ 2 * D ^ 2 * W ^ 4 * (e1 * v) + (nu + e1 * v * max 1 (m : ℝ))) :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    have h2 : 2 * v * (v ^ 2 * D ^ 2 * W ^ 4 * (e1 * v) + (nu + e1 * v * max 1 (m : ℝ))) =
        2 * (v ^ 4 * D ^ 2 * e1 * W ^ 4 + (v * nu) + e1 * v ^ 2 * max 1 (m : ℝ)) := by ring
    have hvn : v * nu = 1 := by rw [mul_comm]; exact hnuv
    rw [h2, hvn] at h1
    have t1 : v ^ 4 * D ^ 2 * e1 * W ^ 4 ≤ v ^ 4 * (1 + (m : ℝ)) * W ^ 4 * (D ^ 2 * e1) := by
      have : 0 ≤ v ^ 4 * W ^ 4 * (D ^ 2 * e1) := by positivity
      nlinarith only [this, hm1]
    have t2 : (1 : ℝ) ≤ v ^ 4 * (1 + (m : ℝ)) * W ^ 4 * 1 := by
      have := mul_le_mul hv4 hm1 zero_le_one (by positivity)
      have := mul_le_mul this hW4 zero_le_one (by positivity)
      nlinarith only [this]
    have t3 : e1 * v ^ 2 * max 1 (m : ℝ) ≤ v ^ 4 * (1 + (m : ℝ)) * W ^ 4 * e1 := by
      have a1 : e1 * v ^ 2 * max 1 (m : ℝ) ≤ e1 * v ^ 4 * (1 + (m : ℝ)) := by
        have := mul_le_mul hv2 hmax (le_trans zero_le_one (le_max_left _ _)) (by positivity)
        nlinarith only [this, he1]
      have a2 : e1 * v ^ 4 * (1 + (m : ℝ)) ≤ e1 * v ^ 4 * (1 + (m : ℝ)) * W ^ 4 := by
        have : 0 ≤ e1 * v ^ 4 * (1 + (m : ℝ)) := by positivity
        nlinarith only [this, hW4]
      nlinarith only [a1, a2]
    rw [hcR]
    nlinarith only [h1, t1, t2, t3]
  refine hstep.trans ?_
  have hvm : v ^ 4 ≤ (1 + (m : ℝ)) / c0 := by
    rw [le_div_iff₀ hc0]; nlinarith only [hnuinv]
  have hcR0 : 0 ≤ cR := by rw [hcR]; positivity
  calc cR * v ^ 4 * (1 + (m : ℝ)) * W ^ 4 ≤ cR * ((1 + (m : ℝ)) / c0) * (1 + (m : ℝ)) * W ^ 4 := by
        have := mul_le_mul_of_nonneg_left hvm hcR0
        have h3 : 0 ≤ (1 + (m : ℝ)) * W ^ 4 := by positivity
        nlinarith only [this, h3]
    _ = (cR / c0) * (1 + (m : ℝ)) ^ 2 * W ^ 4 := by ring

/-- Adding one doubles the amplitude of a `Γ_σ` tail, once the amplitude is at least `1`. -/
theorem srootD4_isBigOWith_one_add {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu] {sigma : ℝ} {X : Omega → ℝ} {a : ℝ} (ha : 1 ≤ a)
    (hX : IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) X a) :
    IndependentSums.IsBigOWith mu (IndependentSums.gammaSigma sigma) (fun omega => 1 + X omega)
      (2 * a) := by
  intro t ht
  refine le_trans (measureReal_mono ?_) (hX ht)
  intro omega homega
  have hat : 1 ≤ a * t := by nlinarith only [ha, ht]
  simp only [IndependentSums.mem_upperTailEvent] at homega ⊢
  linarith only [homega, hat]

/-- **The polynomial crude bound for the deep-scale response, as a `Γ_{1/2}` tail.**

For the centered, shifted cutoff field, the squared response against `σ • 1` is dominated, for
every cutoff and every deep scale simultaneously, by a measurable `R` with a `Γ_{1/2}` tail at
amplitude `A0 (1 + m)^10`; `A0` depends on the dimension alone. The exponent `10 = 2 + 8` is
the `(1 + m)²` of the response majorant times the eighth power `(1 + m)^{2·4}` of the amplitude
of the `Γ₂` envelope raised to the fourth power. -/
theorem srootD4_hCrudePolyHalf (d : ℕ) [NeZero d] :
    ∃ A0 : ℝ, 1 ≤ A0 ∧ ∀ C1 : ℝ, 1 ≤ C1 →
      ∀ (nu cStar nondeg : ℝ), 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure
              (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
          (hPrefix : SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P)
          (hJ2 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P)
          (hJ3 : SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ5 d P cStar nondeg
              hPrefix hJ2 hJ3 →
          ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ K : ℝ, C1 ≤ K → ∀ m n : ℕ,
            SuperdiffusionCLT.Frozen.Section4.lNaught C1 (C1 * s⁻¹ * K) (1 / 2) cStar nu nondeg ≤ (m : ℝ) →
            m - ⌈K * Real.log (m : ℝ)⌉₊ ≤ n → n ≤ m →
            ∀ k : Fin d → ℤ, (fun x => (fun i => (3 : ℝ) ^ ((n : ℤ) - 3) * (k i : ℝ)) + x) ''
                  Homogenization.cubeSet (Homogenization.originCube d (n : ℤ)) ⊆
                Homogenization.cubeSet (Homogenization.originCube d (m : ℤ)) →
              ∃ R : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → ℝ,
                Measurable R ∧
                IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma (1 / 2)) R
                  (A0 * (1 + (m : ℝ)) ^ (10 : ℝ)) ∧
                ∀ᵐ omega ∂P.toMeasure, ∀ L j : ℕ,
                  Real.rpow (Homogenization.scaleResponseAtScale
                      (Homogenization.originCube d (n : ℤ)) ((n : ℤ) - (j : ℤ))
                      Homogenization.MultiscaleExponent.infinity
                      (srootE_field nu omega L m n k)
                      ((SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite nu m P) •
                        (1 : Homogenization.Mat d))) 2 ≤
                    R omega := by
  set e1 : ℝ := 2 * cutoffEnvelopeConst d with he1
  set c0 : ℝ := (512 * Real.log 2 ^ 12) ^ 2 with hc0
  have hc0pos : 0 < c0 := by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [hc0]; positivity
  have he10 : 0 ≤ e1 := by
    have := cutoffEnvelopeConst_pos d
    rw [he1]; positivity
  set cR : ℝ := 2 * (((d : ℝ) ^ 2 + 1) ^ 2 * e1 + 1 + e1) with hcR
  have hcR0 : 0 ≤ cR := by rw [hcR]; positivity
  refine ⟨max 1 (cR / c0 * (16 * srootD4_cT d ^ 4)), le_max_left _ _, ?_⟩
  intro C1 hC11 nu cStar nondeg hnu hnu1 P hPrefix hJ2 hJ3 hJ1 hJ4 hJ5 s hs0 hs1 K hK m n
    hLm hn1 hn2 k hk
  obtain ⟨hσpos, hσinv, hσup⟩ := srootD4_sigma_bounds (P := P) hnu m hPrefix hJ2 hJ3 hJ4
  have hK0 : 0 ≤ K := by linarith only [hC11, hK]
  have hM0 : 0 ≤ C1 * s⁻¹ * K := by
    have : 0 ≤ s⁻¹ := inv_nonneg.2 hs0.le
    have : 0 ≤ C1 := by linarith only [hC11]
    positivity
  have hnuinv : c0 * (nu⁻¹) ^ 4 ≤ 1 + (m : ℝ) := by
    have h := srootD4_lNaught_ge_nu_inv (C := C1) (M := C1 * s⁻¹ * K) (cStar := cStar) (nu := nu)
      (K := nondeg) hC11 hM0 hJ5.K_pos.le hJ5.cStar_pos hJ5.cStar_le_two hnu hnu1
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith only [h, hLm, hm0]
  refine ⟨fun omega => srootD4_R d nu (sigmaBarInfinite nu m P) (srootD4_T m omega), ?_, ?_, ?_⟩
  · unfold srootD4_R
    have hT := measurable_srootD4_T (d := d) m
    fun_prop
  · -- the tail
    set cT : ℝ := srootD4_cT d with hcT
    have hcT1 : 1 ≤ cT := le_max_left _ _
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have h1m : (1 : ℝ) ≤ (1 + (m : ℝ)) ^ 2 := by nlinarith only [hm0]
    have hTW : IndependentSums.IsBigOWith P.toMeasure (IndependentSums.gammaSigma 2)
        (srootD4_T m) (cT * (1 + (m : ℝ)) ^ 2) :=
      (isBigOWith_iff_isBigO_of_nonneg (srootD4_T_nonneg m)).2
        (srootD4_T_isBigO hPrefix hJ3 m)
    have hW := srootD4_isBigOWith_one_add (by nlinarith only [hcT1, h1m]) hTW
    have hW0 : ∀ omega : ShellSeq d, 0 ≤ 1 + srootD4_T m omega := fun omega => by
      linarith only [srootD4_T_nonneg m omega]
    have hW4 := (IndependentSums.isBigOWith_gammaSigma_rpow_iff (μ := P.toMeasure) (σ := 2) (p := 4)
      (by norm_num) (by positivity) hW0).1 hW
    rw [show (2 : ℝ) / 4 = 1 / 2 by norm_num] at hW4
    set cc : ℝ := cR / c0 * (1 + (m : ℝ)) ^ 2 with hcc
    have hcc0 : 0 ≤ cc := by rw [hcc]; positivity
    have hX := hW4.const_mul hcc0
    have hle : ∀ omega : ShellSeq d,
        srootD4_R d nu (sigmaBarInfinite nu m P) (srootD4_T m omega) ≤
          cc * (1 + srootD4_T m omega) ^ (4 : ℝ) := by
      intro omega
      have h := srootD4_R_le d (T := srootD4_T m omega) (e1 := e1) (c0 := c0) m hnu hnu1
        (srootD4_T_nonneg m omega) hσpos he10 hc0pos hσinv hσup hnuinv
      have e4 : (1 + srootD4_T m omega) ^ (4 : ℝ) = (1 + srootD4_T m omega) ^ 4 := by
        exact_mod_cast Real.rpow_natCast (1 + srootD4_T m omega) 4
      rw [e4, hcc]
      exact h
    have hRnn : ∀ omega : ShellSeq d,
        0 ≤ srootD4_R d nu (sigmaBarInfinite nu m P) (srootD4_T m omega) := by
      intro omega
      unfold srootD4_R
      have := inv_nonneg.2 hnu.le
      have := inv_nonneg.2 hσpos.le
      positivity
    have hRW := hX.of_le hle
    refine (isBigOWith_iff_isBigO_of_nonneg hRnn).1 (hRW.mono_scale ?_)
    have e4 : ∀ x : ℝ, x ^ (4 : ℝ) = x ^ 4 := fun x => by
      exact_mod_cast Real.rpow_natCast x 4
    have e10 : (1 + (m : ℝ)) ^ (10 : ℝ) = (1 + (m : ℝ)) ^ 10 := by
      exact_mod_cast Real.rpow_natCast (1 + (m : ℝ)) 10
    rw [e4, e10, hcc]
    have hpos : 0 ≤ (1 + (m : ℝ)) ^ 10 := by positivity
    have heq : cR / c0 * (1 + (m : ℝ)) ^ 2 * (2 * (cT * (1 + (m : ℝ)) ^ 2)) ^ 4 =
        cR / c0 * (16 * cT ^ 4) * (1 + (m : ℝ)) ^ 10 := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hpos
  · have hsumm := ae_forall_summable_shellDerivLinftyNorm_originCube hJ3 (P := P)
    filter_upwards [hsumm] with omega homega L j
    exact srootD4_scaleResponse_sq_le_envelope nu (sigmaBarInfinite nu m P) hnu hnu1 hσpos omega
      L m n k hk (homega (m + 1)) j

end SuperdiffusionCLT.Section4.MinimalScales
