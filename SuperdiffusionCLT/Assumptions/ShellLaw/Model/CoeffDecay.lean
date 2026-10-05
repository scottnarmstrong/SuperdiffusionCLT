/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.CellFourier
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Decay of the frame coefficients: integration by parts

For a smooth function `F` on `Vec d` vanishing outside the closed cube `[-1/2, 1/2]^d`, the
coefficient `cellCoeff p F` against the cosine or sine of frequency `m` satisfies
`(2 π |m j|) ^ N * |cellCoeff p F| ≤ B` whenever all derivatives of `F` up to order `N` are
bounded by `B`.  One integration by parts in the coordinate direction `j` exchanges a derivative
of `F` for a factor `2 π m j` and swaps cosine and sine.

## Main definitions

* `cellFreq`, `cellFreqNorm`: the frequency of a frame index and its `ℓ¹` size.
* `nv_dir`: the directional derivative of a scalar function.

## Main results

* `nv_pow_mul_abs_cellCoeff_le`: the decay for the coordinate `j`.
* `nv_abs_Q_mul_pow_le`: the decay in `(1 + cellFreqNorm p) ^ N` for the coefficient of
  `u ↦ w u * h (x - u)`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization Set Real MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## Frequencies of frame indices -/

/-- The frequency `m` of the frame index `inl m` or `inr m`. -/
def cellFreq : ((Fin d → ℤ) ⊕ (Fin d → ℤ)) → (Fin d → ℤ) := Sum.elim id id

/-- Exchanging cosine and sine of the same frequency. -/
def cellSwap : ((Fin d → ℤ) ⊕ (Fin d → ℤ)) → ((Fin d → ℤ) ⊕ (Fin d → ℤ))
  | .inl m => .inr m
  | .inr m => .inl m

/-- The `ℓ¹` size `∑ i, |m i|` of the frequency of a frame index. -/
def cellFreqNorm (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) : ℝ := ∑ i, |((cellFreq p i : ℤ) : ℝ)|

theorem cellFreq_swap (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) : cellFreq (cellSwap p) = cellFreq p := by
  rcases p with m | m <;> rfl

theorem cellFreqNorm_nonneg (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) : 0 ≤ cellFreqNorm p :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- The directional derivative `y ↦ h'(y) v`. -/
def nv_dir (v : Vec d) (h : Vec d → ℝ) : Vec d → ℝ := fun y ↦ fderiv ℝ h y v

/-! ## The phase as a continuous linear functional -/

/-- The phase `u ↦ 2 π m · u` as a continuous linear functional. -/
def nv_phaseCLM (m : Fin d → ℤ) : Vec d →L[ℝ] ℝ :=
  (2 * π) • ∑ i, (m i : ℝ) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)

theorem nv_phaseCLM_apply (m : Fin d → ℤ) (u : Vec d) : nv_phaseCLM m u = cellPhase m u := by
  simp only [nv_phaseCLM, cellPhase, smul_apply,
    sum_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

theorem nv_phaseCLM_single (m : Fin d → ℤ) (j : Fin d) :
    nv_phaseCLM m (Pi.single j 1) = 2 * π * (m j : ℝ) := by
  rw [nv_phaseCLM_apply]
  simp only [cellPhase, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem nv_hasFDerivAt_cellPhase (m : Fin d → ℤ) (u : Vec d) :
    HasFDerivAt (cellPhase m) (nv_phaseCLM m) u := by
  have h := (nv_phaseCLM m).hasFDerivAt (x := u)
  rwa [show ⇑(nv_phaseCLM m) = cellPhase m from funext (nv_phaseCLM_apply m)] at h

theorem nv_contDiff_cellTrig (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) (n : WithTop ℕ∞) :
    ContDiff ℝ n (cellTrig p) := by
  have hp : ContDiff ℝ n (cellPhase (d := d) (cellFreq p)) := by
    have := (nv_phaseCLM (cellFreq p)).contDiff (n := n)
    rwa [show ⇑(nv_phaseCLM (cellFreq p)) = cellPhase (cellFreq p) from
      funext (nv_phaseCLM_apply _)] at this
  rcases p with m | m
  · exact Real.contDiff_cos.comp hp
  · exact Real.contDiff_sin.comp hp

/-- The derivative of the cosine along `e_j`. -/
theorem nv_fderiv_cos_single (m : Fin d → ℤ) (u : Vec d) (j : Fin d) :
    fderiv ℝ (cellTrig (.inl m)) u (Pi.single j 1)
      = -Real.sin (cellPhase m u) * (2 * π * (m j : ℝ)) := by
  have h : HasFDerivAt (cellTrig (.inl m))
      ((-Real.sin (cellPhase m u)) • nv_phaseCLM m) u :=
    (Real.hasDerivAt_cos (cellPhase m u)).comp_hasFDerivAt u (nv_hasFDerivAt_cellPhase m u)
  rw [h.fderiv, smul_apply, nv_phaseCLM_single, smul_eq_mul]

/-- The derivative of the sine along `e_j`. -/
theorem nv_fderiv_sin_single (m : Fin d → ℤ) (u : Vec d) (j : Fin d) :
    fderiv ℝ (cellTrig (.inr m)) u (Pi.single j 1)
      = Real.cos (cellPhase m u) * (2 * π * (m j : ℝ)) := by
  have h : HasFDerivAt (cellTrig (.inr m))
      ((Real.cos (cellPhase m u)) • nv_phaseCLM m) u :=
    (Real.hasDerivAt_sin (cellPhase m u)).comp_hasFDerivAt u (nv_hasFDerivAt_cellPhase m u)
  rw [h.fderiv, smul_apply, nv_phaseCLM_single, smul_eq_mul]

/-! ## Functions vanishing outside the closed cube -/

theorem nv_isOpen_outCube : IsOpen {u : Vec d | ∃ i, 1 / 2 < |u i|} := by
  have : {u : Vec d | ∃ i, 1 / 2 < |u i|} = ⋃ i, {u : Vec d | 1 / 2 < |u i|} := by
    ext u; simp
  rw [this]
  exact isOpen_iUnion fun i ↦
    isOpen_lt continuous_const (continuous_abs.comp (continuous_apply i))

theorem nv_hasCompactSupport {G : Vec d → ℝ} (h0 : ∀ u, (∃ i, 1 / 2 < |u i|) → G u = 0) :
    HasCompactSupport G := by
  refine HasCompactSupport.intro (K := Set.pi Set.univ fun _ : Fin d ↦ Icc (-(1 / 2 : ℝ)) (1 / 2))
    (isCompact_univ_pi fun _ ↦ isCompact_Icc) fun y hy ↦ ?_
  by_contra hne
  refine hy fun i _ ↦ ?_
  have : ¬ (1 / 2 < |y i|) := fun h ↦ hne (h0 y ⟨i, h⟩)
  have h2 := abs_le.1 (not_lt.1 this)
  exact ⟨h2.1, h2.2⟩

theorem nv_fderiv_eq_zero_outCube {F : Vec d → ℝ} (h0 : ∀ u, (∃ i, 1 / 2 < |u i|) → F u = 0)
    {u : Vec d} (hu : ∃ i, 1 / 2 < |u i|) : fderiv ℝ F u = 0 := by
  have hev : F =ᶠ[nhds u] fun _ ↦ (0 : ℝ) :=
    Filter.eventually_of_mem (nv_isOpen_outCube.mem_nhds hu) fun y hy ↦ h0 y hy
  rw [hev.fderiv_eq]
  exact fderiv_const_apply 0

theorem nv_dir_zero_outCube {F : Vec d → ℝ} (h0 : ∀ u, (∃ i, 1 / 2 < |u i|) → F u = 0)
    (v : Vec d) : ∀ u, (∃ i, 1 / 2 < |u i|) → nv_dir v F u = 0 := fun u hu ↦ by
  simp only [nv_dir, nv_fderiv_eq_zero_outCube h0 hu, zero_apply]

theorem nv_abs_integral_le {G : Vec d → ℝ} {B : ℝ}
    (hG0 : ∀ u, (∃ i, 1 / 2 < |u i|) → G u = 0) (hB : ∀ u, |G u| ≤ B) : |∫ u, G u| ≤ B := by
  let K : Set (Vec d) := Icc (fun _ ↦ -(1 / 2 : ℝ)) (fun _ ↦ 1 / 2)
  have hK : ∫ u in K, G u = ∫ u, G u := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu ↦ hG0 u ?_
    by_contra hne
    refine hu ⟨fun i ↦ ?_, fun i ↦ ?_⟩
    · have := abs_le.1 (not_lt.1 fun h ↦ hne ⟨i, h⟩ : |u i| ≤ 1 / 2)
      exact this.1
    · have := abs_le.1 (not_lt.1 fun h ↦ hne ⟨i, h⟩ : |u i| ≤ 1 / 2)
      exact this.2
  have hvol : (volume K).toReal = 1 := by
    simp [K, Real.volume_Icc_pi]
    norm_num
  have hfin : volume K < ⊤ := by
    simp [K, Real.volume_Icc_pi]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := G) (s := K) (C := B) hfin
    (fun u _ ↦ by simpa only [Real.norm_eq_abs] using hB u)
  rw [hK, Real.norm_eq_abs, Measure.real, hvol, mul_one] at this
  exact this

/-! ## Integration by parts -/

theorem nv_continuous_dir {F : Vec d → ℝ} (hF : ContDiff ℝ 1 F) (v : Vec d) :
    Continuous (nv_dir v F) :=
  (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- Integration by parts for a `C¹` function against a function supported in the cube. -/
theorem nv_ibp {T F : Vec d → ℝ} (hT : ContDiff ℝ 1 T) (hF : ContDiff ℝ 1 F)
    (hF0 : ∀ u, (∃ i, 1 / 2 < |u i|) → F u = 0) (v : Vec d) :
    ∫ u, T u * nv_dir v F u = - ∫ u, fderiv ℝ T u v * F u := by
  have hFc := nv_hasCompactSupport hF0
  have hDc := nv_hasCompactSupport (nv_dir_zero_outCube hF0 v)
  have hTd : Continuous fun u ↦ fderiv ℝ T u v :=
    (hT.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h1 : Integrable (fun u ↦ fderiv ℝ T u v * F u) :=
    (hTd.mul hF.continuous).integrable_of_hasCompactSupport hFc.mul_left
  have h2 : Integrable (fun u ↦ T u * nv_dir v F u) :=
    (hT.continuous.mul (nv_continuous_dir hF v)).integrable_of_hasCompactSupport hDc.mul_left
  have h3 : Integrable (fun u ↦ T u * F u) :=
    (hT.continuous.mul hF.continuous).integrable_of_hasCompactSupport hFc.mul_left
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := v) h1 h2 h3
    (fun x _ ↦ (hT.differentiable one_ne_zero) x) (fun x _ ↦ (hF.differentiable one_ne_zero) x)

/-- The coefficient of the derivative `∂_j F` is the swapped coefficient of `F`, times
`2 π m j`, up to sign. -/
theorem nv_abs_cellCoeff_swap_dir (j : Fin d) (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) {F : Vec d → ℝ}
    (hF : ContDiff ℝ 1 F) (hF0 : ∀ u, (∃ i, 1 / 2 < |u i|) → F u = 0) :
    |cellCoeff (cellSwap p) (nv_dir (Pi.single j 1) F)|
      = 2 * π * |((cellFreq p j : ℤ) : ℝ)| * |cellCoeff p F| := by
  rcases p with m | m
  · -- the swapped index is the sine
    have h := nv_ibp (nv_contDiff_cellTrig (.inr m) 1) hF hF0 (Pi.single j 1)
    have e : cellCoeff (cellSwap (Sum.inl m)) (nv_dir (Pi.single j 1) F)
        = -((2 * π * (m j : ℝ)) * cellCoeff (.inl m) F) := by
      show ∫ u, cellTrig (.inr m) u * nv_dir (Pi.single j 1) F u = _
      rw [h]
      simp only [nv_fderiv_sin_single, cellCoeff, cellTrig, ← integral_const_mul, ← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
      simp only
      ring
    rw [e, abs_neg, abs_mul, abs_mul, abs_mul, abs_two, abs_of_pos Real.pi_pos]
    rfl
  · have h := nv_ibp (nv_contDiff_cellTrig (.inl m) 1) hF hF0 (Pi.single j 1)
    have e : cellCoeff (cellSwap (Sum.inr m)) (nv_dir (Pi.single j 1) F)
        = (2 * π * (m j : ℝ)) * cellCoeff (.inr m) F := by
      show ∫ u, cellTrig (.inl m) u * nv_dir (Pi.single j 1) F u = _
      rw [h]
      simp only [nv_fderiv_cos_single, cellCoeff, cellTrig, ← integral_const_mul, ← integral_neg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
      simp only
      ring
    rw [e, abs_mul, abs_mul, abs_mul, abs_two, abs_of_pos Real.pi_pos]
    rfl

/-! ## The decay lemma -/

/-- Without derivatives: the coefficient is bounded by the sup norm. -/
theorem nv_abs_cellCoeff_le (p : (Fin d → ℤ) ⊕ (Fin d → ℤ)) {F : Vec d → ℝ} {B : ℝ}
    (hF0 : ∀ u, (∃ i, 1 / 2 < |u i|) → F u = 0) (hB : ∀ u, |F u| ≤ B) :
    |cellCoeff p F| ≤ B := by
  refine nv_abs_integral_le (fun u hu ↦ ?_) (fun u ↦ ?_)
  · simp only [hF0 u hu, mul_zero]
  · rw [abs_mul]
    exact (mul_le_of_le_one_left (abs_nonneg _) (abs_cellTrig_le_one p u)).trans (hB u)

theorem nv_norm_iteratedFDeriv_dir_le (j : Fin d) {F : Vec d → ℝ} {N : ℕ}
    (hF : ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) F) {i : ℕ} (hi : i ≤ N) (u : Vec d) :
    ‖iteratedFDeriv ℝ i (nv_dir (Pi.single j 1) F) u‖ ≤ ‖iteratedFDeriv ℝ (i + 1) F u‖ := by
  have hf : ContDiffAt ℝ (N : WithTop ℕ∞) (fderiv ℝ F) u :=
    (hF.fderiv_right (m := (N : WithTop ℕ∞)) (by push_cast; exact le_rfl)).contDiffAt
  have h := norm_iteratedFDeriv_clm_apply_const (c := (Pi.single j 1 : Vec d)) hf
    (n := i) (by exact_mod_cast hi)
  have hn : ‖(Pi.single j 1 : Vec d)‖ = 1 := by
    rw [Pi.norm_single, norm_one]
  rw [hn, one_mul, norm_iteratedFDeriv_fderiv] at h
  exact h

/-- **Decay of the coefficient by repeated integration by parts in the coordinate `j`.** -/
theorem nv_pow_mul_abs_cellCoeff_le (j : Fin d) (B : ℝ) :
    ∀ (N : ℕ) (F : Vec d → ℝ), ContDiff ℝ (N : WithTop ℕ∞) F →
      (∀ u, (∃ i, 1 / 2 < |u i|) → F u = 0) →
      (∀ i ≤ N, ∀ u, ‖iteratedFDeriv ℝ i F u‖ ≤ B) →
      ∀ p : (Fin d → ℤ) ⊕ (Fin d → ℤ),
        (2 * π * |((cellFreq p j : ℤ) : ℝ)|) ^ N * |cellCoeff p F| ≤ B
  | 0, F, _, h0, hB, p => by
    rw [pow_zero, one_mul]
    exact nv_abs_cellCoeff_le p h0 fun u ↦ by
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hB 0 le_rfl u
  | N + 1, F, hc, h0, hB, p => by
    have hc1 : ContDiff ℝ 1 F := hc.of_le (by exact_mod_cast Nat.le_add_left 1 N)
    have hc' : ContDiff ℝ (N : WithTop ℕ∞) (nv_dir (Pi.single j 1) F) :=
      (hc.fderiv_right (m := (N : WithTop ℕ∞)) (by push_cast; exact le_rfl)).clm_apply
        contDiff_const
    have hB' : ∀ i ≤ N, ∀ u, ‖iteratedFDeriv ℝ i (nv_dir (Pi.single j 1) F) u‖ ≤ B :=
      fun i hi u ↦ (nv_norm_iteratedFDeriv_dir_le j hc hi u).trans (hB (i + 1) (by omega) u)
    have ih := nv_pow_mul_abs_cellCoeff_le j B N _ hc' (nv_dir_zero_outCube h0 _) hB' (cellSwap p)
    rw [nv_abs_cellCoeff_swap_dir j p hc1 h0, cellFreq_swap] at ih
    calc (2 * π * |((cellFreq p j : ℤ) : ℝ)|) ^ (N + 1) * |cellCoeff p F|
        = (2 * π * |((cellFreq p j : ℤ) : ℝ)|) ^ N
          * (2 * π * |((cellFreq p j : ℤ) : ℝ)| * |cellCoeff p F|) := by ring
      _ ≤ B := ih

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
