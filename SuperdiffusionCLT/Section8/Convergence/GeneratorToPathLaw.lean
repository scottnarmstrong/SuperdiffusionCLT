/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Convergence.CoreResolvent
public import SuperdiffusionCLT.Section8.Convergence.InvariancePrinciple
public import SuperdiffusionCLT.Section8.Convergence.SemigroupPathConvergenceB
public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusionApiB

/-!
# Dilated Feller semigroups: elementary convergence lemmas

Auxiliary facts for the passage from generator approximation to convergence of the rescaled path
laws:

* `genPath_tendsto_c0_of_iSup`: convergence in `C₀` from convergence of the pointwise suprema
  written in `ℝ≥0∞` (the form of the conclusion of the generator approximation);
* `genPath_tendsto_dilC0`: the dilation `f ↦ f (s ·)` is continuous in the scale `s ≠ 0` for
  every fixed `f ∈ C₀`;
* `genPath_tendsto_dilate_c0`: strong convergence of Feller semigroups is preserved by a
  convergent family of further space dilations.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section8.Convergence

open Filter Homogenization MeasureTheory Topology
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open scoped ENNReal NNReal ZeroAtInfty

noncomputable section

variable {d : ℕ}

/-- Convergence of the pointwise suprema, written in `ℝ≥0∞`, gives convergence in `C₀`. -/
theorem genPath_tendsto_c0_of_iSup {ι : Type*} {l : Filter ι} (a : ι → C₀(Vec d, ℝ))
    (b : C₀(Vec d, ℝ))
    (h : Tendsto (fun i => ⨆ x : Vec d, ENNReal.ofReal |a i x - b x|) l (𝓝 0)) :
    Tendsto a l (𝓝 b) := by
  rw [Metric.tendsto_nhds]
  intro r hr
  have hr2 : (0 : ℝ) < r / 2 := by positivity
  have hev := h.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hr2))
  filter_upwards [hev] with i hi
  have hx : ∀ x : Vec d, |a i x - b x| ≤ r / 2 := by
    intro x
    have h1 : ENNReal.ofReal |a i x - b x| ≤ ⨆ x : Vec d, ENNReal.ofReal |a i x - b x| :=
      le_iSup (fun x : Vec d => ENNReal.ofReal |a i x - b x|) x
    exact (ENNReal.ofReal_le_ofReal_iff hr2.le).mp (h1.trans hi.le)
  rw [dist_eq_norm, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  have hn : ‖(a i - b).toBCF‖ ≤ r / 2 := by
    refine (BoundedContinuousFunction.norm_le hr2.le).mpr fun x => ?_
    simpa only [ZeroAtInftyContinuousMap.toBCF_apply, ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply, Real.norm_eq_abs] using hx x
  linarith only [hn, hr]

/-- A function of `C₀` is small outside a ball. -/
theorem genPath_exists_radius (h : C₀(Vec d, ℝ)) {e : ℝ} (he : 0 < e) :
    ∃ R : ℝ, 0 < R ∧ ∀ y : Vec d, R ≤ ‖y‖ → |h y| < e := by
  have hev : ∀ᶠ y in cocompact (Vec d), |h y| < e := by
    have := h.zero_at_infty'
    exact (this.eventually (Metric.ball_mem_nhds 0 he)).mono fun x hx => by
      simpa only [ContinuousMap.toFun_eq_coe, ZeroAtInftyContinuousMap.coe_toContinuousMap, dist_zero_right, Real.norm_eq_abs] using hx
  obtain ⟨t, ht, htc⟩ := Filter.mem_cocompact.mp hev
  obtain ⟨R, hR⟩ := ht.isBounded.subset_closedBall (0 : Vec d)
  refine ⟨|R| + 1, by positivity, fun y hy => htc ?_⟩
  intro hyt
  have := Metric.mem_closedBall.mp (hR hyt)
  rw [dist_zero_right] at this
  linarith only [this, hy, le_abs_self R]

/-- **Continuity of the dilation in the scale.**  If `s i → κ ≠ 0` then `f (s i ·) → f (κ ·)`
in `C₀` for every `f ∈ C₀`. -/
theorem genPath_tendsto_dilC0 {ι : Type*} {l : Filter ι} {s : ι → ℝ} (hs : ∀ i, s i ≠ 0)
    {κ : ℝ} (hκ : κ ≠ 0) (hsκ : Tendsto s l (𝓝 κ)) (f : C₀(Vec d, ℝ)) :
    Tendsto (fun i => fd_dilC0 (s i) (hs i) f) l (𝓝 (fd_dilC0 κ hκ f)) := by
  rw [Metric.tendsto_nhds]
  intro e he
  have he3 : (0 : ℝ) < e / 3 := by positivity
  obtain ⟨R, hRpos, hR⟩ := genPath_exists_radius f he3
  obtain ⟨η, hη, hηf⟩ := Metric.uniformContinuous_iff.mp
    (ZeroAtInftyContinuousMap.uniformContinuous f) (e / 3) he3
  set m : ℝ := |κ| / 2 with hm
  have hκpos : 0 < |κ| := abs_pos.mpr hκ
  have hmpos : 0 < m := by positivity
  set R' : ℝ := R / m with hR'
  have hR'pos : 0 < R' := by positivity
  set θ : ℝ := min m (η / (R' + 1)) with hθ
  have hθpos : 0 < θ := lt_min hmpos (by positivity)
  have hev : ∀ᶠ i in l, |s i - κ| < θ := by
    have := Metric.tendsto_nhds.mp hsκ θ hθpos
    filter_upwards [this] with i hi
    simpa only [Real.dist_eq] using hi
  filter_upwards [hev] with i hi
  rw [dist_eq_norm, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  have hsm : m ≤ |s i| := by
    have h1 : |κ| - |s i| ≤ |s i - κ| := by
      have := abs_sub_abs_le_abs_sub κ (s i)
      rwa [abs_sub_comm κ (s i)] at this
    have h2 : |s i - κ| < m := lt_of_lt_of_le hi (min_le_left _ _)
    linarith only [h1, h2, hm]
  have hbound : ∀ x : Vec d, |f (s i • x) - f (κ • x)| ≤ 2 * e / 3 := by
    intro x
    by_cases hx : R' ≤ ‖x‖
    · have h1 : R ≤ ‖s i • x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        calc R = m * R' := by rw [hR']; field_simp
          _ ≤ |s i| * ‖x‖ := mul_le_mul hsm hx hR'pos.le (abs_nonneg _)
      have h2 : R ≤ ‖κ • x‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        calc R = m * R' := by rw [hR']; field_simp
          _ ≤ |κ| * ‖x‖ := mul_le_mul (by rw [hm]; linarith only [hκpos]) hx hR'pos.le
              (abs_nonneg _)
      have := hR _ h1
      have := hR _ h2
      have h3 := abs_sub_le (f (s i • x)) 0 (f (κ • x))
      simp only [sub_zero, zero_sub, abs_neg] at h3
      linarith only [h3, hR _ h1, hR _ h2]
    · have hxR : ‖x‖ < R' := not_le.mp hx
      have hd : dist (s i • x) (κ • x) < η := by
        rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]
        have h1 : |s i - κ| * ‖x‖ ≤ θ * R' :=
          mul_le_mul hi.le hxR.le (norm_nonneg _) hθpos.le
        have h2 : θ * R' ≤ η / (R' + 1) * R' :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hR'pos.le
        have h3 : η / (R' + 1) * R' < η := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith only [hη, hR'pos]
        linarith only [h1, h2, h3]
      have := hηf hd
      rw [Real.dist_eq] at this
      linarith only [this, he3]
  have hn : ‖(fd_dilC0 (s i) (hs i) f - fd_dilC0 κ hκ f).toBCF‖ ≤ 2 * e / 3 := by
    refine (BoundedContinuousFunction.norm_le (by positivity)).mpr fun x => ?_
    simpa only [ZeroAtInftyContinuousMap.toBCF_apply, ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply, fd_dilC0_apply, Real.norm_eq_abs] using hbound x
  linarith only [hn, he]

/-- Strong convergence of Feller semigroups survives a convergent family of space dilations. -/
theorem genPath_tendsto_dilate_c0 {ι : Type*} {l : Filter ι}
    {T : ι → SubMarkovKernelSemigroup (Vec d)} {T₀ : SubMarkovKernelSemigroup (Vec d)}
    (hT : ∀ i, (T i).IsFellerKernelSemigroup) (hT₀ : T₀.IsFellerKernelSemigroup)
    (hconv : ∀ (t : ℝ≥0) (f : C₀(Vec d, ℝ)),
      Tendsto (fun i => (hT i).c0Semigroup t f) l (𝓝 (hT₀.c0Semigroup t f)))
    {s : ι → ℝ} (hs : ∀ i, s i ≠ 0) {κ : ℝ} (hκ : κ ≠ 0) (hsκ : Tendsto s l (𝓝 κ))
    (hD : ∀ i, (fd_dilateSemigroup (T i) (hs i) 1).IsFellerKernelSemigroup)
    (hD₀ : (fd_dilateSemigroup T₀ hκ 1).IsFellerKernelSemigroup) (t : ℝ≥0)
    (f : C₀(Vec d, ℝ)) :
    Tendsto (fun i => (hD i).c0Semigroup t f) l (𝓝 (hD₀.c0Semigroup t f)) := by
  have hop : ∀ i, (hD i).c0Semigroup t f = fd_dilC0 (s i)⁻¹ (inv_ne_zero (hs i))
      ((hT i).c0Semigroup (1 * t) (fd_dilC0 (s i) (hs i) f)) := fun i =>
    fd_c0Operator_conj (T i) _ (hs i) (fd_dilateSemigroup_apply (T i) (hs i) 1)
      (hT i).mapsC0 (hD i).mapsC0 t f
  have hop₀ : hD₀.c0Semigroup t f = fd_dilC0 κ⁻¹ (inv_ne_zero hκ)
      (hT₀.c0Semigroup (1 * t) (fd_dilC0 κ hκ f)) :=
    fd_c0Operator_conj T₀ _ hκ (fd_dilateSemigroup_apply T₀ hκ 1) hT₀.mapsC0 hD₀.mapsC0 t f
  simp only [hop, hop₀]
  have h1 : Tendsto (fun i => (hT i).c0Semigroup (1 * t) (fd_dilC0 (s i) (hs i) f)) l
      (𝓝 (hT₀.c0Semigroup (1 * t) (fd_dilC0 κ hκ f))) :=
    MarkovProcess.Semigroup.tendsto_apply_of_opNorm_le_one
      (fun i => (hT i).c0Semigroup (1 * t)) (hT₀.c0Semigroup (1 * t)) _ _
      (fun i => (hT i).c0Semigroup.opNorm_le_one _) (hconv _ _)
      (genPath_tendsto_dilC0 hs hκ hsκ f)
  have hsinv : Tendsto (fun i => (s i)⁻¹) l (𝓝 κ⁻¹) := hsκ.inv₀ hκ
  exact MarkovProcess.Semigroup.tendsto_apply_of_opNorm_le_one
    (fun i => fd_dilC0 (s i)⁻¹ (inv_ne_zero (hs i))) (fd_dilC0 κ⁻¹ (inv_ne_zero hκ)) _ _
    (fun i => LinearMap.mkContinuous_norm_le _ zero_le_one _)
    (genPath_tendsto_dilC0 (fun i => inv_ne_zero (hs i)) (inv_ne_zero hκ) hsinv _) h1

end

end SuperdiffusionCLT.Section8.Convergence
