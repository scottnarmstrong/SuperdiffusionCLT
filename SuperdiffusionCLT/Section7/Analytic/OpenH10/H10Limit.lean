/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.OpenH10.ZeroExtension
public import Homogenization.Sobolev.Truncation.H10Limit
public import Homogenization.Sobolev.W1p.ConvexApproxSmoothing.Kernel
public import Homogenization.Sobolev.W1p.GlobalMollifierLp
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# `H¹₀` on an open set: closure under `H¹` limits, and compactly supported functions

* `memH10_of_tendsto_H1`: for an arbitrary open `U`, the representative-level `H¹₀(U)` is closed
  under `L²` limits of the value and every gradient coordinate.
* `toH10OfCompact`: an `H¹(U)` function vanishing off a compact `K ⊆ U` is an `H¹₀(U)` function
  with the same value and gradient representatives (mollification of the zero extension).
-/

@[expose] public section

open scoped ENNReal Convolution Topology
open MeasureTheory Set Filter Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ} {U : Set (Vec d)}

/-- **`H¹₀(U)` closed under `L²` limits**, for an arbitrary open set `U`. -/
theorem memH10_of_tendsto_H1 (hU : IsOpen U) (f : H1Function U) (F : ℕ → H1Function U)
    (hmem : ∀ n, MemH10 U (F n).toFun)
    (hfun : Tendsto
      (fun n => eLpNorm (fun x => f.toFun x - (F n).toFun x) 2 (volumeMeasureOn U))
      atTop (nhds 0))
    (hgrad : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm (fun x => f.grad x i - (F n).grad x i) 2 (volumeMeasureOn U))
      atTop (nhds 0)) :
    MemH10 U f.toFun := by
  classical
  set μU : Measure (Vec d) := volumeMeasureOn U with hμU
  choose W hW using hmem
  have hloc : ∀ (z : H1Function U) (i : Fin d),
      LocallyIntegrableOn (fun x => z.grad x i) U volume := fun z i =>
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((z.gradMemL2 i).locallyIntegrable (by norm_num))
  have hbridge : ∀ n (i : Fin d),
      (fun x => (W n).toH1Function.grad x i) =ᵐ[μU] (fun x => (F n).grad x i) := by
    intro n i
    have hw := (W n).toH1Function.hasWeakGradient i
    rw [hW n] at hw
    exact HasWeakPartialDerivOn.ae_eq hU (hloc _ i) (hloc _ i) hw
      ((F n).hasWeakGradient i)
  set ε : ℕ → ℝ≥0∞ := fun n => (↑(n + 1))⁻¹ with hε
  have hε_pos : ∀ n, 0 < ε n := by
    intro n
    simp only [hε]
    exact ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top (n + 1))
  have hε_tendsto : Tendsto ε atTop (nhds 0) :=
    (ENNReal.tendsto_inv_nat_nhds_zero).comp (tendsto_add_atTop_nat 1)
  have hex : ∀ n, ∃ k,
      eLpNorm (fun x => (W n).approx k x - (W n).toH1Function.toFun x) 2 μU < ε n ∧
      ∀ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ ((W n).approx k) x) (basisVec i) -
          (W n).toH1Function.grad x i) 2 μU < ε n := by
    intro n
    have e1 : ∀ᶠ k in atTop,
        eLpNorm (fun x => (W n).approx k x - (W n).toH1Function.toFun x) 2 μU < ε n :=
      (W n).tendsto_approx.eventually_lt_const (hε_pos n)
    have e2 : ∀ i : Fin d, ∀ᶠ k in atTop,
        eLpNorm (fun x => (fderiv ℝ ((W n).approx k) x) (basisVec i) -
          (W n).toH1Function.grad x i) 2 μU < ε n :=
      fun i => ((W n).tendsto_approx_grad i).eventually_lt_const (hε_pos n)
    have e2' : ∀ᶠ k in atTop, ∀ i : Fin d,
        eLpNorm (fun x => (fderiv ℝ ((W n).approx k) x) (basisVec i) -
          (W n).toH1Function.grad x i) 2 μU < ε n :=
      Filter.eventually_all.2 e2
    exact (e1.and e2').exists
  choose k hk using hex
  set ψ : ℕ → Vec d → ℝ := fun n => (W n).approx (k n) with hψ
  have htf : Tendsto
      (fun n => eLpNorm (fun x => (W n).toH1Function.toFun x - f.toFun x) 2 μU)
      atTop (nhds 0) := by
    refine hfun.congr (fun n => ?_)
    rw [Homogenization.eLpNorm_sub_swap ((W n).toH1Function.toFun) (f.toFun), hW n]
  have hfun_bound : Tendsto (fun n => ε n +
      eLpNorm (fun x => (W n).toH1Function.toFun x - f.toFun x) 2 μU) atTop (nhds 0) := by
    simpa using hε_tendsto.add htf
  have hgi : ∀ i : Fin d, Tendsto
      (fun n => eLpNorm (fun x => (W n).toH1Function.grad x i - f.grad x i) 2 μU)
      atTop (nhds 0) := by
    intro i
    refine (hgrad i).congr (fun n => ?_)
    rw [Homogenization.eLpNorm_sub_swap (fun x => (W n).toH1Function.grad x i)
      (fun x => f.grad x i)]
    exact eLpNorm_congr_ae (by filter_upwards [hbridge n i] with x hx; rw [hx])
  have hgrad_bound : ∀ i : Fin d, Tendsto (fun n => ε n +
      eLpNorm (fun x => (W n).toH1Function.grad x i - f.grad x i) 2 μU) atTop (nhds 0) := by
    intro i
    simpa using hε_tendsto.add (hgi i)
  refine ⟨{ toH1Function := f
            approx := ψ
            approx_smooth := fun n => (W n).approx_smooth (k n)
            approx_hasCompactSupport := fun n => (W n).approx_hasCompactSupport (k n)
            approx_support_subset := fun n => (W n).approx_support_subset (k n)
            tendsto_approx := ?_
            tendsto_approx_grad := ?_ }, rfl⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hfun_bound
      (fun n => zero_le) (fun n => ?_)
    have heq :
        (fun x => ψ n x - f.toFun x) =
          (fun x => ψ n x - (W n).toH1Function.toFun x) +
            (fun x => (W n).toH1Function.toFun x - f.toFun x) := by
      funext x; simp only [Pi.add_apply]; ring
    rw [heq]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    exact add_le_add (le_of_lt (hk n).1) le_rfl
  · intro i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hgrad_bound i)
      (fun n => zero_le) (fun n => ?_)
    have heq :
        (fun x => (fderiv ℝ (ψ n) x) (basisVec i) - f.grad x i) =
          (fun x => (fderiv ℝ (ψ n) x) (basisVec i) - (W n).toH1Function.grad x i) +
            (fun x => (W n).toH1Function.grad x i - f.grad x i) := by
      funext x; simp only [Pi.add_apply]; ring
    rw [heq]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    exact add_le_add (le_of_lt ((hk n).2 i)) le_rfl

/-- Witness: the closure theorem applies to the constant sequence `F n = f`. -/
example (f : H10Function (Metric.ball (0 : Vec 2) 1)) :
    MemH10 (Metric.ball (0 : Vec 2) 1) f.toH1Function.toFun :=
  memH10_of_tendsto_H1 Metric.isOpen_ball f.toH1Function (fun _ => f.toH1Function)
    (fun _ => ⟨f, rfl⟩)
    (by simp) (fun i => by simp)

/-! ### Mollification of compactly supported functions -/

theorem scaledUnitKernel_eq_zero_of_lt_norm {a : ℝ} (ha : 0 < a) {y : Vec d} (hy : a < ‖y‖) :
    scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) a y = 0 := by
  have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hnorm : 1 < ‖a⁻¹ • y‖ := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg ha.le]
    rw [← div_eq_inv_mul, lt_div_iff₀ ha]
    simpa using hy
  have hnot : a⁻¹ • y ∉ tsupport (unitConvexApproxKernel (d := d)) := fun hmem =>
    absurd (by simpa using hρ.support_subset_closedBall hmem) (not_le.mpr hnorm)
  simp [scaledConvexApproxKernel, image_eq_zero_of_notMem_tsupport hnot]

/-- The mollification at scale `a` of `h` is supported in the closed `a`-thickening of the
support of `h`. -/
theorem support_convolution_subset_cthickening {K h : Vec d → ℝ} {a : ℝ}
    (hK : ∀ y, a < ‖y‖ → K y = 0) :
    Function.support (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) ⊆
      Metric.cthickening a (tsupport h) := by
  intro x hx
  by_contra hxn
  apply hx
  simp only [convolution_def]
  have : ∀ t, (ContinuousLinearMap.lsmul ℝ ℝ) (K t) (h (x - t)) = 0 := by
    intro t
    by_cases ht : a < ‖t‖
    · simp [hK t ht]
    · have hmem : x - t ∉ tsupport h := fun hm =>
        hxn (Metric.mem_cthickening_of_dist_le x (x - t) a _ hm (by
          rw [dist_eq_norm, sub_sub_cancel]; exact not_lt.mp ht))
      simp [image_eq_zero_of_notMem_tsupport hmem]
  simp [this]

/-- The coordinate derivative of a smooth compactly supported kernel convolution is the
convolution with the kernel's coordinate derivative. -/
theorem fderiv_convolution_apply_basisVec {K g : Vec d → ℝ}
    (hK_supp : HasCompactSupport K) (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (hg : LocallyIntegrable g volume) (i : Fin d) (x : Vec d) :
    fderiv ℝ (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x (basisVec i) =
      ((fun y => fderiv ℝ K y (basisVec i)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
  have hderiv :
      fderiv ℝ (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x =
        ((fderiv ℝ K ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec d), volume] g) x) :=
    (hK_supp.hasFDerivAt_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := volume) (hf := hK.of_le (by norm_num)) hg x).fderiv
  rw [hderiv]
  calc
    ((fderiv ℝ K ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec d), volume] g) x)
        (basisVec i)
        = ((g ⋆[((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec d)).flip, volume]
            fderiv ℝ K) x) (basisVec i) := by
          rw [convolution_flip]
    _ = ((g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip.precompR (Vec d), volume]
            fderiv ℝ K) x) (basisVec i) := rfl
    _ = (g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, volume]
            (fun y => (fderiv ℝ K y) (basisVec i))) x :=
          convolution_precompR_apply
            (L := (ContinuousLinearMap.lsmul ℝ ℝ).flip) (f := g) (g := fderiv ℝ K)
            (μ := volume) hg (hK_supp.fderiv ℝ)
            (hK.continuous_fderiv (by norm_num)) x (basisVec i)
    _ = ((fun y => (fderiv ℝ K y) (basisVec i)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            g) x := by
          rw [convolution_flip]

private theorem lsmul_flip_eq :
    (ContinuousLinearMap.lsmul ℝ ℝ).flip = ContinuousLinearMap.lsmul ℝ ℝ := by
  ext; simp

/-- Mollification commutes with the whole-space weak derivative. -/
theorem fderiv_convolution_eq_of_hasWeakPartialDerivOn
    {K u g : Vec d → ℝ} (hK_supp : HasCompactSupport K)
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hu : LocallyIntegrable u volume) {i : Fin d}
    (hweak : HasWeakPartialDerivOn Set.univ i u g) (x : Vec d) :
    fderiv ℝ (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x (basisVec i) =
      (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
  rw [fderiv_convolution_apply_basisVec hK_supp hK hu]
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => K (x - y)) :=
    hK.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport (fun y : Vec d => K (x - y)) :=
    hK_supp.comp_homeomorph (Homeomorph.subLeft x)
  have hw := hweak _ hφ hφc (Set.subset_univ _)
  simp only [Measure.restrict_univ] at hw
  have hderiv : ∀ y, (fderiv ℝ (fun y : Vec d => K (x - y)) y) (basisVec i) =
      -(fderiv ℝ K (x - y) (basisVec i)) := by
    intro y
    have hcomp : fderiv ℝ (fun y : Vec d => K (x - y)) y =
        (fderiv ℝ K (x - y)).comp (-(1 : Vec d →L[ℝ] Vec d)) := by
      change fderiv ℝ (K ∘ fun y : Vec d => x - y) y = _
      rw [fderiv_comp]
      · have harg : fderiv ℝ (fun y : Vec d => x - y) y = -(1 : Vec d →L[ℝ] Vec d) := by
          simpa using! (fderiv_const_sub (𝕜 := ℝ) (f := fun y : Vec d => y) (x := y) x)
        rw [harg]
      · exact (hK.differentiable (by simp)) (x - y)
      · fun_prop
    rw [hcomp]
    simp
  simp only [hderiv, mul_neg, integral_neg, neg_inj] at hw
  have hc : ∀ f h : Vec d → ℝ,
      f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h =
        h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f := fun f h => by
    have := convolution_flip (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := (volume : Measure (Vec d))) (f := f) (g := h)
    rw [lsmul_flip_eq] at this
    exact this.symm
  rw [hc (fun y => fderiv ℝ K y (basisVec i)) u, hc K g]
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  exact hw

/-- **Compactly supported `H¹` functions are `H¹₀`**: an `H¹(U)` function vanishing off a compact
`K ⊆ U` is realised as an `H¹₀(U)` function with the same value and gradient representatives. -/
theorem exists_h10_of_compact (hU : IsOpen U) (f : H1Function U)
    {K : Set (Vec d)} (hKU : K ⊆ U) (hK : IsCompact K)
    (hf0 : ∀ x ∈ U, x ∉ K → f.toFun x = 0) : ∃ v : H10Function U, v.toH1Function = f := by
  classical
  have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  let a : ℕ → ℝ := fun n => unitConvexApproxScale n * δ
  have hsc : ∀ n, 0 < unitConvexApproxScale n := fun n => by
    unfold unitConvexApproxScale; positivity
  have ha : ∀ n, 0 < a n := fun n => mul_pos (hsc n) hδ
  have haδ : ∀ n, a n ≤ δ := fun n =>
    calc a n ≤ 1 * δ := mul_le_mul_of_nonneg_right (unitConvexApproxScale_le_one n) hδ.le
      _ = δ := one_mul δ
  set F : Vec d → ℝ := U.indicator f.toFun with hF
  set G : Fin d → Vec d → ℝ := fun i => U.indicator (fun x => f.grad x i) with hG
  have hFmem : MemLp F 2 volume := (memLp_indicator_iff_restrict hU.measurableSet).2 f.memL2
  have hGmem : ∀ i, MemLp (G i) 2 volume := fun i =>
    (memLp_indicator_iff_restrict hU.measurableSet).2 (f.gradMemL2 i)
  have hweak := hasWeakPartialDerivOn_univ_zeroExtend hU f hKU hK hf0
  have hFK : tsupport F ⊆ K := by
    refine closure_minimal (fun x hx => ?_) hK.isClosed
    by_contra hxK
    apply hx
    by_cases hxU : x ∈ U
    · simp [hF, Set.indicator_of_mem hxU, hf0 x hxU hxK]
    · simp [hF, Set.indicator_of_notMem hxU]
  let k : ℕ → Vec d → ℝ := fun n =>
    scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) (a n)
  have hkc : ∀ n, HasCompactSupport (k n) := fun n =>
    hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport (ha n)
  have hks : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (k n) := fun n => contDiff_scaledConvexApproxKernel hρ _
  have hk0 : ∀ n y, a n < ‖y‖ → k n y = 0 := fun n y hy =>
    scaledUnitKernel_eq_zero_of_lt_norm (ha n) hy
  let M : ℕ → Vec d → ℝ := fun n => k n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F
  have hMs : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (M n) := fun n =>
    (hkc n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) (hks n)
      (hFmem.locallyIntegrable (by norm_num))
  have hMsupp : ∀ n, Function.support (M n) ⊆ Metric.cthickening (a n) K := fun n =>
    (support_convolution_subset_cthickening (hk0 n)).trans
      (Metric.cthickening_subset_of_subset (a n) hFK)
  have hMts : ∀ n, tsupport (M n) ⊆ Metric.cthickening (a n) K := fun n =>
    closure_minimal (hMsupp n) Metric.isClosed_cthickening
  have hMc : ∀ n, HasCompactSupport (M n) := fun n =>
    HasCompactSupport.of_support_subset_isCompact (hK.cthickening (r := a n)) (hMsupp n)
  have hMderiv : ∀ n i x, fderiv ℝ (M n) x (basisVec i) =
      (k n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G i) x := fun n i x =>
    fderiv_convolution_eq_of_hasWeakPartialDerivOn (hkc n) (hks n)
      (hFmem.locallyIntegrable (by norm_num)) (hweak i) x
  have hε0 : Tendsto unitConvexApproxScale atTop (𝓝 0) := tendsto_unitConvexApproxScale_zero
  have hεp : ∀ᶠ n in atTop, 0 < unitConvexApproxScale n := Eventually.of_forall hsc
  refine ⟨
    { toH1Function := f
      approx := M
      approx_smooth := hMs
      approx_hasCompactSupport := hMc
      approx_support_subset := fun n =>
        (hMts n).trans ((Metric.cthickening_mono (haδ n) K).trans hδU)
      tendsto_approx := ?_
      tendsto_approx_grad := ?_ }, rfl⟩
  · have h := tendsto_eLpNorm_sub_zero_convolution_scaledConvexApproxKernel (p := 2) hρ
      (by norm_num) (by norm_num) hFmem hδ hε0 hεp
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n => bot_le)
      (fun n => ?_)
    have e : eLpNorm (fun x => M n x - f.toFun x) 2 (volume.restrict U) =
        eLpNorm (fun x => M n x - F x) 2 (volume.restrict U) := by
      apply eLpNorm_congr_ae
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      simp [hF, Set.indicator_of_mem hx]
    rw [e]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self
  · intro i
    have h := tendsto_eLpNorm_sub_zero_convolution_scaledConvexApproxKernel (p := 2) hρ
      (by norm_num) (by norm_num) (hGmem i) hδ hε0 hεp
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun n => bot_le)
      (fun n => ?_)
    have e : eLpNorm (fun x => fderiv ℝ (M n) x (basisVec i) - f.grad x i) 2
        (volume.restrict U) =
        eLpNorm (fun x => (k n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G i) x - G i x) 2
          (volume.restrict U) := by
      apply eLpNorm_congr_ae
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      simp [hMderiv, hG, Set.indicator_of_mem hx]
    rw [e]
    exact eLpNorm_mono_measure _ Measure.restrict_le_self

/-- An `H¹(U)` function vanishing outside a compact subset of `U` is an `H¹₀(U)` function
with the same value and gradient representatives. -/
noncomputable def toH10OfCompact (hU : IsOpen U) (f : H1Function U)
    {K : Set (Vec d)} (hKU : K ⊆ U) (hK : IsCompact K)
    (hf0 : ∀ x ∈ U, x ∉ K → f.toFun x = 0) : H10Function U :=
  (exists_h10_of_compact hU f hKU hK hf0).choose

@[simp] theorem toH10OfCompact_toH1Function (hU : IsOpen U) (f : H1Function U)
    {K : Set (Vec d)} (hKU : K ⊆ U) (hK : IsCompact K)
    (hf0 : ∀ x ∈ U, x ∉ K → f.toFun x = 0) :
    (toH10OfCompact hU f hKU hK hf0).toH1Function = f :=
  (exists_h10_of_compact hU f hKU hK hf0).choose_spec

/-- Witness: the zero function on the unit ball is compactly supported in it (`K = ∅`). -/
example : MemH10 (Metric.ball (0 : Vec 2) 1)
    (0 : H1Function (Metric.ball (0 : Vec 2) 1)).toFun :=
  ⟨toH10OfCompact Metric.isOpen_ball 0 (K := ∅) (Set.empty_subset _) isCompact_empty
    (fun _ _ _ => rfl), by simp⟩

/-- Witness with a nonempty compact set: the zero function on the unit ball vanishes off the
origin (`K = {0}`). -/
example : MemH10 (Metric.ball (0 : Vec 2) 1)
    (0 : H1Function (Metric.ball (0 : Vec 2) 1)).toFun :=
  ⟨toH10OfCompact Metric.isOpen_ball 0 (K := {0})
    (Set.singleton_subset_iff.2 (Metric.mem_ball_self one_pos)) isCompact_singleton
    (fun _ _ _ => rfl), by simp⟩

end SuperdiffusionCLT.Section7
