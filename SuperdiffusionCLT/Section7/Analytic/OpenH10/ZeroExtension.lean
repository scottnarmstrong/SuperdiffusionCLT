/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Homogenization.Sobolev.WeakDerivatives
public import Homogenization.Sobolev.H1.Definitions
public import Homogenization.Sobolev.H1.BasicLemmas
public import Homogenization.Sobolev.H1.Algebra.H1Function

/-!
# Locality of weak derivatives and zero extension on open sets

A locally integrable function has weak derivative `g` on an open set `U` as soon as every
point of `U` has an open neighbourhood inside `U` on which `g` is a weak derivative (split a
test function along a finite smooth partition of unity). As a consequence, an `H¹(U)` function
vanishing off a compact subset of `U` has a zero extension to `ℝ^d` with the same weak gradient.
-/

@[expose] public section

open MeasureTheory Set
open scoped Manifold ContDiff ENNReal
open Homogenization

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- A finite smooth partition of unity on a compact set, subordinate to open neighbourhoods
of its points. -/
theorem exists_finite_partition {K U : Set (Vec d)} (hK : IsCompact K) (hKU : K ⊆ U)
    (V : Vec d → Set (Vec d)) (hVo : ∀ x ∈ U, IsOpen (V x)) (hVx : ∀ x ∈ U, x ∈ V x) :
    ∃ (t : Finset K) (f : SmoothPartitionOfUnity t 𝓘(ℝ, Vec d) (Vec d) K),
      f.IsSubordinate (fun i : t => V (i : K)) := by
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x _ => V x)
    (fun x hx => (hVo x (hKU hx)).mem_nhds (hVx x (hKU hx)))
  refine ⟨t, ?_⟩
  refine SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Vec d) hK.isClosed _
    (fun i => hVo _ (hKU i.1.2)) ?_
  intro x hx
  have := ht hx
  simp only [mem_iUnion] at this ⊢
  obtain ⟨i, hi, hxi⟩ := this
  exact ⟨⟨i, hi⟩, hxi⟩

/-- A compactly supported continuous multiplier keeps a locally integrable function
integrable on the ambient open set. -/
theorem integrableOn_mul_of_compactSupport {U : Set (Vec d)} (hU : IsOpen U)
    {u h : Vec d → ℝ} (hu : LocallyIntegrableOn u U volume)
    (hh : Continuous h) (hhc : HasCompactSupport h) (hhU : tsupport h ⊆ U) :
    IntegrableOn (fun x => u x * h x) U := by
  have h1 : IntegrableOn u (tsupport h) volume := hu.integrableOn_compact_subset hhU hhc
  have h2 : IntegrableOn (fun x => u x * h x) (tsupport h) volume :=
    h1.mul_continuousOn hh.continuousOn hhc
  refine h2.of_forall_sdiff_eq_zero hU.measurableSet ?_
  intro x hx
  have : h x = 0 := image_eq_zero_of_notMem_tsupport hx.2
  simp [this]

theorem setIntegral_eq_of_tsupport_subset {U V : Set (Vec d)} (hU : IsOpen U) (hVU : V ⊆ U)
    {f : Vec d → ℝ} (hf : ∀ x, x ∉ V → f x = 0) :
    ∫ x in U, f x = ∫ x in V, f x :=
  (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hVU
    (fun x hx => hf x hx.2))

/-- **Locality of weak partial derivatives.** -/
theorem hasWeakPartialDerivOn_of_local {U : Set (Vec d)} (hU : IsOpen U) {i : Fin d}
    {u g : Vec d → ℝ} (hu : LocallyIntegrableOn u U volume)
    (hg : LocallyIntegrableOn g U volume)
    (hloc : ∀ x ∈ U, ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ HasWeakPartialDerivOn V i u g) :
    HasWeakPartialDerivOn U i u g := by
  classical
  intro φ hφ hφc hφU
  choose! V hVo hVx hVU hVw using hloc
  obtain ⟨t, f, hf⟩ := exists_finite_partition hφc hφU V hVo hVx
  let ψ : t → Vec d → ℝ := fun j x => φ x * f j x
  have hfs : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j) := fun j => by
    have := (f j).contMDiff
    rw [contMDiff_iff_contDiff] at this
    exact this
  have hψs : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j) := fun j => hφ.mul (hfs j)
  have hψc : ∀ j, HasCompactSupport (ψ j) := fun j => hφc.mul_right
  have hψV : ∀ j, tsupport (ψ j) ⊆ V (j.1 : Vec d) := fun j =>
    (tsupport_mul_subset_right (f := φ) (g := f j)).trans (hf j)
  have hψU : ∀ j, tsupport (ψ j) ⊆ U := fun j =>
    (hψV j).trans (hVU _ (hφU j.1.2))
  have hsum : ∀ x, φ x = ∑ j, ψ j x := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · have h1 := (f.sum_eq_one (x := x) hx)
      rw [finsum_eq_sum_of_fintype] at h1
      simp only [ψ, ← Finset.mul_sum, h1, mul_one]
    · have : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this, ψ]
  have hφeq : φ = fun x => ∑ j, ψ j x := funext hsum
  have hderiv : ∀ x, (fderiv ℝ φ x) (basisVec i) = ∑ j, (fderiv ℝ (ψ j) x) (basisVec i) := by
    intro x
    have e : fderiv ℝ φ x = fderiv ℝ (fun x => ∑ j, ψ j x) x :=
      congrArg (fun F => fderiv ℝ F x) hφeq
    rw [e, fderiv_fun_sum (fun j _ => ((hψs j).differentiable (by simp)) x)]
    simp
  have hcont : ∀ j, Continuous (fun x => (fderiv ℝ (ψ j) x) (basisVec i)) := fun j =>
    ((hψs j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hdsupp : ∀ j, Function.support (fun x => (fderiv ℝ (ψ j) x) (basisVec i)) ⊆ tsupport (ψ j) :=
    fun j x hx => by
      by_contra h
      apply hx
      simp [fderiv_of_notMem_tsupport ℝ h]
  have hdc : ∀ j, HasCompactSupport (fun x => (fderiv ℝ (ψ j) x) (basisVec i)) := fun j =>
    (hψc j).mono' (hdsupp j)
  have hdU : ∀ j, tsupport (fun x => (fderiv ℝ (ψ j) x) (basisVec i)) ⊆ U := fun j =>
    (closure_minimal (hdsupp j) (isClosed_tsupport _)).trans (hψU j)
  have hIu : ∀ j, IntegrableOn (fun x => u x * (fderiv ℝ (ψ j) x) (basisVec i)) U :=
    fun j => integrableOn_mul_of_compactSupport hU hu (hcont j) (hdc j) (hdU j)
  have hIg : ∀ j, IntegrableOn (fun x => g x * ψ j x) U := fun j =>
    integrableOn_mul_of_compactSupport hU hg (hψs j).continuous (hψc j) (hψU j)
  have hzero : ∀ (j : t) (F : Vec d → ℝ), (∀ x, x ∉ tsupport (ψ j) → F x = 0) →
      ∀ x, x ∉ V (j.1 : Vec d) → F x = 0 := fun j F hF x hx =>
    hF x fun h => hx (hψV j h)
  have hterm : ∀ j : t, ∫ x in U, u x * (fderiv ℝ (ψ j) x) (basisVec i) =
      -∫ x in U, g x * ψ j x := by
    intro j
    have hVj := hVU _ (hφU j.1.2)
    have h1 := hVw _ (hφU j.1.2) (ψ j) (hψs j) (hψc j) (hψV j)
    rw [setIntegral_eq_of_tsupport_subset hU hVj (f := fun x => u x * (fderiv ℝ (ψ j) x) (basisVec i))
      (hzero j _ (fun x hx => by simp [fderiv_of_notMem_tsupport ℝ hx])), h1,
      ← setIntegral_eq_of_tsupport_subset hU hVj (f := fun x => g x * ψ j x)
      (hzero j _ (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx]))]
  calc ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i)
      = ∫ x in U, ∑ j : t, u x * (fderiv ℝ (ψ j) x) (basisVec i) := by
        refine setIntegral_congr_fun hU.measurableSet fun x _ => ?_
        simp only [hderiv x, Finset.mul_sum]
    _ = ∑ j : t, ∫ x in U, u x * (fderiv ℝ (ψ j) x) (basisVec i) := integral_finsetSum _ (fun j _ => hIu j)
    _ = -∑ j : t, ∫ x in U, g x * ψ j x := by simp [hterm, Finset.sum_neg_distrib]
    _ = -∫ x in U, g x * φ x := by
        rw [← integral_finsetSum _ (fun j _ => hIg j)]
        congr 1
        refine setIntegral_congr_fun hU.measurableSet fun x _ => ?_
        rw [← Finset.mul_sum, ← hsum x]
/-- **Locality of weak gradients.** -/
theorem hasWeakGradientOn_of_local {U : Set (Vec d)} (hU : IsOpen U)
    {u : Vec d → ℝ} {g : Vec d → Vec d} (hu : LocallyIntegrableOn u U volume)
    (hg : ∀ i, LocallyIntegrableOn (fun x => g x i) U volume)
    (hloc : ∀ x ∈ U, ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ HasWeakGradientOn V u g) :
    HasWeakGradientOn U u g := fun i =>
  hasWeakPartialDerivOn_of_local hU hu (hg i) fun x hx => by
    obtain ⟨V, h1, h2, h3, h4⟩ := hloc x hx
    exact ⟨V, h1, h2, h3, h4 i⟩

/-- Locality of weak gradients, with sup-norm cubes (`Metric.ball`) as neighbourhoods; these
are open bounded convex domains, so the convex-domain Sobolev calculus applies on them. -/
theorem hasWeakGradientOn_of_local_ball {U : Set (Vec d)} (hU : IsOpen U)
    {u : Vec d → ℝ} {g : Vec d → Vec d} (hu : LocallyIntegrableOn u U volume)
    (hg : ∀ i, LocallyIntegrableOn (fun x => g x i) U volume)
    (hloc : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ U ∧
      HasWeakGradientOn (Metric.ball x r) u g) :
    HasWeakGradientOn U u g :=
  hasWeakGradientOn_of_local hU hu hg fun x hx => by
    obtain ⟨r, hr, h1, h2⟩ := hloc x hx
    exact ⟨Metric.ball x r, Metric.isOpen_ball, Metric.mem_ball_self hr, h1, h2⟩

/-- Every point of an open set has a sup-norm cube around it inside the set. -/
theorem exists_ball_subset {U : Set (Vec d)} (hU : IsOpen U) {x : Vec d} (hx : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ U := Metric.isOpen_iff.mp hU x hx


/-- Weak partial derivatives transfer along an a.e. equality of the candidate derivative. -/
theorem hasWeakPartialDerivOn_congr_ae {U : Set (Vec d)} {i : Fin d}
    {u g g' : Vec d → ℝ} (h : HasWeakPartialDerivOn U i u g)
    (hae : g =ᵐ[volume.restrict U] g') : HasWeakPartialDerivOn U i u g' := by
  intro φ hφ hφc hφU
  rw [h φ hφ hφc hφU]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx]

variable {U : Set (Vec d)}

theorem hasWeakPartialDerivOn_of_zero {V : Set (Vec d)} (i : Fin d) {f g : Vec d → ℝ}
    (hf : ∀ x ∈ V, f x = 0) (hg : ∀ᵐ x ∂(volume.restrict V), g x = 0) :
    HasWeakPartialDerivOn V i f g := by
  intro φ _ _ _
  have h1 : ∫ x in V, f x * (fderiv ℝ φ x) (basisVec i) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun x hx => by simp [hf x hx]
  have h2 : ∫ x in V, g x * φ x = 0 :=
    integral_eq_zero_of_ae (hg.mono fun x hx => by simp [hx])
  rw [h1, h2, neg_zero]

/-- A weak gradient of a function vanishing on an open set vanishes a.e. there. -/
theorem grad_ae_zero_of_zero {V : Set (Vec d)} (hV : IsOpen V) (i : Fin d) {f g : Vec d → ℝ}
    (hf : ∀ x ∈ V, f x = 0) (hg : LocallyIntegrableOn g V volume)
    (h : HasWeakPartialDerivOn V i f g) : ∀ᵐ x ∂(volume.restrict V), g x = 0 := by
  have h0 : HasWeakPartialDerivOn V i f (fun _ => (0 : ℝ)) :=
    hasWeakPartialDerivOn_of_zero i hf (Filter.Eventually.of_forall fun _ => rfl)
  exact HasWeakPartialDerivOn.ae_eq hV hg (locallyIntegrableOn_const _) h h0

/-- **Zero extension of a compactly supported `H¹` function.** -/
theorem hasWeakPartialDerivOn_univ_zeroExtend (hU : IsOpen U) (f : H1Function U)
    {K : Set (Vec d)} (hKU : K ⊆ U) (hK : IsCompact K)
    (hf0 : ∀ x ∈ U, x ∉ K → f.toFun x = 0) (i : Fin d) :
    HasWeakPartialDerivOn Set.univ i (U.indicator f.toFun)
      (U.indicator (fun x => f.grad x i)) := by
  have hf2 : MemLp (U.indicator f.toFun) 2 volume :=
    (memLp_indicator_iff_restrict hU.measurableSet).2 f.memL2
  have hg2 : MemLp (U.indicator (fun x => f.grad x i)) 2 volume :=
    (memLp_indicator_iff_restrict hU.measurableSet).2 (f.gradMemL2 i)
  refine hasWeakPartialDerivOn_of_local isOpen_univ
    ((hf2.locallyIntegrable (by norm_num)).locallyIntegrableOn _)
    ((hg2.locallyIntegrable (by norm_num)).locallyIntegrableOn _) ?_
  intro x _
  by_cases hxU : x ∈ U
  · refine ⟨U, hU, hxU, subset_univ _, ?_⟩
    intro φ hφ hφc hφU
    have h := f.hasWeakPartialDerivOn i φ hφ hφc hφU
    rw [setIntegral_congr_fun hU.measurableSet (g := fun x => f.toFun x * (fderiv ℝ φ x) (basisVec i))
        (fun y hy => by simp [Set.indicator_of_mem hy]),
      h]
    congr 1
    exact setIntegral_congr_fun hU.measurableSet (fun y hy => by simp [Set.indicator_of_mem hy])
  · have hxK : x ∉ K := fun h => hxU (hKU h)
    refine ⟨Kᶜ, hK.isClosed.isOpen_compl, hxK, subset_univ _, ?_⟩
    have hW : IsOpen (U ∩ Kᶜ) := hU.inter hK.isClosed.isOpen_compl
    have hgrad : ∀ᵐ y ∂(volume.restrict (U ∩ Kᶜ)), f.grad y i = 0 := by
      refine grad_ae_zero_of_zero hW i (fun y hy => hf0 y hy.1 hy.2)
        (locallyIntegrableOn_of_locallyIntegrable_restrict
          ((f.gradMemL2 i).locallyIntegrable (by norm_num)) |>.mono_set inter_subset_left)
        ((f.hasWeakPartialDerivOn i).restrict hW inter_subset_left)
    apply hasWeakPartialDerivOn_of_zero
    · intro y hy
      by_cases hyU : y ∈ U
      · simp [Set.indicator_of_mem hyU, hf0 y hyU hy]
      · simp [Set.indicator_of_notMem hyU]
    · rw [ae_restrict_iff' hK.isClosed.isOpen_compl.measurableSet]
      have := (ae_restrict_iff' hW.measurableSet).1 hgrad
      filter_upwards [this] with y hy hyK
      by_cases hyU : y ∈ U
      · simp [Set.indicator_of_mem hyU, hy ⟨hyU, hyK⟩]
      · simp [Set.indicator_of_notMem hyU]

/-- Witness: the zero extension theorem applies (to the zero function, with `K = ∅`) on the
unit ball. -/
example (i : Fin 2) :
    HasWeakPartialDerivOn Set.univ i
      ((Metric.ball (0 : Vec 2) 1).indicator (0 : H1Function (Metric.ball (0 : Vec 2) 1)).toFun)
      ((Metric.ball (0 : Vec 2) 1).indicator
        (fun x => (0 : H1Function (Metric.ball (0 : Vec 2) 1)).grad x i)) :=
  hasWeakPartialDerivOn_univ_zeroExtend Metric.isOpen_ball _ (K := ∅) (Set.empty_subset _)
    isCompact_empty (fun _ _ _ => rfl) i

/-- Witness: locality applies, with `u = g = 0` and neighbourhoods the unit ball. -/
example (i : Fin 2) :
    HasWeakPartialDerivOn (Metric.ball (0 : Vec 2) 1) i (fun _ => (0 : ℝ)) (fun _ => 0) :=
  hasWeakPartialDerivOn_of_local Metric.isOpen_ball (locallyIntegrableOn_const _)
    (locallyIntegrableOn_const _) fun _ hx =>
    ⟨Metric.ball (0 : Vec 2) 1, Metric.isOpen_ball, hx, subset_rfl,
      fun φ _ _ _ => by simp⟩

end SuperdiffusionCLT.Section7
