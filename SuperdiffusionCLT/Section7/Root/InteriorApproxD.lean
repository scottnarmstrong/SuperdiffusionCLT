/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Root.InteriorApproxC
public import SuperdiffusionCLT.Section7.Analytic.OpenH10.LipschitzB
public import SuperdiffusionCLT.Section7.Analytic.Change.Dilation
public import SuperdiffusionCLT.Section7.Prereq.RhsLemmaB

/-!
# Interior approximation: the mollified equation

For a solution `u` of `-∇·a∇u = f` in a bounded open `Q` and a bounded open `V ⊆ Q` whose
`h`-thickening stays well inside `Q`, the function `uhom - η_h ∗ u` solves in `V`
`s Δ w = ∇·(η_h ∗ ((a - s)∇u)) + (f - η_h ∗ f)` weakly.

* `ia_extension`: cutoff extension of `u` to `H¹(ℝᵈ)` (agreeing with `u` away from `∂Q`);
* `ia_conv_V`: the convolution identity tested against `H¹₀(V)`;
* `ia_weak_eq`: the tested equation of `uhom - η_h ∗ u`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- **Cutoff extension.**  An `H¹(Q)` function on a bounded open set agrees, together with its
gradient, with an `H¹(ℝᵈ)` function at all points of `Q` that are at distance more than `2 r`
from the complement. -/
theorem ia_extension {Q : Set (Vec d)} (hQ : IsOpen Q) (hQb : Bornology.IsBounded Q)
    (u : H1Function Q) {r : ℝ} (hr : 0 < r) :
    ∃ ut : H1Function (Set.univ : Set (Vec d)), ∀ x ∈ Q, 2 * r < Metric.infDist x Qᶜ →
      ut.toFun x = u.toFun x ∧ ut.grad x = u.grad x := by
  obtain ⟨hζc, hζU⟩ := l2a_cutoff_compact hQb hr
  set cut := mulLipH10 hQ u (l2a_cutoff_lipschitz Q hr) (fun x => l2a_cutoff_abs_le Q r x)
    hζc hζU with hcut
  refine ⟨(cut.extendByZeroToOpenSuperset hQ.measurableSet isOpen_univ (Set.subset_univ _)).toH1Function,
    fun x hx hd => ?_⟩
  have h1 : l2a_cutoff Q r x = 1 := l2a_cutoff_eq_one hr hd.le
  have h2 : lipGradient (l2a_cutoff Q r) x = 0 := l2a_lipGradient_cutoff_eq_zero Q hr (Or.inr hd)
  have hT : (cut.extendByZeroToOpenSuperset hQ.measurableSet isOpen_univ
      (Set.subset_univ _)).toH1Function.toFun x = cut.toH1Function.toFun x := by
    rw [H10Function.extendByZeroToOpenSuperset_toFun, H10Function.zeroExtension_apply_of_mem _ hx]
  have hG : (cut.extendByZeroToOpenSuperset hQ.measurableSet isOpen_univ
      (Set.subset_univ _)).toH1Function.grad x = cut.toH1Function.grad x := by
    rw [H10Function.extendByZeroToOpenSuperset_grad, H10Function.zeroExtensionGrad_apply_of_mem _ hx]
  refine ⟨?_, ?_⟩
  · rw [hT, hcut, mulLipH10_toH1Function]
    simp [mulLip_toFun, h1]
  · rw [hG, hcut, mulLipH10_toH1Function]
    simp [mulLip_grad, h1, h2]

/-- **The convolution identity tested against `H¹₀(V)`** (`e.Dir.new.convolution.identity`),
for `V ⊆ Q`: if `-∇·F = f` weakly in `Q`, then `∫_V (η_h ∗ F)·∇φ = ∫_V (η_h ∗ f) φ` for
`φ ∈ H¹₀(V)`, when the `h`-thickening of `V` lies in `Q`. -/
theorem ia_conv_V {Q V : Set (Vec d)} (hQ : IsOpen Q) (hQb : Bornology.IsBounded Q)
    (hV : IsOpen V) (hVQ : V ⊆ Q) {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0)
    (hKW : Metric.cthickening h (closure V) ⊆ Q) {F : Vec d → Vec d} {f : Vec d → ℝ}
    (hF : ∀ i, LocallyIntegrableOn (fun x => F x i) Q volume)
    (hf : LocallyIntegrableOn f Q volume)
    (hweak : ∀ ψ : H10Function Q,
      ∫ x in Q, vecDot (F x) (ψ.toH1Function.grad x) = ∫ x in Q, f x * ψ.toH1Function.toFun x)
    (φ : H10Function V) :
    ∫ x in V, vecDot (a16_mollify d h η F x) (φ.toH1Function.grad x) =
      ∫ x in V, l2a_moll d h η f x * φ.toH1Function.toFun x := by
  have hVb : Bornology.IsBounded V := hQb.subset hVQ
  have hK : IsCompact (closure V) := hVb.isCompact_closure
  set Θ := (φ.extendByZeroToOpenSuperset hV.measurableSet hQ hVQ) with hΘdef
  have hΘ : ∀ x ∈ Q, x ∉ closure V → Θ.toH1Function.toFun x = 0 := by
    intro x _ hx
    rw [hΘdef, H10Function.extendByZeroToOpenSuperset_toFun,
      H10Function.zeroExtension_apply_of_not_mem _ (fun hxV => hx (subset_closure hxV))]
  have key := l2a_convolution_identity hQ hQb hh hη hηs hK hKW hF hf hweak Θ.toH1Function hΘ
  have e1 : ∫ x in Q, vecDot (a16_mollify d h η F x) (Θ.toH1Function.grad x) =
      ∫ x in V, vecDot (a16_mollify d h η F x) (φ.toH1Function.grad x) := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hQ.measurableSet hVQ]
    · refine setIntegral_congr_fun hV.measurableSet fun x hx => ?_
      simp only [hΘdef, H10Function.extendByZeroToOpenSuperset_grad,
        H10Function.zeroExtensionGrad_apply_of_mem _ hx]
    · intro x hx
      simp only [hΘdef, H10Function.extendByZeroToOpenSuperset_grad,
        H10Function.zeroExtensionGrad_apply_of_not_mem _ hx.2]
      simp [vecDot]
  have e2 : ∫ x in Q, l2a_moll d h η f x * Θ.toH1Function.toFun x =
      ∫ x in V, l2a_moll d h η f x * φ.toH1Function.toFun x := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hQ.measurableSet hVQ]
    · refine setIntegral_congr_fun hV.measurableSet fun x hx => ?_
      simp only [hΘdef, H10Function.extendByZeroToOpenSuperset_toFun,
        H10Function.zeroExtension_apply_of_mem _ hx]
    · intro x hx
      simp only [hΘdef, H10Function.extendByZeroToOpenSuperset_toFun,
        H10Function.zeroExtension_apply_of_not_mem _ hx.2]
      simp
  rw [← e1, ← e2]
  exact key

/-- A continuous modification of the cut-off mollification. -/
theorem ia_moll_cont {Q V : Set (Vec d)} (hVb : Bornology.IsBounded V) {h : ℝ} (hh : 0 < h)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0)
    (hKW : Metric.cthickening h (closure V) ⊆ Q) {g : Vec d → ℝ}
    (hg : LocallyIntegrableOn g Q volume) :
    ∃ c : Vec d → ℝ, Continuous c ∧ ∀ x ∈ closure V, c x = l2a_moll d h η g x := by
  have hK : IsCompact (closure V) := hVb.isCompact_closure
  obtain ⟨hi, hc⟩ := l2a_cut_integrable hK hKW hg
  obtain ⟨hco, -⟩ := l2a_moll_cont_compact hh hη hηs hi hc
  exact ⟨_, hco, fun x hx => l2a_moll_indicator_eq hh hηs hx⟩

/-- The mollification of a locally integrable function is integrable against an `L²(V)`
function. -/
theorem ia_integrableOn_moll_mul {Q V : Set (Vec d)} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0) (hKW : Metric.cthickening h (closure V) ⊆ Q)
    {g : Vec d → ℝ} (hg : LocallyIntegrableOn g Q volume) {p : Vec d → ℝ} (hp : MemL2On V p) :
    IntegrableOn (fun x => l2a_moll d h η g x * p x) V := by
  obtain ⟨c, hc, hce⟩ := ia_moll_cont (Q := Q) hVb hh hη hηs hKW hg
  have h1 := l2a_integrableOn_mul_memL2 (l2a_memL2_of_continuous hV.measurableSet hVb hc) hp
  refine h1.congr_fun (fun x hx => ?_) hV.measurableSet
  simp only [hce x (subset_closure hx)]

/-- Matrix-vector product with a difference. -/
theorem ia_matVecMul_sub (A : Mat d) (S : ℝ) (v : Vec d) :
    matVecMul (A - S • (1 : Mat d)) v = matVecMul A v - S • v :=
  r1_matVecMul_sub_smul_one A S v

/-- Weak derivatives only see the values on the set. -/
theorem ia_weakDeriv_congr_on {U : Set (Vec d)} (hUm : MeasurableSet U) {i : Fin d} {u u' g : Vec d → ℝ}
    (h : HasWeakPartialDerivOn U i u g) (hu : ∀ x ∈ U, u x = u' x) :
    HasWeakPartialDerivOn U i u' g := by
  intro φ hφ hφc hφU
  rw [← h φ hφ hφc hφU]
  refine setIntegral_congr_fun ?_ fun x hx => ?_
  · exact hUm
  · simp only [hu x hx]

theorem ia_vecDot_smul_left (c : ℝ) (v w : Vec d) : vecDot (c • v) w = c * vecDot v w := by
  simp [vecDot, Finset.mul_sum, mul_assoc]

/-- **The equation of `uhom - η_h ∗ u`** (the mollified equation, tested
against `H¹₀(V)`):
`s ∫_V ∇w·∇φ = ∫_V (f - η_h ∗ f) φ + ∫_V G·∇φ` with `G = η_h ∗ ((a - s)∇u)`. -/
theorem ia_weak_eq {Q V : Set (Vec d)} (hQ : IsOpen Q) (hQb : Bornology.IsBounded Q)
    (hV : IsOpen V) (hVQ : V ⊆ Q) {h : ℝ} (hh : 0 < h) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0) {r : ℝ} (hr : 0 < r)
    (hmarg : ∀ x ∈ Metric.cthickening h V, x ∈ Q ∧ 2 * r < Metric.infDist x Qᶜ)
    {a : CoeffField d} {u : H1Function Q} {f : Vec d → ℝ} {s : ℝ}
    (hF : ∀ i, LocallyIntegrableOn (fun x => matVecMul (a x) (u.grad x) i) Q volume)
    (hf : LocallyIntegrableOn f Q volume) (hfm : Measurable f) {Fs : ℝ} (hfb : ∀ x ∈ V, |f x| ≤ Fs)
    (hu : IsWeakSolutionOn a Q u f (fun _ => 0))
    (uhom : H1Function V)
    (hhom : IsWeakSolutionOn (fun _ => s • (1 : Mat d)) V uhom f (fun _ => 0))
    (w : H10Function V)
    (hw : ∀ x ∈ V, w.toH1Function.toFun x = uhom.toFun x - l2a_moll d h η u.toFun x)
    (φ : H10Function V) :
    s * ∫ x in V, vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x) =
      (∫ x in V, (f x - l2a_moll d h η f x) * φ.toH1Function.toFun x) +
        ∫ x in V, vecDot (a16_mollify d h η
          (fun y => matVecMul (a y - s • (1 : Mat d)) (u.grad y)) x) (φ.toH1Function.grad x) := by
  have hVb : Bornology.IsBounded V := hQb.subset hVQ
  have hKW : Metric.cthickening h (closure V) ⊆ Q := by
    rw [Metric.cthickening_closure]; exact fun x hx => (hmarg x hx).1
  obtain ⟨ut, hut⟩ := ia_extension hQ hQb u hr
  -- agreement of the extension near `V`
  have hagree : ∀ x ∈ V, ∀ y, dist y x ≤ h → ut.toFun y = u.toFun y ∧ ut.grad y = u.grad y := by
    intro x hx y hy
    have hyT : y ∈ Metric.cthickening h V := Metric.mem_cthickening_of_dist_le y x h V hx hy
    exact hut y (hmarg y hyT).1 (hmarg y hyT).2
  have hmoll : ∀ x ∈ V, l2a_moll d h η ut.toFun x = l2a_moll d h η u.toFun x := fun x hx =>
    l2a_moll_congr hh hηs fun y hy => (hagree x hx y hy).1
  have hmollg : ∀ x ∈ V, ∀ i, l2a_moll d h η (fun y => ut.grad y i) x =
      l2a_moll d h η (fun y => u.grad y i) x := fun x hx i =>
    l2a_moll_congr hh hηs fun y hy => by rw [(hagree x hx y hy).2]
  set F : Vec d → Vec d := fun y => matVecMul (a y) (u.grad y) with hFdef
  have hFcomp : ∀ i, LocallyIntegrableOn (fun x => F x i) Q volume := hF
  have hgl : ∀ i, LocallyIntegrableOn (fun y => ut.grad y i) Q volume := fun i =>
    (l2a_locInt_of_memL2_univ (ut.gradMemL2 i)).locallyIntegrableOn _
  have hφg : ∀ i, MemL2On V (fun x => φ.toH1Function.grad x i) := fun i => φ.toH1Function.gradMemL2 i
  -- integrability of the three vector pairings
  have hpair : ∀ {g : Fin d → Vec d → ℝ}, (∀ i, LocallyIntegrableOn (g i) Q volume) →
      IntegrableOn (fun x => vecDot (fun i => l2a_moll d h η (g i) x) (φ.toH1Function.grad x)) V := by
    intro g hg
    refine l2a_integrableOn_sum (f := fun i x => l2a_moll d h η (g i) x * φ.toH1Function.grad x i) ?_
    intro i
    exact ia_integrableOn_moll_mul hV hVb hh hη hηs hKW (hg i) (hφg i)
  have hIMg : IntegrableOn (fun x => vecDot (a16_mollify d h η ut.grad x) (φ.toH1Function.grad x)) V :=
    hpair (g := fun i y => ut.grad y i) hgl
  have hIF : IntegrableOn (fun x => vecDot (a16_mollify d h η F x) (φ.toH1Function.grad x)) V :=
    hpair (g := fun i y => F y i) hFcomp
  have hIu : IntegrableOn (fun x => vecDot (uhom.grad x) (φ.toH1Function.grad x)) V :=
    l2a_integrableOn_sum (f := fun i x => uhom.grad x i * φ.toH1Function.grad x i) fun i =>
      l2a_integrableOn_mul_memL2 (uhom.gradMemL2 i) (hφg i)
  have hIf : IntegrableOn (fun x => f x * φ.toH1Function.toFun x) V := by
    have h1 := l2a_integrableOn_bdd (W := V) (c := V.indicator f)
      (hfm.indicator hV.measurableSet).aestronglyMeasurable (C := |Fs|)
      (fun x => by
        by_cases hx : x ∈ V
        · rw [Set.indicator_of_mem hx, Real.norm_eq_abs]; exact (hfb x hx).trans (le_abs_self _)
        · rw [Set.indicator_of_notMem hx]; simp)
      (l2a_integrableOn_of_memL2 hVb φ.toH1Function.memL2)
    exact h1.congr_fun (fun x hx => by simp only [Set.indicator_of_mem hx]) hV.measurableSet
  have hIm : IntegrableOn (fun x => l2a_moll d h η f x * φ.toH1Function.toFun x) V :=
    ia_integrableOn_moll_mul hV hVb hh hη hηs hKW hf φ.toH1Function.memL2
  -- gradient identification
  set θ := l2a_mollH1 hV hVb hh hη hηs ut with hθ
  have hwg : ∀ᵐ x ∂(volume.restrict V),
      w.toH1Function.grad x = uhom.grad x - a16_mollify d h η ut.grad x := by
    have hi : ∀ i, (fun x => w.toH1Function.grad x i) =ᵐ[volume.restrict V]
        (fun x => uhom.grad x i - l2a_moll d h η (fun y => ut.grad y i) x) := by
      intro i
      have h1 := ia_weakDeriv_congr_on hV.measurableSet (w.toH1Function.hasWeakGradient i)
        (u' := (uhom - θ).toFun) (fun x hx => by
          rw [hw x hx]; simp [hθ, hmoll x hx])
      have h2 := (uhom - θ).hasWeakGradient i
      have hl1 : LocallyIntegrableOn (fun x => w.toH1Function.grad x i) V volume :=
        locallyIntegrableOn_of_locallyIntegrable_restrict
          ((w.toH1Function.gradMemL2 i).locallyIntegrable (by norm_num))
      have hl2 : LocallyIntegrableOn (fun x => (uhom - θ).grad x i) V volume :=
        locallyIntegrableOn_of_locallyIntegrable_restrict
          (((uhom - θ).gradMemL2 i).locallyIntegrable (by norm_num))
      have := HasWeakPartialDerivOn.ae_eq hV hl1 hl2 h1 h2
      simpa [hθ] using this
    have hall : ∀ᵐ x ∂(volume.restrict V), ∀ i, w.toH1Function.grad x i =
        uhom.grad x i - l2a_moll d h η (fun y => ut.grad y i) x := by
      rw [ae_all_iff]; exact hi
    filter_upwards [hall] with x hx
    funext i
    exact hx i
  have N1 : ∫ x in V, vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x) =
      (∫ x in V, vecDot (uhom.grad x) (φ.toH1Function.grad x)) -
        ∫ x in V, vecDot (a16_mollify d h η ut.grad x) (φ.toH1Function.grad x) := by
    rw [← integral_sub hIu hIMg]
    refine integral_congr_ae ?_
    filter_upwards [hwg] with x hx
    rw [hx]
    simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have E1 : s * ∫ x in V, vecDot (uhom.grad x) (φ.toH1Function.grad x) =
      ∫ x in V, f x * φ.toH1Function.toFun x := by
    have := hhom φ
    simp only [a18_matVecMul_smul_one, ia_vecDot_smul_left] at this
    rw [integral_const_mul] at this
    rw [this]
    simp [vecDot]
  have E2 := ia_conv_V hQ hQb hV hVQ hh hη hηs hKW hFcomp hf (f := f) (fun ψ => by
    have := hu ψ
    simp only [vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, integral_zero,
      add_zero] at this ⊢
    exact this) φ
  set G : Vec d → Vec d := fun x => a16_mollify d h η
    (fun y => matVecMul (a y - s • (1 : Mat d)) (u.grad y)) x with hG
  have E3 : ∀ x ∈ V, vecDot (a16_mollify d h η F x) (φ.toH1Function.grad x) =
      s * vecDot (a16_mollify d h η ut.grad x) (φ.toH1Function.grad x) +
        vecDot (G x) (φ.toH1Function.grad x) := by
    intro x hx
    have hsplit : ∀ i, a16_mollify d h η F x i = s * a16_mollify d h η ut.grad x i + G x i := by
      intro i
      have h1 := l2a_flux_split hh hη hηs (hVb.isCompact_closure) hKW hFcomp ut s
        (subset_closure hx) i
      rw [h1]
      congr 1
      rw [hG]
      simp only [l2a_mollify_apply]
      refine l2a_moll_congr hh hηs fun y hy => ?_
      have := (hagree x hx y hy).2
      simp only [hFdef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, this, ia_matVecMul_sub]
    simp only [vecDot, hsplit, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  have hIG : IntegrableOn (fun x => vecDot (G x) (φ.toH1Function.grad x)) V := by
    have := hIF.sub (hIMg.const_mul s)
    refine this.congr_fun (fun x hx => ?_) hV.measurableSet
    have h3 := E3 x hx
    simp only [Pi.sub_apply]
    linarith only [h3]
  have E4 : ∫ x in V, vecDot (a16_mollify d h η F x) (φ.toH1Function.grad x) =
      s * (∫ x in V, vecDot (a16_mollify d h η ut.grad x) (φ.toH1Function.grad x)) +
        ∫ x in V, vecDot (G x) (φ.toH1Function.grad x) := by
    rw [← integral_const_mul (μ := volume.restrict V) s, ← integral_add (hIMg.const_mul s) hIG]
    exact setIntegral_congr_fun hV.measurableSet E3
  have hfm' : ∫ x in V, (f x - l2a_moll d h η f x) * φ.toH1Function.toFun x =
      (∫ x in V, f x * φ.toH1Function.toFun x) -
        ∫ x in V, l2a_moll d h η f x * φ.toH1Function.toFun x := by
    rw [← integral_sub hIf hIm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [N1, mul_sub, E1, hfm']
  have := E4
  rw [E2] at this
  linarith only [this]

end SuperdiffusionCLT.Section7
