/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.L2AssemblyB
public import SuperdiffusionCLT.Section7.Prereq.L2BoundaryC
public import SuperdiffusionCLT.Section7.Prereq.L2ComparisonD
public import SuperdiffusionCLT.Section7.Root.RescalingB
public import SuperdiffusionCLT.Section7.Analytic.CZ.GlobalC
public import Homogenization.HighContrast.Coupled.Stampacchia.LevelEnergy

/-!
# The equation for the comparison difference `w - uhom`

Display `e.Dir.new.convolution.identity`, divided by
the homogenized coefficient: for the comparison function `w = ζ (η_h ∗ ũ) + (1 - ζ) g`, the
difference `v = w - uhom` lies in `H¹₀(V)` and solves `-Δ v = h - ∇·Fv` weakly, with the scalar datum
`h = s⁻¹ (ζ η∗f - f - ∇ζ·η∗F)` and the flux `Fv = -s⁻¹ ζ η∗(F - s ∇ũ) + (1-ζ) ∇g + (η∗ũ - g) ∇ζ`
(`l2d_equation`).
-/

@[expose] public section

open MeasureTheory Set Filter Homogenization
open scoped ENNReal NNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- **An `H¹₀` witness with the prescribed gradient**: if `u - g` has an `H¹₀` representative of
its value, then there is an `H¹₀` function whose underlying `H¹` function is `u - g`. -/
theorem l2d_h10_of_mem {V : Set (Vec d)} (hV : IsOpen V) (u g : H1Function V)
    (hm : MemH10 V (fun x => u.toFun x - g.toFun x)) :
    ∃ ψ : H10Function V, ψ.toH1Function = u - g := by
  obtain ⟨ψ0, h0⟩ := hm
  have hv : ψ0.toH1Function.toFun = (u - g).toFun := by
    rw [h0, H1Function.sub_toFun]
  have hae : ψ0.toH1Function.grad =ᵐ[volume.restrict V] (u - g).grad :=
    h1grad_ae_eq_of_toFun_ae_eq hV (Filter.Eventually.of_forall fun x => congrFun hv x)
  refine ⟨{ toH1Function := u - g
            approx := ψ0.approx
            approx_smooth := ψ0.approx_smooth
            approx_hasCompactSupport := ψ0.approx_hasCompactSupport
            approx_support_subset := ψ0.approx_support_subset
            tendsto_approx := ?_
            tendsto_approx_grad := ?_ }, rfl⟩
  · rw [← hv]
    exact ψ0.tendsto_approx
  · intro i
    refine (ψ0.tendsto_approx_grad i).congr' ?_
    filter_upwards with n
    refine eLpNorm_congr_ae ?_
    filter_upwards [hae] with x hx
    simp [hx]


section Helpers

variable {V : Set (Vec d)}

theorem l2d_vecDot_eq_sum (X Y : Vec d) : vecDot X Y = ∑ i, X i * Y i := rfl

/-- A bounded measurable multiplier times a product of two `L²` functions is integrable. -/
theorem l2d_int_bdd_prod {c a b : Vec d → ℝ} (hc : AEStronglyMeasurable c volume) {B : ℝ}
    (hB : ∀ x, ‖c x‖ ≤ B) (ha : MemL2On V a) (hb : MemL2On V b) :
    IntegrableOn (fun x => c x * (a x * b x)) V :=
  l2a_integrableOn_bdd hc hB (l2a_integrableOn_mul_memL2 ha hb)

/-- A continuous compactly supported function is bounded. -/
theorem l2d_bdd_of_compact {c : Vec d → ℝ} (hc : Continuous c) (hs : HasCompactSupport c) :
    ∃ B : ℝ, ∀ x, ‖c x‖ ≤ B := hc.bounded_above_of_compact_support hs

/-- The pairing `∇ζ · G` of the gradient of the cutoff with a continuous field is bounded. -/
theorem l2d_lip_dot_bdd {r : ℝ} (hr : 0 < r) (hc : HasCompactSupport (l2a_cutoff V r))
    {G : Vec d → Vec d} (hG : ∀ i, Continuous fun x => G x i) :
    ∃ B : ℝ, ∀ x, ‖vecDot (lipGradient (l2a_cutoff V r) x) (G x)‖ ≤ B := by
  have hK : IsCompact (tsupport (l2a_cutoff V r)) := hc
  have hb : ∀ i, ∃ Bi : ℝ, ∀ x ∈ tsupport (l2a_cutoff V r), ‖G x i‖ ≤ Bi := fun i =>
    hK.exists_bound_of_continuousOn (hG i).continuousOn
  choose Bi hBi using hb
  refine ⟨∑ i, (1 / r) * max (Bi i) 0, fun x => ?_⟩
  by_cases hx : x ∈ tsupport (l2a_cutoff V r)
  · rw [Real.norm_eq_abs, l2d_vecDot_eq_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    have h1 : |lipGradient (l2a_cutoff V r) x i| ≤ 1 / r := by
      have := l2a_lipGradient_abs_le (l2a_cutoff_lipschitz V hr) x i
      rwa [Real.coe_toNNReal _ (by positivity)] at this
    have h2 := hBi i x hx
    rw [Real.norm_eq_abs] at h2
    exact mul_le_mul h1 (h2.trans (le_max_left _ _)) (abs_nonneg _) (by positivity)
  · have h0 : lipGradient (l2a_cutoff V r) x = 0 :=
      l2a_lipGradient_eq_zero_off (isClosed_tsupport _)
        (fun y hy => image_eq_zero_of_notMem_tsupport hy) hx
    have hnn : 0 ≤ ∑ i, (1 / r) * max (Bi i) 0 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (le_max_right _ _)
    simpa [h0, vecDot] using hnn

end Helpers


section Equation

variable {V : Set (Vec d)}

/-- The comparison function `w = ζ (η_h ∗ ũ) + (1 - ζ) g` with the cutoff of margin `r`. -/
noncomputable def l2d_w (hV : IsOpen V) (hVb : Bornology.IsBounded V) {r h : ℝ} (hr : 0 < r)
    (hh : 0 < h) {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0) (ũ : H1Function (Set.univ : Set (Vec d)))
    (g : H1Function V) : H1Function V :=
  l2a_wH1 hV hVb hh hη hηs ũ g (l2a_cutoff_lipschitz V hr) (l2a_cutoff_nonneg V r)
    (l2a_cutoff_le_one V r)

/-- The scalar part of the equation for `w - uhom`. -/
noncomputable def l2d_h1 (V : Set (Vec d)) (r h : ℝ) (η : Vec d → ℝ) (s : ℝ) (f : Vec d → ℝ)
    (x : Vec d) : ℝ :=
  s⁻¹ * (l2a_cutoff V r x * l2a_moll d h η f x - f x)

/-- The layer part of the scalar datum. -/
noncomputable def l2d_h2 (V : Set (Vec d)) (r h : ℝ) (η : Vec d → ℝ) (s : ℝ) (F : Vec d → Vec d)
    (x : Vec d) : ℝ :=
  (-s⁻¹) * vecDot (lipGradient (l2a_cutoff V r) x) (a16_mollify d h η F x)

/-- The flux part of the equation for `w - uhom`. -/
noncomputable def l2d_Fv (V : Set (Vec d)) (r h : ℝ) (η : Vec d → ℝ) (s : ℝ)
    (ũ : H1Function (Set.univ : Set (Vec d))) (g : H1Function V) (F : Vec d → Vec d)
    (x : Vec d) : Vec d :=
  ((-s⁻¹) * l2a_cutoff V r x) • a16_mollify d h η (fun y => F y - s • ũ.grad y) x +
    (1 - l2a_cutoff V r x) • g.grad x +
    (l2a_moll d h η ũ.toFun x - g.toFun x) • lipGradient (l2a_cutoff V r) x

theorem l2d_matVecMul_one (v : Vec d) : matVecMul (1 : Mat d) v = v := Matrix.one_mulVec v



/-- **The equation for `v = w - uhom`** (the convolution identity divided by `s`):
`v ∈ H¹₀(V)` solves `-Δ v = h - ∇·Fv` weakly, with the data `h = h₁ + h₂` and `Fv` of the five
error terms. -/
theorem l2d_equation [NeZero d] (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {r h : ℝ} (hr : 0 < r) (hh : 0 < h) (hhr : h ≤ r / 4)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηs : ∀ w, (∃ i, 1 < |w i|) → η w = 0)
    (ũ : H1Function (Set.univ : Set (Vec d))) (g ub : H1Function V)
    (hub : ∃ ψ : H10Function V, ψ.toH1Function = ub - g)
    {F : Vec d → Vec d} {f : Vec d → ℝ}
    (hFc : ∀ i, LocallyIntegrable (fun x => F x i) volume) (hfc : LocallyIntegrable f volume)
    (hweak : ∀ φ : H10Function V, ∫ x in V, vecDot (F x) (φ.toH1Function.grad x) =
      ∫ x in V, f x * φ.toH1Function.toFun x)
    {s : ℝ} (hs : s ≠ 0)
    (hhom : ∀ φ : H10Function V, s * ∫ x in V, vecDot (ub.grad x) (φ.toH1Function.grad x) =
      ∫ x in V, f x * φ.toH1Function.toFun x)
    (hfφ : ∀ φ : H10Function V, IntegrableOn (fun x => f x * φ.toH1Function.toFun x) V) :
    ∃ v : H10Function V,
      v.toH1Function = l2d_w hV hVb hr hh hη hηs ũ g - ub ∧
      IsWeakSolutionOn (fun _ => (1 : Mat d)) V v.toH1Function
        (fun x => l2d_h1 V r h η s f x + l2d_h2 V r h η s F x)
        (l2d_Fv V r h η s ũ g F) ∧
      MemVectorL2 V (l2d_Fv V r h η s ũ g F) ∧
      (∀ ψ : H10Function V, IntegrableOn (fun x => l2d_h1 V r h η s f x * ψ.toH1Function.toFun x) V) ∧
      (∀ ψ : H10Function V, IntegrableOn (fun x => l2d_h2 V r h η s F x * ψ.toH1Function.toFun x) V) := by
  obtain ⟨ψub, hψub⟩ := hub
  have hhr' : h < r := by linarith only [hhr, hr]
  obtain ⟨K, hK, hKW, hζK⟩ := l2a_cutoff_margin_data hVb hr hh.le hhr'
  set ζ := l2a_cutoff V r with hζdef
  have hζL := l2a_cutoff_lipschitz V hr
  have hζ0 := l2a_cutoff_nonneg V r
  have hζ1 := l2a_cutoff_le_one V r
  obtain ⟨hcs, hts⟩ := l2a_cutoff_compact hVb hr
  have hζc : Continuous ζ := l2a_cutoff_continuous V hr
  set w := l2d_w hV hVb hr hh hη hηs ũ g with hw
  -- the `H¹₀` function `v`
  let v : H10Function V := h10Sub (l2a_wMinusG hV hVb hh hη hηs ũ g hζL hζ0 hζ1 hcs hts) ψub
  have hvH : v.toH1Function = w - ub := by
    show (l2a_wMinusG hV hVb hh hη hηs ũ g hζL hζ0 hζ1 hcs hts).toH1Function - ψub.toH1Function = _
    rw [l2a_wMinusG_toH1Function, hψub]
    exact sub_sub_sub_cancel_right _ _ _
  -- continuity
  have hmf : Continuous (l2a_moll d h η f) := (l2a_moll_contDiff hh hη hηs hfc).continuous
  have hmu : Continuous (l2a_moll d h η ũ.toFun) :=
    (l2a_moll_contDiff hh hη hηs (l2a_locInt_of_memL2_univ ũ.memL2)).continuous
  have hG2 : ∀ i, Continuous fun x => a16_mollify d h η F x i := fun i =>
    (l2a_moll_contDiff hh hη hηs (hFc i)).continuous
  have hG3 : ∀ i, Continuous fun x => a16_mollify d h η (fun y => F y - s • ũ.grad y) x i := by
    intro i
    have hl : LocallyIntegrable (fun y => F y i - s * ũ.grad y i) volume :=
      (hFc i).sub ((l2a_locInt_of_memL2_univ (ũ.gradMemL2 i)).smul s)
    exact (l2a_moll_contDiff hh hη hηs hl).continuous
  -- integrability
  have hφi : ∀ φ : H10Function V, IntegrableOn φ.toH1Function.toFun V := fun φ =>
    l2a_integrableOn_of_memL2 hVb φ.toH1Function.memL2
  have hZ : Continuous fun x => ζ x * l2a_moll d h η f x := hζc.mul hmf
  have hZc : HasCompactSupport fun x => ζ x * l2a_moll d h η f x := hcs.mul_right
  obtain ⟨BZ, hBZ⟩ := l2d_bdd_of_compact hZ hZc
  have hJ1 : ∀ φ : H10Function V,
      IntegrableOn (fun x => (ζ x * l2a_moll d h η f x) * φ.toH1Function.toFun x) V := fun φ =>
    l2a_integrableOn_bdd hZ.aestronglyMeasurable hBZ (hφi φ)
  have hZ3 : ∀ i, Continuous fun x => ζ x * a16_mollify d h η (fun y => F y - s • ũ.grad y) x i :=
    fun i => hζc.mul (hG3 i)
  have hZ3c : ∀ i, HasCompactSupport fun x =>
      ζ x * a16_mollify d h η (fun y => F y - s • ũ.grad y) x i := fun i => hcs.mul_right
  have hJ3 : ∀ (φ : H10Function V) (i : Fin d), IntegrableOn (fun x =>
      (ζ x * a16_mollify d h η (fun y => F y - s • ũ.grad y) x i) * φ.toH1Function.grad x i) V := by
    intro φ i
    obtain ⟨B, hB⟩ := l2d_bdd_of_compact (hZ3 i) (hZ3c i)
    exact l2a_integrableOn_bdd (hZ3 i).aestronglyMeasurable hB
      (l2a_integrableOn_of_memL2 hVb (φ.toH1Function.gradMemL2 i))
  obtain ⟨B2, hB2⟩ := l2d_lip_dot_bdd hr hcs hG2
  have hm2 : AEStronglyMeasurable (fun x => vecDot (lipGradient ζ x) (a16_mollify d h η F x))
      volume := by
    unfold vecDot
    refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
    exact ((((aemeasurable_pi_iff.1 (l2b_lipGradient_measurable ζ).aemeasurable) i)).aestronglyMeasurable).mul
      (hG2 i).aestronglyMeasurable
  have hJ2 : ∀ φ : H10Function V, IntegrableOn (fun x =>
      vecDot (lipGradient ζ x) (a16_mollify d h η F x) * φ.toH1Function.toFun x) V := fun φ =>
    l2a_integrableOn_bdd hm2 hB2 (hφi φ)
  have hmg : MemL2On V (fun x => l2a_moll d h η ũ.toFun x - g.toFun x) :=
    (l2a_memL2_of_continuous hV.measurableSet hVb hmu).sub g.memL2
  have hlip_i : ∀ i, AEStronglyMeasurable (fun x => lipGradient ζ x i) volume := fun i =>
    (aemeasurable_pi_iff.1 (l2b_lipGradient_measurable ζ).aemeasurable i).aestronglyMeasurable
  have hlip_b : ∀ i x, ‖lipGradient ζ x i‖ ≤ 1 / r := fun i x => by
    have := l2a_lipGradient_abs_le hζL x i
    rw [Real.norm_eq_abs]
    rwa [Real.coe_toNNReal _ (by positivity)] at this
  have hJ4 : ∀ (φ : H10Function V) (i : Fin d), IntegrableOn (fun x =>
      (1 - ζ x) * (g.grad x i * φ.toH1Function.grad x i)) V := fun φ i =>
    l2d_int_bdd_prod (c := fun x => 1 - ζ x) (continuous_const.sub hζc).aestronglyMeasurable
      (B := 1) (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith only [hζ1 x])]
        linarith only [hζ0 x]) (g.gradMemL2 i) (φ.toH1Function.gradMemL2 i)
  have hJ5 : ∀ (φ : H10Function V) (i : Fin d), IntegrableOn (fun x =>
      lipGradient ζ x i * ((l2a_moll d h η ũ.toFun x - g.toFun x) *
        φ.toH1Function.grad x i)) V := fun φ i =>
    l2d_int_bdd_prod (hlip_i i) (hlip_b i) hmg (φ.toH1Function.gradMemL2 i)
  have hI1 : ∀ ψ : H10Function V,
      IntegrableOn (fun x => l2d_h1 V r h η s f x * ψ.toH1Function.toFun x) V := by
    intro ψ
    refine (((hJ1 ψ).sub (hfφ ψ)).const_mul s⁻¹).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [l2d_h1, hζdef, Pi.sub_apply]
    ring
  have hI2 : ∀ ψ : H10Function V,
      IntegrableOn (fun x => l2d_h2 V r h η s F x * ψ.toH1Function.toFun x) V := by
    intro ψ
    refine ((hJ2 ψ).const_mul (-s⁻¹)).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [l2d_h2, hζdef]
    ring
  -- the flux is in `L²`
  have hFv : MemVectorL2 V (l2d_Fv V r h η s ũ g F) := by
    refine (MeasureTheory.memLp_pi_iff).2 fun i => ?_
    have t1 : MemL2On V (fun x => ((-s⁻¹) * ζ x) *
        a16_mollify d h η (fun y => F y - s • ũ.grad y) x i) := by
      have hc : Continuous fun x => ((-s⁻¹) * ζ x) *
          a16_mollify d h η (fun y => F y - s • ũ.grad y) x i :=
        (continuous_const.mul hζc).mul (hG3 i)
      exact l2a_memL2_of_continuous hV.measurableSet hVb hc
    have t2 : MemL2On V (fun x => (1 - ζ x) * g.grad x i) := by
      refine MemLp.of_le_mul (c := 1) (g.gradMemL2 i)
        ((continuous_const.sub hζc).aestronglyMeasurable.mul
          (g.gradMemL2 i).aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul, Real.norm_of_nonneg (by linarith only [hζ1 x] : 0 ≤ 1 - ζ x)]
      have : 1 - ζ x ≤ 1 := by linarith only [hζ0 x]
      nlinarith only [this, norm_nonneg (g.grad x i), hζ1 x]
    have t3 : MemL2On V (fun x => (l2a_moll d h η ũ.toFun x - g.toFun x) *
        lipGradient ζ x i) := by
      refine MemLp.of_le_mul (c := 1 / r) hmg
        (hmg.aestronglyMeasurable.mul ((hlip_i i).mono_measure Measure.restrict_le_self))
        (Filter.Eventually.of_forall fun x => ?_)
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hlip_b i x) (norm_nonneg _)
    have := (t1.add t2).add t3
    refine this.ae_eq (Filter.Eventually.of_forall fun x => ?_)
    simp only [l2d_Fv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hζdef]
  refine ⟨v, hvH, ?_, hFv, hI1, hI2⟩
  intro φ
  have hid := l2a_comparison_identity_hom hV hVb hh hη hηs hK hKW hζL hζ0 hζ1 hζK ũ g ub
    (F := F) (f := f) (fun i => (hFc i).locallyIntegrableOn V) (hfc.locallyIntegrableOn V) hweak s
    hhom hfφ φ
  have e0 : v.toH1Function.grad = fun x => w.grad x - ub.grad x := by
    rw [hvH, H1Function.sub_grad]
  have hsum : ∀ (c : Vec d → ℝ) (A B : Vec d → Vec d),
      (∀ i, IntegrableOn (fun x => c x * (A x i * B x i)) V) →
      IntegrableOn (fun x => c x * vecDot (A x) (B x)) V := by
    intro c A B hi
    refine (l2a_integrableOn_sum hi).congr_fun (fun x _ => ?_) hV.measurableSet
    simp only [vecDot, Finset.mul_sum]
  have iK3 : IntegrableOn (fun x => ζ x *
      vecDot (a16_mollify d h η (fun y => F y - s • ũ.grad y) x) (φ.toH1Function.grad x)) V := by
    refine hsum _ _ _ fun i => (hJ3 φ i).congr_fun (fun x _ => ?_) hV.measurableSet
    ring
  have iK4 : IntegrableOn (fun x => (1 - ζ x) *
      vecDot (g.grad x) (φ.toH1Function.grad x)) V := hsum _ _ _ (hJ4 φ)
  have iK5 : IntegrableOn (fun x => (l2a_moll d h η ũ.toFun x - g.toFun x) *
      vecDot (lipGradient ζ x) (φ.toH1Function.grad x)) V := by
    refine (l2a_integrableOn_sum (fun i => hJ5 φ i)).congr_fun (fun x _ => ?_) hV.measurableSet
    simp only [vecDot, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have R2 : ∫ x in V, vecDot (l2d_Fv V r h η s ũ g F x) (φ.toH1Function.grad x) =
      (-s⁻¹) * (∫ x in V, ζ x * vecDot (a16_mollify d h η (fun y => F y - s • ũ.grad y) x)
          (φ.toH1Function.grad x)) +
        (∫ x in V, (1 - ζ x) * vecDot (g.grad x) (φ.toH1Function.grad x)) +
        ∫ x in V, (l2a_moll d h η ũ.toFun x - g.toFun x) *
          vecDot (lipGradient ζ x) (φ.toH1Function.grad x) := by
    have e : ∀ x, vecDot (l2d_Fv V r h η s ũ g F x) (φ.toH1Function.grad x) =
        (-s⁻¹) * (ζ x * vecDot (a16_mollify d h η (fun y => F y - s • ũ.grad y) x)
          (φ.toH1Function.grad x)) +
        (1 - ζ x) * vecDot (g.grad x) (φ.toH1Function.grad x) +
        (l2a_moll d h η ũ.toFun x - g.toFun x) *
          vecDot (lipGradient ζ x) (φ.toH1Function.grad x) := by
      intro x
      simp only [l2d_Fv, l2a_vecDot_three]
      ring
    simp only [e]
    have hA := iK3.const_mul (-s⁻¹)
    have h12 : ∫ x in V, (-s⁻¹ * (ζ x * vecDot (a16_mollify d h η (fun y => F y - s • ũ.grad y) x)
          (φ.toH1Function.grad x)) + (1 - ζ x) * vecDot (g.grad x) (φ.toH1Function.grad x)) =
        (∫ x in V, -s⁻¹ * (ζ x * vecDot (a16_mollify d h η (fun y => F y - s • ũ.grad y) x)
          (φ.toH1Function.grad x))) +
        ∫ x in V, (1 - ζ x) * vecDot (g.grad x) (φ.toH1Function.grad x) := integral_add hA iK4
    have h123 := integral_add (hA.add iK4) iK5
    simp only [Pi.add_apply] at h123
    rw [h123, h12, integral_const_mul]
  have R1 : ∫ x in V, (l2d_h1 V r h η s f x + l2d_h2 V r h η s F x) * φ.toH1Function.toFun x =
      s⁻¹ * (∫ x in V, (ζ x * l2a_moll d h η f x - f x) * φ.toH1Function.toFun x) +
        (-s⁻¹) * ∫ x in V, φ.toH1Function.toFun x *
          vecDot (lipGradient ζ x) (a16_mollify d h η F x) := by
    have e1 : ∀ x, (l2d_h1 V r h η s f x + l2d_h2 V r h η s F x) * φ.toH1Function.toFun x =
        l2d_h1 V r h η s f x * φ.toH1Function.toFun x +
          l2d_h2 V r h η s F x * φ.toH1Function.toFun x := fun x => add_mul _ _ _
    simp only [e1]
    rw [integral_add (hI1 φ) (hI2 φ), ← integral_const_mul, ← integral_const_mul]
    congr 1
    · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [l2d_h1, hζdef]
      ring
    · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [l2d_h2, hζdef]
      ring
  show ∫ x in V, vecDot (matVecMul (1 : Mat d) (v.toH1Function.grad x)) (φ.toH1Function.grad x) =
    (∫ x in V, (l2d_h1 V r h η s f x + l2d_h2 V r h η s F x) * φ.toH1Function.toFun x) +
      ∫ x in V, vecDot (l2d_Fv V r h η s ũ g F x) (φ.toH1Function.grad x)
  rw [R1, R2]
  simp only [l2d_matVecMul_one, e0]
  have hid' : s * (∫ x in V, vecDot (w.grad x - ub.grad x) (φ.toH1Function.grad x)) = _ := hid
  set L := ∫ x in V, vecDot (w.grad x - ub.grad x) (φ.toH1Function.grad x) with hL
  have hL' : L = s⁻¹ * (s * L) := by field_simp
  rw [hL', hid']
  field_simp
  ring


/-- Satisfiability: zero data on the unit ball (margin `1`, mollification scale `1/4`, `s = 1`). -/
example : True := by
  obtain ⟨η, hη, hηs⟩ := l2a_exists_smooth_profile 2
  have _ := l2d_equation (d := 2) (V := Metric.ball (0 : Vec 2) 1) Metric.isOpen_ball
    Metric.isBounded_ball (r := 1) (h := 1 / 4) one_pos (by norm_num) (by norm_num) hη hηs
    (0 : H1Function (Set.univ : Set (Vec 2))) (0 : H1Function (Metric.ball (0 : Vec 2) 1))
    (0 : H1Function (Metric.ball (0 : Vec 2) 1))
    ⟨0, by rw [sub_self]; rfl⟩ (F := fun _ => 0) (f := fun _ => 0) (fun i => locallyIntegrable_const _)
    (locallyIntegrable_const _) (fun φ => by simp [vecDot]) (s := 1) one_ne_zero
    (fun φ => by simp [vecDot]) (fun φ => by simp)
  trivial

end Equation

end SuperdiffusionCLT.Section7
