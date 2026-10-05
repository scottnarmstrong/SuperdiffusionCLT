/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.L2AssemblyG
public import SuperdiffusionCLT.Section7.Prereq.LinftyReductionC
public import SuperdiffusionCLT.Section7.Root.InteriorApproxE
public import SuperdiffusionCLT.Section7.Root.RescalingB

/-!
# The weak norms of the solution against the comparison function: scalar estimates

The scalar pieces of the weak-norm estimates of the paper: the dual norm `W^{-1,2}`
of a mollification error with the cutoff, of a function supported in the boundary layer, and of a
bounded function.
-/

@[expose] public section

open MeasureTheory Set Filter Homogenization
open scoped ENNReal NNReal Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The dual norm only sees the values of the function on the set. -/
theorem linf_weak_wm_congr {W : Set (Vec d)} (hW : MeasurableSet W) (p : ℝ≥0∞)
    {f g : Vec d → ℝ} (h : ∀ x ∈ W, f x = g x) : wMinusOneBar W p f = wMinusOneBar W p g := by
  unfold wMinusOneBar
  refine iSup_congr fun ψ => iSup_congr fun _ => ?_
  rw [setIntegral_congr_fun hW (fun x hx => by rw [h x hx])]

/-- **The layer estimate**: a function in `L²(W)` supported in the boundary layer has dual norm at
most `CP r` times its normalized `L²` norm. -/
theorem linf_weak_layer [NeZero d] (M₁ : ℝ) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ {r₀ : ℝ} {W : Set (Vec d)} {M₂ D : ℝ},
      IsUniformC11Domain W r₀ M₁ M₂ D → ∀ {r : ℝ}, 0 < r →
      3 * r ≤ r₀ / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) → volume W ≠ 0 →
      ∀ {X : Vec d → ℝ}, MemLp X 2 (volume.restrict W) →
      (∀ x ∈ W, X x ≠ 0 → x ∈ l2b_layerB W r) →
      wMinusOneBar W 2 X ≤ ENNReal.ofReal (CP * r) * lpBar W 2 X := by
  obtain ⟨CP, hCP, H⟩ := l2d_hPoinc (d := d) M₁
  refine ⟨CP, hCP, ?_⟩
  intro r₀ W M₂ D hU r hr h3r h0 X hX hXA
  have hWm : MeasurableSet W := hU.1.measurableSet
  have ht : volume W ≠ ⊤ := (l2b_bounded_of_uniform hU).measure_lt_top.ne
  have hLB : l2b_layerB W r ⊆ boundaryLayer W (3 * r) := fun x hx =>
    l2b_layer_of_infDist hU.2.2.1 hx.1 (by linarith only [hx.2, hr])
  have hAm := l2b_layerB_measurable hWm r
  rw [li1_lpBar_two_eq W X hX.aestronglyMeasurable h0 ht]
  unfold wMinusOneBar
  refine iSup₂_le fun ψ hψ => ?_
  rw [li1_conj_two, li1_lpBar_two_eq W _ (li1_grad_aesm ψ) h0 ht] at hψ
  set k : ℝ≥0∞ := (volume W)⁻¹ ^ (1 / 2 : ℝ) with hk
  have hkk := li1_sqrt_inv_mul_self (volume W) h0 ht
  set A := l2b_layerB W r with hAdef
  have hψA : MemLp (A.indicator ψ.toH1Function.toFun) 2 (volume.restrict W) :=
    ψ.toH1Function.memL2.indicator hAm
  have hpair := li1_pairing_le W X _ hX hψA
  have hint : ∫ x in W, X x * ψ.toH1Function.toFun x =
      ∫ x in W, X x * A.indicator ψ.toH1Function.toFun x := by
    refine setIntegral_congr_fun hWm fun x hx => ?_
    by_cases hX0 : X x = 0
    · simp [hX0]
    · rw [Set.indicator_of_mem (hXA x hx hX0)]
  have hnorm : eLpNorm (A.indicator ψ.toH1Function.toFun) 2 (volume.restrict W) ≤
      ENNReal.ofReal (CP * r) * eLpNorm ψ.toH1Function.grad 2 (volume.restrict W) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hAm, Measure.restrict_restrict hAm]
    have h1 : eLpNorm ψ.toH1Function.toFun 2 (volume.restrict (A ∩ W)) ≤
        eLpNorm ψ.toH1Function.toFun 2 (volume.restrict A) :=
      eLpNorm_mono_measure _ (Measure.restrict_mono inter_subset_left le_rfl)
    have h2 := H hU (q := 2) (by norm_num) hr h3r (A := A) hLB ψ
    have e : eLpNorm (fun x => ‖ψ.toH1Function.grad x‖) 2 (volume.restrict W) =
        eLpNorm ψ.toH1Function.grad 2 (volume.restrict W) := eLpNorm_norm _ (li1_grad_aesm ψ)
    rw [ENNReal.ofReal_ofNat, e] at h2
    exact h1.trans h2
  rw [hint, abs_mul, ENNReal.ofReal_mul (abs_nonneg _),
    abs_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg), ← hkk]
  calc k * k * ENNReal.ofReal |∫ x in W, X x * A.indicator ψ.toH1Function.toFun x|
      ≤ k * k * (eLpNorm X 2 (volume.restrict W) *
          (ENNReal.ofReal (CP * r) * eLpNorm ψ.toH1Function.grad 2 (volume.restrict W))) := by
        gcongr
        exact hpair.trans (by gcongr)
    _ = (k * eLpNorm ψ.toH1Function.grad 2 (volume.restrict W)) * k *
          (ENNReal.ofReal (CP * r) * eLpNorm X 2 (volume.restrict W)) := by ring
    _ ≤ 1 * k * (ENNReal.ofReal (CP * r) * eLpNorm X 2 (volume.restrict W)) := by gcongr
    _ = ENNReal.ofReal (CP * r) * (k * eLpNorm X 2 (volume.restrict W)) := by ring


/-- A function bounded by `b` on `W` has normalized `L²` norm at most `b`. -/
theorem linf_weak_lpBar_le {W : Set (Vec d)} (hW : MeasurableSet W) (ht : volume W ≠ ⊤)
    {X : Vec d → ℝ} (hX : AEStronglyMeasurable X (volume.restrict W)) {b : ℝ}
    (hb : ∀ x ∈ W, |X x| ≤ b) : lpBar W 2 X ≤ ENNReal.ofReal b :=
  ia_lpBar_le_of_bound ht hX (fun x hx => by simpa [Real.norm_eq_abs] using hb x hx) hW 2

/-- The layer estimate for a function bounded by `b`. -/
theorem linf_weak_layer_bound [NeZero d] (M₁ : ℝ) :
    ∃ CP : ℝ, 0 ≤ CP ∧ ∀ {r₀ : ℝ} {W : Set (Vec d)} {M₂ D : ℝ},
      IsUniformC11Domain W r₀ M₁ M₂ D → ∀ {r : ℝ}, 0 < r →
      3 * r ≤ r₀ / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) → volume W ≠ 0 →
      ∀ {X : Vec d → ℝ}, MemLp X 2 (volume.restrict W) →
      (∀ x ∈ W, X x ≠ 0 → x ∈ l2b_layerB W r) → ∀ {b : ℝ}, 0 ≤ b → (∀ x ∈ W, |X x| ≤ b) →
      wMinusOneBar W 2 X ≤ ENNReal.ofReal (CP * r * b) := by
  obtain ⟨CP, hCP, H⟩ := linf_weak_layer (d := d) M₁
  refine ⟨CP, hCP, ?_⟩
  intro r₀ W M₂ D hU r hr h3r h0 X hX hXA b hb hXb
  have hWm : MeasurableSet W := hU.1.measurableSet
  have ht : volume W ≠ ⊤ := (l2b_bounded_of_uniform hU).measure_lt_top.ne
  refine (H hU hr h3r h0 hX hXA).trans ?_
  rw [ENNReal.ofReal_mul (mul_nonneg hCP hr.le)]
  exact mul_le_mul' le_rfl (linf_weak_lpBar_le hWm ht hX.aestronglyMeasurable hXb)

/-- The dual norm of a bounded function on a subset of a cube is at most `c L` times the bound. -/
theorem linf_weak_sup [NeZero d] :
    ∃ c : ℝ, 0 < c ∧ ∀ {U : Set (Vec d)}, IsOpen U → ∀ (z : Vec d) {L : ℝ}, 0 < L →
      U ⊆ axisCube z L → volume U ≠ 0 → ∀ {X : Vec d → ℝ}, MemLp X 2 (volume.restrict U) →
      ∀ {b : ℝ}, (∀ x ∈ U, |X x| ≤ b) → wMinusOneBar U 2 X ≤ ENNReal.ofReal (c * L * b) := by
  obtain ⟨c, hc, H⟩ := li1_wMinusOneBar_two_le_lpBar (d := d)
  refine ⟨c, hc, ?_⟩
  intro U hU z L hL hsub h0 X hX b hb
  have ht : volume U ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
    rw [axisCube, Real.volume_pi_Ioo]
    exact ENNReal.prod_lt_top (fun i _ => ENNReal.ofReal_lt_top) |>.ne
  have hb0 : 0 ≤ b := by
    by_contra hneg
    obtain ⟨x, hx⟩ : U.Nonempty := nonempty_of_measure_ne_zero h0
    linarith only [hb x hx, abs_nonneg (X x), not_le.1 hneg]
  refine (H hU z hL hsub h0 X hX).trans ?_
  rw [ENNReal.ofReal_mul (mul_nonneg hc.le hL.le)]
  exact mul_le_mul' le_rfl (linf_weak_lpBar_le hU.measurableSet ht hX.aestronglyMeasurable hb)

/-- **The mollification error with the cutoff** at `p = 2` against a function of normalized `L²`
norm at most `b`. -/
theorem linf_weak_E1 [NeZero d] (M₁ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {r₀ : ℝ} {W : Set (Vec d)} {M₂ D : ℝ},
      IsUniformC11Domain W r₀ M₁ M₂ D → ∀ (n : ℕ) {r : ℝ}, 0 < r →
      3 * r ≤ r₀ / (3 * ((d : ℝ) + (1 + d) * max M₁ 0) + 4) →
      2 * (3 : ℝ) ^ n < r → volume W ≠ 0 → ∀ {η : Vec d → ℝ}, Continuous η →
      ∀ {Bη : ℝ}, (∀ w, |η w| ≤ Bη) → (∀ w, 0 ≤ η w) → ∫ w, η w = 1 →
      (∀ w, (∃ i, 1 < |w i|) → η w = 0) → ∀ {f : Vec d → ℝ}, MemLp f 2 (volume.restrict W) →
      ∀ {b : ℝ}, 0 ≤ b → lpBar W 2 f ≤ ENNReal.ofReal b →
      wMinusOneBar W 2 (fun x => l2a_cutoff W r x * l2a_moll d ((3 : ℝ) ^ n) η f x - f x) ≤
        ENNReal.ofReal ((d * (3 : ℝ) ^ n + K * r) * b) := by
  obtain ⟨K, hK, H⟩ := l2d_E1_cutoff (d := d) M₁
  refine ⟨K, hK, ?_⟩
  intro r₀ W M₂ D hU n r hr h3r hn h0 η hηc Bη hηA hη0 hη1 hηs f hf b hb hfb
  have hWb := l2b_bounded_of_uniform hU
  have hWT : volume W ≠ ⊤ := hWb.measure_lt_top.ne
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have := H hU n hr h3r hn h0 hWT hηc hηA hη0 hη1 hηs Real.HolderConjugate.two_two
    (l2a_integrableOn_of_memL2 hWb hf)
    (fun ψ => l2a_integrableOn_mul_memL2 hf ψ.toH1Function.memL2)
  rw [ENNReal.ofReal_ofNat] at this
  refine this.trans ?_
  rw [ENNReal.ofReal_mul (by positivity)]
  exact mul_le_mul' le_rfl hfb


/-- The dual norm is even. -/
theorem linf_weak_wm_neg (V : Set (Vec d)) (p : ℝ≥0∞) (h : Vec d → ℝ) :
    wMinusOneBar V p (fun x => -h x) = wMinusOneBar V p h := by
  have e : (fun x => -h x) = fun x => (-1 : ℝ) * h x := by
    funext x
    ring
  rw [e, s12_wMinusOneBar_const_mul]
  simp

/-- Subadditivity of the dual norm for three functions in `L²`. -/
theorem linf_weak_wm_add3 (V : Set (Vec d)) {X Y Z : Vec d → ℝ}
    (hX : MemLp X 2 (volume.restrict V)) (hY : MemLp Y 2 (volume.restrict V))
    (hZ : MemLp Z 2 (volume.restrict V)) :
    wMinusOneBar V 2 (fun x => X x + Y x + Z x) ≤
      wMinusOneBar V 2 X + wMinusOneBar V 2 Y + wMinusOneBar V 2 Z := by
  refine (li1_wMinusOneBar_add_le V (fun x => X x + Y x) Z (hX.add hY) hZ).trans ?_
  exact add_le_add (li1_wMinusOneBar_add_le V X Y hX hY) le_rfl

/-- Subadditivity of the dual norm for five functions in `L²`. -/
theorem linf_weak_wm_add5 (V : Set (Vec d)) {X Y Z U T : Vec d → ℝ}
    (hX : MemLp X 2 (volume.restrict V)) (hY : MemLp Y 2 (volume.restrict V))
    (hZ : MemLp Z 2 (volume.restrict V)) (hU : MemLp U 2 (volume.restrict V))
    (hT : MemLp T 2 (volume.restrict V)) :
    wMinusOneBar V 2 (fun x => X x + Y x + Z x + U x + T x) ≤
      wMinusOneBar V 2 X + wMinusOneBar V 2 Y + wMinusOneBar V 2 Z + wMinusOneBar V 2 U +
        wMinusOneBar V 2 T := by
  refine (li1_wMinusOneBar_add_le V (fun x => X x + Y x + Z x + U x) T
    (((hX.add hY).add hZ).add hU) hT).trans ?_
  refine add_le_add ?_ le_rfl
  refine (li1_wMinusOneBar_add_le V (fun x => X x + Y x + Z x) U ((hX.add hY).add hZ) hU).trans ?_
  refine add_le_add ?_ le_rfl
  exact linf_weak_wm_add3 V hX hY hZ

/-- Monotonicity of the normalized norm under a pointwise bound on the set. -/
theorem linf_weak_lpBar_mono {V : Set (Vec d)} (hV : MeasurableSet V) {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] {p : ℝ≥0∞} {f : Vec d → E} {g : Vec d → F}
    (hf : AEStronglyMeasurable f (volume.restrict V)) (h : ∀ x ∈ V, ‖f x‖ ≤ ‖g x‖) :
    lpBar V p f ≤ lpBar V p g := by
  unfold lpBar
  refine eLpNorm_mono_ae (hf.smul_measure _) ?_
  exact ((ae_restrict_iff' hV).2 (Filter.Eventually.of_forall h)).filter_mono
    (Measure.ae_smul_measure_le _)

/-- A function in `L²(W)` cut off to `W` is locally integrable on the whole space. -/
theorem linf_weak_locInt {W : Set (Vec d)} (hW : MeasurableSet W) {g : Vec d → ℝ}
    (hg : MemLp g 2 (volume.restrict W)) : LocallyIntegrable (W.indicator g) volume :=
  ((memLp_indicator_iff_restrict hW).2 hg).locallyIntegrable (by norm_num)

end SuperdiffusionCLT.Section7
