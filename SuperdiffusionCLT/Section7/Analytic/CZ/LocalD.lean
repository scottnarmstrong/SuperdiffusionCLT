/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.CZ.LocalC
public import SuperdiffusionCLT.Section7.Analytic.Change.FlattenB

/-!
# Local `W^{1,p}` estimates at a boundary point: the chart-flattened problem

For a chart `(e, ψ)` of `U` at a boundary point `x₀` (`HasC11ChartAt`), the chart map
`Ψ' y = Ψ y + τ`, with `Ψ = flattenMap e ψ x₀ u` the exact flattening of `P9`, sends `U` (near `x₀`)
to a half space bounded by the plane through `τ` orthogonal to `u`.  `p12_chartFun` is the
corresponding `H¹₀` function `φ ∘ Ψ'⁻¹`, and `p12_chartFun_weak` is the transported weak equation
(`IsWeakSolutionOn.flatten` followed by `IsWeakSolutionOn.translate`).
-/

@[expose] public section

open Homogenization MeasureTheory Matrix
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- The domain of the chart-flattened problem: the image of `U` under the chart map
`y ↦ Ψ y + τ`. -/
noncomputable def p12_chartDom {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (u x₀ τ : Vec d) (U : Set (Vec d)) : Set (Vec d) :=
  translateSet (τ - flattenShift e ψ x₀ u) (flattenEquiv he hψ u x₀ '' (shear e (-ψ) ⁻¹' U))

/-- The chart-flattened `H¹₀` function `φ ∘ (chart map)⁻¹`. -/
noncomputable def p12_chartFun {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {M₁ : ℝ} (hb1 : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁) (u x₀ τ : Vec d)
    {U : Set (Vec d)} (φ : H10Function U) : H10Function (p12_chartDom he hψ u x₀ τ U) :=
  ((H10Function.compShear (ψ := -ψ) he hψ.neg (exists_bound_neg (flatten_hb hb1)) φ).compLinearEquiv
    (flattenEquiv he hψ u x₀)).translate (τ - flattenShift e ψ x₀ u)

theorem p12_chartFun_toFun {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {M₁ : ℝ} (hb1 : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁) (u x₀ τ : Vec d)
    {U : Set (Vec d)} (φ : H10Function U) (x : Vec d) :
    (p12_chartFun he hψ hb1 u x₀ τ φ).toH1Function.toFun x =
      φ.toH1Function.toFun (flattenInv e ψ x₀ u (x - τ)) := by
  have h := flattenInv_sub_shift he hψ u x₀ (x - (τ - flattenShift e ψ x₀ u))
  have e1 : x - (τ - flattenShift e ψ x₀ u) - flattenShift e ψ x₀ u = x - τ := by abel
  rw [e1] at h
  rw [h]
  rfl

theorem p12_chartFun_weak {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {M₁ : ℝ} (hb1 : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁) (u x₀ τ : Vec d)
    {U : Set (Vec d)} (φ : H10Function U) {f : Vec d → ℝ} {g : Vec d → Vec d}
    (hw : IsWeakSolutionOn (fun _ => (1 : Mat d)) U φ.toH1Function f g) :
    IsWeakSolutionOn (fun x => flattenCoeff e ψ x₀ u (fun _ => (1 : Mat d)) (x - τ))
      (p12_chartDom he hψ u x₀ τ U) (p12_chartFun he hψ hb1 u x₀ τ φ).toH1Function
      (fun x => f (flattenInv e ψ x₀ u (x - τ)))
      (fun x => matVecMul (flattenLin e (projGradVec e ψ x₀) u *
          shearJac e ψ (flattenInv e ψ x₀ u (x - τ))) (g (flattenInv e ψ x₀ u (x - τ)))) := by
  have h := (IsWeakSolutionOn.flatten he hψ hb1 u x₀ hw).translate (τ - flattenShift e ψ x₀ u)
  have e1 : ∀ x : Vec d, x - (τ - flattenShift e ψ x₀ u) - flattenShift e ψ x₀ u = x - τ := by
    intro x; abel
  refine IsWeakSolutionOn.congr (fun x => ?_) (fun x => ?_) (fun x => ?_) h
  · simp only [e1]
  · simp only [e1]
  · simp only [e1]

theorem p12_mem_chartDom {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (u x₀ τ : Vec d) (U : Set (Vec d)) (x : Vec d) :
    x ∈ p12_chartDom he hψ u x₀ τ U ↔ flattenInv e ψ x₀ u (x - τ) ∈ U := by
  unfold p12_chartDom
  rw [mem_translateSet_iff_sub_mem]
  have h := flattenInv_sub_shift he hψ u x₀ (x - (τ - flattenShift e ψ x₀ u))
  have e1 : x - (τ - flattenShift e ψ x₀ u) - flattenShift e ψ x₀ u = x - τ := by abel
  rw [e1] at h
  rw [h]
  have himg : ((flattenEquiv he hψ u x₀) '' (shear e (-ψ) ⁻¹' U)) =
      (flattenEquiv he hψ u x₀).symm ⁻¹' (shear e (-ψ) ⁻¹' U) :=
    (flattenEquiv he hψ u x₀).toEquiv.image_eq_preimage_symm _
  rw [himg]
  rfl

/-- The chart map `y ↦ Ψ y + τ` as a homeomorphism. -/
noncomputable def p12_chartHomeo {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (u x₀ τ : Vec d) : Vec d ≃ₜ Vec d where
  toFun y := flattenMap e ψ x₀ u y + τ
  invFun x := flattenInv e ψ x₀ u (x - τ)
  left_inv y := by simp [flattenInv_flattenMap he hψ]
  right_inv x := by simp [flattenMap_flattenInv he hψ]
  continuous_toFun := by
    have h1 : Continuous (shear e ψ) := (contDiff_shear hψ).continuous
    unfold flattenMap
    unfold matVecMul
    fun_prop
  continuous_invFun := by
    have h1 : Continuous (shear e (-ψ)) := (contDiff_shear hψ.neg).continuous
    unfold flattenInv
    refine h1.comp ?_
    unfold matVecMul
    fun_prop

theorem p12_chartMap_measurePreserving {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (u x₀ τ : Vec d) :
    MeasurePreserving (fun y => flattenMap e ψ x₀ u y + τ) volume volume :=
  (measurePreserving_add_right volume τ).comp (measurePreserving_flattenMap he hψ u x₀)

/-- Change of variables for normalized `L^q` norms under the chart map. -/
theorem p12_eLpNorm_chart {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (u x₀ τ : Vec d) {E : Type*} [NormedAddCommGroup E]
    (F : Vec d → E) (q c : ℝ≥0∞) (S : Set (Vec d)) :
    eLpNorm (fun x => F (flattenInv e ψ x₀ u (x - τ))) q
        (c • volume.restrict ((fun y => flattenMap e ψ x₀ u y + τ) '' S)) =
      eLpNorm F q (c • volume.restrict S) := by
  have hemb : MeasurableEmbedding (fun y => flattenMap e ψ x₀ u y + τ) :=
    (p12_chartHomeo he hψ u x₀ τ).measurableEmbedding
  have hmp := p12_chartMap_measurePreserving he hψ u x₀ τ
  have h1 : c • volume.restrict ((fun y => flattenMap e ψ x₀ u y + τ) '' S) =
      Measure.map (fun y => flattenMap e ψ x₀ u y + τ) (c • volume.restrict S) := by
    rw [Measure.map_smul, (hmp.restrict_image_emb hemb S).map_eq]
    exact hemb.measurable.aemeasurable
  rw [h1, hemb.eLpNorm_map_measure]
  congr 1
  funext y
  simp [flattenInv_flattenMap he hψ]

theorem p12a_integral_ext {U V : Set (Vec d)} (hV : IsOpen V) (hVU : V ⊆ U) (hU : IsOpen U)
    (F : Vec d → ℝ) (ψ : H10Function V) :
    ∫ x in U, F x * (ψ.extendByZeroToOpenSuperset hV.measurableSet hU hVU).toH1Function.toFun x =
      ∫ x in V, F x * ψ.toH1Function.toFun x := by
  have : (fun x => F x * (ψ.extendByZeroToOpenSuperset hV.measurableSet hU hVU).toH1Function.toFun x)
      = V.indicator (fun x => F x * ψ.toH1Function.toFun x) := by
    funext x
    rw [H10Function.extendByZeroToOpenSuperset_toFun]
    by_cases hx : x ∈ V
    · simp [H10Function.zeroExtension_apply_of_mem _ hx, Set.indicator_of_mem hx]
    · simp [H10Function.zeroExtension_apply_of_not_mem _ hx, Set.indicator_of_notMem hx]
  rw [this, integral_indicator hV.measurableSet, Measure.restrict_restrict hV.measurableSet,
    Set.inter_eq_left.mpr hVU]

theorem p12a_integral_extGrad {U V : Set (Vec d)} (hV : IsOpen V) (hVU : V ⊆ U) (hU : IsOpen U)
    (F : Vec d → Vec d) (ψ : H10Function V) :
    ∫ x in U, vecDot (F x) ((ψ.extendByZeroToOpenSuperset hV.measurableSet hU hVU).toH1Function.grad x) =
      ∫ x in V, vecDot (F x) (ψ.toH1Function.grad x) := by
  have : (fun x => vecDot (F x) ((ψ.extendByZeroToOpenSuperset hV.measurableSet hU hVU).toH1Function.grad x))
      = V.indicator (fun x => vecDot (F x) (ψ.toH1Function.grad x)) := by
    funext x
    rw [H10Function.extendByZeroToOpenSuperset_grad]
    by_cases hx : x ∈ V
    · simp [H10Function.zeroExtensionGrad_apply_of_mem _ hx, Set.indicator_of_mem hx]
    · simp [H10Function.zeroExtensionGrad_apply_of_not_mem _ hx, Set.indicator_of_notMem hx,
        vecDot]
  rw [this, integral_indicator hV.measurableSet, Measure.restrict_restrict hV.measurableSet,
    Set.inter_eq_left.mpr hVU]

/-- (A) The weak equation restricts to an open subset (test functions are zero-extended). -/
theorem p12_restrict_weak {a : CoeffField d} {U V : Set (Vec d)} (hU : IsOpen U) (hV : IsOpen V)
    (hVU : V ⊆ U) {u : H1Function U} {f : Vec d → ℝ} {g : Vec d → Vec d}
    (h : IsWeakSolutionOn a U u f g) : IsWeakSolutionOn a V (u.restrict hV hVU) f g := by
  intro ψ
  have h1 := h (ψ.extendByZeroToOpenSuperset hV.measurableSet hU hVU)
  rw [p12a_integral_extGrad hV hVU hU (fun x => matVecMul (a x) (u.grad x)) ψ,
    p12a_integral_ext hV hVU hU f ψ, p12a_integral_extGrad hV hVU hU g ψ] at h1
  exact h1

/-- (B) Localized zero trace on a subdomain: an `H¹₀(D)` function, cut off inside a window `T` with
`T ∩ D ⊆ Q ⊆ D`, is `H¹₀(Q)`. -/
theorem p12_localized_zero_trace_restrict {D Q T : Set (Vec d)} (hQ : IsOpen Q) (hQD : Q ⊆ D)
    (hT : T ∩ D ⊆ Q) (w : H10Function D) :
    LocalizedZeroTraceFunctionOn Q T (w.toH1Function.restrict hQ hQD).toFun := by
  intro η hη hηc hηT
  let W := w.mulContDiffHasCompactSupport hη hηc
  have hsub : ∀ n, tsupport (W.approx n) ⊆ Q := fun n x hx =>
    hT ⟨hηT (tsupport_mul_subset_left hx), w.approx_support_subset n
      (tsupport_mul_subset_right hx)⟩
  have hle : (volume.restrict Q : Measure (Vec d)) ≤ volume.restrict D := Measure.restrict_mono hQD le_rfl
  refine ⟨{ toH1Function := W.toH1Function.restrict hQ hQD
            approx := W.approx
            approx_smooth := W.approx_smooth
            approx_hasCompactSupport := W.approx_hasCompactSupport
            approx_support_subset := hsub
            tendsto_approx := ?_
            tendsto_approx_grad := fun i => ?_ }, ?_⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds W.tendsto_approx
      (fun _ => zero_le) (fun n => eLpNorm_mono_measure _ hle)
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (W.tendsto_approx_grad i)
      (fun _ => zero_le) (fun n => eLpNorm_mono_measure _ hle)
  · rfl

theorem p12b_rank1_norm_le {e g : Vec d} (he : vecNormSq e = 1) {G : ℝ} (hG : ‖g‖ ≤ G)
    (w : Vec d) : ‖w + vecDot g w • e‖ ≤ (1 + d * G) * ‖w‖ := by
  have h0 : 0 ≤ G := (norm_nonneg _).trans hG
  have h1 : |vecDot g w| ≤ d * (G * ‖w‖) :=
    (p12_abs_vecDot_le g w).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hG (norm_nonneg _)) (Nat.cast_nonneg d))
  have h2 : ‖vecDot g w • e‖ ≤ d * (G * ‖w‖) := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |vecDot g w| * ‖e‖ ≤ (d * (G * ‖w‖)) * 1 :=
          mul_le_mul h1 (norm_le_one_of_vecNormSq he) (norm_nonneg _) (by positivity)
      _ = _ := mul_one _
  calc ‖w + vecDot g w • e‖ ≤ ‖w‖ + ‖vecDot g w • e‖ := norm_add_le _ _
    _ ≤ ‖w‖ + d * (G * ‖w‖) := by linarith only [h2]
    _ = (1 + d * G) * ‖w‖ := by ring

theorem p12b_tilt_norm_le {e g : Vec d} (he : vecNormSq e = 1) {G : ℝ} (hG : ‖g‖ ≤ G)
    (w : Vec d) : ‖flattenTilt e g *ᵥ w‖ ≤ (1 + d * G) * ‖w‖ := by
  have := matVecMul_rankOne e g w
  unfold matVecMul at this
  have h : flattenTilt e g *ᵥ w = w + vecDot g w • e := this
  rw [h]
  exact p12b_rank1_norm_le he hG w

theorem p12b_jac_norm_le {e g : Vec d} (he : vecNormSq e = 1) {G : ℝ} (hG : ‖g‖ ≤ G)
    (w : Vec d) : ‖(1 - Matrix.vecMulVec e g) *ᵥ w‖ ≤ (1 + d * G) * ‖w‖ := by
  have h : (1 - Matrix.vecMulVec e g) *ᵥ w = w + vecDot (-g) w • e := by
    have := matVecMul_rankOne e (-g) w
    have e1 : (1 - Matrix.vecMulVec e g) = 1 + Matrix.vecMulVec e (-g) := by
      ext i j; simp [Matrix.vecMulVec_apply, sub_eq_add_neg]
    rw [e1]; exact this
  rw [h]
  exact p12b_rank1_norm_le he (by simpa using hG) w

theorem p12b_lin_norm_le {e g : Vec d} (he : vecNormSq e = 1) (u : Vec d) {G : ℝ}
    (hG : ‖g‖ ≤ G) (w : Vec d) : ‖flattenLin e g u *ᵥ w‖ ≤ d * ((1 + d * G) * ‖w‖) := by
  have hOO := flattenHouseholder_mul_transpose (flattenNormal e g) u
  have hA := flatten_abs_entry_le_one hOO
  have : flattenLin e g u *ᵥ w =
      flattenHouseholder (flattenNormal e g) u *ᵥ (flattenTilt e g *ᵥ w) := by
    unfold flattenLin; rw [Matrix.mulVec_mulVec]
  rw [this]
  exact (flatten_norm_mulVec_le hA _).trans
    (mul_le_mul_of_nonneg_left (p12b_tilt_norm_le he hG w) (Nat.cast_nonneg d))

theorem p12_chart_lip (d : ℕ) (M₁ : ℝ) : ∃ K : ℝ, 1 ≤ K ∧
    ∀ {e : Vec d} (_he : vecNormSq e = 1) {ψ : Vec d → ℝ} (_hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
      (_hb1 : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁) {u : Vec d} (_hu : vecNormSq u = 1) (x₀ y z : Vec d),
      ‖flattenMap e ψ x₀ u y - flattenMap e ψ x₀ u z‖ ≤ K * ‖y - z‖ ∧
      ‖flattenInv e ψ x₀ u y - flattenInv e ψ x₀ u z‖ ≤ K * ‖y - z‖ := by
  set m : ℝ := max M₁ 0 with hm
  have hm0 : 0 ≤ m := le_max_right _ _
  refine ⟨max 1 (d * (1 + d * (2 * m)) * (1 + (1 + d) * m)), le_max_left _ _, ?_⟩
  intro e he ψ hψ hb1 u _ x₀ y z
  have hM : ‖projGradVec e ψ x₀‖ ≤ 2 * m :=
    (flatten_norm_projGradVec_le he hψ hb1 x₀).trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))
  have hg := vecDot_self_projGradVec he hψ x₀
  have hLip : ∀ ψ' : Vec d → ℝ, (∀ a b, |ψ' a - ψ' b| ≤ m * ‖a - b‖) → ∀ a b : Vec d,
      ‖shear e ψ' a - shear e ψ' b‖ ≤ (1 + (1 + d) * m) * ‖a - b‖ := fun ψ' h a b =>
    norm_shear_sub_le he hm0 h a b
  have hψlip : ∀ a b, |ψ a - ψ b| ≤ m * ‖a - b‖ := fun a b =>
    (abs_sub_le_of_fderiv_bound hψ hb1 a b).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hψlip' : ∀ a b, |(-ψ) a - (-ψ) b| ≤ m * ‖a - b‖ := fun a b => by
    have := hψlip a b
    rw [Pi.neg_apply, Pi.neg_apply, show -ψ a - -ψ b = -(ψ a - ψ b) by ring, abs_neg]
    exact this
  have hK0 : 0 ≤ d * (1 + d * (2 * m)) * (1 + (1 + d) * m) := by positivity
  have hKle : d * (1 + d * (2 * m)) * (1 + (1 + d) * m) ≤
      max 1 (d * (1 + d * (2 * m)) * (1 + (1 + d) * m)) := le_max_right _ _
  constructor
  · have e1 : flattenMap e ψ x₀ u y - flattenMap e ψ x₀ u z =
        flattenLin e (projGradVec e ψ x₀) u *ᵥ (shear e ψ y - shear e ψ z) := by
      unfold flattenMap; simp only [flatten_matVecMul_eq]
      rw [← Matrix.mulVec_sub]; congr 1; abel
    rw [e1]
    refine (p12b_lin_norm_le he u hM _).trans ?_
    calc (d : ℝ) * ((1 + d * (2 * m)) * ‖shear e ψ y - shear e ψ z‖)
        ≤ d * ((1 + d * (2 * m)) * ((1 + (1 + d) * m) * ‖y - z‖)) := by
          gcongr; exact hLip ψ hψlip y z
      _ = (d * (1 + d * (2 * m)) * (1 + (1 + d) * m)) * ‖y - z‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hKle (norm_nonneg _)
  · have e1 : flattenInv e ψ x₀ u y - flattenInv e ψ x₀ u z =
        shear e (-ψ) (flattenLinInv e (projGradVec e ψ x₀) u *ᵥ y + shear e ψ x₀) -
        shear e (-ψ) (flattenLinInv e (projGradVec e ψ x₀) u *ᵥ z + shear e ψ x₀) := rfl
    rw [e1]
    refine (hLip (-ψ) hψlip' _ _).trans ?_
    have h2 := flatten_norm_linInv_le he (u := u) hM (y - z)
    have e2 : flattenLinInv e (projGradVec e ψ x₀) u *ᵥ y + shear e ψ x₀ -
        (flattenLinInv e (projGradVec e ψ x₀) u *ᵥ z + shear e ψ x₀) =
        flattenLinInv e (projGradVec e ψ x₀) u *ᵥ (y - z) := by
      rw [Matrix.mulVec_sub]; abel
    rw [e2]
    calc (1 + (1 + d) * m) * ‖flattenLinInv e (projGradVec e ψ x₀) u *ᵥ (y - z)‖
        ≤ (1 + (1 + d) * m) * (d * (1 + d * (2 * m)) * ‖y - z‖) := by gcongr
      _ = (d * (1 + d * (2 * m)) * (1 + (1 + d) * m)) * ‖y - z‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hKle (norm_nonneg _)

theorem p12_chart_jac_le (d : ℕ) (M₁ : ℝ) : ∃ K : ℝ, 1 ≤ K ∧
    ∀ {e : Vec d} (_he : vecNormSq e = 1) {ψ : Vec d → ℝ} (_hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
      (_hb1 : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁) {u : Vec d} (_hu : vecNormSq u = 1) (x₀ y w : Vec d),
      ‖matVecMul (flattenLin e (projGradVec e ψ x₀) u * shearJac e ψ y) w‖ ≤ K * ‖w‖ := by
  set m : ℝ := max M₁ 0 with hm
  have hm0 : 0 ≤ m := le_max_right _ _
  refine ⟨max 1 (d * (1 + d * (2 * m)) * (1 + d * (2 * m))), le_max_left _ _, ?_⟩
  intro e he ψ hψ hb1 u _ x₀ y w
  have hM : ∀ x, ‖projGradVec e ψ x‖ ≤ 2 * m := fun x =>
    (flatten_norm_projGradVec_le he hψ hb1 x).trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))
  have e1 : matVecMul (flattenLin e (projGradVec e ψ x₀) u * shearJac e ψ y) w =
      flattenLin e (projGradVec e ψ x₀) u *ᵥ (shearJac e ψ y *ᵥ w) := by
    rw [flatten_matVecMul_eq, Matrix.mulVec_mulVec]
  rw [e1]
  have h2 := p12b_jac_norm_le he (hM y) w
  have h3 : ‖shearJac e ψ y *ᵥ w‖ ≤ (1 + d * (2 * m)) * ‖w‖ := h2
  refine (p12b_lin_norm_le he u (hM x₀) _).trans ?_
  calc (d : ℝ) * ((1 + d * (2 * m)) * ‖shearJac e ψ y *ᵥ w‖)
      ≤ d * ((1 + d * (2 * m)) * ((1 + d * (2 * m)) * ‖w‖)) := by gcongr
    _ = (d * (1 + d * (2 * m)) * (1 + d * (2 * m))) * ‖w‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

theorem p12g_grad_eq {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {M₁ : ℝ} (hb1 : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁) (u x₀ τ : Vec d)
    {U : Set (Vec d)} (φ : H10Function U) (x : Vec d) :
    (p12_chartFun he hψ hb1 u x₀ τ φ).toH1Function.grad x = fun i =>
      vecDot (fun j => φ.toH1Function.grad (flattenInv e ψ x₀ u (x - τ)) j -
          vecDot e (φ.toH1Function.grad (flattenInv e ψ x₀ u (x - τ))) *
            projGrad e (-ψ) j (matVecMul (flattenLinInv e (projGradVec e ψ x₀) u)
              (x - (τ - flattenShift e ψ x₀ u))))
        (fun k => flattenLinInv e (projGradVec e ψ x₀) u k i) := by
  have hg := vecDot_self_projGradVec he hψ x₀
  have h := flattenInv_sub_shift he hψ u x₀ (x - (τ - flattenShift e ψ x₀ u))
  have e1 : x - (τ - flattenShift e ψ x₀ u) - flattenShift e ψ x₀ u = x - τ := by abel
  rw [e1] at h
  funext i
  have hs : shear e (-ψ) ((flattenEquiv he hψ u x₀).symm (x - (τ - flattenShift e ψ x₀ u))) =
      flattenInv e ψ x₀ u (x - τ) := h.symm
  have hy : (flattenEquiv he hψ u x₀).symm (x - (τ - flattenShift e ψ x₀ u)) =
      matVecMul (flattenLinInv e (projGradVec e ψ x₀) u) (x - (τ - flattenShift e ψ x₀ u)) := by
    unfold flattenEquiv
    rw [matrixContinuousLinearEquiv_symm_apply, flattenLin_inv_eq hg]
  unfold p12_chartFun
  simp only [H10Function.translate_toH1Function, H1Function.translate_grad,
    H10Function.compLinearEquiv_grad, hy]
  have hs' : shear e (-ψ) (matVecMul (flattenLinInv e (projGradVec e ψ x₀) u)
      (x - (τ - flattenShift e ψ x₀ u))) = flattenInv e ψ x₀ u (x - τ) := by rw [← hy]; exact hs
  have hb : (flattenEquiv he hψ u x₀).symm (basisVec i) =
      fun k => flattenLinInv e (projGradVec e ψ x₀) u k i := by
    unfold flattenEquiv
    rw [matrixContinuousLinearEquiv_symm_apply, flattenLin_inv_eq hg]
    funext k
    simp [matVecMul, basisVec, Pi.single_apply]
  rw [hb]
  show vecDot (fun j => φ.toH1Function.grad (shear e (-ψ) (matVecMul (flattenLinInv e
      (projGradVec e ψ x₀) u) (x - (τ - flattenShift e ψ x₀ u)))) j -
      vecDot e (φ.toH1Function.grad (shear e (-ψ) (matVecMul (flattenLinInv e
      (projGradVec e ψ x₀) u) (x - (τ - flattenShift e ψ x₀ u))))) * _) _ = _
  rw [hs']


theorem p12g_sum_le {B : ℝ} {c : Fin d → ℝ} (hc : ∀ i, |c i| ≤ B) (v : Vec d) :
    |∑ i, c i * v i| ≤ d * B * ‖v‖ := by
  calc |∑ i, c i * v i| ≤ ∑ i, |c i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, B * ‖v‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hc i) (by simpa using norm_le_pi_norm v i) (abs_nonneg _)
          ((abs_nonneg _).trans (hc i))
    _ = d * B * ‖v‖ := by simp [mul_assoc]

theorem p12g_dot_le (a b : Vec d) : |vecDot a b| ≤ d * (‖a‖ * ‖b‖) := by
  unfold vecDot
  have := p12g_sum_le (c := a) (B := ‖a‖) (fun i => by simpa using norm_le_pi_norm a i) b
  linarith only [this]

theorem p12g_linInv_entry {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {M₁ : ℝ} (hb1 : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁) (u x₀ : Vec d)
    (i k : Fin d) :
    |flattenLinInv e (projGradVec e ψ x₀) u i k| ≤ d * (1 + d * (2 * M₁)) := by
  have h := flatten_norm_linInv_le (u := u) he (flatten_norm_projGradVec_le he hψ hb1 x₀)
    (Pi.single k (1 : ℝ))
  have h1 : ‖(Pi.single k (1 : ℝ) : Vec d)‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => by
      by_cases hj : j = k <;> simp [hj]
  have hM : 0 ≤ M₁ := (norm_nonneg _).trans (hb1 0)
  have h2 : |(flattenLinInv e (projGradVec e ψ x₀) u *ᵥ Pi.single k (1 : ℝ)) i| ≤
      ‖flattenLinInv e (projGradVec e ψ x₀) u *ᵥ Pi.single k (1 : ℝ)‖ := by
    simpa using norm_le_pi_norm (flattenLinInv e (projGradVec e ψ x₀) u *ᵥ Pi.single k (1 : ℝ)) i
  have h3 : (flattenLinInv e (projGradVec e ψ x₀) u *ᵥ Pi.single k (1 : ℝ)) i =
      flattenLinInv e (projGradVec e ψ x₀) u i k := by
    simp
  rw [h3] at h2
  calc _ ≤ _ := h2
    _ ≤ d * (1 + d * (2 * M₁)) * ‖(Pi.single k (1 : ℝ) : Vec d)‖ := h
    _ ≤ d * (1 + d * (2 * M₁)) * 1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := mul_one _

theorem p12g_lin_entry {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {M₁ : ℝ} (hb1 : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁) (u x₀ : Vec d)
    (i j : Fin d) :
    |flattenLin e (projGradVec e ψ x₀) u i j| ≤ d * (1 + 2 * M₁) := by
  have hM : 0 ≤ M₁ := (norm_nonneg _).trans (hb1 0)
  have hH := flatten_abs_entry_le_one
    (flattenHouseholder_mul_transpose (flattenNormal e (projGradVec e ψ x₀)) u)
  have hT : ∀ k, |flattenTilt e (projGradVec e ψ x₀) k j| ≤ 1 + 2 * M₁ := by
    intro k
    unfold flattenTilt
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.one_apply]
    have h1 : |(if k = j then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    have h2 : |e k * projGradVec e ψ x₀ j| ≤ 2 * M₁ := by
      rw [abs_mul]
      have := abs_apply_le_one he k
      have h3 : |projGradVec e ψ x₀ j| ≤ 2 * M₁ := by
        simpa [projGradVec] using flatten_abs_projGrad_le he hψ hb1 x₀ j
      calc |e k| * |projGradVec e ψ x₀ j| ≤ 1 * (2 * M₁) :=
            mul_le_mul this h3 (abs_nonneg _) zero_le_one
        _ = 2 * M₁ := one_mul _
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ 1 + 2 * M₁ := add_le_add h1 h2
  unfold flattenLin
  rw [Matrix.mul_apply]
  calc |∑ k, flattenHouseholder (flattenNormal e (projGradVec e ψ x₀)) u i k *
          flattenTilt e (projGradVec e ψ x₀) k j|
      ≤ ∑ k, |flattenHouseholder (flattenNormal e (projGradVec e ψ x₀)) u i k *
          flattenTilt e (projGradVec e ψ x₀) k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin d, (1 + 2 * M₁) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        calc _ ≤ 1 * (1 + 2 * M₁) := mul_le_mul (hH i k) (hT k) (abs_nonneg _) zero_le_one
          _ = _ := one_mul _
    _ = d * (1 + 2 * M₁) := by simp; ring


theorem p12g_vecDot_b {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (y : Vec d) :
    vecDot e (fun j => projGrad e (-ψ) j y) = 0 := by
  have h := vecDot_self_projGradVec he hψ y
  have : vecDot e (fun j => projGrad e (-ψ) j y) = - vecDot e (projGradVec e ψ y) := by
    unfold vecDot projGradVec
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by
      show e j * projGrad e (-ψ) j y = _
      rw [projGrad_neg]; ring
  rw [this, h, neg_zero]

/-- (G'') The gradient of the chart-flattened function is comparable to the original gradient,
in both directions, pointwise. -/
theorem p12_chartFun_grad_le (d : ℕ) (M₁ : ℝ) : ∃ K : ℝ, 1 ≤ K ∧
    ∀ {e : Vec d} (he : vecNormSq e = 1) {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
      (hb1 : ∀ y, ‖fderiv ℝ ψ y‖ ≤ M₁) {u : Vec d} (_hu : vecNormSq u = 1) (x₀ τ : Vec d)
      {U : Set (Vec d)} (φ : H10Function U) (x : Vec d),
      ‖(p12_chartFun he hψ hb1 u x₀ τ φ).toH1Function.grad x‖ ≤
        K * ‖φ.toH1Function.grad (flattenInv e ψ x₀ u (x - τ))‖ ∧
      ‖φ.toH1Function.grad (flattenInv e ψ x₀ u (x - τ))‖ ≤
        K * ‖(p12_chartFun he hψ hb1 u x₀ τ φ).toH1Function.grad x‖ := by
  set M : ℝ := max M₁ 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  set c0 : ℝ := 1 + d * (2 * M) with hc0
  have hc00 : 0 ≤ c0 := by positivity
  refine ⟨1 + d * (d * c0) * c0 + c0 * (d * (d * (1 + 2 * M))), ?_, ?_⟩
  · have : 0 ≤ (d : ℝ) * (d * c0) * c0 := by positivity
    have : 0 ≤ c0 * (d * (d * (1 + 2 * M))) := by positivity
    linarith only [‹0 ≤ (d : ℝ) * (d * c0) * c0›, this]
  intro e he ψ hψ hb1 u _hu x₀ τ U φ x
  have hM : 0 ≤ M₁ := (norm_nonneg _).trans (hb1 0)
  have hMM : M = M₁ := max_eq_left hM
  rw [hMM] at hc0 ⊢
  have hg := vecDot_self_projGradVec he hψ x₀
  rw [p12g_grad_eq he hψ hb1 u x₀ τ φ x]
  set a := φ.toH1Function.grad (flattenInv e ψ x₀ u (x - τ)) with ha
  set y := matVecMul (flattenLinInv e (projGradVec e ψ x₀) u) (x - (τ - flattenShift e ψ x₀ u))
    with hy
  set b : Vec d := fun j => projGrad e (-ψ) j y with hbdef
  set w : Vec d := fun j => a j - vecDot e a * b j with hwdef
  set Li := flattenLinInv e (projGradVec e ψ x₀) u with hLi
  set L := flattenLin e (projGradVec e ψ x₀) u with hL
  have hbj : ∀ j, |b j| ≤ 2 * M₁ := fun j => by
    simp only [hbdef, projGrad_neg, abs_neg]
    exact flatten_abs_projGrad_le he hψ hb1 y j
  have he1 : ‖e‖ ≤ 1 := norm_le_one_of_vecNormSq he
  have hdot : ∀ z : Vec d, |vecDot e z| ≤ d * ‖z‖ := fun z =>
    (p12g_dot_le e z).trans (by
      calc (d : ℝ) * (‖e‖ * ‖z‖) ≤ d * (1 * ‖z‖) := by gcongr
        _ = _ := by ring)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  -- the vector `v = ∇φ₂`
  set v : Vec d := fun i => vecDot w (fun k => Li k i) with hv
  have hwa : ‖w‖ ≤ c0 * ‖a‖ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    simp only [hwdef, Real.norm_eq_abs]
    calc |a j - vecDot e a * b j| ≤ |a j| + |vecDot e a| * |b j| := by
          refine (abs_sub _ _).trans ?_; rw [abs_mul]
      _ ≤ ‖a‖ + (d * ‖a‖) * (2 * M₁) := by
          gcongr
          · simpa using norm_le_pi_norm a j
          · exact hdot a
          · exact hbj j
      _ = c0 * ‖a‖ := by rw [hc0]; ring
  constructor
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    have h1 := p12g_sum_le (c := fun k => Li k i) (B := d * (1 + d * (2 * M₁)))
      (fun k => p12g_linInv_entry he hψ hb1 u x₀ k i) w
    calc |vecDot w (fun k => Li k i)| = |∑ k, Li k i * w k| := by
          unfold vecDot; exact congrArg _ (Finset.sum_congr rfl fun k _ => mul_comm _ _)
      _ ≤ d * (d * (1 + d * (2 * M₁))) * ‖w‖ := h1
      _ ≤ d * (d * (1 + d * (2 * M₁))) * (c0 * ‖a‖) := by gcongr
      _ = (d * (d * c0) * c0) * ‖a‖ := by rw [hc0]; ring
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have : 0 ≤ c0 * (d * (d * (1 + 2 * M₁))) := by rw [hc0]; positivity
        linarith only [this]
  · -- reverse: `w = v ᵥ* L`
    have hwv : w = v ᵥ* L := by
      have : v = w ᵥ* Li := by
        funext i; rfl
      rw [this, Matrix.vecMul_vecMul, hLi, hL, flattenLinInv_mul hg, Matrix.vecMul_one]
    have hwv' : ‖w‖ ≤ d * (d * (1 + 2 * M₁)) * ‖v‖ := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
      rw [Real.norm_eq_abs, hwv]
      have := p12g_sum_le (c := fun i => L i j) (B := d * (1 + 2 * M₁))
        (fun i => p12g_lin_entry he hψ hb1 u x₀ i j) v
      have e : (v ᵥ* L) j = ∑ i, L i j * v i := by
        simp [Matrix.vecMul, dotProduct, mul_comm]
      rw [e]; exact this
    have heb : vecDot e b = 0 := p12g_vecDot_b he hψ y
    have hew : vecDot e w = vecDot e a := by
      have : vecDot e w = vecDot e a - vecDot e a * vecDot e b := by
        have h1 : ∀ j, e j * w j = e j * a j - vecDot e a * (e j * b j) := by
          intro j; simp only [hwdef]; ring
        show ∑ j, e j * w j = _
        rw [Finset.sum_congr rfl (fun j _ => h1 j), Finset.sum_sub_distrib, ← Finset.mul_sum]
        rfl
      rw [this, heb]; ring
    have hav : ‖a‖ ≤ c0 * ‖w‖ := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
      have haj : a j = w j + vecDot e w * b j := by
        show a j = (a j - vecDot e a * b j) + vecDot e w * b j
        rw [hew]; ring
      rw [Real.norm_eq_abs, haj]
      calc |w j + vecDot e w * b j| ≤ |w j| + |vecDot e w| * |b j| := by
            refine (abs_add_le _ _).trans ?_; rw [abs_mul]
        _ ≤ ‖w‖ + (d * ‖w‖) * (2 * M₁) := by
            gcongr
            · simpa using norm_le_pi_norm w j
            · exact hdot w
            · exact hbj j
        _ = c0 * ‖w‖ := by rw [hc0]; ring
    calc ‖a‖ ≤ c0 * ‖w‖ := hav
      _ ≤ c0 * (d * (d * (1 + 2 * M₁)) * ‖v‖) := by gcongr
      _ = (c0 * (d * (d * (1 + 2 * M₁)))) * ‖v‖ := by ring
      _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        have : 0 ≤ (d : ℝ) * (d * c0) * c0 := by positivity
        linarith only [this]


/-- (G''') The transported Laplacian coefficient is continuous (entrywise). -/
theorem p12_chartCoeff_continuous {e : Vec d} (_he : vecNormSq e = 1) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {u : Vec d} (x₀ τ : Vec d) (i j : Fin d) :
    Continuous (fun x => flattenCoeff e ψ x₀ u (fun _ => (1 : Mat d)) (x - τ) i j) := by
  have hsh : Continuous (shear e (-ψ)) := (contDiff_shear hψ.neg).continuous
  have hlin : Continuous (fun z : Vec d => matVecMul (flattenLinInv e (projGradVec e ψ x₀) u) z) :=
    continuous_pi fun k => by
      simp only [matVecMul]
      fun_prop
  have hinv : Continuous (fun x : Vec d => flattenInv e ψ x₀ u (x - τ)) := by
    unfold flattenInv
    refine hsh.comp ?_
    exact (hlin.comp (continuous_id.sub continuous_const)).add continuous_const
  have hJ : Continuous (fun x : Vec d => shearJac e ψ (flattenInv e ψ x₀ u (x - τ))) := by
    refine continuous_matrix fun a b => ?_
    simp only [shearJac, Matrix.sub_apply, Matrix.vecMulVec_apply, projGradVec]
    exact continuous_const.sub (continuous_const.mul
      ((contDiff_projGrad hψ b).continuous.comp hinv))
  have hall : Continuous (fun x : Vec d => flattenCoeff e ψ x₀ u (fun _ => (1 : Mat d)) (x - τ)) := by
    unfold flattenCoeff
    simp only [Matrix.mul_one]
    refine ((continuous_const.matrix_mul (hJ.matrix_mul ?_)).matrix_mul continuous_const)
    exact continuous_matrix fun a b => hJ.matrix_elem b a
  exact (continuous_apply j).comp ((continuous_apply i).comp hall)

end SuperdiffusionCLT.Section7
