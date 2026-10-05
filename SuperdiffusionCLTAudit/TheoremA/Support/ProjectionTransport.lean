module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import SuperdiffusionCLT.Probability.StationaryProjection

/-!
# Transport of the stationary potential projection

If `e : Ω₁ ≃ᵐ Ω₂` is a measurable equivalence that intertwines the translation actions and
carries `μ₁` to `μ₂`, then composition with `e` is a linear isometry equivalence between the
`L²` spaces. It commutes with the Koopman operators and with the coordinate maps, hence maps
horizontal gradients to horizontal gradients and the potential subspace onto the potential
subspace. Consequently it intertwines the two stationary potential projections, and the norms of
the projections of corresponding vector fields agree.
-/

@[expose] public section

namespace SuperdiffusionCLT.StatementAudit.TheoremA
open MeasureTheory Homogenization
open SuperdiffusionCLT.Probability.Stationary

noncomputable section

section Transport

variable {d : ℕ} {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
  [AddAction (Vec d) Ω₁] [AddAction (Vec d) Ω₂]
  [MeasurableConstVAdd (Vec d) Ω₁] [MeasurableConstVAdd (Vec d) Ω₂]
  {μ₁ : Measure Ω₁} {μ₂ : Measure Ω₂}

private theorem mp (e : Ω₁ ≃ᵐ Ω₂) (hμ : μ₁.map e = μ₂) : MeasurePreserving e μ₁ μ₂ :=
  ⟨e.measurable, hμ⟩

/-- Composition with `e` on `L²`. -/
private def U (e : Ω₁ ≃ᵐ Ω₂) (hμ : μ₁.map e = μ₂) (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : Lp E 2 μ₂ →ₗᵢ[ℝ] Lp E 2 μ₁ :=
  Lp.compMeasurePreservingₗᵢ ℝ e (mp e hμ)

private theorem coe_U (e : Ω₁ ≃ᵐ Ω₂) (hμ : μ₁.map e = μ₂) (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : Lp E 2 μ₂) :
    (U e hμ E g : Ω₁ → E) =ᵐ[μ₁] (g : Ω₂ → E) ∘ e :=
  Lp.coeFn_compMeasurePreserving g (mp e hμ)

private theorem U_koopman [VAddInvariantMeasure (Vec d) Ω₁ μ₁]
    [VAddInvariantMeasure (Vec d) Ω₂ μ₂]
    (e : Ω₁ ≃ᵐ Ω₂) (he : ∀ (z : Vec d) (a : Ω₁), e (z +ᵥ a) = z +ᵥ e a)
    (hμ : μ₁.map e = μ₂) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : Vec d) (φ : Lp E 2 μ₂) :
    U e hμ E (koopman (μ := μ₂) x φ) = koopman (μ := μ₁) x (U e hμ E φ) := by
  apply Lp.ext
  have h1 := coe_U e hμ E (koopman (μ := μ₂) x φ)
  have h2 : ((koopman (μ := μ₂) x φ : Lp E 2 μ₂) : Ω₂ → E) =ᵐ[μ₂]
      (φ : Ω₂ → E) ∘ (x +ᵥ ·) := Lp.coeFn_compMeasurePreserving φ _
  have h2' := (mp e hμ).quasiMeasurePreserving.ae_eq_comp h2
  have h3 := coe_U e hμ E φ
  have h4 : ((koopman (μ := μ₁) x (U e hμ E φ) : Lp E 2 μ₁) : Ω₁ → E) =ᵐ[μ₁]
      (U e hμ E φ : Ω₁ → E) ∘ (x +ᵥ ·) := Lp.coeFn_compMeasurePreserving _ _
  have h5 := (measurePreserving_const_vadd (μ := μ₁) x).quasiMeasurePreserving.ae_eq_comp h3
  filter_upwards [h1, h2', h4, h5] with a ha1 ha2 ha4 ha5
  rw [ha1, ha4]
  simp only [Function.comp_apply] at ha2 ha5 ⊢
  rw [ha2, ha5, he]

omit [AddAction (Vec d) Ω₁] [AddAction (Vec d) Ω₂] [MeasurableConstVAdd (Vec d) Ω₁]
  [MeasurableConstVAdd (Vec d) Ω₂] in
private theorem U_coord (e : Ω₁ ≃ᵐ Ω₂) (hμ : μ₁.map e = μ₂) (i : Fin d)
    (F : VectorL2 d μ₂) :
    U e hμ ℝ (vectorL2Coord (μ := μ₂) i F) =
      vectorL2Coord (μ := μ₁) i (U e hμ (HilbertVec d) F) := by
  apply Lp.ext
  have h1 := coe_U e hμ ℝ (vectorL2Coord (μ := μ₂) i F)
  have h2 : ((vectorL2Coord (μ := μ₂) i F : Lp ℝ 2 μ₂) : Ω₂ → ℝ) =ᵐ[μ₂]
      fun ω ↦ (F : Ω₂ → HilbertVec d) ω i :=
    ContinuousLinearMap.coeFn_compLpL _ F
  have h2' := (mp e hμ).quasiMeasurePreserving.ae_eq_comp h2
  have h3 := coe_U e hμ (HilbertVec d) F
  have h4 : ((vectorL2Coord (μ := μ₁) i (U e hμ (HilbertVec d) F) : Lp ℝ 2 μ₁) : Ω₁ → ℝ)
      =ᵐ[μ₁] fun ω ↦ (U e hμ (HilbertVec d) F : Ω₁ → HilbertVec d) ω i :=
    ContinuousLinearMap.coeFn_compLpL _ _
  filter_upwards [h1, h2', h3, h4] with a ha1 ha2 ha3 ha4
  rw [ha1, ha4, ha3]
  simpa only [Function.comp_apply] using ha2

private theorem U_hasHorizontalGradient [VAddInvariantMeasure (Vec d) Ω₁ μ₁]
    [VAddInvariantMeasure (Vec d) Ω₂ μ₂]
    (e : Ω₁ ≃ᵐ Ω₂) (he : ∀ (z : Vec d) (a : Ω₁), e (z +ᵥ a) = z +ᵥ e a)
    (hμ : μ₁.map e = μ₂) {φ : ScalarL2 μ₂} {G : VectorL2 d μ₂}
    (h : HasHorizontalGradient (μ := μ₂) φ G) :
    HasHorizontalGradient (μ := μ₁) (U e hμ ℝ φ) (U e hμ (HilbertVec d) G) := by
  intro i
  have := HasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (ContinuousLinearMap.hasFDerivAt (U e hμ ℝ).toContinuousLinearMap) (h i)
  convert this using 1
  · funext t
    exact (U_koopman e he hμ ℝ _ φ).symm
  · exact (U_coord e hμ i G).symm

private theorem U_mem_potential [VAddInvariantMeasure (Vec d) Ω₁ μ₁]
    [VAddInvariantMeasure (Vec d) Ω₂ μ₂]
    (e : Ω₁ ≃ᵐ Ω₂) (he : ∀ (z : Vec d) (a : Ω₁), e (z +ᵥ a) = z +ᵥ e a)
    (hμ : μ₁.map e = μ₂) {G : VectorL2 d μ₂}
    (hG : G ∈ stationaryPotentialSubspace (μ := μ₂) (d := d)) :
    U e hμ (HilbertVec d) G ∈ stationaryPotentialSubspace (μ := μ₁) (d := d) := by
  have hG' : G ∈ closure ((horizontalGradientRange (μ := μ₂) (d := d) : Submodule ℝ _) :
      Set (VectorL2 d μ₂)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hG
  have := map_mem_closure (U e hμ (HilbertVec d)).continuous hG'
    (t := (horizontalGradientRange (μ := μ₁) (d := d) : Set (VectorL2 d μ₁)))
    (by
      rintro F ⟨φ, hφ⟩
      exact ⟨U e hμ ℝ φ, U_hasHorizontalGradient e he hμ hφ⟩)
  rw [← Submodule.topologicalClosure_coe] at this
  exact this

private theorem U_U_symm (e : Ω₁ ≃ᵐ Ω₂) (hμ : μ₁.map e = μ₂) (hμ' : μ₂.map e.symm = μ₁)
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (y : Lp E 2 μ₁) :
    U e hμ E (U e.symm hμ' E y) = y := by
  apply Lp.ext
  have h1 := coe_U e hμ E (U e.symm hμ' E y)
  have h2 := coe_U e.symm hμ' E y
  have h2' := (mp e hμ).quasiMeasurePreserving.ae_eq_comp h2
  filter_upwards [h1, h2'] with a ha1 ha2
  rw [ha1]
  simpa only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] using ha2

/-- The stationary potential projection is intertwined by composition with `e`. -/
private theorem U_projection [VAddInvariantMeasure (Vec d) Ω₁ μ₁]
    [VAddInvariantMeasure (Vec d) Ω₂ μ₂]
    (e : Ω₁ ≃ᵐ Ω₂) (he : ∀ (z : Vec d) (a : Ω₁), e (z +ᵥ a) = z +ᵥ e a)
    (hμ : μ₁.map e = μ₂) (v : VectorL2 d μ₂) :
    stationaryPotentialProjection (μ := μ₁) (U e hμ (HilbertVec d) v) =
      U e hμ (HilbertVec d) (stationaryPotentialProjection (μ := μ₂) v) := by
  have hμ' : μ₂.map e.symm = μ₁ := by
    rw [← hμ, Measure.map_map e.symm.measurable e.measurable]
    simp
  have he' : ∀ (z : Vec d) (b : Ω₂), e.symm (z +ᵥ b) = z +ᵥ e.symm b := by
    intro z b
    apply e.injective
    rw [he, MeasurableEquiv.apply_symm_apply, MeasurableEquiv.apply_symm_apply]
  unfold stationaryPotentialProjection
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_
  · exact U_mem_potential e he hμ (stationaryPotentialProjection_mem (μ := μ₂) v)
  · have hw' := U_mem_potential e.symm he' hμ' hw
    have hww := U_U_symm e hμ hμ' (HilbertVec d) w
    calc inner ℝ (U e hμ (HilbertVec d) v - U e hμ (HilbertVec d)
            ((stationaryPotentialSubspace (μ := μ₂) (d := d)).starProjection v)) w
        = inner ℝ (U e hμ (HilbertVec d) (v - (stationaryPotentialSubspace (μ := μ₂)
            (d := d)).starProjection v)) (U e hμ (HilbertVec d)
              (U e.symm hμ' (HilbertVec d) w)) := by
          rw [hww, map_sub]
      _ = inner ℝ (v - (stationaryPotentialSubspace (μ := μ₂)
            (d := d)).starProjection v) (U e.symm hμ' (HilbertVec d) w) :=
          LinearIsometry.inner_map_map _ _ _
      _ = 0 := Submodule.inner_left_of_mem_orthogonal hw'
            (sub_stationaryPotentialProjection_mem_orthogonal (μ := μ₂) v)

theorem norm_stationaryPotentialProjection_congr
    [VAddInvariantMeasure (Vec d) Ω₁ μ₁] [VAddInvariantMeasure (Vec d) Ω₂ μ₂]
    (e : Ω₁ ≃ᵐ Ω₂) (he : ∀ (z : Vec d) (a : Ω₁), e (z +ᵥ a) = z +ᵥ e a)
    (hμ : μ₁.map e = μ₂)
    (F : Ω₂ → HilbertVec d) (h₂ : MemLp F 2 μ₂) (h₁ : MemLp (F ∘ e) 2 μ₁) :
    ‖SuperdiffusionCLT.Probability.Stationary.stationaryPotentialProjection (μ := μ₁)
        (h₁.toLp (F ∘ e))‖ =
      ‖SuperdiffusionCLT.Probability.Stationary.stationaryPotentialProjection (μ := μ₂)
        (h₂.toLp F)‖ := by
  have hU : h₁.toLp (F ∘ e) = U e hμ (HilbertVec d) (h₂.toLp F) := by
    apply Lp.ext
    have h1 := coe_U e hμ (HilbertVec d) (h₂.toLp F)
    have h2 := (mp e hμ).quasiMeasurePreserving.ae_eq_comp h₂.coeFn_toLp
    filter_upwards [h₁.coeFn_toLp, h1, h2] with a ha1 ha2 ha3
    rw [ha1, ha2]
    simpa only [Function.comp_apply] using ha3.symm
  rw [hU, U_projection e he hμ]
  exact LinearIsometry.norm_map _ _

end Transport

end

end SuperdiffusionCLT.StatementAudit.TheoremA
