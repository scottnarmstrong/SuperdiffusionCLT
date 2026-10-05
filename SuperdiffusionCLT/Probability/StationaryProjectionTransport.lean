/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.FactorsThrough
public import SuperdiffusionCLT.Probability.StationaryProjectionIndependence

/-!
# Transport of the stationary potential projection along an equivariant map

Let `T : Ω → Ω'` be measure preserving from `μ` to `μ'` and equivariant for two
real translation actions, `T (z +ᵥ ω) = z +ᵥ T ω`. Composition with `T` is a
linear isometry `Lp E 2 μ' →ₗᵢ[ℝ] Lp E 2 μ` which commutes with the Koopman
operators of the translations, hence maps horizontal gradients to horizontal
gradients and the stationary potential subspace of `μ'` into the stationary
potential subspace of `μ`.

This file proves that composition with `T` also commutes with the *orthogonal
projection* onto the stationary potential subspace. The solenoidal half of the
statement uses the conditional expectation onto the pullback sub-sigma-field
`MeasurableSpace.comap T`, which is translation invariant by equivariance, and
the Doob-Dynkin factorization
`MeasureTheory.StronglyMeasurable.exists_eq_measurable_comp`, which identifies
the range of the pullback isometry with the square-integrable functions that are
measurable for that sub-sigma-field.

## Main results

* `isVAddInvariantSubalgebra_comap`: the pullback of a sigma-field along an
  equivariant map is a translation-invariant sub-sigma-field.
* `transportL2`: composition with `T`, as a linear isometry of `L²` spaces.
* `transportL2_koopman`: it commutes with every Koopman operator.
* `HasHorizontalGradient.transportL2` and
  `hasHorizontalGradient_of_transportL2`: it preserves and reflects the
  horizontal-gradient relation.
* `transportL2_mem_lpMeas` and `exists_transportL2_eq`: the two inclusions that
  together say its range is exactly the square-integrable functions measurable
  for `MeasurableSpace.comap T`.
* `transportL2_mem_stationarySolenoidalSubspace`: it preserves the stationary
  solenoidal subspace.
* `transportL2_stationaryPotentialProjection`: **the transport identity**
  `(proj F) ∘ T = proj (F ∘ T)`.
* `norm_stationaryPotentialProjection_transportL2`: the two responses have the
  same energy.
-/

@[expose] public section

open MeasureTheory
open Homogenization

namespace SuperdiffusionCLT.Probability.Stationary

noncomputable section

/-- A linear isometry reflects differentiability: it is injective and preserves
norms, so a difference quotient converges before it is mapped exactly when it
converges after. -/
private theorem hasDerivAt_of_linearIsometry {F₁ F₂ : Type*}
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂]
    [NormedSpace ℝ F₂] (U : F₁ →ₗᵢ[ℝ] F₂) {f : ℝ → F₁} {v : F₁} {x : ℝ}
    (h : HasDerivAt (fun t ↦ U (f t)) (U v) x) : HasDerivAt f v x := by
  rw [hasDerivAt_iff_isLittleO] at h ⊢
  have hfun : (fun t : ℝ ↦ U (f t) - U (f x) - (t - x) • U v)
      = fun t : ℝ ↦ U (f t - f x - (t - x) • v) := by
    funext t
    rw [map_sub, map_sub, map_smul]
  rw [hfun, ← Asymptotics.isLittleO_norm_left] at h
  rw [← Asymptotics.isLittleO_norm_left]
  simpa only [U.norm_map] using h

/-! ## Invariant sub-sigma-fields from equivariant maps -/

section Comap

variable {d : ℕ} {Ω : Type*} [AddAction (Vec d) Ω]
variable {α : Type*} [mα : MeasurableSpace α] [AddAction (Vec d) α]
variable [MeasurableConstVAdd (Vec d) α]

/-- The pullback of a sigma-field along a translation-equivariant map is a
translation-invariant sub-sigma-field. -/
theorem isVAddInvariantSubalgebra_comap (T : Ω → α)
    (hT : ∀ (z : Vec d) (ω : Ω), T (z +ᵥ ω) = z +ᵥ T ω) :
    IsVAddInvariantSubalgebra d (mα.comap T) := by
  rintro z s ⟨t, ht, rfl⟩
  refine ⟨(fun y : α ↦ z +ᵥ y) ⁻¹' t, measurable_const_vadd z ht, ?_⟩
  ext ω
  simp only [Set.mem_preimage, hT z ω]

end Comap

/-! ## The pullback isometry -/

variable {d : ℕ}
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
variable {T : Ω → Ω'}

section Pullback

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable (E) in
/-- Composition with a measure-preserving map, as a linear isometry of `L²`
spaces. -/
def transportL2 (hT : MeasurePreserving T μ μ') : Lp E 2 μ' →ₗᵢ[ℝ] Lp E 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℝ T hT

theorem coeFn_transportL2 (hT : MeasurePreserving T μ μ') (f : Lp E 2 μ') :
    (transportL2 E hT f : Ω → E) =ᵐ[μ] (f : Ω' → E) ∘ T :=
  Lp.coeFn_compMeasurePreserving f hT

theorem norm_transportL2 (hT : MeasurePreserving T μ μ') (f : Lp E 2 μ') :
    ‖transportL2 E hT f‖ = ‖f‖ :=
  (transportL2 E hT).norm_map f


/-! ## The range of the pullback isometry -/

/-- Every function pulled back along `T` is measurable for the pullback
sigma-field. -/
theorem transportL2_mem_lpMeas (hT : MeasurePreserving T μ μ') (f : Lp E 2 μ') :
    transportL2 E hT f ∈ lpMeas E ℝ (mΩ'.comap T) 2 μ := by
  rw [mem_lpMeas_iff_aestronglyMeasurable]
  obtain ⟨g, hgm, hgae⟩ := Lp.aestronglyMeasurable f
  refine ⟨g ∘ T, hgm.comp_measurable (comap_measurable T), ?_⟩
  refine (coeFn_transportL2 hT f).trans (ae_eq_comp hT.measurable.aemeasurable ?_)
  rw [hT.map_eq]
  exact hgae

theorem aestronglyMeasurable_transportL2 (hT : MeasurePreserving T μ μ')
    (f : Lp E 2 μ') :
    AEStronglyMeasurable[mΩ'.comap T] (transportL2 E hT f : Ω → E) μ :=
  mem_lpMeas_iff_aestronglyMeasurable.mp (transportL2_mem_lpMeas hT f)

/-- **The range of the pullback isometry is exactly the square-integrable
functions measurable for the pullback sigma-field.** The nontrivial inclusion is
the Doob-Dynkin factorization
`MeasureTheory.StronglyMeasurable.exists_eq_measurable_comp`. -/
theorem exists_transportL2_eq [CompleteSpace E] (hT : MeasurePreserving T μ μ')
    {f : Lp E 2 μ} (hf : AEStronglyMeasurable[mΩ'.comap T] (f : Ω → E) μ) :
    ∃ g : Lp E 2 μ', transportL2 E hT g = f := by
  have : Nonempty E := ⟨0⟩
  obtain ⟨f₀, hf₀m, hf₀ae⟩ := hf
  obtain ⟨h, hhm, hh⟩ := hf₀m.exists_eq_measurable_comp
  have hmemf₀ : MemLp f₀ 2 μ := (Lp.memLp f).ae_eq hf₀ae
  have hmemh : MemLp h 2 μ' := by
    rw [← hT.map_eq]
    refine (memLp_map_measure_iff hhm.aestronglyMeasurable
      hT.measurable.aemeasurable).mpr ?_
    rw [← hh]
    exact hmemf₀
  refine ⟨hmemh.toLp h, Lp.ext ?_⟩
  have step1 : (transportL2 E hT (hmemh.toLp h) : Ω → E)
      =ᵐ[μ] (hmemh.toLp h : Ω' → E) ∘ T := coeFn_transportL2 hT _
  have step2 : ((hmemh.toLp h : Ω' → E) ∘ T) =ᵐ[μ] h ∘ T := by
    refine ae_eq_comp hT.measurable.aemeasurable ?_
    rw [hT.map_eq]
    exact hmemh.coeFn_toLp
  refine (step1.trans step2).trans ?_
  rw [← hh]
  exact hf₀ae.symm

end Pullback

/-! ## Coordinates and horizontal gradients -/

theorem vectorL2Coord_transportL2 (hT : MeasurePreserving T μ μ') (i : Fin d)
    (F : VectorL2 d μ') :
    vectorL2Coord (μ := μ) i (transportL2 (HilbertVec d) hT F) =
      transportL2 ℝ hT (vectorL2Coord (μ := μ') i F) := by
  refine Lp.ext ?_
  have h1 : (vectorL2Coord (μ := μ) i (transportL2 (HilbertVec d) hT F) : Ω → ℝ)
      =ᵐ[μ] fun ω ↦ (transportL2 (HilbertVec d) hT F : Ω → HilbertVec d) ω i :=
    ContinuousLinearMap.coeFn_compLpL _ _
  have h2 := coeFn_transportL2 (μ := μ) hT F
  have h3 : (transportL2 ℝ hT (vectorL2Coord (μ := μ') i F) : Ω → ℝ)
      =ᵐ[μ] (vectorL2Coord (μ := μ') i F : Ω' → ℝ) ∘ T := coeFn_transportL2 hT _
  have h4 : ((vectorL2Coord (μ := μ') i F : Ω' → ℝ) ∘ T)
      =ᵐ[μ] ((fun ω' ↦ (F : Ω' → HilbertVec d) ω' i) ∘ T) := by
    refine ae_eq_comp hT.measurable.aemeasurable ?_
    rw [hT.map_eq]
    exact ContinuousLinearMap.coeFn_compLpL _ _
  refine h1.trans (Filter.EventuallyEq.trans ?_ (h3.trans h4).symm)
  filter_upwards [h2] with ω hω
  simp only [Function.comp_apply] at hω ⊢
  rw [hω]

variable [AddAction (Vec d) Ω] [MeasurableConstVAdd (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]
variable [AddAction (Vec d) Ω'] [MeasurableConstVAdd (Vec d) Ω']
variable [VAddInvariantMeasure (Vec d) Ω' μ']

section Koopman

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The pullback isometry commutes with every Koopman operator. -/
theorem transportL2_koopman (hT : MeasurePreserving T μ μ')
    (hTequiv : ∀ (z : Vec d) (ω : Ω), T (z +ᵥ ω) = z +ᵥ T ω) (z : Vec d)
    (f : Lp E 2 μ') :
    transportL2 E hT (koopman (μ := μ') z f) =
      koopman (μ := μ) z (transportL2 E hT f) := by
  refine Lp.ext ?_
  have hvadd := measurePreserving_const_vadd (μ := μ) (Ω := Ω) z
  have h1 : (transportL2 E hT (koopman (μ := μ') z f) : Ω → E)
      =ᵐ[μ] (koopman (μ := μ') z f : Ω' → E) ∘ T := coeFn_transportL2 hT _
  have h2 : ((koopman (μ := μ') z f : Ω' → E) ∘ T)
      =ᵐ[μ] (((f : Ω' → E) ∘ fun ω' : Ω' ↦ z +ᵥ ω') ∘ T) := by
    refine ae_eq_comp hT.measurable.aemeasurable ?_
    rw [hT.map_eq]
    exact Lp.coeFn_compMeasurePreserving _ _
  have h3 : (koopman (μ := μ) z (transportL2 E hT f) : Ω → E)
      =ᵐ[μ] (transportL2 E hT f : Ω → E) ∘ fun ω : Ω ↦ z +ᵥ ω :=
    Lp.coeFn_compMeasurePreserving _ _
  have h4 : ((transportL2 E hT f : Ω → E) ∘ fun ω : Ω ↦ z +ᵥ ω)
      =ᵐ[μ] (((f : Ω' → E) ∘ T) ∘ fun ω : Ω ↦ z +ᵥ ω) := by
    refine ae_eq_comp hvadd.measurable.aemeasurable ?_
    rw [hvadd.map_eq]
    exact coeFn_transportL2 hT f
  have heq : (((f : Ω' → E) ∘ fun ω' : Ω' ↦ z +ᵥ ω') ∘ T)
      = (((f : Ω' → E) ∘ T) ∘ fun ω : Ω ↦ z +ᵥ ω) := by
    funext ω
    simp only [Function.comp_apply, hTequiv z ω]
  refine (h1.trans h2).trans ?_
  rw [heq]
  exact (h3.trans h4).symm

end Koopman

/-- The pullback isometry maps horizontal gradients to horizontal gradients. -/
theorem HasHorizontalGradient.transportL2 (hT : MeasurePreserving T μ μ')
    (hTequiv : ∀ (z : Vec d) (ω : Ω), T (z +ᵥ ω) = z +ᵥ T ω) {φ : ScalarL2 μ'}
    {F : VectorL2 d μ'} (h : HasHorizontalGradient (μ := μ') φ F) :
    HasHorizontalGradient (μ := μ) (Stationary.transportL2 ℝ hT φ)
      (Stationary.transportL2 (HilbertVec d) hT F) := by
  intro i
  have hd : HasDerivAt
      ((Stationary.transportL2 ℝ hT).toContinuousLinearMap ∘
        fun t : ℝ ↦ koopman (μ := μ') (t • (Pi.single i 1 : Vec d)) φ)
      (Stationary.transportL2 ℝ hT (vectorL2Coord (μ := μ') i F)) 0 :=
    HasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (ContinuousLinearMap.hasFDerivAt
        (Stationary.transportL2 ℝ hT).toContinuousLinearMap) (h i)
  have hfun : ((Stationary.transportL2 ℝ hT).toContinuousLinearMap ∘
        fun t : ℝ ↦ koopman (μ := μ') (t • (Pi.single i 1 : Vec d)) φ) =
      fun t : ℝ ↦ koopman (μ := μ) (t • (Pi.single i 1 : Vec d))
        (Stationary.transportL2 ℝ hT φ) := by
    funext t
    exact transportL2_koopman hT hTequiv _ φ
  rw [hfun] at hd
  rw [vectorL2Coord_transportL2]
  exact hd

/-- The pullback isometry also reflects the horizontal-gradient relation. -/
theorem hasHorizontalGradient_of_transportL2 (hT : MeasurePreserving T μ μ')
    (hTequiv : ∀ (z : Vec d) (ω : Ω), T (z +ᵥ ω) = z +ᵥ T ω) {φ : ScalarL2 μ'}
    {F : VectorL2 d μ'}
    (h : HasHorizontalGradient (μ := μ) (transportL2 ℝ hT φ)
      (transportL2 (HilbertVec d) hT F)) :
    HasHorizontalGradient (μ := μ') φ F := by
  intro i
  refine hasDerivAt_of_linearIsometry (transportL2 ℝ hT) ?_
  have hi := h i
  rw [vectorL2Coord_transportL2] at hi
  have hfun : (fun t : ℝ ↦ transportL2 ℝ hT
        (koopman (μ := μ') (t • (Pi.single i 1 : Vec d)) φ)) =
      fun t : ℝ ↦ koopman (μ := μ) (t • (Pi.single i 1 : Vec d))
        (transportL2 ℝ hT φ) := by
    funext t
    exact transportL2_koopman hT hTequiv _ φ
  rw [hfun]
  exact hi

theorem transportL2_mem_horizontalGradientRange (hT : MeasurePreserving T μ μ')
    (hTequiv : ∀ (z : Vec d) (ω : Ω), T (z +ᵥ ω) = z +ᵥ T ω) {F : VectorL2 d μ'}
    (hF : F ∈ horizontalGradientRange (μ := μ') (d := d)) :
    transportL2 (HilbertVec d) hT F ∈ horizontalGradientRange (μ := μ) (d := d) := by
  obtain ⟨φ, hφ⟩ := hF
  exact ⟨transportL2 ℝ hT φ, hφ.transportL2 hT hTequiv⟩

/-- The pullback isometry maps the stationary potential subspace of `μ'` into the
stationary potential subspace of `μ`. -/
theorem transportL2_mem_stationaryPotentialSubspace (hT : MeasurePreserving T μ μ')
    (hTequiv : ∀ (z : Vec d) (ω : Ω), T (z +ᵥ ω) = z +ᵥ T ω) {F : VectorL2 d μ'}
    (hF : F ∈ stationaryPotentialSubspace (μ := μ') (d := d)) :
    transportL2 (HilbertVec d) hT F ∈
      stationaryPotentialSubspace (μ := μ) (d := d) := by
  have hle : stationaryPotentialSubspace (μ := μ') (d := d) ≤
      Submodule.comap (transportL2 (HilbertVec d) hT).toContinuousLinearMap.toLinearMap
        (stationaryPotentialSubspace (μ := μ) (d := d)) := by
    refine (horizontalGradientRange (μ := μ') (d := d)).topologicalClosure_minimal
      (fun G hG ↦ ?_) ?_
    · exact Submodule.le_topologicalClosure _
        (transportL2_mem_horizontalGradientRange hT hTequiv hG)
    · exact (Submodule.isClosed_topologicalClosure _).preimage
        (transportL2 (HilbertVec d) hT).continuous
  exact hle hF

/-! ## Transport of the stationary Helmholtz decomposition -/

/-- The pullback isometry maps the stationary solenoidal subspace of `μ'` into
the stationary solenoidal subspace of `μ`.

The proof tests the pulled-back solenoidal field against the conditional
expectation onto the pullback sigma-field: that conditional expectation carries
each horizontal gradient of `μ` into the range of the pullback isometry, where
the orthogonality is the one already available over `μ'`. -/
theorem transportL2_mem_stationarySolenoidalSubspace (hT : MeasurePreserving T μ μ')
    (hTequiv : ∀ (z : Vec d) (ω : Ω), T (z +ᵥ ω) = z +ᵥ T ω) {G : VectorL2 d μ'}
    (hG : G ∈ stationarySolenoidalSubspace (μ := μ') (d := d)) :
    transportL2 (HilbertVec d) hT G ∈
      stationarySolenoidalSubspace (μ := μ) (d := d) := by
  have hm : mΩ'.comap T ≤ mΩ := hT.measurable.comap_le
  have hinv : IsVAddInvariantSubalgebra d (mΩ'.comap T) :=
    isVAddInvariantSubalgebra_comap T hTequiv
  have hUGfix : condExpL2Proj (HilbertVec d) hm (transportL2 (HilbertVec d) hT G) =
      transportL2 (HilbertVec d) hT G :=
    condExpL2Proj_eq_self hm (aestronglyMeasurable_transportL2 hT G)
  set Λ : VectorL2 d μ →L[ℝ] ℝ :=
    (innerSL ℝ (transportL2 (HilbertVec d) hT G)).comp
      (condExpL2Proj (HilbertVec d) hm) with hΛdef
  have hΛapply : ∀ u : VectorL2 d μ, Λ u =
      inner ℝ (transportL2 (HilbertVec d) hT G)
        (condExpL2Proj (HilbertVec d) hm u) := fun _ ↦ rfl
  have hker : stationaryPotentialSubspace (μ := μ) (d := d) ≤ LinearMap.ker Λ.toLinearMap := by
    refine (horizontalGradientRange (μ := μ) (d := d)).topologicalClosure_minimal ?_
      (ContinuousLinearMap.isClosed_ker Λ)
    rintro H ⟨ψ, hψ⟩
    have hEH := hψ.condExpL2Proj hm hinv
    obtain ⟨ψ', hψ'⟩ := exists_transportL2_eq hT
      (aestronglyMeasurable_condExpL2Proj hm ψ)
    obtain ⟨H', hH'⟩ := exists_transportL2_eq hT
      (aestronglyMeasurable_condExpL2Proj hm H)
    rw [← hψ', ← hH'] at hEH
    have hmemH' : H' ∈ stationaryPotentialSubspace (μ := μ') (d := d) :=
      Submodule.le_topologicalClosure _
        ⟨ψ', hasHorizontalGradient_of_transportL2 hT hTequiv hEH⟩
    show Λ H = 0
    rw [hΛapply, ← hH', (transportL2 (HilbertVec d) hT).inner_map_map, real_inner_comm]
    exact hG H' hmemH'
  intro u hu
  have hΛu : Λ u = 0 := hker hu
  rw [hΛapply, real_inner_comm] at hΛu
  calc inner ℝ u (transportL2 (HilbertVec d) hT G)
      = inner ℝ u (condExpL2Proj (HilbertVec d) hm
          (transportL2 (HilbertVec d) hT G)) := by rw [hUGfix]
    _ = inner ℝ (condExpL2Proj (HilbertVec d) hm u)
          (transportL2 (HilbertVec d) hT G) :=
        (inner_condExpL2Proj_left_eq_right hm u _).symm
    _ = 0 := hΛu

/-- **The transport identity.** The stationary potential projection commutes
with composition along a measure-preserving equivariant map: `(proj F) ∘ T` is
the stationary potential projection of `F ∘ T`. -/
theorem transportL2_stationaryPotentialProjection (hT : MeasurePreserving T μ μ')
    (hTequiv : ∀ (z : Vec d) (ω : Ω), T (z +ᵥ ω) = z +ᵥ T ω) (F : VectorL2 d μ') :
    transportL2 (HilbertVec d) hT (stationaryPotentialProjection (μ := μ') F) =
      stationaryPotentialProjection (μ := μ)
        (transportL2 (HilbertVec d) hT F) := by
  refine eq_stationaryPotentialProjection_of_mem_of_sub_mem_orthogonal
    (transportL2_mem_stationaryPotentialSubspace hT hTequiv
      (stationaryPotentialProjection_mem F)) ?_
  have hsub : transportL2 (HilbertVec d) hT F -
        transportL2 (HilbertVec d) hT (stationaryPotentialProjection (μ := μ') F) =
      transportL2 (HilbertVec d) hT
        (F - stationaryPotentialProjection (μ := μ') F) :=
    ((transportL2 (HilbertVec d) hT).toLinearMap.map_sub _ _).symm
  rw [hsub]
  exact transportL2_mem_stationarySolenoidalSubspace hT hTequiv
    (sub_stationaryPotentialProjection_mem_orthogonal F)

/-- The pulled-back forcing has exactly the same response energy. -/
theorem norm_stationaryPotentialProjection_transportL2
    (hT : MeasurePreserving T μ μ')
    (hTequiv : ∀ (z : Vec d) (ω : Ω), T (z +ᵥ ω) = z +ᵥ T ω) (F : VectorL2 d μ') :
    ‖stationaryPotentialProjection (μ := μ)
        (transportL2 (HilbertVec d) hT F)‖ =
      ‖stationaryPotentialProjection (μ := μ') F‖ := by
  rw [← transportL2_stationaryPotentialProjection hT hTequiv]
  exact norm_transportL2 hT _

end

end SuperdiffusionCLT.Probability.Stationary
