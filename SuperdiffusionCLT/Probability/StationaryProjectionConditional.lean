/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import SuperdiffusionCLT.Probability.StationaryProjection

/-!
# Conditional expectation and the stationary potential projection

This file relates the stationary potential projection built in
`StationaryProjection.lean` to the `L²` conditional expectation onto a
*translation-invariant* sub-sigma-field.

The `L²` conditional expectation is the orthogonal projection onto the closed
subspace `MeasureTheory.lpMeas` of square-integrable functions with an almost
everywhere `m`-measurable representative. Mathlib's `MeasureTheory.condExpL2`
takes values in that subspace; `condExpL2Proj` is the same operator with values
in the whole of `Lp E 2 μ`, which is the form needed to compose it with the
Koopman operators of the translations and with the coordinate maps of
`VectorL2`.

## Main results

* `koopmanEquiv`: a fixed translation acts on `Lp E 2 μ` as a linear isometry
  *equivalence*, whose inverse is the translation by the opposite vector.
* `condExpL2Proj_koopman`: the conditional expectation onto a translation
  invariant sub-sigma-field commutes with every Koopman operator.
* `HasHorizontalGradient.condExpL2Proj`: the conditional expectation of a
  horizontal gradient is the horizontal gradient of the conditional expectation
  of the potential.
* `condExpL2Proj_mem_stationaryPotentialSubspace` and
  `condExpL2Proj_mem_stationarySolenoidalSubspace`: the conditional expectation
  preserves both summands of the stationary Helmholtz decomposition.
* `condExpL2Proj_stationaryPotentialProjection`: the stationary potential
  projection of an `m`-measurable field is again `m`-measurable.
-/

@[expose] public section

open MeasureTheory
open Homogenization

namespace SuperdiffusionCLT.Probability.Stationary

noncomputable section

/-! ## A general commutation rule for orthogonal projections -/

/-- Orthogonal projection onto a closed subspace commutes with every isometric
automorphism of the ambient Hilbert space that preserves the subspace in both
directions. -/
private theorem starProjection_linearIsometryEquiv {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    (U : H ≃ₗᵢ[ℝ] H) (hU : ∀ v ∈ K, U v ∈ K) (hU' : ∀ v ∈ K, U.symm v ∈ K) (x : H) :
    U (K.starProjection x) = K.starProjection (U x) := by
  refine (Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (hU _ (K.starProjection_apply_mem x)) ?_).symm
  intro w hw
  have hsub : U x - U (K.starProjection x) = U (x - K.starProjection x) :=
    (U.map_sub _ _).symm
  rw [hsub]
  have hmap : inner ℝ (U (x - K.starProjection x)) w
      = inner ℝ (x - K.starProjection x) (U.symm w) := by
    conv_lhs => rw [← U.apply_symm_apply w]
    exact U.inner_map_map _ _
  rw [hmap]
  exact Submodule.starProjection_inner_eq_zero x (U.symm w) (hU' w hw)

variable {d : ℕ} {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ## The `L²` conditional expectation as an operator on `Lp E 2 μ` -/

section CondExpBasic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable (E) in
/-- The `L²` conditional expectation with respect to a sub-sigma-field `m`,
presented as an operator of `Lp E 2 μ` into itself: the orthogonal projection
onto the closed subspace `MeasureTheory.lpMeas` of the elements with an almost
everywhere `m`-measurable representative.

This is `MeasureTheory.condExpL2` followed by the inclusion of `lpMeas`; the
self-map presentation is what allows the operator to be composed with the
Koopman operators and with the coordinate maps of `VectorL2`. -/
def condExpL2Proj (hm : m ≤ mΩ) : Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  haveI : Fact (m ≤ mΩ) := ⟨hm⟩
  (lpMeas E ℝ m 2 μ).starProjection

theorem condExpL2Proj_mem_lpMeas (hm : m ≤ mΩ) (f : Lp E 2 μ) :
    condExpL2Proj E hm f ∈ lpMeas E ℝ m 2 μ := by
  have : Fact (m ≤ mΩ) := ⟨hm⟩
  exact Submodule.starProjection_apply_mem _ f

theorem aestronglyMeasurable_condExpL2Proj (hm : m ≤ mΩ) (f : Lp E 2 μ) :
    AEStronglyMeasurable[m] (condExpL2Proj E hm f : Ω → E) μ :=
  mem_lpMeas_iff_aestronglyMeasurable.mp (condExpL2Proj_mem_lpMeas hm f)

theorem condExpL2Proj_eq_self_iff (hm : m ≤ mΩ) {f : Lp E 2 μ} :
    condExpL2Proj E hm f = f ↔ AEStronglyMeasurable[m] (f : Ω → E) μ := by
  have : Fact (m ≤ mΩ) := ⟨hm⟩
  rw [condExpL2Proj, Submodule.starProjection_eq_self_iff,
    mem_lpMeas_iff_aestronglyMeasurable]

theorem condExpL2Proj_eq_self (hm : m ≤ mΩ) {f : Lp E 2 μ}
    (hf : AEStronglyMeasurable[m] (f : Ω → E) μ) : condExpL2Proj E hm f = f :=
  (condExpL2Proj_eq_self_iff hm).mpr hf

/-- The `L²` conditional expectation operator is self-adjoint. -/
theorem inner_condExpL2Proj_left_eq_right (hm : m ≤ mΩ) (f g : Lp E 2 μ) :
    inner ℝ (condExpL2Proj E hm f) g = inner ℝ f (condExpL2Proj E hm g) := by
  have : Fact (m ≤ mΩ) := ⟨hm⟩
  exact Submodule.inner_starProjection_left_eq_right _ f g

end CondExpBasic

/-! ## Coordinates of a vector-valued conditional expectation -/

/-- The conditional expectation acts coordinatewise on vector-valued fields. -/
theorem vectorL2Coord_condExpL2Proj (hm : m ≤ mΩ) (i : Fin d) (F : VectorL2 d μ) :
    vectorL2Coord (μ := μ) i (condExpL2Proj (HilbertVec d) hm F) =
      condExpL2Proj ℝ hm (vectorL2Coord (μ := μ) i F) :=
  (Lp.ext (condExpL2_comp_continuousLinearMap (μ := μ) ℝ ℝ hm
    (PiLp.proj (p := 2) (β := fun _ : Fin d ↦ ℝ) i) F)).symm

/-! ## Translation-invariant sub-sigma-fields -/

section Invariant

variable [AddAction (Vec d) Ω]

variable (d) in
/-- A sigma-field `m` on `Ω` is translation invariant when the preimage of every
`m`-measurable set under every translation is again `m`-measurable. No relation
to an ambient sigma-field is part of this definition; consumers that need one
supply `m ≤ mΩ` separately. -/
def IsVAddInvariantSubalgebra (m : MeasurableSpace Ω) : Prop :=
  ∀ (z : Vec d) ⦃s : Set Ω⦄, MeasurableSet[m] s → MeasurableSet[m] ((z +ᵥ ·) ⁻¹' s)

theorem IsVAddInvariantSubalgebra.measurable
    (hinv : IsVAddInvariantSubalgebra d m) (z : Vec d) :
    Measurable[m, m] (fun ω : Ω ↦ z +ᵥ ω) :=
  fun _ hs ↦ hinv z hs

end Invariant

variable [AddAction (Vec d) Ω]
variable [MeasurableConstVAdd (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ]

/-! ## Koopman operators as isometric equivalences -/

section Koopman

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem koopman_zero (f : Lp E 2 μ) : koopman (μ := μ) (0 : Vec d) f = f := by
  refine Lp.ext ?_
  refine (Lp.coeFn_compMeasurePreserving (E := E) f
    (measurePreserving_const_vadd (μ := μ) (0 : Vec d))).trans ?_
  filter_upwards with ω
  simp

/-- Translating by `x` after translating by `y` is translating by `y + x`. -/
theorem koopman_koopman (x y : Vec d) (f : Lp E 2 μ) :
    koopman (μ := μ) x (koopman (μ := μ) y f) = koopman (μ := μ) (y + x) f := by
  refine Lp.ext ?_
  have h1 : (koopman (μ := μ) x (koopman (μ := μ) y f) : Ω → E)
      =ᵐ[μ] (koopman (μ := μ) y f : Ω → E) ∘ (x +ᵥ ·) :=
    Lp.coeFn_compMeasurePreserving _ _
  have h2 : (koopman (μ := μ) y f : Ω → E) =ᵐ[μ] (f : Ω → E) ∘ (y +ᵥ ·) :=
    Lp.coeFn_compMeasurePreserving _ _
  have hmp := measurePreserving_const_vadd (μ := μ) (Ω := Ω) x
  have h3 : ((koopman (μ := μ) y f : Ω → E) ∘ (x +ᵥ ·))
      =ᵐ[μ] (((f : Ω → E) ∘ (y +ᵥ ·)) ∘ (x +ᵥ ·)) := by
    refine ae_eq_comp hmp.measurable.aemeasurable ?_
    rw [hmp.map_eq]
    exact h2
  have h4 : (koopman (μ := μ) (y + x) f : Ω → E) =ᵐ[μ] (f : Ω → E) ∘ ((y + x) +ᵥ ·) :=
    Lp.coeFn_compMeasurePreserving _ _
  have heq : (((f : Ω → E) ∘ (y +ᵥ ·)) ∘ (x +ᵥ ·)) = (f : Ω → E) ∘ ((y + x) +ᵥ ·) := by
    funext ω
    simp only [Function.comp_apply, add_vadd]
  refine (h1.trans h3).trans ?_
  rw [heq]
  exact h4.symm

/-- The Koopman operator of a fixed translation, as a linear isometry
equivalence of `Lp E 2 μ`. Its inverse is the Koopman operator of the opposite
translation. -/
def koopmanEquiv (x : Vec d) : Lp E 2 μ ≃ₗᵢ[ℝ] Lp E 2 μ where
  toFun := koopman (μ := μ) x
  map_add' := (koopman (μ := μ) (E := E) x).map_add
  map_smul' := (koopman (μ := μ) (E := E) x).map_smul
  invFun := koopman (μ := μ) (-x)
  left_inv f := by
    rw [koopman_koopman, add_neg_cancel, koopman_zero]
  right_inv f := by
    rw [koopman_koopman, neg_add_cancel, koopman_zero]
  norm_map' := (koopman (μ := μ) (E := E) x).norm_map

@[simp] theorem koopmanEquiv_apply (x : Vec d) (f : Lp E 2 μ) :
    koopmanEquiv (μ := μ) x f = koopman (μ := μ) x f := rfl

@[simp] theorem koopmanEquiv_symm_apply (x : Vec d) (f : Lp E 2 μ) :
    (koopmanEquiv (μ := μ) (E := E) x).symm f = koopman (μ := μ) (-x) f := rfl

/-- A translation-invariant sub-sigma-field has a Koopman-invariant `lpMeas`
subspace. -/
theorem koopman_mem_lpMeas (hinv : IsVAddInvariantSubalgebra d m) (z : Vec d)
    {f : Lp E 2 μ} (hf : f ∈ lpMeas E ℝ m 2 μ) :
    koopman (μ := μ) z f ∈ lpMeas E ℝ m 2 μ := by
  rw [mem_lpMeas_iff_aestronglyMeasurable] at hf ⊢
  have hmp := measurePreserving_const_vadd (μ := μ) (Ω := Ω) z
  refine ⟨hf.mk (f : Ω → E) ∘ (fun ω : Ω ↦ z +ᵥ ω),
    (hf.stronglyMeasurable_mk).comp_measurable (hinv.measurable z), ?_⟩
  refine (Lp.coeFn_compMeasurePreserving (E := E) f hmp).trans ?_
  refine ae_eq_comp hmp.measurable.aemeasurable ?_
  rw [hmp.map_eq]
  exact hf.ae_eq_mk

end Koopman

/-! ## Commutation of the conditional expectation with the translations -/

section CondExpKoopman

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Conditional expectation commutes with the translations.** For a
translation-invariant sub-sigma-field, the `L²` conditional expectation of a
translated field is the translate of its conditional expectation. -/
theorem condExpL2Proj_koopman (hm : m ≤ mΩ) (hinv : IsVAddInvariantSubalgebra d m)
    (z : Vec d) (f : Lp E 2 μ) :
    condExpL2Proj E hm (koopman (μ := μ) z f) =
      koopman (μ := μ) z (condExpL2Proj E hm f) := by
  have : Fact (m ≤ mΩ) := ⟨hm⟩
  exact (starProjection_linearIsometryEquiv (lpMeas E ℝ m 2 μ)
    (koopmanEquiv (μ := μ) z) (fun _ hv ↦ koopman_mem_lpMeas hinv z hv)
    (fun _ hv ↦ koopman_mem_lpMeas hinv (-z) hv) f).symm

end CondExpKoopman

/-! ## Preservation of the stationary Helmholtz summands -/

section Helmholtz

/-- The conditional expectation of a horizontal gradient is the horizontal
gradient of the conditional expectation of the potential. -/
theorem HasHorizontalGradient.condExpL2Proj (hm : m ≤ mΩ)
    (hinv : IsVAddInvariantSubalgebra d m) {φ : ScalarL2 μ} {F : VectorL2 d μ}
    (h : HasHorizontalGradient (μ := μ) φ F) :
    HasHorizontalGradient (μ := μ)
      (Stationary.condExpL2Proj ℝ hm φ)
      (Stationary.condExpL2Proj (HilbertVec d) hm F) := by
  intro i
  have hd : HasDerivAt
      ((Stationary.condExpL2Proj (μ := μ) ℝ hm) ∘
        fun t : ℝ ↦ koopman (μ := μ) (t • (Pi.single i 1 : Vec d)) φ)
      (Stationary.condExpL2Proj ℝ hm (vectorL2Coord (μ := μ) i F)) 0 :=
    HasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (ContinuousLinearMap.hasFDerivAt (Stationary.condExpL2Proj (μ := μ) ℝ hm)) (h i)
  have hfun : ((Stationary.condExpL2Proj (μ := μ) ℝ hm) ∘
        fun t : ℝ ↦ koopman (μ := μ) (t • (Pi.single i 1 : Vec d)) φ) =
      fun t : ℝ ↦ koopman (μ := μ) (t • (Pi.single i 1 : Vec d))
        (Stationary.condExpL2Proj ℝ hm φ) := by
    funext t
    exact condExpL2Proj_koopman hm hinv _ φ
  rw [hfun] at hd
  rw [vectorL2Coord_condExpL2Proj]
  exact hd

theorem condExpL2Proj_mem_horizontalGradientRange (hm : m ≤ mΩ)
    (hinv : IsVAddInvariantSubalgebra d m) {F : VectorL2 d μ}
    (hF : F ∈ horizontalGradientRange (μ := μ) (d := d)) :
    condExpL2Proj (HilbertVec d) hm F ∈ horizontalGradientRange (μ := μ) (d := d) := by
  obtain ⟨φ, hφ⟩ := hF
  exact ⟨condExpL2Proj ℝ hm φ, hφ.condExpL2Proj hm hinv⟩

/-- The conditional expectation preserves the closed stationary potential
subspace. -/
theorem condExpL2Proj_mem_stationaryPotentialSubspace (hm : m ≤ mΩ)
    (hinv : IsVAddInvariantSubalgebra d m) {F : VectorL2 d μ}
    (hF : F ∈ stationaryPotentialSubspace (μ := μ) (d := d)) :
    condExpL2Proj (HilbertVec d) hm F ∈
      stationaryPotentialSubspace (μ := μ) (d := d) := by
  have hle :
      stationaryPotentialSubspace (μ := μ) (d := d) ≤
        Submodule.comap (condExpL2Proj (μ := μ) (HilbertVec d) hm).toLinearMap
          (stationaryPotentialSubspace (μ := μ) (d := d)) := by
    refine (horizontalGradientRange (μ := μ) (d := d)).topologicalClosure_minimal
      (fun G hG ↦ ?_) ?_
    · exact Submodule.le_topologicalClosure _
        (condExpL2Proj_mem_horizontalGradientRange hm hinv hG)
    · exact (Submodule.isClosed_topologicalClosure _).preimage
        (condExpL2Proj (HilbertVec d) hm).continuous
  exact hle hF

/-- The conditional expectation preserves the stationary solenoidal subspace,
because it is a self-adjoint operator preserving the potential subspace. -/
theorem condExpL2Proj_mem_stationarySolenoidalSubspace (hm : m ≤ mΩ)
    (hinv : IsVAddInvariantSubalgebra d m) {G : VectorL2 d μ}
    (hG : G ∈ stationarySolenoidalSubspace (μ := μ) (d := d)) :
    condExpL2Proj (HilbertVec d) hm G ∈
      stationarySolenoidalSubspace (μ := μ) (d := d) := by
  intro q hq
  rw [← inner_condExpL2Proj_left_eq_right hm q G]
  exact hG _ (condExpL2Proj_mem_stationaryPotentialSubspace hm hinv hq)

/-- **The stationary potential projection of an `m`-measurable field is
`m`-measurable.** This is the uniqueness statement
`eq_stationaryPotentialProjection_of_mem_of_sub_mem_orthogonal` applied to the
conditional expectation of the projection. -/
theorem condExpL2Proj_stationaryPotentialProjection (hm : m ≤ mΩ)
    (hinv : IsVAddInvariantSubalgebra d m) {F : VectorL2 d μ}
    (hF : condExpL2Proj (HilbertVec d) hm F = F) :
    condExpL2Proj (HilbertVec d) hm (stationaryPotentialProjection (μ := μ) F) =
      stationaryPotentialProjection (μ := μ) F := by
  have hq : condExpL2Proj (HilbertVec d) hm (stationaryPotentialProjection (μ := μ) F) ∈
      stationaryPotentialSubspace (μ := μ) (d := d) :=
    condExpL2Proj_mem_stationaryPotentialSubspace hm hinv
      (stationaryPotentialProjection_mem F)
  have hsub : F - condExpL2Proj (HilbertVec d) hm
        (stationaryPotentialProjection (μ := μ) F) =
      condExpL2Proj (HilbertVec d) hm
        (F - stationaryPotentialProjection (μ := μ) F) := by
    rw [map_sub, hF]
  have hFq : F - condExpL2Proj (HilbertVec d) hm
      (stationaryPotentialProjection (μ := μ) F) ∈
      stationarySolenoidalSubspace (μ := μ) (d := d) := by
    rw [hsub]
    exact condExpL2Proj_mem_stationarySolenoidalSubspace hm hinv
      (sub_stationaryPotentialProjection_mem_orthogonal F)
  exact eq_stationaryPotentialProjection_of_mem_of_sub_mem_orthogonal hq hFq

/-- The measurability form of `condExpL2Proj_stationaryPotentialProjection`. -/
theorem aestronglyMeasurable_stationaryPotentialProjection (hm : m ≤ mΩ)
    (hinv : IsVAddInvariantSubalgebra d m) {F : VectorL2 d μ}
    (hF : AEStronglyMeasurable[m] (F : Ω → HilbertVec d) μ) :
    AEStronglyMeasurable[m]
      (stationaryPotentialProjection (μ := μ) F : Ω → HilbertVec d) μ :=
  (condExpL2Proj_eq_self_iff hm).mp
    (condExpL2Proj_stationaryPotentialProjection hm hinv
      ((condExpL2Proj_eq_self_iff hm).mpr hF))

end Helmholtz

end

end SuperdiffusionCLT.Probability.Stationary
