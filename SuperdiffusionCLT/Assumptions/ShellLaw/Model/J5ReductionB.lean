/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.J5DilationB

/-!
# J5 for the product law from a constant seed energy

If the stationary response energy of the seed law, for the forcing `j ↦ j(0) e`, is one and the
same positive number `q` for every unit direction `e`, then the product law of the seed satisfies
the non-degeneracy condition J5 with `cStar = q / log 3` and `K = 1`. The energy of the block
`(n, m]` is exactly `(m - n) q`, so the deviation from `cStar log 3 (m - n)` vanishes.

* `nv_shellLawJ5_productLaw_of_energy`: the assembly.

The second half proves that the energy does not depend on the unit direction `e`, for a law that
is invariant under the sign flips and the transpositions of the coordinates. For such a matrix `R`
(symmetric, `R * R = 1`) the pullback of vector fields by the rotation of the shell field, followed
by the pointwise action of `R`, is an involutive isometry of the vector-valued `L²` space that maps
horizontal gradients to horizontal gradients (the rotation intertwines the translation by `z` with
the translation by `R z`, and `R` maps axes to signed axes). Hence it commutes with the stationary
potential projection and carries the forcing in direction `e` to the forcing in direction `R e`.
Flips make the projected forcings of the coordinate directions orthogonal, transpositions make them
equinorm.

* `nv_stationaryPotentialProjection_Wmap`: the projection commutes with the conjugation.
* `nv_shellEnergy_const_of_symmetric`: the energy is independent of the unit direction.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Probability.Stationary
open SuperdiffusionCLT.Section2.Cutoff
open scoped InnerProductSpace Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

theorem nv_log_three_pos : 0 < Real.log 3 :=
  Real.log_pos (by norm_num)

/-- **J5 for the product law from a constant seed energy.** -/
theorem nv_shellLawJ5_productLaw_of_energy (hd : 2 ≤ d)
    (ν₀ : ProbabilityMeasure (ShellField d))
    (hν : ∀ z : Vec d, Measure.map (ShellField.translate z) ν₀.toMeasure = ν₀.toMeasure)
    (hJ3 : ShellLawJ3 d (nv_productLaw ν₀)) (q : ℝ) (hq : 0 < q)
    (hE : ∀ (e : Vec d) (he : Book.Ch02.vecNorm e = 1),
      nv_shellEnergy ν₀.toMeasure hν e (nv_memLp_fieldForcing_seed ν₀ hJ3 e he) = q) :
    ShellLawJ5 d (nv_productLaw ν₀) (q / Real.log 3) 1
      (nv_shellLawPrefix_productLaw hd ν₀ hν) (nv_shellLawJ2_productLaw ν₀) hJ3 where
  cStar_pos := div_pos hq nv_log_three_pos
  K_pos := one_pos
  nondegenerate n m _ e he := by
    rw [nv_norm_sq_blockPotentialResponse_productLaw hd ν₀ hν hJ3 n m e he, hE e he]
    have h : ((m - n : ℕ) : ℝ) * q - q / Real.log 3 * Real.log 3 * ((m - n : ℕ) : ℝ) = 0 := by
      rw [div_mul_cancel₀ _ nv_log_three_pos.ne']
      ring
    rw [h, abs_zero]
    exact zero_le_one

/-! ## Conjugation of the response by signed permutations -/

theorem nv_matVecMul_involution (R : Mat d) (hRR : R * R = 1) (x : Vec d) :
    matVecMul R (matVecMul R x) = x := by
  rw [matVecMul_mul, hRR]
  ext i
  simp [matVecMul, Matrix.one_apply]

/-- A symmetric signed permutation intertwines the translation by `z` with the translation by
`R z`. -/
theorem nv_rotate_translate (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (_hS : matTranspose R = R) (hRR : R * R = 1) (z : Vec d) (j : ShellField d) :
    ShellField.rotate R hR (ShellField.translate z j) =
      ShellField.translate (matVecMul R z) (ShellField.rotate R hR j) := by
  refine ShellField.ext fun x ↦ ?_
  simp only [ShellField.rotate_apply, ShellField.translate_apply, matVecMul_add]
  rw [nv_matVecMul_involution R hRR z]

theorem nv_rotate_rotate (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (hS : matTranspose R = R) (hRR : R * R = 1) (j : ShellField d) :
    ShellField.rotate R hR (ShellField.rotate R hR j) = j := by
  refine ShellField.ext fun x ↦ ?_
  simp only [ShellField.rotate_apply, hS, nv_matVecMul_involution R hRR]
  simp only [Matrix.mul_assoc, hRR, Matrix.mul_one]
  rw [← Matrix.mul_assoc, hRR, Matrix.one_mul]

/-- The pointwise action of a matrix on the Hilbert carrier of vectors. -/
def nv_Rmap (R : Mat d) : HilbertVec d →L[ℝ] HilbertVec d :=
  Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) R

theorem nv_Rmap_apply (R : Mat d) (x : HilbertVec d) (a : Fin d) :
    nv_Rmap R x a = ∑ b, R a b * x b := by
  simp [nv_Rmap, Matrix.mulVec, dotProduct]

theorem nv_Rmap_apply_perm (R : Mat d) (σ : Equiv.Perm (Fin d)) (s : Fin d → ℝ)
    (hRdef : ∀ i j, R i j = if i = σ j then s j else 0) (x : HilbertVec d) (b : Fin d) :
    nv_Rmap R x (σ b) = s b * x b := by
  rw [nv_Rmap_apply, Finset.sum_eq_single b]
  · simp [hRdef]
  · intro c _ hcb
    simp [hRdef, σ.injective.eq_iff, hcb.symm]
  · simp

theorem nv_norm_Rmap (R : Mat d) (hR : IsSignedPermutationMatrix R) (x : HilbertVec d) :
    ‖nv_Rmap R x‖ = ‖x‖ := by
  obtain ⟨σ, s, hs, hRdef⟩ := hR
  have hsq : ∀ b, (s b * x b) ^ 2 = x b ^ 2 := fun b ↦ by
    rcases hs b with h | h <;> simp [h]
  have h1 : ‖nv_Rmap R x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, nv_Rmap_apply_perm R σ s hRdef x b,
      hsq]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

section Lp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)

/-- The pointwise action of a signed permutation matrix on vector-valued `L²` classes, as a
linear isometry. -/
def nv_Smap (R : Mat d) (hR : IsSignedPermutationMatrix R) : VectorL2 d μ →ₗᵢ[ℝ] VectorL2 d μ where
  toLinearMap := ((nv_Rmap R).compLpL 2 μ).toLinearMap
  norm_map' F := by
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    refine eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable ((nv_Rmap R).compLpL 2 μ F))
      (Lp.aestronglyMeasurable F) ?_
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (nv_Rmap R) F] with ω hω
    change ‖((nv_Rmap R).compLpL 2 μ F : Ω → HilbertVec d) ω‖ = ‖(F : Ω → HilbertVec d) ω‖
    rw [hω]
    exact nv_norm_Rmap R hR _

theorem nv_coeFn_Smap (R : Mat d) (hR : IsSignedPermutationMatrix R) (F : VectorL2 d μ) :
    (nv_Smap μ R hR F : Ω → HilbertVec d) =ᵐ[μ] fun ω ↦ nv_Rmap R ((F : Ω → HilbertVec d) ω) :=
  ContinuousLinearMap.coeFn_compLpL (nv_Rmap R) F

end Lp

section Koopman

variable (ν : Measure (ShellField d)) [VAddInvariantMeasure (Vec d) (ShellField d) ν]

/-- Pullback along a measure-preserving map that rescales translations by a linear map commutes
with the Koopman operators up to that linear map. -/
theorem nv_transportL2_koopman_twist {T : ShellField d → ShellField d}
    (hT : MeasurePreserving T ν ν) (A : Vec d → Vec d)
    (hTequiv : ∀ (z : Vec d) (ω : ShellField d), T (z +ᵥ ω) = A z +ᵥ T ω) (z : Vec d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Lp E 2 ν) :
    transportL2 E hT (koopman (μ := ν) (A z) f) = koopman (μ := ν) z (transportL2 E hT f) := by
  refine Lp.ext ?_
  have hvadd := measurePreserving_const_vadd (μ := ν) (Ω := ShellField d) z
  have h1 : (transportL2 E hT (koopman (μ := ν) (A z) f) : ShellField d → E)
      =ᵐ[ν] (koopman (μ := ν) (A z) f : ShellField d → E) ∘ T := coeFn_transportL2 hT _
  have h2 : ((koopman (μ := ν) (A z) f : ShellField d → E) ∘ T)
      =ᵐ[ν] (((f : ShellField d → E) ∘ fun ω ↦ A z +ᵥ ω) ∘ T) := by
    refine ae_eq_comp hT.measurable.aemeasurable ?_
    rw [hT.map_eq]
    exact Lp.coeFn_compMeasurePreserving _ _
  have h3 : (koopman (μ := ν) z (transportL2 E hT f) : ShellField d → E)
      =ᵐ[ν] (transportL2 E hT f : ShellField d → E) ∘ fun ω ↦ z +ᵥ ω :=
    Lp.coeFn_compMeasurePreserving _ _
  have h4 : ((transportL2 E hT f : ShellField d → E) ∘ fun ω ↦ z +ᵥ ω)
      =ᵐ[ν] (((f : ShellField d → E) ∘ T) ∘ fun ω ↦ z +ᵥ ω) := by
    refine ae_eq_comp hvadd.measurable.aemeasurable ?_
    rw [hvadd.map_eq]
    exact coeFn_transportL2 hT f
  have heq : (((f : ShellField d → E) ∘ fun ω ↦ A z +ᵥ ω) ∘ T)
      = (((f : ShellField d → E) ∘ T) ∘ fun ω ↦ z +ᵥ ω) := by
    funext ω
    simp only [Function.comp_apply, hTequiv z ω]
  refine (h1.trans h2).trans ?_
  rw [heq]
  exact (h4.symm.trans h3.symm)

theorem nv_Rmap_apply_symm (R : Mat d) (hS : matTranspose R = R) (σ : Equiv.Perm (Fin d))
    (s : Fin d → ℝ) (hRdef : ∀ i j, R i j = if i = σ j then s j else 0) (x : HilbertVec d)
    (a : Fin d) : nv_Rmap R x a = s a * x (σ a) := by
  have hsym : ∀ i j, R i j = R j i := fun i j ↦ by
    exact (congrFun (congrFun hS i) j).symm
  rw [nv_Rmap_apply, Finset.sum_eq_single (σ a)]
  · rw [hsym, hRdef]
    simp
  · intro c _ hca
    rw [hsym, hRdef]
    simp [hca]
  · simp

theorem nv_matVecMul_single (R : Mat d) (σ : Equiv.Perm (Fin d))
    (s : Fin d → ℝ) (hRdef : ∀ i j, R i j = if i = σ j then s j else 0) (a : Fin d) (t : ℝ) :
    matVecMul R (t • (Pi.single a 1 : Vec d)) = (s a * t) • (Pi.single (σ a) 1 : Vec d) := by
  ext i
  simp only [matVecMul, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single a]
  · by_cases hi : i = σ a
    · subst hi
      simp [hRdef]
    · simp [hRdef, hi, Pi.single_eq_of_ne]
  · intro c _ hca
    simp [Pi.single_eq_of_ne hca]
  · simp

/-- The map on vector fields that conjugates a gradient by a signed permutation: pull back by the
rotation of the shell field, then apply the matrix pointwise. -/
def nv_Wmap (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (hρ : MeasurePreserving (ShellField.rotate R hR) ν ν) : VectorL2 d ν →ₗᵢ[ℝ] VectorL2 d ν :=
  (nv_Smap ν R hR).comp (transportL2 (HilbertVec d) hρ)

theorem nv_hasHorizontalGradient_Wmap (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (hS : matTranspose R = R) (hRR : R * R = 1)
    (hρ : MeasurePreserving (ShellField.rotate R hR) ν ν) {φ : ScalarL2 ν} {F : VectorL2 d ν}
    (h : HasHorizontalGradient (μ := ν) φ F) :
    HasHorizontalGradient (μ := ν) (transportL2 ℝ hρ φ) (nv_Wmap ν R hR hρ F) := by
  obtain ⟨σ, s, hs, hRdef⟩ := id hR
  intro a
  have hsne : s a ≠ 0 := by
    rcases hs a with h1 | h1 <;> simp [h1]
  have hequiv : ∀ (z : Vec d) (ω : ShellField d),
      ShellField.rotate R hR (z +ᵥ ω) = matVecMul R z +ᵥ ShellField.rotate R hR ω :=
    fun z ω ↦ nv_rotate_translate R hR hS hRR z ω
  have hb := h (σ a)
  have hresc := (nv_hasDerivAt_rescale (c := s a) hsne _ _).1 hb
  have hU := ((transportL2 ℝ hρ).toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hresc
  have hcurve : ((transportL2 ℝ hρ).toContinuousLinearMap ∘ fun t : ℝ ↦
        koopman (μ := ν) ((s a * t) • (Pi.single (σ a) 1 : Vec d)) φ) =
      fun t : ℝ ↦ koopman (μ := ν) (t • (Pi.single a 1 : Vec d)) (transportL2 ℝ hρ φ) := by
    funext t
    rw [Function.comp_apply]
    change transportL2 ℝ hρ (koopman (μ := ν) ((s a * t) • (Pi.single (σ a) 1 : Vec d)) φ) = _
    rw [← nv_matVecMul_single R σ s hRdef a t]
    exact nv_transportL2_koopman_twist ν hρ (matVecMul R) hequiv _ φ
  rw [hcurve] at hU
  convert hU using 1
  -- the coordinate of the transformed field
  refine Lp.ext ?_
  have c1 : (vectorL2Coord (μ := ν) a (nv_Wmap ν R hR hρ F) : ShellField d → ℝ) =ᵐ[ν]
      fun ω ↦ ((nv_Wmap ν R hR hρ F : VectorL2 d ν) : ShellField d → HilbertVec d) ω a :=
    ContinuousLinearMap.coeFn_compLpL _ _
  have c2 := nv_coeFn_Smap ν R hR (transportL2 (HilbertVec d) hρ F)
  have c3 := coeFn_transportL2 (μ := ν) hρ F
  have c4 := coeFn_transportL2 (μ := ν) hρ (s a • vectorL2Coord (μ := ν) (σ a) F)
  have c5 := Lp.coeFn_smul (s a) (vectorL2Coord (μ := ν) (σ a) F)
  have c6 : (vectorL2Coord (μ := ν) (σ a) F : ShellField d → ℝ) =ᵐ[ν]
      fun ω ↦ (F : ShellField d → HilbertVec d) ω (σ a) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  have c5' : ((s a • vectorL2Coord (μ := ν) (σ a) F : ScalarL2 ν) : ShellField d → ℝ) =ᵐ[ν]
      fun ω ↦ s a * (F : ShellField d → HilbertVec d) ω (σ a) := by
    filter_upwards [c5, c6] with ω h5 h6
    rw [h5, Pi.smul_apply, h6, smul_eq_mul]
  have c7 : ((s a • vectorL2Coord (μ := ν) (σ a) F : ScalarL2 ν) ∘ ShellField.rotate R hR) =ᵐ[ν]
      fun ω ↦ s a * (F : ShellField d → HilbertVec d) (ShellField.rotate R hR ω) (σ a) := by
    have := (hρ.quasiMeasurePreserving.ae_eq_comp c5')
    exact this
  filter_upwards [c1, c2, c3, c4, c7] with ω h1 h2 h3 h4 h7
  have h2' : (nv_Wmap ν R hR hρ F : ShellField d → HilbertVec d) ω =
      nv_Rmap R ((transportL2 (HilbertVec d) hρ F : ShellField d → HilbertVec d) ω) := h2
  show _ = ((transportL2 ℝ hρ (s a • vectorL2Coord (μ := ν) (σ a) F) : ScalarL2 ν) :
    ShellField d → ℝ) ω
  rw [h1, h2', h3, h4]
  simp only [Function.comp_apply] at h7 ⊢
  rw [h7]
  exact nv_Rmap_apply_symm R hS σ s hRdef _ a

theorem nv_Rmap_Rmap (R : Mat d) (hRR : R * R = 1) (x : HilbertVec d) :
    nv_Rmap R (nv_Rmap R x) = x := by
  have h : nv_Rmap R * nv_Rmap R = 1 := by
    unfold nv_Rmap
    rw [← map_mul, hRR, map_one]
  exact congrArg (fun L : HilbertVec d →L[ℝ] HilbertVec d ↦ L x) h

omit [VAddInvariantMeasure (Vec d) (ShellField d) ν] in
theorem nv_coeFn_Wmap (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (hρ : MeasurePreserving (ShellField.rotate R hR) ν ν) (G : VectorL2 d ν) :
    (nv_Wmap ν R hR hρ G : ShellField d → HilbertVec d) =ᵐ[ν]
      fun ω ↦ nv_Rmap R ((G : ShellField d → HilbertVec d) (ShellField.rotate R hR ω)) := by
  have c2 := nv_coeFn_Smap ν R hR (transportL2 (HilbertVec d) hρ G)
  have c3 := coeFn_transportL2 (μ := ν) hρ G
  filter_upwards [c2, c3] with ω h2 h3
  have h2' : (nv_Wmap ν R hR hρ G : ShellField d → HilbertVec d) ω =
      nv_Rmap R ((transportL2 (HilbertVec d) hρ G : ShellField d → HilbertVec d) ω) := h2
  rw [h2', h3]
  rfl

omit [VAddInvariantMeasure (Vec d) (ShellField d) ν] in
/-- The map `nv_Wmap` is an involution. -/
theorem nv_Wmap_Wmap (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (hS : matTranspose R = R) (hRR : R * R = 1)
    (hρ : MeasurePreserving (ShellField.rotate R hR) ν ν) (F : VectorL2 d ν) :
    nv_Wmap ν R hR hρ (nv_Wmap ν R hR hρ F) = F := by
  refine Lp.ext ?_
  have c1 := nv_coeFn_Wmap ν R hR hρ (nv_Wmap ν R hR hρ F)
  have c2 := nv_coeFn_Wmap ν R hR hρ F
  have c3 := hρ.quasiMeasurePreserving.ae_eq_comp c2
  filter_upwards [c1, c3] with ω h1 h3
  rw [h1]
  simp only [Function.comp_apply] at h3
  rw [h3, nv_rotate_rotate R hR hS hRR, nv_Rmap_Rmap R hRR]

theorem nv_Wmap_mem_potential (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (hS : matTranspose R = R) (hRR : R * R = 1)
    (hρ : MeasurePreserving (ShellField.rotate R hR) ν ν) {F : VectorL2 d ν}
    (hF : F ∈ stationaryPotentialSubspace (μ := ν) (d := d)) :
    nv_Wmap ν R hR hρ F ∈ stationaryPotentialSubspace (μ := ν) (d := d) := by
  have hle : stationaryPotentialSubspace (μ := ν) (d := d) ≤
      Submodule.comap (nv_Wmap ν R hR hρ).toContinuousLinearMap.toLinearMap
        (stationaryPotentialSubspace (μ := ν) (d := d)) := by
    refine (horizontalGradientRange (μ := ν) (d := d)).topologicalClosure_minimal
      (fun G hG ↦ ?_) ?_
    · obtain ⟨φ, hφ⟩ := hG
      exact Submodule.le_topologicalClosure _
        ⟨transportL2 ℝ hρ φ, nv_hasHorizontalGradient_Wmap ν R hR hS hRR hρ hφ⟩
    · exact (Submodule.isClosed_topologicalClosure _).preimage
        (nv_Wmap ν R hR hρ).continuous
  exact hle hF

/-- **The stationary potential projection commutes with the signed-permutation conjugation.** -/
theorem nv_stationaryPotentialProjection_Wmap (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (hS : matTranspose R = R) (hRR : R * R = 1)
    (hρ : MeasurePreserving (ShellField.rotate R hR) ν ν) (F : VectorL2 d ν) :
    stationaryPotentialProjection (μ := ν) (nv_Wmap ν R hR hρ F) =
      nv_Wmap ν R hR hρ (stationaryPotentialProjection (μ := ν) F) := by
  symm
  refine eq_stationaryPotentialProjection_of_mem_of_sub_mem_orthogonal
    (nv_Wmap_mem_potential ν R hR hS hRR hρ (stationaryPotentialProjection_mem F)) ?_
  rw [← map_sub]
  intro u hu
  have hG := sub_stationaryPotentialProjection_mem_orthogonal (μ := ν) F
  have hWu := nv_Wmap_mem_potential ν R hR hS hRR hρ hu
  have hinv := nv_Wmap_Wmap ν R hR hS hRR hρ u
  have : ⟪u, nv_Wmap ν R hR hρ (F - stationaryPotentialProjection (μ := ν) F)⟫_ℝ =
      ⟪nv_Wmap ν R hR hρ u, F - stationaryPotentialProjection (μ := ν) F⟫_ℝ := by
    rw [← (nv_Wmap ν R hR hρ).inner_map_map (nv_Wmap ν R hR hρ u), hinv]
  rw [this]
  exact hG _ hWu

end Koopman

theorem nv_Rmap_ofVec (R : Mat d) (v : Vec d) :
    nv_Rmap R (HilbertVec.ofVec v) = HilbertVec.ofVec (matVecMul R v) := by
  ext a
  rw [nv_Rmap_apply]
  rfl

/-- The forcing transforms covariantly under the rotation of the shell field. -/
theorem nv_fieldForcing_rotate (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (hS : matTranspose R = R) (hRR : R * R = 1) (e : Vec d) (ω : ShellField d) :
    nv_Rmap R (nv_fieldForcing e (ShellField.rotate R hR ω)) =
      nv_fieldForcing (matVecMul R e) ω := by
  have h0 : (ShellField.forgetShell (ShellField.rotate R hR ω)) 0 = R * ω 0 * R := by
    change matTranspose R * ω (matVecMul R 0) * R = R * ω 0 * R
    rw [hS, matVecMul_zero]
  change nv_Rmap R (HilbertVec.ofVec (matVecMul ((ShellField.forgetShell
    (ShellField.rotate R hR ω)) 0) e)) = HilbertVec.ofVec (matVecMul (ω 0) (matVecMul R e))
  rw [h0, nv_Rmap_ofVec, matVecMul_mul, matVecMul_mul]
  have hm : R * (R * ω 0 * R) = ω 0 * R := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hRR, Matrix.one_mul]
  rw [hm]

section Koopman2

variable (ν : Measure (ShellField d)) [VAddInvariantMeasure (Vec d) (ShellField d) ν]

omit [VAddInvariantMeasure (Vec d) (ShellField d) ν] in
theorem nv_Wmap_forcing (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (hS : matTranspose R = R) (hRR : R * R = 1)
    (hρ : MeasurePreserving (ShellField.rotate R hR) ν ν) (e : Vec d)
    (hmem : MemLp (nv_fieldForcing e) 2 ν) (hmem' : MemLp (nv_fieldForcing (matVecMul R e)) 2 ν) :
    nv_Wmap ν R hR hρ (hmem.toLp (nv_fieldForcing e)) =
      hmem'.toLp (nv_fieldForcing (matVecMul R e)) := by
  refine Lp.ext ?_
  have c1 := nv_coeFn_Wmap ν R hR hρ (hmem.toLp (nv_fieldForcing e))
  have c2 := hρ.quasiMeasurePreserving.ae_eq_comp hmem.coeFn_toLp
  have c3 := hmem'.coeFn_toLp
  filter_upwards [c1, c2, c3] with ω h1 h2 h3
  rw [h1, h3]
  simp only [Function.comp_apply] at h2
  rw [h2, nv_fieldForcing_rotate R hR hS hRR]

end Koopman2

/-! ## Linearity of the forcing in the direction -/

theorem nv_fieldForcing_add (e e' : Vec d) (j : ShellField d) :
    nv_fieldForcing (e + e') j = nv_fieldForcing e j + nv_fieldForcing e' j := by
  ext a
  change (∑ c : Fin d, j 0 a c * (e + e') c) = (∑ c : Fin d, j 0 a c * e c) +
    ∑ c : Fin d, j 0 a c * e' c
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun c _ ↦ by simp only [Pi.add_apply]; ring

theorem nv_fieldForcing_smul (r : ℝ) (e : Vec d) (j : ShellField d) :
    nv_fieldForcing (r • e) j = r • nv_fieldForcing e j := by
  ext a
  change (∑ c : Fin d, j 0 a c * (r • e) c) = r * ∑ c : Fin d, j 0 a c * e c
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ ↦ by simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem nv_fieldForcing_single_apply (b a : Fin d) (j : ShellField d) :
    nv_fieldForcing (Pi.single b 1 : Vec d) j a = j 0 a b := by
  change (∑ c : Fin d, j 0 a c * (Pi.single b 1 : Vec d) c) = j 0 a b
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hcb
    simp [Pi.single_eq_of_ne hcb]
  · simp

theorem nv_memLp_fieldForcing_of_basis (ν : Measure (ShellField d))
    (hb : ∀ a : Fin d, MemLp (nv_fieldForcing (Pi.single a 1 : Vec d)) 2 ν) (e : Vec d) :
    MemLp (nv_fieldForcing e) 2 ν := by
  have h : nv_fieldForcing e = ∑ a : Fin d, e a • nv_fieldForcing (Pi.single a 1 : Vec d) := by
    funext j
    ext b
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply]
    rw [WithLp.ofLp_sum]
    simp only [Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
      nv_fieldForcing_single_apply]
    change (∑ c : Fin d, j 0 b c * e c) = _
    exact Finset.sum_congr rfl fun c _ ↦ by ring
  rw [h]
  exact memLp_finsetSum' _ fun a _ ↦ (hb a).const_smul (e a)

section Forcing

variable (ν : Measure (ShellField d))

/-- The forcing, as a linear map from directions to vector-valued `L²` classes. -/
def nv_forcingL2 (hall : ∀ e : Vec d, MemLp (nv_fieldForcing e) 2 ν) : Vec d →ₗ[ℝ] VectorL2 d ν where
  toFun e := (hall e).toLp (nv_fieldForcing e)
  map_add' e e' := by
    refine Lp.ext ?_
    filter_upwards [(hall (e + e')).coeFn_toLp, (hall e).coeFn_toLp, (hall e').coeFn_toLp,
      Lp.coeFn_add ((hall e).toLp (nv_fieldForcing e)) ((hall e').toLp (nv_fieldForcing e'))]
      with j h1 h2 h3 h4
    rw [h1, h4, Pi.add_apply, h2, h3]
    exact nv_fieldForcing_add e e' j
  map_smul' r e := by
    refine Lp.ext ?_
    filter_upwards [(hall (r • e)).coeFn_toLp, (hall e).coeFn_toLp,
      Lp.coeFn_smul r ((hall e).toLp (nv_fieldForcing e))] with j h1 h2 h3
    rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h2]
    exact nv_fieldForcing_smul r e j

theorem nv_norm_projection_forcing_rotate (hν : ∀ z : Vec d, Measure.map (ShellField.translate z) ν = ν)
    (hall : ∀ e : Vec d, MemLp (nv_fieldForcing e) 2 ν) (R : Mat d)
    (hR : IsSignedPermutationMatrix R) (hS : matTranspose R = R) (hRR : R * R = 1)
    (hrot : Measure.map (ShellField.rotate R hR) ν = ν) (e : Vec d) :
    letI := nv_vaddInvariant_of_stationary ν hν
    ‖stationaryPotentialProjection (μ := ν) (nv_forcingL2 ν hall (matVecMul R e))‖ =
      ‖stationaryPotentialProjection (μ := ν) (nv_forcingL2 ν hall e)‖ := by
  have := nv_vaddInvariant_of_stationary ν hν
  have hρ : MeasurePreserving (ShellField.rotate R hR) ν ν := ⟨ShellField.measurable_rotate R hR, hrot⟩
  have hW : nv_forcingL2 ν hall (matVecMul R e) = nv_Wmap ν R hR hρ (nv_forcingL2 ν hall e) :=
    (nv_Wmap_forcing ν R hR hS hRR hρ e (hall e) (hall (matVecMul R e))).symm
  rw [hW, nv_stationaryPotentialProjection_Wmap ν R hR hS hRR hρ, LinearIsometry.norm_map]

end Forcing

/-! ## Flips and swaps -/

/-- The diagonal matrix with entry `-1` at `c` and `1` elsewhere. -/
def nv_flipMat (c : Fin d) : Mat d := Matrix.diagonal fun i ↦ if i = c then -1 else 1

theorem nv_flipMat_signedPerm (c : Fin d) : IsSignedPermutationMatrix (nv_flipMat c) := by
  refine ⟨Equiv.refl _, fun i ↦ if i = c then -1 else 1, fun i ↦ ?_, fun i j ↦ ?_⟩
  · by_cases h : i = c <;> simp [h]
  · by_cases h : i = j
    · subst h
      simp [nv_flipMat]
    · simp [nv_flipMat, h]

theorem nv_flipMat_symm (c : Fin d) : matTranspose (nv_flipMat c) = nv_flipMat c :=
  Matrix.diagonal_transpose _

theorem nv_flipMat_mul (c : Fin d) : nv_flipMat c * nv_flipMat c = 1 := by
  unfold nv_flipMat
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases h : i = c <;> simp [h]

/-- The permutation matrix of the transposition of `a` and `b`. -/
def nv_swapMat (a b : Fin d) : Mat d := Matrix.of fun i j ↦ if i = Equiv.swap a b j then 1 else 0

theorem nv_swapMat_signedPerm (a b : Fin d) : IsSignedPermutationMatrix (nv_swapMat a b) :=
  ⟨Equiv.swap a b, fun _ ↦ 1, fun _ ↦ Or.inl rfl, fun i j ↦ by simp [nv_swapMat]⟩

theorem nv_swapMat_symm (a b : Fin d) : matTranspose (nv_swapMat a b) = nv_swapMat a b := by
  ext i j
  simp only [matTranspose, Matrix.transpose_apply, nv_swapMat, Matrix.of_apply]
  have : (i = Equiv.swap a b j) ↔ (j = Equiv.swap a b i) := by
    rw [eq_comm, Equiv.swap_apply_eq_iff]
  simp only [this]

theorem nv_swapMat_mul (a b : Fin d) : nv_swapMat a b * nv_swapMat a b = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Equiv.swap a b j)]
  · simp only [nv_swapMat, Matrix.of_apply, Equiv.swap_apply_self, Matrix.one_apply]
    by_cases h : i = j
    · simp [h]
    · simp [h]
  · intro k _ hk
    have : ¬ k = Equiv.swap a b j := hk
    simp [nv_swapMat, this]
  · simp

theorem nv_norm_sq_sum_of_symmetric {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : Fin d → H) (hflip : ∀ c b, c ≠ b → ‖v b - v c‖ = ‖v c + v b‖)
    (hswap : ∀ a b, ‖v a‖ = ‖v b‖) (i0 : Fin d) (e : Fin d → ℝ) :
    ‖∑ a, e a • v a‖ ^ 2 = (∑ a, e a ^ 2) * ‖v i0‖ ^ 2 := by
  have horth : ∀ c b, c ≠ b → ⟪v c, v b⟫_ℝ = 0 := by
    intro c b hcb
    have h := hflip c b hcb
    have h1 : ‖v b - v c‖ ^ 2 = ‖v c + v b‖ ^ 2 := by rw [h]
    rw [norm_sub_sq_real, norm_add_sq_real, real_inner_comm] at h1
    linarith only [h1]
  rw [← real_inner_self_eq_norm_sq, sum_inner, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [inner_sum, Finset.sum_eq_single a]
  · rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, hswap a i0]
    ring
  · intro b _ hba
    rw [real_inner_smul_left, real_inner_smul_right, horth a b hba.symm]
    ring
  · simp

theorem nv_flipMat_apply (c i j : Fin d) :
    nv_flipMat c i j = if i = Equiv.refl (Fin d) j then (if j = c then -1 else 1) else 0 := by
  by_cases h : i = j
  · subst h
    simp [nv_flipMat]
  · simp [nv_flipMat, h]

theorem nv_matVecMul_flip (c a : Fin d) :
    matVecMul (nv_flipMat c) (Pi.single a 1 : Vec d) =
      (if a = c then (-1 : ℝ) else 1) • (Pi.single a 1 : Vec d) := by
  have h := nv_matVecMul_single (nv_flipMat c) (Equiv.refl (Fin d))
    (fun i ↦ if i = c then (-1 : ℝ) else 1) (nv_flipMat_apply c) a 1
  simpa using h

theorem nv_matVecMul_swap (a b x : Fin d) :
    matVecMul (nv_swapMat a b) (Pi.single x 1 : Vec d) = (Pi.single (Equiv.swap a b x) 1 : Vec d) := by
  have h := nv_matVecMul_single (nv_swapMat a b) (Equiv.swap a b) (fun _ ↦ (1 : ℝ))
    (fun i j ↦ by simp [nv_swapMat]) x 1
  simpa using h

theorem nv_pi_eq_sum_single (e : Vec d) : e = ∑ a : Fin d, e a • (Pi.single a 1 : Vec d) := by
  ext i
  simp [Finset.sum_apply, Pi.single_apply]

/-- **Direction independence of the response energy.** If the seed law is invariant under the
sign flips and the transpositions of the coordinates, the energy of the forcing in a unit direction
`e` is the energy in any fixed coordinate direction. -/
theorem nv_shellEnergy_const_of_symmetric (ν : Measure (ShellField d))
    (hν : ∀ z : Vec d, Measure.map (ShellField.translate z) ν = ν)
    (hall : ∀ e : Vec d, MemLp (nv_fieldForcing e) 2 ν)
    (hrot : ∀ (R : Mat d) (hR : IsSignedPermutationMatrix R),
      Measure.map (ShellField.rotate R hR) ν = ν) (i0 : Fin d) (e : Vec d)
    (he : Book.Ch02.vecNorm e = 1) :
    nv_shellEnergy ν hν e (hall e) = nv_shellEnergy ν hν (Pi.single i0 1) (hall _) := by
  have := nv_vaddInvariant_of_stationary ν hν
  unfold nv_shellEnergy
  set Φ : Vec d →ₗ[ℝ] VectorL2 d ν :=
    (stationaryPotentialProjection (μ := ν)).toLinearMap ∘ₗ nv_forcingL2 ν hall with hΦ
  have hΦapply : ∀ x : Vec d, Φ x = stationaryPotentialProjection (μ := ν)
      (nv_forcingL2 ν hall x) := fun x ↦ rfl
  set v : Fin d → VectorL2 d ν := fun a ↦ Φ (Pi.single a 1) with hv
  have hnormflip : ∀ (c : Fin d) (x : Vec d), ‖Φ (matVecMul (nv_flipMat c) x)‖ = ‖Φ x‖ := fun c x ↦
    nv_norm_projection_forcing_rotate ν hν hall (nv_flipMat c) (nv_flipMat_signedPerm c)
      (nv_flipMat_symm c) (nv_flipMat_mul c) (hrot _ _) x
  have hnormswap : ∀ (a b : Fin d) (x : Vec d), ‖Φ (matVecMul (nv_swapMat a b) x)‖ = ‖Φ x‖ :=
    fun a b x ↦ nv_norm_projection_forcing_rotate ν hν hall (nv_swapMat a b)
      (nv_swapMat_signedPerm a b) (nv_swapMat_symm a b) (nv_swapMat_mul a b) (hrot _ _) x
  have hflip : ∀ c b : Fin d, c ≠ b → ‖v b - v c‖ = ‖v c + v b‖ := by
    intro c b hcb
    have h1 := hnormflip c (Pi.single c 1 + Pi.single b 1)
    rw [matVecMul_add, nv_matVecMul_flip, nv_matVecMul_flip] at h1
    simp only [↓reduceIte, hcb.symm, map_add, map_sub, neg_one_smul, one_smul,
      neg_add_eq_sub] at h1
    exact h1
  have hswap : ∀ a b : Fin d, ‖v a‖ = ‖v b‖ := by
    intro a b
    have h1 := hnormswap a b (Pi.single a 1)
    rw [nv_matVecMul_swap, Equiv.swap_apply_left] at h1
    exact h1.symm
  have hsum : Φ e = ∑ a : Fin d, e a • v a := by
    conv_lhs => rw [nv_pi_eq_sum_single e]
    rw [map_sum]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [map_smul]
  have hunit : ∑ a : Fin d, e a ^ 2 = 1 := by
    have h := Book.Ch02.vecNorm_sq_eq_vecNormSq e
    rw [he, vecNormSq, vecDot] at h
    simp only [one_pow] at h
    rw [h]
    exact Finset.sum_congr rfl fun a _ ↦ sq (e a)
  have hkey := nv_norm_sq_sum_of_symmetric v hflip hswap i0 e
  rw [← hsum, hunit, one_mul] at hkey
  exact hkey

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
