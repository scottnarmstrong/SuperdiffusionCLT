/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.J5Koopman
public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.GaussLaw

/-!
# The Koopman derivative of the point evaluation of an entry

Let `ν` be a translation-stationary law on the one-shell carrier such that the J3 observable at
scale zero is square integrable. For every point `x` and entry `(i, k)` the scalar function
`j ↦ j x i k` belongs to `L²(ν)` and has the strong horizontal gradient `j ↦ (∂_l j x i k)_l`:
the Koopman difference quotient along the axis `e_l` differs from the gradient coordinate by at
most `t²` times the observable of the translate (the pointwise Taylor bound of `J5Koopman`),
which is `o(t)` in `L²(ν)`.

* `nv_entryEval`, `nv_entryDeriv`, `nv_entryGrad`: the functional and its gradient.
* `nv_memLp_entryEval`, `nv_memLp_entryDeriv`, `nv_memLp_entryGrad`: square integrability.
* `nv_hasHorizontalGradient_entry`: the horizontal gradient.
* `nv_memLp_j3Observable_seed`: the observable is square integrable for the seed law of a product
  law that satisfies J3.
* `nv_shellEnergy_pos_of_hasHorizontalGradient`: a gradient with nonzero pairing with the forcing
  forces a positive response energy.
* `nv_integral_entry_mul_self`, `nv_integral_entry_mul_ne`: correlations of entry evaluations under
  the seed shell law.
* `nv_shellEnergy_seed_pos`: the Gaussian seed has positive response energy for the forcing in
  the second coordinate direction.
* `nv_shellLawJ5_gaussLaw`: J5 for the Gaussian shell law, from the positive energy, the
  independence of the direction (`J5ReductionB`) and the assembly.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Probability.Stationary
open scoped Topology InnerProductSpace

noncomputable section

variable {d : ℕ}

/-- The entry `(i, k)` of a shell field at the point `x`. -/
def nv_entryEval (x : Vec d) (i k : Fin d) (j : ShellField d) : ℝ := j x i k

/-- The `l`-th partial derivative of the entry `(i, k)` of a shell field at `x`. -/
def nv_entryDeriv (x : Vec d) (l i k : Fin d) (j : ShellField d) : ℝ :=
  ShellField.deriv j x (Pi.single l 1) i k

/-- The gradient of the entry `(i, k)` at `x`, as a vector. -/
def nv_entryGrad (x : Vec d) (i k : Fin d) (j : ShellField d) : HilbertVec d :=
  HilbertVec.ofVec fun l ↦ nv_entryDeriv x l i k j

theorem measurable_nv_entryEval (x : Vec d) (i k : Fin d) : Measurable (nv_entryEval x i k) :=
  ShellField.measurable_eval_entry x i k

theorem measurable_nv_entryDeriv (x : Vec d) (l i k : Fin d) :
    Measurable (nv_entryDeriv x l i k) :=
  measurable_eval_deriv_entry x (Pi.single l 1) i k

section Measure

variable (ν : Measure (ShellField d))

theorem nv_measurePreserving_translate
    (hν : ∀ z : Vec d, Measure.map (ShellField.translate z) ν = ν) (z : Vec d) :
    MeasurePreserving (ShellField.translate z) ν ν :=
  ⟨ShellField.measurable_translate z, hν z⟩

theorem nv_memLp_obs_translate (hν : ∀ z : Vec d, Measure.map (ShellField.translate z) ν = ν)
    (hobs : MemLp (ShellField.j3Observable d 0) 2 ν) (x : Vec d) :
    MemLp (fun j : ShellField d ↦ ShellField.j3Observable d 0 (ShellField.translate x j)) 2 ν :=
  hobs.comp_measurePreserving (nv_measurePreserving_translate ν hν x)

theorem nv_memLp_entryEval (hν : ∀ z : Vec d, Measure.map (ShellField.translate z) ν = ν)
    (hobs : MemLp (ShellField.j3Observable d 0) 2 ν) (x : Vec d) (i k : Fin d) :
    MemLp (nv_entryEval x i k) 2 ν :=
  (nv_memLp_obs_translate ν hν hobs x).mono' (measurable_nv_entryEval x i k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun j ↦ by
      rw [Real.norm_eq_abs]
      exact nv_abs_entry_le_obs j x i k)

theorem nv_memLp_entryDeriv (hd : 0 < d)
    (hν : ∀ z : Vec d, Measure.map (ShellField.translate z) ν = ν)
    (hobs : MemLp (ShellField.j3Observable d 0) 2 ν) (x : Vec d) (l i k : Fin d) :
    MemLp (nv_entryDeriv x l i k) 2 ν :=
  (nv_memLp_obs_translate ν hν hobs x).mono' (measurable_nv_entryDeriv x l i k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun j ↦ by
      rw [Real.norm_eq_abs]
      exact nv_abs_deriv_entry_le_obs hd j x l i k)

theorem nv_memLp_entryGrad (hd : 0 < d)
    (hν : ∀ z : Vec d, Measure.map (ShellField.translate z) ν = ν)
    (hobs : MemLp (ShellField.j3Observable d 0) 2 ν) (x : Vec d) (i k : Fin d) :
    MemLp (nv_entryGrad x i k) 2 ν := by
  refine (MeasureTheory.memLp_piLp_iff (f := nv_entryGrad x i k)).2 fun l ↦ ?_
  exact nv_memLp_entryDeriv ν hd hν hobs x l i k

theorem nv_coeFn_koopman_toLp [VAddInvariantMeasure (Vec d) (ShellField d) ν] (z : Vec d)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ShellField d → E}
    (hf : MemLp f 2 ν) :
    (koopman (μ := ν) z (hf.toLp f) : ShellField d → E) =ᵐ[ν] fun j ↦ f (z +ᵥ j) := by
  refine (Lp.coeFn_compMeasurePreserving _ (measurePreserving_const_vadd (μ := ν) z)).trans ?_
  exact (measurePreserving_const_vadd (μ := ν) z).quasiMeasurePreserving.ae_eq_comp
    hf.coeFn_toLp

theorem nv_vectorL2Coord_toLp_entryGrad (hd : 0 < d)
    (hν : ∀ z : Vec d, Measure.map (ShellField.translate z) ν = ν)
    (hobs : MemLp (ShellField.j3Observable d 0) 2 ν) (x : Vec d) (l i k : Fin d) :
    vectorL2Coord (μ := ν) l ((nv_memLp_entryGrad ν hd hν hobs x i k).toLp (nv_entryGrad x i k)) =
      (nv_memLp_entryDeriv ν hd hν hobs x l i k).toLp (nv_entryDeriv x l i k) := by
  refine Lp.ext ?_
  have h1 : (vectorL2Coord (μ := ν) l
        ((nv_memLp_entryGrad ν hd hν hobs x i k).toLp (nv_entryGrad x i k)) : ShellField d → ℝ)
      =ᵐ[ν] fun j ↦ ((nv_memLp_entryGrad ν hd hν hobs x i k).toLp (nv_entryGrad x i k) :
        ShellField d → HilbertVec d) j l :=
    ContinuousLinearMap.coeFn_compLpL _ _
  have h2 := (nv_memLp_entryGrad ν hd hν hobs x i k).coeFn_toLp
  have h3 := (nv_memLp_entryDeriv ν hd hν hobs x l i k).coeFn_toLp
  filter_upwards [h1, h2, h3] with j hj1 hj2 hj3
  rw [hj1, hj2, hj3]
  rfl

/-- **The Koopman derivative of the point evaluation of an entry.** The function
`j ↦ j x i k` has the horizontal gradient `j ↦ (∂_l j x i k)_l`, for every stationary law with a
square integrable J3 observable at scale zero. -/
theorem nv_hasHorizontalGradient_entry (hd : 0 < d)
    (hν : ∀ z : Vec d, Measure.map (ShellField.translate z) ν = ν)
    (hobs : MemLp (ShellField.j3Observable d 0) 2 ν) (x : Vec d) (i k : Fin d) :
    letI := nv_vaddInvariant_of_stationary ν hν
    HasHorizontalGradient (μ := ν)
      ((nv_memLp_entryEval ν hν hobs x i k).toLp (nv_entryEval x i k))
      ((nv_memLp_entryGrad ν hd hν hobs x i k).toLp (nv_entryGrad x i k)) := by
  have := nv_vaddInvariant_of_stationary ν hν
  intro l
  rw [nv_vectorL2Coord_toLp_entryGrad ν hd hν hobs x l i k]
  set e : Vec d := Pi.single l 1 with he
  set hφ := nv_memLp_entryEval ν hν hobs x i k with hφdef
  set hG := nv_memLp_entryDeriv ν hd hν hobs x l i k with hGdef
  set hB := nv_memLp_obs_translate ν hν hobs x with hBdef
  set φ := hφ.toLp (nv_entryEval x i k) with hφL
  set Gl := hG.toLp (nv_entryDeriv x l i k) with hGL
  set Bl := hB.toLp (fun j : ShellField d ↦ ShellField.j3Observable d 0 (ShellField.translate x j))
    with hBL
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hD : ∀ h : ℝ, koopman (μ := ν) ((0 + h) • e) φ - koopman (μ := ν) ((0 : ℝ) • e) φ -
      h • Gl = koopman (μ := ν) (h • e) φ - φ - h • Gl := by
    intro h
    simp only [zero_add, zero_smul, koopman_zero]
  simp_rw [hD]
  have hbound : ∀ h : ℝ, |h| ≤ 1 / 4 →
      ‖koopman (μ := ν) (h • e) φ - φ - h • Gl‖ ≤ ‖Bl‖ * ‖h ^ 2‖ := by
    intro h hh
    have hnorm : ‖koopman (μ := ν) (h • e) φ - φ - h • Gl‖ ≤ ‖(h ^ 2) • Bl‖ := by
      refine Lp.norm_le_norm_of_ae_le ?_
      have c1 := Lp.coeFn_sub (koopman (μ := ν) (h • e) φ - φ) (h • Gl)
      have c2 := Lp.coeFn_sub (koopman (μ := ν) (h • e) φ) φ
      have c3 := Lp.coeFn_smul h Gl
      have c4 := nv_coeFn_koopman_toLp ν (h • e) hφ
      have c5 := hφ.coeFn_toLp
      have c6 := hG.coeFn_toLp
      have c7 := Lp.coeFn_smul (h ^ 2) Bl
      have c8 := hB.coeFn_toLp
      filter_upwards [c1, c2, c3, c4, c5, c6, c7, c8] with j d1 d2 d3 d4 d5 d6 d7 d8
      rw [d1, Pi.sub_apply, d2, Pi.sub_apply, d3, Pi.smul_apply, d4, d5, d6, d7,
        Pi.smul_apply, d8]
      have htay := nv_entry_taylor hd j x l i k h hh
      have hnn : 0 ≤ ShellField.j3Observable d 0 (ShellField.translate x j) :=
        ShellField.j3Observable_nonneg d 0 _
      rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul, smul_eq_mul,
        abs_of_nonneg (mul_nonneg (sq_nonneg h) hnn)]
      simpa only [nv_entryEval, nv_entryDeriv, ShellField.translate_apply, he,
        MeasureTheory.MeasurePreserving.id, ShellField.vadd_eq_translate] using htay
    refine hnorm.trans ?_
    rw [norm_smul, mul_comm]
  have hbig : (fun h : ℝ ↦ koopman (μ := ν) (h • e) φ - φ - h • Gl) =O[𝓝 0] fun h : ℝ ↦ h ^ 2 := by
    refine Asymptotics.IsBigO.of_bound ‖Bl‖ ?_
    have hev : ∀ᶠ h : ℝ in 𝓝 0, |h| ≤ 1 / 4 := by
      have : Metric.ball (0 : ℝ) (1 / 4) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ (by norm_num)
      filter_upwards [this] with h hh
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hh
      exact hh.le
    filter_upwards [hev] with h hh
    exact hbound h hh
  exact hbig.trans_isLittleO (Asymptotics.isLittleO_pow_id (by norm_num))

end Measure

/-- J3 for the product law makes the observable at scale zero square integrable for the seed. -/
theorem nv_memLp_j3Observable_seed (ν₀ : ProbabilityMeasure (ShellField d))
    (hJ3 : ShellLawJ3 d (nv_productLaw ν₀)) :
    MemLp (ShellField.j3Observable d 0) 2 ν₀.toMeasure := by
  have h := hJ3.memLp_two_j3Observable_coordinate 0
  have hmap : (ShellField.shellMarginalLaw (nv_productLaw ν₀) 0).toMeasure =
      Measure.map (fun omega : ℕ → ShellField d ↦ omega 0) (nv_productLaw ν₀).toMeasure :=
    ProbabilityMeasure.toMeasure_map _
  have h2 : MemLp (ShellField.j3Observable d 0) 2
      (ShellField.shellMarginalLaw (nv_productLaw ν₀) 0).toMeasure := by
    rw [hmap]
    exact (memLp_map_measure_iff (ShellField.j3Observable_measurable d 0).aestronglyMeasurable
      (ShellField.measurable_shellCoordinate 0).aemeasurable).mpr h
  rwa [nv_shellMarginalLaw_productLaw, scaledShellLaw_zero] at h2

section Generic

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)

/-- The inner product of two vector-valued `L²` classes is the sum of the inner products of their
coordinates. -/
theorem nv_inner_eq_sum_coord (F G : VectorL2 d μ) :
    ⟪F, G⟫_ℝ = ∑ a : Fin d, ⟪vectorL2Coord (μ := μ) a F, vectorL2Coord (μ := μ) a G⟫_ℝ := by
  rw [MeasureTheory.L2.inner_def]
  have hint : ∀ a ∈ Finset.univ, Integrable
      (fun j ↦ ⟪(vectorL2Coord (μ := μ) a F : Ω → ℝ) j, (vectorL2Coord (μ := μ) a G : Ω → ℝ) j⟫_ℝ) μ :=
    fun a _ ↦ MeasureTheory.L2.integrable_inner _ _
  have hsum : ∑ a : Fin d, ⟪vectorL2Coord (μ := μ) a F, vectorL2Coord (μ := μ) a G⟫_ℝ =
      ∫ j, ∑ a : Fin d, ⟪(vectorL2Coord (μ := μ) a F : Ω → ℝ) j,
        (vectorL2Coord (μ := μ) a G : Ω → ℝ) j⟫_ℝ ∂μ := by
    rw [integral_finsetSum _ hint]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [MeasureTheory.L2.inner_def]
  rw [hsum]
  refine integral_congr_ae ?_
  have h1 : ∀ a : Fin d, (vectorL2Coord (μ := μ) a F : Ω → ℝ) =ᵐ[μ]
      fun j ↦ (F : Ω → HilbertVec d) j a := fun a ↦ ContinuousLinearMap.coeFn_compLpL _ _
  have h2 : ∀ a : Fin d, (vectorL2Coord (μ := μ) a G : Ω → ℝ) =ᵐ[μ]
      fun j ↦ (G : Ω → HilbertVec d) j a := fun a ↦ ContinuousLinearMap.coeFn_compLpL _ _
  have h3 := (Filter.eventually_all.2 h1)
  have h4 := (Filter.eventually_all.2 h2)
  filter_upwards [h3, h4] with j hj3 hj4
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [hj3 a, hj4 a]

end Generic

/-- **Positivity from a gradient test.** If a gradient `G` of some potential has nonzero inner
product with the forcing, the response energy is positive. -/
theorem nv_shellEnergy_pos_of_hasHorizontalGradient (ν : Measure (ShellField d))
    (hν : ∀ z : Vec d, Measure.map (ShellField.translate z) ν = ν) (e : Vec d)
    (hmem : MemLp (nv_fieldForcing e) 2 ν) (φ : Lp ℝ 2 ν) (G : VectorL2 d ν)
    (hG : letI := nv_vaddInvariant_of_stationary ν hν
      HasHorizontalGradient (μ := ν) φ G)
    (hinner : ⟪hmem.toLp (nv_fieldForcing e), G⟫_ℝ ≠ 0) :
    0 < nv_shellEnergy ν hν e hmem := by
  have := nv_vaddInvariant_of_stationary ν hν
  unfold nv_shellEnergy
  set F := hmem.toLp (nv_fieldForcing e) with hF
  have hGmem : G ∈ stationaryPotentialSubspace (μ := ν) (d := d) :=
    Submodule.le_topologicalClosure _ ⟨φ, hG⟩
  have horth : ⟪G, F - stationaryPotentialProjection (μ := ν) F⟫_ℝ = 0 :=
    (Submodule.mem_orthogonal _ _).mp
      (sub_stationaryPotentialProjection_mem_orthogonal (μ := ν) F) G hGmem
  have hne : stationaryPotentialProjection (μ := ν) F ≠ 0 := by
    intro h0
    rw [h0, sub_zero] at horth
    exact hinner (by rw [real_inner_comm]; exact horth)
  exact pow_pos (norm_pos_iff.2 hne) 2

/-! ## Covariances of entry evaluations under the seed shell law -/

section Seed

open ProbabilityTheory

theorem nv_integral_seed (x : Vec d) : ∫ ξ, nv_seed ξ x ∂(nvNoiseLaw d) = 0 := by
  have h := nv_map_comb_eq_gaussianReal (ι := Unit) (fun _ ↦ (1 : ℝ)) (fun _ ↦ x)
  have h1 : ∫ ξ, ∑ _j : Unit, (1 : ℝ) * nv_seed ξ x ∂(nvNoiseLaw d) = 0 := by
    calc ∫ ξ, ∑ _j : Unit, (1 : ℝ) * nv_seed ξ x ∂(nvNoiseLaw d)
        = ∫ y, id y ∂(Measure.map (fun ξ ↦ ∑ _j : Unit, (1 : ℝ) * nv_seed ξ x) (nvNoiseLaw d)) :=
          (integral_map (nv_measurable_comb (fun _ : Unit ↦ (1 : ℝ)) (fun _ ↦ x)).aemeasurable
            aestronglyMeasurable_id).symm
      _ = 0 := by
          rw [h]
          exact integral_id_gaussianReal
  simpa using h1

theorem nv_integral_seed_mul (x y : Vec d) :
    ∫ ξ, nv_seed ξ x * nv_seed ξ y ∂(nvNoiseLaw d) = nvCov x y := by
  have h := covariance_eq_sub (nv_memLp_seed x) (nv_memLp_seed y)
  rw [nv_covariance_seed] at h
  simp only [Pi.mul_apply, nv_integral_seed x, zero_mul, sub_zero] at h
  exact h.symm

theorem nv_integral_seedLaw_eval (ε : ℝ) (x : Vec d) :
    ∫ f, f x ∂(nv_seedLaw d ε) = 0 := by
  unfold nv_seedLaw
  rw [integral_map (nv_measurable_seedMap ε).aemeasurable
    (ScalarC2Field.measurable_eval x).aestronglyMeasurable]
  simp only [nv_seedMap_apply, integral_const_mul, nv_integral_seed, mul_zero]

/-- The product of two point evaluations on the scalar carrier. -/
def nv_evalMul (x y : Vec d) (f : ScalarC2Field d) : ℝ := f x * f y

theorem measurable_nv_evalMul (x y : Vec d) : Measurable (nv_evalMul x y) :=
  (ScalarC2Field.measurable_eval x).mul (ScalarC2Field.measurable_eval y)

theorem nv_integral_seedLaw_mul (ε : ℝ) (x y : Vec d) :
    ∫ f, nv_evalMul x y f ∂(nv_seedLaw d ε) = ε ^ 2 * nvCov x y := by
  unfold nv_seedLaw
  rw [integral_map (nv_measurable_seedMap ε).aemeasurable
    (measurable_nv_evalMul x y).aestronglyMeasurable]
  have : ∀ ξ : NvNoise d, nv_evalMul x y (nv_seedMap ε ξ) =
      ε ^ 2 * (nv_seed ξ x * nv_seed ξ y) := fun ξ ↦ by
    simp only [nv_evalMul, nv_seedMap_apply]
    ring
  simp only [this, integral_const_mul, nv_integral_seed_mul]

theorem nv_integral_entry_mul_self (ε : ℝ) (p : SkewIdx d) (x y : Vec d) :
    ∫ j, nv_entryEval x p.1.1 p.1.2 j * nv_entryEval y p.1.1 p.1.2 j
      ∂(nv_seedShellLaw d ε).toMeasure = ε ^ 2 * nvCov x y := by
  have hm : Measurable (fun j : ShellField d ↦
      nv_entryEval x p.1.1 p.1.2 j * nv_entryEval y p.1.1 p.1.2 j) :=
    (measurable_nv_entryEval x _ _).mul (measurable_nv_entryEval y _ _)
  rw [nv_seedShellLaw_toMeasure, integral_map measurable_assembleSkew.aemeasurable
    hm.aestronglyMeasurable]
  have : ∀ φ : SkewIdx d → ScalarC2Field d,
      nv_entryEval x p.1.1 p.1.2 (assembleSkew φ) * nv_entryEval y p.1.1 p.1.2 (assembleSkew φ) =
        nv_evalMul x y (φ p) := fun φ ↦ by
    simp only [nv_entryEval, nv_evalMul, assembleSkew_apply_lt φ _ p.2]
  simp only [this]
  rw [integral_comp_eval (μ := fun _ : SkewIdx d ↦ nv_seedLaw d ε) (i := p)
    (measurable_nv_evalMul x y).aestronglyMeasurable]
  exact nv_integral_seedLaw_mul ε x y

theorem nv_integral_entry_mul_ne (ε : ℝ) {p q : SkewIdx d} (hpq : p ≠ q) (x y : Vec d) :
    ∫ j, nv_entryEval x p.1.1 p.1.2 j * nv_entryEval y q.1.1 q.1.2 j
      ∂(nv_seedShellLaw d ε).toMeasure = 0 := by
  have hm : Measurable (fun j : ShellField d ↦
      nv_entryEval x p.1.1 p.1.2 j * nv_entryEval y q.1.1 q.1.2 j) :=
    (measurable_nv_entryEval x _ _).mul (measurable_nv_entryEval y _ _)
  rw [nv_seedShellLaw_toMeasure, integral_map measurable_assembleSkew.aemeasurable
    hm.aestronglyMeasurable]
  have hind := iIndepFun_pi (μ := fun _ : SkewIdx d ↦ nv_seedLaw d ε)
    (X := fun r f ↦ (f : ScalarC2Field d) (if r = p then x else y))
    (fun r ↦ (ScalarC2Field.measurable_eval _).aemeasurable)
  have hpq' := hind.indepFun hpq
  have hint := hpq'.integral_mul_eq_mul_integral
    ((ScalarC2Field.measurable_eval _).comp (measurable_pi_apply p) |>.aestronglyMeasurable)
    ((ScalarC2Field.measurable_eval _).comp (measurable_pi_apply q) |>.aestronglyMeasurable)
  have hqp : ¬ q = p := fun h ↦ hpq h.symm
  simp only [ite_true, hqp, ite_false, Pi.mul_apply] at hint
  have : ∀ φ : SkewIdx d → ScalarC2Field d,
      nv_entryEval x p.1.1 p.1.2 (assembleSkew φ) * nv_entryEval y q.1.1 q.1.2 (assembleSkew φ) =
        φ p x * φ q y := fun φ ↦ by
    simp only [nv_entryEval, assembleSkew_apply_lt φ _ p.2, assembleSkew_apply_lt φ _ q.2]
  simp only [this]
  rw [hint]
  have h1 : ∫ ω : SkewIdx d → ScalarC2Field d, (ω p : ScalarC2Field d) x
      ∂(Measure.pi fun _ : SkewIdx d ↦ nv_seedLaw d ε) = 0 := by
    rw [integral_comp_eval (μ := fun _ : SkewIdx d ↦ nv_seedLaw d ε) (i := p)
      (f := fun f : ScalarC2Field d ↦ f x) (ScalarC2Field.measurable_eval x).aestronglyMeasurable]
    exact nv_integral_seedLaw_eval ε x
  rw [h1, zero_mul]

end Seed

/-! ## The pairing of the forcing with a Koopman translate -/

theorem nv_inner_toLp_koopman (ν : Measure (ShellField d))
    (hν : ∀ z : Vec d, Measure.map (ShellField.translate z) ν = ν) (z : Vec d)
    {f g : ShellField d → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    letI := nv_vaddInvariant_of_stationary ν hν
    ⟪hf.toLp f, koopman (μ := ν) z (hg.toLp g)⟫_ℝ = ∫ j, f j * g (ShellField.translate z j) ∂ν := by
  have := nv_vaddInvariant_of_stationary ν hν
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, nv_coeFn_koopman_toLp ν z hg] with j h1 h2
  rw [h1, h2]
  simp only [RCLike.inner_apply, conj_trivial]
  exact mul_comm _ _

theorem nv_hasDerivAt_pairing (hd : 0 < d) (ν : Measure (ShellField d))
    (hν : ∀ z : Vec d, Measure.map (ShellField.translate z) ν = ν)
    (hobs : MemLp (ShellField.j3Observable d 0) 2 ν) (x : Vec d) (i k a : Fin d)
    (u : Lp ℝ 2 ν) :
    letI := nv_vaddInvariant_of_stationary ν hν
    HasDerivAt (fun t : ℝ ↦ ⟪u, koopman (μ := ν) (t • (Pi.single a 1 : Vec d))
        ((nv_memLp_entryEval ν hν hobs x i k).toLp (nv_entryEval x i k))⟫_ℝ)
      ⟪u, vectorL2Coord (μ := ν) a
        ((nv_memLp_entryGrad ν hd hν hobs x i k).toLp (nv_entryGrad x i k))⟫_ℝ 0 := by
  have := nv_vaddInvariant_of_stationary ν hν
  have h := nv_hasHorizontalGradient_entry ν hd hν hobs x i k a
  exact ((innerSL ℝ u).hasFDerivAt).comp_hasDerivAt (0 : ℝ) h

/-! ## Coordinates of the forcing -/

theorem nv_fieldForcing_single (b a : Fin d) (j : ShellField d) :
    nv_fieldForcing (Pi.single b 1 : Vec d) j a = nv_entryEval 0 a b j := by
  change (∑ c : Fin d, j 0 a c * (Pi.single b 1 : Vec d) c) = j 0 a b
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hcb
    simp [Pi.single_eq_of_ne hcb]
  · simp

theorem nv_vectorL2Coord_toLp_fieldForcing (ν : Measure (ShellField d))
    (hν : ∀ z : Vec d, Measure.map (ShellField.translate z) ν = ν)
    (hobs : MemLp (ShellField.j3Observable d 0) 2 ν) (b a : Fin d)
    (hmem : MemLp (nv_fieldForcing (Pi.single b 1 : Vec d)) 2 ν) :
    vectorL2Coord (μ := ν) a (hmem.toLp (nv_fieldForcing (Pi.single b 1 : Vec d))) =
      (nv_memLp_entryEval ν hν hobs 0 a b).toLp (nv_entryEval 0 a b) := by
  refine Lp.ext ?_
  have h1 : (vectorL2Coord (μ := ν) a (hmem.toLp (nv_fieldForcing (Pi.single b 1 : Vec d))) :
      ShellField d → ℝ) =ᵐ[ν] fun j ↦ (hmem.toLp (nv_fieldForcing (Pi.single b 1 : Vec d)) :
        ShellField d → HilbertVec d) j a := ContinuousLinearMap.coeFn_compLpL _ _
  have h2 := hmem.coeFn_toLp
  have h3 := (nv_memLp_entryEval ν hν hobs 0 a b).coeFn_toLp
  filter_upwards [h1, h2, h3] with j hj1 hj2 hj3
  rw [hj1, hj2, hj3, nv_fieldForcing_single]

theorem nv_entry_diag_zero (j : ShellField d) (x : Vec d) (i : Fin d) : j x i i = 0 := by
  have h := j.skew_entry x i i
  linarith only [h]

/-- The correlation function of the `a`-th coordinate of the forcing with the `(0, 1)` entry
vanishes for `a ≠ 0`: the coordinate is zero, or a different independent entry. -/
theorem nv_correlation_forcing_zero (hd : 2 ≤ d) (ε : ℝ) (a : Fin d) (ha : a.val ≠ 0) (y : Vec d) :
    ∫ j, nv_entryEval 0 a ⟨1, by omega⟩ j * nv_entryEval y ⟨0, by omega⟩ ⟨1, by omega⟩ j
      ∂(nv_seedShellLaw d ε).toMeasure = 0 := by
  by_cases h1 : a.val = 1
  · have : ∀ j : ShellField d, nv_entryEval 0 a ⟨1, by omega⟩ j = 0 := fun j ↦ by
      have ha1 : a = ⟨1, by omega⟩ := Fin.ext h1
      rw [ha1]
      exact nv_entry_diag_zero j 0 _
    simp [this]
  · have h2 : 1 < a.val := by omega
    have : ∀ j : ShellField d, nv_entryEval 0 a ⟨1, by omega⟩ j =
        -nv_entryEval 0 ⟨1, by omega⟩ a j := fun j ↦ j.skew_entry 0 a ⟨1, by omega⟩
    simp only [this, neg_mul, integral_neg]
    rw [nv_integral_entry_mul_ne ε (p := (⟨(⟨1, by omega⟩, a), h2⟩ : SkewIdx d))
      (q := (⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.lt_def]⟩ : SkewIdx d)) (by
        intro h
        have := congrArg (fun r : SkewIdx d ↦ r.1.1.val) h
        simp at this) 0 y]
    simp

/-- The pairing of the `a`-th coordinate of the forcing with the Koopman translate of the
`(0, 1)` entry, as a correlation integral. -/
theorem nv_inner_coord_forcing_koopman (ν : Measure (ShellField d))
    (hν : ∀ z : Vec d, Measure.map (ShellField.translate z) ν = ν)
    (hobs : MemLp (ShellField.j3Observable d 0) 2 ν) (b a i k : Fin d) (x z : Vec d)
    (hmem : MemLp (nv_fieldForcing (Pi.single b 1 : Vec d)) 2 ν) :
    letI := nv_vaddInvariant_of_stationary ν hν
    ⟪vectorL2Coord (μ := ν) a (hmem.toLp (nv_fieldForcing (Pi.single b 1 : Vec d))),
        koopman (μ := ν) z ((nv_memLp_entryEval ν hν hobs x i k).toLp (nv_entryEval x i k))⟫_ℝ =
      ∫ j, nv_entryEval 0 a b j * nv_entryEval (x + z) i k j ∂ν := by
  have := nv_vaddInvariant_of_stationary ν hν
  rw [nv_vectorL2Coord_toLp_fieldForcing ν hν hobs b a hmem,
    nv_inner_toLp_koopman ν hν z (nv_memLp_entryEval ν hν hobs 0 a b)
      (nv_memLp_entryEval ν hν hobs x i k)]
  rfl

/-- **Positive response energy for the Gaussian seed.** -/
theorem nv_shellEnergy_seed_pos (hd : 2 ≤ d) (ε : ℝ) (hε : ε ≠ 0)
    (hobs : MemLp (ShellField.j3Observable d 0) 2 (nv_seedShellLaw d ε).toMeasure)
    (hmem : MemLp (nv_fieldForcing (Pi.single (⟨1, by omega⟩ : Fin d) 1 : Vec d)) 2
      (nv_seedShellLaw d ε).toMeasure) :
    0 < nv_shellEnergy (nv_seedShellLaw d ε).toMeasure (nv_seedShellLaw_map_translate d ε)
      (Pi.single (⟨1, by omega⟩ : Fin d) 1) hmem := by
  have hdpos : 0 < d := by omega
  set ν := (nv_seedShellLaw d ε).toMeasure with hνdef
  have hν := nv_seedShellLaw_map_translate d ε
  have := nv_vaddInvariant_of_stationary ν hν
  set i0 : Fin d := ⟨0, hdpos⟩ with hi0
  set i1 : Fin d := ⟨1, by omega⟩ with hi1
  set F := hmem.toLp (nv_fieldForcing (Pi.single i1 1 : Vec d)) with hF
  by_contra hcon
  have hkey : ∀ x : Vec d, ⟪F, (nv_memLp_entryGrad ν hdpos hν hobs x i0 i1).toLp
      (nv_entryGrad x i0 i1)⟫_ℝ = 0 := by
    intro x
    by_contra h
    exact hcon (nv_shellEnergy_pos_of_hasHorizontalGradient ν hν _ hmem
      ((nv_memLp_entryEval ν hν hobs x i0 i1).toLp (nv_entryEval x i0 i1)) _
      (nv_hasHorizontalGradient_entry ν hdpos hν hobs x i0 i1) h)
  -- the derivative of the correlation along each axis
  have hder : ∀ (x : Vec d) (a : Fin d),
      HasDerivAt (fun t : ℝ ↦ ∫ j, nv_entryEval 0 a i1 j *
          nv_entryEval (x + t • (Pi.single a 1 : Vec d)) i0 i1 j ∂ν)
        ⟪vectorL2Coord (μ := ν) a F, vectorL2Coord (μ := ν) a
          ((nv_memLp_entryGrad ν hdpos hν hobs x i0 i1).toLp (nv_entryGrad x i0 i1))⟫_ℝ 0 := by
    intro x a
    have h := nv_hasDerivAt_pairing hdpos ν hν hobs x i0 i1 a (vectorL2Coord (μ := ν) a F)
    have hfun : (fun t : ℝ ↦ ⟪vectorL2Coord (μ := ν) a F, koopman (μ := ν)
        (t • (Pi.single a 1 : Vec d))
        ((nv_memLp_entryEval ν hν hobs x i0 i1).toLp (nv_entryEval x i0 i1))⟫_ℝ) =
        fun t : ℝ ↦ ∫ j, nv_entryEval 0 a i1 j *
          nv_entryEval (x + t • (Pi.single a 1 : Vec d)) i0 i1 j ∂ν := by
      funext t
      exact nv_inner_coord_forcing_koopman ν hν hobs i1 a i0 i1 x _ hmem
    rw [hfun] at h
    exact h
  -- the terms with `a ≠ 0` vanish
  have hzero : ∀ (x : Vec d) (a : Fin d), a ≠ i0 →
      ⟪vectorL2Coord (μ := ν) a F, vectorL2Coord (μ := ν) a
        ((nv_memLp_entryGrad ν hdpos hν hobs x i0 i1).toLp (nv_entryGrad x i0 i1))⟫_ℝ = 0 := by
    intro x a ha
    have h0 : (fun t : ℝ ↦ ∫ j, nv_entryEval 0 a i1 j *
        nv_entryEval (x + t • (Pi.single a 1 : Vec d)) i0 i1 j ∂ν) = fun _ ↦ 0 := by
      funext t
      exact nv_correlation_forcing_zero hd ε a (fun h ↦ ha (Fin.ext h)) _
    have h1 := hder x a
    rw [h0] at h1
    exact h1.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have hmain : ∀ x : Vec d,
      HasDerivAt (fun t : ℝ ↦ ε ^ 2 * nvCov (0 : Vec d) (x + t • (Pi.single i0 1 : Vec d))) 0 0 := by
    intro x
    have h1 := hder x i0
    have hsum := nv_inner_eq_sum_coord ν F ((nv_memLp_entryGrad ν hdpos hν hobs x i0 i1).toLp
      (nv_entryGrad x i0 i1))
    rw [Finset.sum_eq_single i0 (fun a _ ha ↦ hzero x a ha) (fun h ↦ absurd (Finset.mem_univ i0) h),
      ] at hsum
    rw [← hsum, hkey x] at h1
    have hfun : (fun t : ℝ ↦ ∫ j, nv_entryEval 0 i0 i1 j *
        nv_entryEval (x + t • (Pi.single i0 1 : Vec d)) i0 i1 j ∂ν) =
        fun t : ℝ ↦ ε ^ 2 * nvCov (0 : Vec d) (x + t • (Pi.single i0 1 : Vec d)) := by
      funext t
      exact nv_integral_entry_mul_self ε (⟨(i0, i1), by simp [hi0, hi1, Fin.lt_def]⟩ : SkewIdx d) 0 _
    rw [hfun] at h1
    exact h1
  set e0 : Vec d := Pi.single i0 1 with he0
  set g : ℝ → ℝ := fun s ↦ ε ^ 2 * nvCov (0 : Vec d) (s • e0) with hg
  have hgd : ∀ s : ℝ, HasDerivAt g 0 s := by
    intro s
    have h := hmain (s • e0)
    have h2 : HasDerivAt (fun u : ℝ ↦ ε ^ 2 * nvCov (0 : Vec d) (s • e0 + (u - s) • e0)) 0 s :=
      HasDerivAt.comp_sub_const s s (by simpa using h)
    convert h2 using 1
    funext u
    simp only [hg, ← add_smul, add_sub_cancel]
  have hconst := is_const_of_deriv_eq_zero (fun s ↦ (hgd s).differentiableAt)
    (fun s ↦ (hgd s).deriv) 0 1
  have hg0 : g 0 = ε ^ 2 * nvCov (0 : Vec d) 0 := by simp [hg]
  have hg1 : g 1 = 0 := by
    have hnorm : 1 ≤ Book.Ch02.vecNorm ((1 : ℝ) • e0 - 0) := by
      rw [one_smul, sub_zero, he0, nv_vecNorm_single]
    simp only [hg, nvCov_comm (0 : Vec d), nvCov_eq_zero_of_one_le_vecNorm hnorm, mul_zero]
  have hpos : 0 < ε ^ 2 * nvCov (0 : Vec d) 0 :=
    mul_pos (by positivity) (nvCov_self_pos _)
  rw [hg0, hg1] at hconst
  exact hpos.ne' hconst

/-! ## J5 for the Gaussian law -/

/-- **J5 for the Gaussian shell law.** The product law of the Gaussian seed of amplitude
`nv_epsJ3 d` satisfies the non-degeneracy condition J5, with `cStar` the common response energy of
the seed divided by `log 3`, and `K = 1`. -/
theorem nv_shellLawJ5_gaussLaw (hd : 2 ≤ d) :
    ∃ cStar K : ℝ, ShellLawJ5 d (nv_gaussLaw d) cStar K (nv_gaussLaw_prefix hd)
      nv_gaussLaw_J2 (nv_gaussLaw_J3 (by omega)) := by
  have hJ3 : ShellLawJ3 d (nv_productLaw (nv_seedShellLaw d (nv_epsJ3 d))) :=
    nv_gaussLaw_J3 (by omega)
  have hν := nv_seedShellLaw_map_translate d (nv_epsJ3 d)
  have hall : ∀ e : Vec d, MemLp (nv_fieldForcing e) 2 (nv_seedShellLaw d (nv_epsJ3 d)).toMeasure :=
    nv_memLp_fieldForcing_of_basis _ fun a ↦
      nv_memLp_fieldForcing_seed _ hJ3 (Pi.single a 1) (nv_vecNorm_single a)
  have hrot : ∀ (R : Mat d) (hR : IsSignedPermutationMatrix R),
      Measure.map (ShellField.rotate R hR) (nv_seedShellLaw d (nv_epsJ3 d)).toMeasure =
        (nv_seedShellLaw d (nv_epsJ3 d)).toMeasure :=
    fun R hR ↦ nv_seedShellLaw_map_rotate d _ R hR
  have hε : nv_epsJ3 d ≠ 0 := (nv_epsJ3_pos (by omega)).ne'
  have hq : 0 < nv_shellEnergy (nv_seedShellLaw d (nv_epsJ3 d)).toMeasure hν
      (Pi.single (⟨1, by omega⟩ : Fin d) 1) (hall _) :=
    nv_shellEnergy_seed_pos hd _ hε (nv_memLp_j3Observable_seed _ hJ3) (hall _)
  refine ⟨_, 1, nv_shellLawJ5_productLaw_of_energy hd _ hν hJ3 _ hq fun e he ↦ ?_⟩
  exact nv_shellEnergy_const_of_symmetric _ hν hall hrot ⟨1, by omega⟩ e he

end

/-! ## Satisfiability witness -/

/-- The hypotheses of the Koopman derivative are met by the Gaussian seed shell law of amplitude
`nv_epsJ3 2` in dimension two. -/
example (x : Vec 2) (i k : Fin 2) :
    letI := nv_vaddInvariant_of_stationary (nv_seedShellLaw 2 (nv_epsJ3 2)).toMeasure
      (nv_seedShellLaw_map_translate 2 _)
    HasHorizontalGradient (μ := (nv_seedShellLaw 2 (nv_epsJ3 2)).toMeasure)
      ((nv_memLp_entryEval (nv_seedShellLaw 2 (nv_epsJ3 2)).toMeasure
        (nv_seedShellLaw_map_translate 2 _)
        (nv_memLp_j3Observable_seed _ (nv_gaussLaw_J3 (by norm_num))) x i k).toLp
          (nv_entryEval x i k))
      ((nv_memLp_entryGrad (nv_seedShellLaw 2 (nv_epsJ3 2)).toMeasure (by norm_num)
        (nv_seedShellLaw_map_translate 2 _)
        (nv_memLp_j3Observable_seed _ (nv_gaussLaw_J3 (by norm_num))) x i k).toLp
          (nv_entryGrad x i k)) :=
  nv_hasHorizontalGradient_entry _ (by norm_num) (nv_seedShellLaw_map_translate 2 _)
    (nv_memLp_j3Observable_seed _ (nv_gaussLaw_J3 (by norm_num))) x i k

/-- The Gaussian seed shell law of amplitude `nv_epsJ3 2` has positive response energy in
dimension two, for the forcing in the second coordinate direction. -/
example : 0 < nv_shellEnergy (nv_seedShellLaw 2 (nv_epsJ3 2)).toMeasure
    (nv_seedShellLaw_map_translate 2 _) (Pi.single (⟨1, by norm_num⟩ : Fin 2) 1)
    (nv_memLp_fieldForcing_seed _ (nv_gaussLaw_J3 (by norm_num)) _ (nv_vecNorm_single _)) :=
  nv_shellEnergy_seed_pos (by norm_num) _ (nv_epsJ3_pos (by norm_num)).ne'
    (nv_memLp_j3Observable_seed _ (nv_gaussLaw_J3 (by norm_num))) _

/-- The hypotheses of the conjugation identity are met by the Gaussian seed shell law of amplitude
`nv_epsJ3 2` and the sign flip of the first coordinate in dimension two: the stationarity class,
the symmetric involutive signed permutation, and the invariance of the law under the rotation. -/
example :
    VAddInvariantMeasure (Vec 2) (ShellField 2) (nv_seedShellLaw 2 (nv_epsJ3 2)).toMeasure ∧
      matTranspose (nv_flipMat (0 : Fin 2)) = nv_flipMat 0 ∧
      nv_flipMat (0 : Fin 2) * nv_flipMat 0 = 1 ∧
      MeasurePreserving (ShellField.rotate (nv_flipMat (0 : Fin 2)) (nv_flipMat_signedPerm 0))
        (nv_seedShellLaw 2 (nv_epsJ3 2)).toMeasure (nv_seedShellLaw 2 (nv_epsJ3 2)).toMeasure :=
  ⟨nv_vaddInvariant_of_stationary _ (nv_seedShellLaw_map_translate 2 _), nv_flipMat_symm 0,
    nv_flipMat_mul 0, ⟨ShellField.measurable_rotate _ _, nv_seedShellLaw_map_rotate 2 _ _ _⟩⟩

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
