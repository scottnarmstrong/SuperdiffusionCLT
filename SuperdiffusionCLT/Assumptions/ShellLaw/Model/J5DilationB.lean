/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.J5Dilation
public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.ProductLaw
public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.GaussLaw

/-!
# Dilation covariance of the shell response energy

The dilation `D_c j (x) = j (x / c)` carries a stationary law `ν` to a stationary law, intertwines
the translation by `z / c` with the translation by `z`, and does not move the value at the origin.
Hence the stationary potential projection of the forcing `j ↦ j(0) e` has the same energy for
`ν` and for `(D_c)_* ν`, for every direction `e`.

* `nv_shellEnergy_map_dilate`: the energy is invariant under dilation of the law.
* `nv_shellEnergy_scaledShellLaw`: every dilated shell law has the energy of the seed law.
* `nv_norm_sq_blockPotentialResponse_productLaw`: the block response energy of the product law is
  `(m - n)` times the energy of the seed law.
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Probability.Stationary
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

theorem nv_fieldForcing_dilate (c : ℝˣ) (e : Vec d) (j : ShellField d) :
    nv_fieldForcing e (dilate c j) = nv_fieldForcing e j := by
  unfold nv_fieldForcing originForcing
  have h : (ShellField.forgetShell (dilate c j)) 0 = (ShellField.forgetShell j) 0 := by
    change (dilate c j) 0 = j 0
    simp
  rw [h]

/-- Dilation maps a stationary law to a stationary law. -/
theorem nv_stationary_map_dilate (ν : Measure (ShellField d))
    (hν : ∀ z : Vec d, Measure.map (ShellField.translate z) ν = ν) (c : ℝˣ) (z : Vec d) :
    Measure.map (ShellField.translate z) (Measure.map (dilate c) ν) = Measure.map (dilate c) ν := by
  rw [Measure.map_map (ShellField.measurable_translate z) (measurable_dilate c)]
  have h : ShellField.translate z ∘ dilate c =
      dilate c ∘ ShellField.translate (((c⁻¹ : ℝˣ) : ℝ) • z) := by
    funext j
    exact translate_dilate z c j
  rw [h, ← Measure.map_map (measurable_dilate c) (ShellField.measurable_translate _), hν]

/-- The forcing of a dilated law is square integrable when that of the seed law is. -/
theorem nv_memLp_fieldForcing_map_dilate (ν : Measure (ShellField d)) (c : ℝˣ) (e : Vec d)
    (hmem : MemLp (nv_fieldForcing e) 2 ν) :
    MemLp (nv_fieldForcing e) 2 (Measure.map (dilate c) ν) := by
  refine (memLp_map_measure_iff (measurable_nv_fieldForcing e).aestronglyMeasurable
    (measurable_dilate c).aemeasurable).mpr ?_
  have : nv_fieldForcing e ∘ dilate c = nv_fieldForcing e := by
    funext j
    exact nv_fieldForcing_dilate c e j
  rw [this]
  exact hmem

/-- **Dilation covariance of the response energy.** -/
theorem nv_shellEnergy_map_dilate (ν : Measure (ShellField d))
    (hν : ∀ z : Vec d, Measure.map (ShellField.translate z) ν = ν) (c : ℝˣ) (e : Vec d)
    (hmem : MemLp (nv_fieldForcing e) 2 ν)
    (hmem' : MemLp (nv_fieldForcing e) 2 (Measure.map (dilate c) ν)) :
    nv_shellEnergy (Measure.map (dilate c) ν) (nv_stationary_map_dilate ν hν c) e hmem' =
      nv_shellEnergy ν hν e hmem := by
  have := nv_vaddInvariant_of_stationary ν hν
  have := nv_vaddInvariant_of_stationary _ (nv_stationary_map_dilate ν hν c)
  set c' : ℝ := ((c⁻¹ : ℝˣ) : ℝ) with hc'
  have hc'ne : c' ≠ 0 := (c⁻¹).ne_zero
  let T : nv_Twist c' (ShellField d) → ShellField d := fun ω ↦ dilate c ω.untwist
  have hTm : Measurable T := measurable_dilate c
  have hT : MeasurePreserving T (nv_twistMeasure c' ν) (Measure.map (dilate c) ν) :=
    ⟨hTm, rfl⟩
  have hTequiv : ∀ (z : Vec d) (ω : nv_Twist c' (ShellField d)), T (z +ᵥ ω) = z +ᵥ T ω := by
    intro z ω
    exact (translate_dilate z c ω.untwist).symm
  have hnorm := norm_stationaryPotentialProjection_transportL2 hT hTequiv
    (hmem'.toLp (nv_fieldForcing e))
  have hU : transportL2 (HilbertVec d) hT (hmem'.toLp (nv_fieldForcing e)) =
      (hmem.toLp (nv_fieldForcing e) : VectorL2 d (nv_twistMeasure c' ν)) := by
    refine Lp.ext ?_
    have h1 := coeFn_transportL2 (μ := nv_twistMeasure c' ν) hT (hmem'.toLp (nv_fieldForcing e))
    have h2 : ((hmem'.toLp (nv_fieldForcing e) : ShellField d → HilbertVec d) ∘ T)
        =ᵐ[nv_twistMeasure c' ν] nv_fieldForcing e ∘ T := by
      refine ae_eq_comp hTm.aemeasurable ?_
      rw [hT.map_eq]
      exact hmem'.coeFn_toLp
    have h3 : (hmem.toLp (nv_fieldForcing e) : ShellField d → HilbertVec d)
        =ᵐ[ν] nv_fieldForcing e := hmem.coeFn_toLp
    filter_upwards [h1, h2, h3] with ω hh1 hh2 hh3
    rw [hh1]
    simp only [Function.comp_apply] at hh2 ⊢
    rw [hh2]
    exact (nv_fieldForcing_dilate c e ω.untwist).trans hh3.symm
  rw [hU] at hnorm
  have h2 := congrArg norm (nv_stationaryPotentialProjection_twist ν hc'ne (hmem.toLp (nv_fieldForcing e)))
  have h3 : ‖stationaryPotentialProjection (μ := ν) (hmem.toLp (nv_fieldForcing e))‖ =
      ‖stationaryPotentialProjection (μ := Measure.map (dilate c) ν)
        (hmem'.toLp (nv_fieldForcing e))‖ := h2.symm.trans hnorm
  unfold nv_shellEnergy
  exact (congrArg (fun x : ℝ ↦ x ^ 2) h3).symm

/-- Every dilated shell law has the energy of the seed law. -/
theorem nv_shellEnergy_scaledShellLaw (ν₀ : ProbabilityMeasure (ShellField d))
    (hν : ∀ z : Vec d, Measure.map (ShellField.translate z) ν₀.toMeasure = ν₀.toMeasure)
    (n : ℕ) (e : Vec d) (hmem : MemLp (nv_fieldForcing e) 2 ν₀.toMeasure)
    (hmemn : MemLp (nv_fieldForcing e) 2 (scaledShellLaw ν₀ n).toMeasure)
    (hνn : ∀ z : Vec d,
      Measure.map (ShellField.translate z) (scaledShellLaw ν₀ n).toMeasure =
        (scaledShellLaw ν₀ n).toMeasure) :
    nv_shellEnergy (scaledShellLaw ν₀ n).toMeasure hνn e hmemn =
      nv_shellEnergy ν₀.toMeasure hν e hmem := by
  have hmem' : MemLp (nv_fieldForcing e) 2 (Measure.map (dilate (nv_scaleUnit n)) ν₀.toMeasure) :=
    nv_memLp_fieldForcing_map_dilate _ _ e hmem
  have key := nv_shellEnergy_map_dilate ν₀.toMeasure hν (nv_scaleUnit n) e hmem hmem'
  have heq : (scaledShellLaw ν₀ n).toMeasure =
      Measure.map (dilate (nv_scaleUnit n)) ν₀.toMeasure := scaledShellLaw_toMeasure ν₀ n
  unfold nv_shellEnergy at key ⊢
  rw [← key]
  congr 1

theorem nv_shellEnergy_congr {ν ν' : Measure (ShellField d)} (h : ν = ν')
    (hν : ∀ z : Vec d, Measure.map (ShellField.translate z) ν = ν)
    (hν' : ∀ z : Vec d, Measure.map (ShellField.translate z) ν' = ν') (e : Vec d)
    (hmem : MemLp (nv_fieldForcing e) 2 ν) (hmem' : MemLp (nv_fieldForcing e) 2 ν') :
    nv_shellEnergy ν hν e hmem = nv_shellEnergy ν' hν' e hmem' := by
  subst h
  rfl

/-- The forcing of the seed law is square integrable when J3 holds for the product law. -/
theorem nv_memLp_fieldForcing_seed (ν₀ : ProbabilityMeasure (ShellField d))
    (hJ3 : ShellLawJ3 d (nv_productLaw ν₀)) (e : Vec d) (he : Book.Ch02.vecNorm e = 1) :
    MemLp (nv_fieldForcing e) 2 ν₀.toMeasure := by
  have h := nv_memLp_fieldForcing_marginal hJ3 e he 0
  rwa [nv_shellMarginalLaw_productLaw, scaledShellLaw_zero] at h

/-- **The block response energy of the product law is `(m - n)` times the seed energy.** -/
theorem nv_norm_sq_blockPotentialResponse_productLaw (hd : 2 ≤ d)
    (ν₀ : ProbabilityMeasure (ShellField d))
    (hν : ∀ z : Vec d, Measure.map (ShellField.translate z) ν₀.toMeasure = ν₀.toMeasure)
    (hJ3 : ShellLawJ3 d (nv_productLaw ν₀)) (n m : ℕ) (e : Vec d)
    (he : Book.Ch02.vecNorm e = 1) :
    ‖blockPotentialResponse (nv_productLaw ν₀) n m
        (blockRegLaw_stationary (nv_shellLawPrefix_productLaw hd ν₀ hν)
          (nv_shellLawJ2_productLaw ν₀) n m) e
        (memLp_originForcing_blockRegLaw hJ3 n m e he)‖ ^ 2 =
      ((m - n : ℕ) : ℝ) * nv_shellEnergy ν₀.toMeasure hν e
        (nv_memLp_fieldForcing_seed ν₀ hJ3 e he) := by
  rw [nv_norm_sq_blockPotentialResponse_eq (nv_shellLawPrefix_productLaw hd ν₀ hν)
    (nv_shellLawJ2_productLaw ν₀) hJ3 n m e he]
  have hterm : ∀ l ∈ Finset.Ioc n m,
      nv_shellEnergy (ShellField.shellMarginalLaw (nv_productLaw ν₀) l).toMeasure
        ((nv_shellLawPrefix_productLaw hd ν₀ hν).stationary l) e
        (nv_memLp_fieldForcing_marginal hJ3 e he l) =
      nv_shellEnergy ν₀.toMeasure hν e (nv_memLp_fieldForcing_seed ν₀ hJ3 e he) := by
    intro l _
    have hl : (ShellField.shellMarginalLaw (nv_productLaw ν₀) l).toMeasure =
        (scaledShellLaw ν₀ l).toMeasure := by
      rw [nv_shellMarginalLaw_productLaw]
    have hstat : ∀ z : Vec d, Measure.map (ShellField.translate z) (scaledShellLaw ν₀ l).toMeasure =
        (scaledShellLaw ν₀ l).toMeasure := map_translate_scaledShellLaw ν₀ hν l
    have hmemL : MemLp (nv_fieldForcing e) 2 (scaledShellLaw ν₀ l).toMeasure :=
      hl ▸ nv_memLp_fieldForcing_marginal hJ3 e he l
    exact (nv_shellEnergy_congr hl _ hstat e _ hmemL).trans
      (nv_shellEnergy_scaledShellLaw ν₀ hν l e (nv_memLp_fieldForcing_seed ν₀ hJ3 e he) hmemL hstat)
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]

end

/-! ## Satisfiability witnesses -/

/-- The product law of the Gaussian seed of amplitude `nv_epsJ3 2` in dimension two meets every
hypothesis of the block energy identity. -/
example (n m : ℕ) (e : Vec 2) (he : Book.Ch02.vecNorm e = 1) :
    ‖blockPotentialResponse (nv_gaussLaw 2) n m
        (blockRegLaw_stationary (nv_shellLawPrefix_productLaw (by norm_num)
          (nv_seedShellLaw 2 (nv_epsJ3 2)) (nv_seedShellLaw_map_translate 2 _))
          (nv_shellLawJ2_productLaw _) n m) e
        (memLp_originForcing_blockRegLaw (nv_gaussLaw_J3 (by norm_num)) n m e he)‖ ^ 2 =
      ((m - n : ℕ) : ℝ) * nv_shellEnergy (nv_seedShellLaw 2 (nv_epsJ3 2)).toMeasure
        (nv_seedShellLaw_map_translate 2 _) e
        (nv_memLp_fieldForcing_seed _ (nv_gaussLaw_J3 (by norm_num)) e he) :=
  nv_norm_sq_blockPotentialResponse_productLaw (by norm_num) _
    (nv_seedShellLaw_map_translate 2 _) (nv_gaussLaw_J3 (by norm_num)) n m e he

/-- The rescaled-action projection identity has a nontrivial instance: the Dirac law at zero on
the shell carrier, rescaling factor two. -/
example (F : VectorL2 2 (Measure.dirac (ShellField.zero 2))) :
    haveI : VAddInvariantMeasure (Vec 2) (ShellField 2) (Measure.dirac (ShellField.zero 2)) :=
      nv_vaddInvariant_of_stationary _ fun z ↦ by
        rw [Measure.map_dirac' (ShellField.measurable_translate z), ShellField.translate_zero]
    stationaryPotentialProjection (μ := nv_twistMeasure (2 : ℝ) (Measure.dirac (ShellField.zero 2)))
        (d := 2) (F : VectorL2 2 (nv_twistMeasure (2 : ℝ) (Measure.dirac (ShellField.zero 2)))) =
      stationaryPotentialProjection (μ := Measure.dirac (ShellField.zero 2)) (d := 2) F := by
  have : VAddInvariantMeasure (Vec 2) (ShellField 2) (Measure.dirac (ShellField.zero 2)) :=
    nv_vaddInvariant_of_stationary _ fun z ↦ by
      rw [Measure.map_dirac' (ShellField.measurable_translate z), ShellField.translate_zero]
  exact nv_stationaryPotentialProjection_twist _ (by norm_num) F

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
