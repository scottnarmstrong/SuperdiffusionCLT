/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Assumptions.ShellLaw.Model.SeedCovarianceD

/-!
# Invariances in law of the scalar seed field

Translation of a scalar field is defined on the scalar carrier. A measurable self-map `T` of the
carrier of the form `T f x = σ * f (g x)` with `σ ^ 2 = 1` and `nvCov (g x) (g y) = nvCov x y`
preserves the law `nv_seedLaw d ε` (law uniqueness from the Gaussian finite-dimensional marginals).
This gives invariance under translations, signed permutations of the coordinates and negation.

## Main results

* `ScalarC2Field.nv_translate`, `ScalarC2Field.measurable_nv_translate`
* `nv_seedLaw_map_eq_self`: the general invariance criterion
* `nv_seedLaw_map_translate`, `nv_seedLaw_map_signedPerm`, `nv_seedLaw_map_neg`
-/

@[expose] public section

namespace SuperdiffusionCLT.Assumptions.ShellLaw.Model

open Homogenization MeasureTheory

noncomputable section

variable {d : ℕ}

namespace ScalarC2Field

def seedTranslateAmbient (v : Vec d) : ScalarAmbient d → ScalarAmbient d := fun p ↦
  (p.1.comp ⟨fun x ↦ x + v, continuous_id.add continuous_const⟩,
    (p.2.1.comp ⟨fun x ↦ x + v, continuous_id.add continuous_const⟩,
      p.2.2.comp ⟨fun x ↦ x + v, continuous_id.add continuous_const⟩))

theorem continuous_seedTranslateAmbient (v : Vec d) :
    Continuous (seedTranslateAmbient v) :=
  ((ContinuousMap.continuous_precomp _).comp continuous_fst).prodMk
    (((ContinuousMap.continuous_precomp _).comp continuous_snd.fst).prodMk
      ((ContinuousMap.continuous_precomp _).comp continuous_snd.snd))

/-- Translation `f ↦ f (· + v)` of a scalar field. -/
def nv_translate (v : Vec d) (f : ScalarC2Field d) : ScalarC2Field d :=
  ⟨seedTranslateAmbient v f.1, by
    refine ⟨?_, ?_⟩
    · intro x
      exact ((f.hasFDerivAt (x + v)).comp x ((hasFDerivAt_id x).add_const v)).congr_fderiv
        (by simp; rfl)
    · intro x
      exact ((f.deriv_hasFDerivAt (x + v)).comp x ((hasFDerivAt_id x).add_const v)).congr_fderiv
        (by simp; rfl)⟩

@[simp]
theorem nv_translate_apply (v : Vec d) (f : ScalarC2Field d) (x : Vec d) :
    nv_translate v f x = f (x + v) :=
  rfl

theorem continuous_nv_translate (v : Vec d) : Continuous (nv_translate (d := d) v) :=
  Continuous.subtype_mk
    ((continuous_seedTranslateAmbient v).comp continuous_subtype_val)
    (fun f ↦ (nv_translate v f).2)

theorem measurable_nv_translate (v : Vec d) : Measurable (nv_translate (d := d) v) :=
  (continuous_nv_translate v).measurable

end ScalarC2Field

/-- **Invariance criterion.** A measurable self-map `T f x = σ * f (g x)` of the scalar carrier
with `σ ^ 2 = 1` and `nvCov (g x) (g y) = nvCov x y` preserves the law of the seed field. -/
theorem nv_seedLaw_map_eq_self (ε : ℝ) (T : ScalarC2Field d → ScalarC2Field d)
    (hT : Measurable T) (σ : ℝ) (hσ : σ ^ 2 = 1) (g : Vec d → Vec d)
    (hTg : ∀ (f : ScalarC2Field d) (x : Vec d), T f x = σ * f (g x))
    (hg : ∀ x y, nvCov (g x) (g y) = nvCov x y) :
    (nv_seedLaw d ε).map T = nv_seedLaw d ε := by
  refine nv_scalarField_map_eq_self d T hT _ fun s ↦ ?_
  rw [nv_seedLaw_marginal_eq]
  have hs : Measurable fun (f : ScalarC2Field d) (x : s) ↦ T f (x : Vec d) :=
    measurable_pi_iff.2 fun x ↦ (ScalarC2Field.measurable_eval (x : Vec d)).comp hT
  have hL : (nv_seedLaw d ε).map (fun (f : ScalarC2Field d) (x : s) ↦ T f (x : Vec d))
      = (nvNoiseLaw d).map (nv_vec (fun _ : s ↦ σ * ε) (fun x : s ↦ g (x : Vec d))) := by
    unfold nv_seedLaw
    rw [Measure.map_map hs (nv_measurable_seedMap ε)]
    congr 1
    funext ξ x
    simp only [Function.comp_apply, nv_vec, hTg, nv_seedMap_apply]
    ring
  rw [hL]
  refine nv_map_vec_eq _ _ _ _ fun j l ↦ ?_
  rw [hg]
  have : σ * ε * (σ * ε) = ε * ε * σ ^ 2 := by ring
  rw [this, hσ, mul_one]

/-- The seed law is invariant under translations. -/
theorem nv_seedLaw_map_translate (ε : ℝ) (v : Vec d) :
    (nv_seedLaw d ε).map (ScalarC2Field.nv_translate v) = nv_seedLaw d ε :=
  nv_seedLaw_map_eq_self ε _ (ScalarC2Field.measurable_nv_translate v) 1 (by norm_num)
    (fun x ↦ x + v) (fun f x ↦ by simp) (fun x y ↦ nvCov_translate x y v)

/-- The seed law is invariant under `φ ↦ -φ`. -/
theorem nv_seedLaw_map_neg (ε : ℝ) :
    (nv_seedLaw d ε).map (ScalarC2Field.smulConst (-1)) = nv_seedLaw d ε :=
  nv_seedLaw_map_eq_self ε _ (ScalarC2Field.measurable_smulConst (-1)) (-1) (by norm_num)
    id (fun f x ↦ by simp) (fun _ _ ↦ rfl)

/-- The signed permutation as a continuous linear map. -/
def nv_signedPermCLM (σ : Equiv.Perm (Fin d)) (s : Fin d → ℝ) : Vec d →L[ℝ] Vec d :=
  LinearMap.toContinuousLinearMap
    { toFun := nv_signedPerm σ s
      map_add' := fun x y ↦ by funext i; simp [nv_signedPerm, mul_add]
      map_smul' := fun c x ↦ by funext i; simp [nv_signedPerm]; ring }

theorem nv_signedPermCLM_apply (σ : Equiv.Perm (Fin d)) (s : Fin d → ℝ) (x : Vec d) :
    nv_signedPermCLM σ s x = nv_signedPerm σ s x := rfl

/-- The seed law is invariant under precomposition with a signed permutation of the
coordinates. -/
theorem nv_seedLaw_map_signedPerm (ε : ℝ) (σ : Equiv.Perm (Fin d)) (s : Fin d → ℝ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) :
    (nv_seedLaw d ε).map (ScalarC2Field.precomp (nv_signedPermCLM σ s)) = nv_seedLaw d ε :=
  nv_seedLaw_map_eq_self ε _ (ScalarC2Field.measurable_precomp _) 1 (by norm_num)
    (nv_signedPerm σ s) (fun f x ↦ by simp [nv_signedPermCLM_apply])
    (fun x y ↦ nvCov_signedPerm σ s hs x y)

/-! ## Satisfiability witnesses -/

/-- In dimension two: the variance at a point is positive, the covariance at distance at least one
vanishes, and the law of the sum of the values at two such points is the centred Gaussian of the
sum of the two variances. -/
example : ∃ x y : Vec 2, 0 < nvCov x x ∧ nvCov x y = 0 ∧
    (nvNoiseLaw 2).map (fun ξ ↦ nv_seed ξ x + nv_seed ξ y)
      = ProbabilityTheory.gaussianReal 0 (nvCov x x + nvCov y y).toNNReal := by
  refine ⟨0, Pi.single 0 1, nvCov_self_pos _, nvCov_eq_zero_of_one_le ?_, ?_⟩
  · simp [Pi.single_apply]
  · have h := nv_map_comb_eq_gaussianReal (fun _ : Fin 2 ↦ (1 : ℝ))
      (![0, Pi.single 0 1] : Fin 2 → Vec 2)
    have h0 : nvCov (0 : Vec 2) (Pi.single 0 1) = 0 :=
      nvCov_eq_zero_of_one_le (by simp [Pi.single_apply])
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, nvVar,
      mul_one, h0, nvCov_comm _ (0 : Vec 2), add_zero, zero_add] at h
    exact h

/-- The invariance criterion has satisfiable hypotheses: translations of the plane. -/
example : (nv_seedLaw 2 1).map (ScalarC2Field.nv_translate (Pi.single 0 1))
    = nv_seedLaw 2 1 := nv_seedLaw_map_translate 1 _

end

end SuperdiffusionCLT.Assumptions.ShellLaw.Model
