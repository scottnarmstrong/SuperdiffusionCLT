/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.BoundaryC
public import SuperdiffusionCLT.Section7.Lipschitz.BoundaryOriginB
public import SuperdiffusionCLT.Section7.Lipschitz.Calc
public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.IterationD
public import Mathlib.Order.CompletePartialOrder

/-!
# From the frame of the centre to the boundary estimate in `ℝ≥0∞`

The estimate in the frame of the centre `z` (real carriers, the dilation `t`, the exponent `E + 1`
of the datum) gives the display at the centre `z` of the fine grid, in `ℝ≥0∞`: translation of the
solution and of the zero trace, comparison of the values of `σ̄` at the scales `m'` and `m`, and
the passage from the real carriers to the normalized norms.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

variable {d : ℕ}

/-- Containment of the cube in the dilate, seen from the centre. -/
theorem lip_fine_subset_iff (z : Vec d) (n : ℕ) (S : Set (Vec d)) :
    shiftCube z (n : ℤ) ⊆ S ↔ shiftCube (0 : Vec d) (n : ℤ) ⊆ translateSet (-z) S := by
  rw [← lip_interior_translate_shiftCube z n]
  constructor
  · intro h x hx
    rw [mem_translateSet_iff_sub_mem] at hx ⊢
    exact h hx
  · intro h w hw
    have hw' : w - z ∈ translateSet (-z) (shiftCube z (n : ℤ)) := by
      rw [mem_translateSet_iff_sub_mem]
      have e : w - z - -z = w := by abel
      rw [e]; exact hw
    have := h hw'
    rw [mem_translateSet_iff_sub_mem] at this
    have e : w - z - -z = w := by abel
    rwa [e] at this

private theorem lip_fine_ofReal_sum {K σ Fr G1 G2 α β D mE : ℝ} {m' : ℕ} (hK : 0 ≤ K)
    (hσ : 0 < σ) (hFr : 0 ≤ Fr) (hG1 : 0 ≤ G1) (hG2 : 0 ≤ G2) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hD : 0 ≤ D) (hmE : 0 ≤ mE) :
    ENNReal.ofReal (K * ((3 : ℝ)⁻¹) ^ m') * (ENNReal.ofReal α + ENNReal.ofReal β) +
        ENNReal.ofReal (K * σ⁻¹ * (3 : ℝ) ^ m') * ENNReal.ofReal Fr +
        ENNReal.ofReal (K * D) * ENNReal.ofReal G1 +
        ENNReal.ofReal (K * mE * (3 : ℝ) ^ m') * ENNReal.ofReal G2 =
      ENNReal.ofReal (K * ((3 : ℝ)⁻¹) ^ m' * (α + β) + K * σ⁻¹ * (3 : ℝ) ^ m' * Fr +
        K * D * G1 + K * mE * (3 : ℝ) ^ m' * G2) := by
  have h1 : 0 ≤ K * ((3 : ℝ)⁻¹) ^ m' := by positivity
  have h2 : 0 ≤ K * σ⁻¹ * (3 : ℝ) ^ m' := by positivity
  have h3 : 0 ≤ K * D := by positivity
  have h4 : 0 ≤ K * mE * (3 : ℝ) ^ m' := by positivity
  rw [← ENNReal.ofReal_add hα hβ, ← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h2,
    ← ENNReal.ofReal_mul h3, ← ENNReal.ofReal_mul h4,
    ← ENNReal.ofReal_add (mul_nonneg h1 (add_nonneg hα hβ)) (mul_nonneg h2 hFr),
    ← ENNReal.ofReal_add (add_nonneg (mul_nonneg h1 (add_nonneg hα hβ)) (mul_nonneg h2 hFr))
      (mul_nonneg h3 hG1),
    ← ENNReal.ofReal_add (add_nonneg (add_nonneg (mul_nonneg h1 (add_nonneg hα hβ))
      (mul_nonneg h2 hFr)) (mul_nonneg h3 hG1)) (mul_nonneg h4 hG2)]

/-- **The display at the centre `z`**, from the estimate in the frame of `z`. -/
theorem lip_fine_main [NeZero d] {a a' : CoeffField d} {nu C0 K σ σ' E t : ℝ} {z : Vec d}
    {n m' m : ℕ} {U : Set (Vec d)}
    (hC0 : 1 ≤ C0) (hK : K = 4 * C0) (hσ : 0 < σ) (hσ' : 0 < σ') (h1 : σ ≤ 2 * σ')
    (h2 : σ' ≤ 2 * σ) (hnm' : n < m') (hm'm : m' ≤ m)
    (hnE : (n : ℝ) ^ (-(E + 1)) ≤ (m : ℝ) ^ (-E))
    (hUo : IsOpen (t • U)) (hzt : z ∈ t • U)
    (hframe : ∀ (f : Vec d → ℝ) (u : H1Function (shiftCube z (m' : ℤ) ∩ t • U)),
      IsWeakSolutionOn a (shiftCube z (m' : ℤ) ∩ t • U) u f (fun _ => 0) →
      ∃ v : H1Function (translateSet (-z) (shiftCube z (m' : ℤ) ∩ t • U)),
        (∀ x, v.toFun x = u.toFun (x + z)) ∧ (∀ x, v.grad x = u.grad (x + z)) ∧
        IsWeakSolutionOn a' (translateSet (-z) (shiftCube z (m' : ℤ) ∩ t • U)) v
          (fun x => f (x + z)) (fun _ => 0))
    (horigin :
          ∀ (f g : Vec d → ℝ) (F G1 G2 : ℝ)
            (u : H1Function (shiftCube (0 : Vec d) (m' : ℤ) ∩ translateSet (-z) (t • U))),
            ContDiff ℝ 2 g → 0 ≤ F → 0 ≤ G1 → 0 ≤ G2 →
            (∀ x ∈ shiftCube (0 : Vec d) (m' : ℤ), ‖fderiv ℝ g x‖ ≤ G1) →
            (∀ x ∈ shiftCube (0 : Vec d) (m' : ℤ), ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ G2) →
            (∀ᵐ x ∂volume.restrict (shiftCube (0 : Vec d) (m' : ℤ) ∩ translateSet (-z) (t • U)),
              |f x| ≤ F) →
            IsWeakSolutionOn
              (a')
              (shiftCube (0 : Vec d) (m' : ℤ) ∩ translateSet (-z) (t • U)) u f (fun _ => 0) →
            LocalizedZeroTraceFunctionOn
              (shiftCube (0 : Vec d) (m' : ℤ) ∩ translateSet (-z) (t • U))
              (shiftCube (0 : Vec d) (m' : ℤ)) (fun x => u.toFun x - g x) →
            AEStronglyMeasurable f
              (volume.restrict (shiftCube (0 : Vec d) (m' : ℤ) ∩ translateSet (-z) (t • U))) →
            ∀ R : ℝ,
              R = C0 * (((3 : ℝ)⁻¹) ^ m' *
                  (lipL2 (shiftCube (0 : Vec d) (m' : ℤ) ∩ translateSet (-z) (t • U))
                      (fun x => u.toFun x -
                        ⨍ w in shiftCube (0 : Vec d) (m' : ℤ) ∩ translateSet (-z) (t • U),
                          u.toFun w) +
                    lipL2 (shiftCube (0 : Vec d) (m' : ℤ) ∩ translateSet (-z) (t • U))
                      (fun x => u.toFun x - g x)) +
                (σ')⁻¹ * (3 : ℝ) ^ m' * F +
                ((m' : ℝ) - (n : ℝ)) * G1 + (n : ℝ) ^ (-(E + 1)) * (3 : ℝ) ^ m' * G2) →
            (Real.sqrt (σ'))⁻¹ * Real.sqrt nu *
                lipGradL2 (shiftCube (0 : Vec d) (n : ℤ) ∩ translateSet (-z) (t • U)) u.grad +
              ((3 : ℝ)⁻¹) ^ n *
                lipL2 (shiftCube (0 : Vec d) (n : ℤ) ∩ translateSet (-z) (t • U))
                  (fun x => u.toFun x -
                    ⨍ w in shiftCube (0 : Vec d) (n : ℤ) ∩ translateSet (-z) (t • U),
                      u.toFun w) ≤ R ∧
            (¬ shiftCube (0 : Vec d) (n : ℤ) ⊆ translateSet (-z) (t • U) →
              ((3 : ℝ)⁻¹) ^ n *
                lipL2 (shiftCube (0 : Vec d) (n : ℤ) ∩ translateSet (-z) (t • U))
                  (fun x => u.toFun x - g x) ≤ R)) :
          ∀ (f g : Vec d → ℝ), ContDiff ℝ 2 g →
          ∀ u : H1Function (shiftCube z (m' : ℤ) ∩ t • U),
            IsWeakSolutionOn a
              (shiftCube z (m' : ℤ) ∩ t • U) u f (fun _ => 0) →
            LocalizedZeroTraceFunctionOn (shiftCube z (m' : ℤ) ∩ t • U)
              (shiftCube z (m' : ℤ)) (fun x => u.toFun x - g x) →
            ∀ R : ℝ≥0∞,
              R = ENNReal.ofReal (K * (3 : ℝ) ^ (-(m' : ℝ))) *
                  (lpBar (shiftCube z (m' : ℤ) ∩ t • U) 2
                      (fun x => u.toFun x - ⨍ w in shiftCube z (m' : ℤ) ∩ t • U, u.toFun w) +
                    lpBar (shiftCube z (m' : ℤ) ∩ t • U) 2 (fun x => u.toFun x - g x)) +
                ENNReal.ofReal (K * σ⁻¹ * (3 : ℝ) ^ m') *
                  eLpNorm f ⊤ (volume.restrict (shiftCube z (m' : ℤ) ∩ t • U)) +
                ENNReal.ofReal (K * ((m' : ℝ) - (n : ℝ))) *
                  eLpNorm (fun x => ‖fderiv ℝ g x‖) ⊤ (volume.restrict (shiftCube z (m' : ℤ))) +
                ENNReal.ofReal (K * (m : ℝ) ^ (-E) * (3 : ℝ) ^ m') *
                  eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ g) x‖) ⊤
                    (volume.restrict (shiftCube z (m' : ℤ))) →
            -- e.Dir.new.C01.boundary, with the oscillation kept on the left
            ENNReal.ofReal ((Real.sqrt σ)⁻¹ * Real.sqrt nu) *
                  lpBar (shiftCube z (n : ℤ) ∩ t • U) 2 (fun x => eucNorm (u.grad x)) +
                ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
                  lpBar (shiftCube z (n : ℤ) ∩ t • U) 2
                    (fun x => u.toFun x - ⨍ w in shiftCube z (n : ℤ) ∩ t • U, u.toFun w) ≤ R ∧
              -- on a cube that meets the boundary, the solution itself is flat relative to `g`
              (¬ shiftCube z (n : ℤ) ⊆ t • U →
                ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
                  lpBar (shiftCube z (n : ℤ) ∩ t • U) 2 (fun x => u.toFun x - g x) ≤ R)
 := by
  intro f g hg u hu hzero R hR
  classical
  have hQo : ∀ j : ℕ, IsOpen (shiftCube z (j : ℤ)) := fun j => lip_bdry_approx_isOpen_cube z j
  have hDo : ∀ j : ℕ, IsOpen (shiftCube z (j : ℤ) ∩ t • U) := fun j => (hQo j).inter hUo
  have hDm : ∀ j : ℕ, MeasurableSet (shiftCube z (j : ℤ) ∩ t • U) := fun j =>
    (hDo j).measurableSet
  have hzD : ∀ j : ℕ, z ∈ shiftCube z (j : ℤ) ∩ t • U := fun j =>
    ⟨by rw [lip_bdry_approx_shiftCube_eq_ball]; exact Metric.mem_ball_self (by positivity), hzt⟩
  have hD0 : ∀ j : ℕ, volume (shiftCube z (j : ℤ) ∩ t • U) ≠ 0 := fun j =>
    ((hDo j).measure_pos volume ⟨z, hzD j⟩).ne'
  have hDT : ∀ j : ℕ, volume (shiftCube z (j : ℤ) ∩ t • U) ≠ ⊤ := fun j =>
    ne_top_of_le_ne_top (lip_bdry_approx_vol_cube_ne_top z j)
      (measure_mono Set.inter_subset_left)
  have hfin : ∀ j : ℕ, IsFiniteMeasure (volume.restrict (shiftCube z (j : ℤ) ∩ t • U)) :=
    fun j => ⟨by simpa using (hDT j).lt_top⟩
  have hsub : shiftCube z (n : ℤ) ∩ t • U ⊆ shiftCube z (m' : ℤ) ∩ t • U :=
    Set.inter_subset_inter_left _ (lip_bdry_approx_cube_mono z hnm'.le)
  have hm0 : (0 : ℝ) < m := by
    have : (0 : ℝ) < m' := by exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le n) hnm'
    have h' : (m' : ℝ) ≤ m := by exact_mod_cast hm'm
    linarith only [this, h']
  have hC0p : 0 < K := by rw [hK]; linarith only [hC0]
  by_cases hRtop : R = ⊤
  · rw [hRtop]; exact ⟨le_top, fun _ => le_top⟩
  rw [hR] at hRtop
  simp only [ENNReal.add_eq_top, not_or] at hRtop
  obtain ⟨⟨⟨-, hf⟩, hg1⟩, hg2⟩ := hRtop
  have hf_ne : eLpNorm f ⊤ (volume.restrict (shiftCube z (m' : ℤ) ∩ t • U)) ≠ ⊤ := by
    intro h
    refine hf ?_
    rw [h, ENNReal.mul_top]
    exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hnm'R : (0 : ℝ) < (m' : ℝ) - n := by
    have : (n : ℝ) < m' := by exact_mod_cast hnm'
    linarith only [this]
  have hg1_ne : eLpNorm (fun x => ‖fderiv ℝ g x‖) ⊤ (volume.restrict (shiftCube z (m' : ℤ))) ≠ ⊤ := by
    intro h
    refine hg1 ?_
    rw [h, ENNReal.mul_top]
    exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hg2_ne : eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ g) x‖) ⊤
      (volume.restrict (shiftCube z (m' : ℤ))) ≠ ⊤ := by
    intro h
    refine hg2 ?_
    rw [h, ENNReal.mul_top]
    exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  obtain ⟨Fr, hFr⟩ : ∃ Fr : ℝ, Fr = (eLpNorm f ⊤ (volume.restrict
      (shiftCube z (m' : ℤ) ∩ t • U))).toReal := ⟨_, rfl⟩
  obtain ⟨G1, hG1⟩ : ∃ G1 : ℝ, G1 = (eLpNorm (fun x => ‖fderiv ℝ g x‖) ⊤
      (volume.restrict (shiftCube z (m' : ℤ)))).toReal := ⟨_, rfl⟩
  obtain ⟨G2, hG2⟩ : ∃ G2 : ℝ, G2 = (eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ g) x‖) ⊤
      (volume.restrict (shiftCube z (m' : ℤ)))).toReal := ⟨_, rfl⟩
  have hFr0 : 0 ≤ Fr := by rw [hFr]; exact ENNReal.toReal_nonneg
  have hG10 : 0 ≤ G1 := by rw [hG1]; exact ENNReal.toReal_nonneg
  have hG20 : 0 ≤ G2 := by rw [hG2]; exact ENNReal.toReal_nonneg
  have hFre : ENNReal.ofReal Fr = eLpNorm f ⊤ (volume.restrict
      (shiftCube z (m' : ℤ) ∩ t • U)) := by rw [hFr]; exact ENNReal.ofReal_toReal hf_ne
  have hG1e : ENNReal.ofReal G1 = eLpNorm (fun x => ‖fderiv ℝ g x‖) ⊤
      (volume.restrict (shiftCube z (m' : ℤ))) := by rw [hG1]; exact ENNReal.ofReal_toReal hg1_ne
  have hG2e : ENNReal.ofReal G2 = eLpNorm (fun x => ‖fderiv ℝ (fderiv ℝ g) x‖) ⊤
      (volume.restrict (shiftCube z (m' : ℤ))) := by rw [hG2]; exact ENNReal.ofReal_toReal hg2_ne
  have hg1c : Continuous (fun x => ‖fderiv ℝ g x‖) :=
    (hg.continuous_fderiv (by norm_num)).norm
  have hg2c : Continuous (fun x => ‖fderiv ℝ (fderiv ℝ g) x‖) :=
    ((hg.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by simp)).norm
  have hg1pt : ∀ x ∈ shiftCube z (m' : ℤ), ‖fderiv ℝ g x‖ ≤ G1 := by
    refine lip_fine_le_of_ae_le (hQo m') hg1c ?_
    filter_upwards [lip_fine_ae_abs_le hg1_ne] with x hx
    rw [hG1]
    exact (le_abs_self _).trans hx
  have hg2pt : ∀ x ∈ shiftCube z (m' : ℤ), ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ G2 := by
    refine lip_fine_le_of_ae_le (hQo m') hg2c ?_
    filter_upwards [lip_fine_ae_abs_le hg2_ne] with x hx
    rw [hG2]
    exact (le_abs_self _).trans hx
  obtain ⟨hg'c, hg'1, hg'2⟩ := lip_fine_fderiv_translate hg z
  have hcube0 : ∀ x, x ∈ shiftCube (0 : Vec d) (m' : ℤ) → x + z ∈ shiftCube z (m' : ℤ) := by
    intro x hx
    rw [← lip_interior_translate_shiftCube z m', mem_translateSet_iff_sub_mem] at hx
    simpa using hx
  have hG1' : ∀ x ∈ shiftCube (0 : Vec d) (m' : ℤ), ‖fderiv ℝ (fun x => g (x + z)) x‖ ≤ G1 := by
    intro x hx
    rw [hg'1 x]
    exact hg1pt _ (hcube0 x hx)
  have hG2' : ∀ x ∈ shiftCube (0 : Vec d) (m' : ℤ),
      ‖fderiv ℝ (fderiv ℝ (fun x => g (x + z))) x‖ ≤ G2 := by
    intro x hx
    rw [hg'2 x]
    exact hg2pt _ (hcube0 x hx)
  obtain ⟨v, hvf, hvg, hvs⟩ := hframe f u hu
  obtain ⟨v0, hv0f, hv0g, hv0s⟩ := lip_interior_congr_solution
    (lip_fine_translate_inter z m' (t • U)) v hvs
  have hv0f' : v0.toFun = fun x => u.toFun (x + z) := by rw [hv0f]; exact funext hvf
  have hv0g' : v0.grad = fun x => u.grad (x + z) := by rw [hv0g]; exact funext hvg
  have hmp : MeasurePreserving (fun x : Vec d => x + z) volume volume :=
    measurePreserving_add_right volume z
  have hpre : (fun x : Vec d => x + z) ⁻¹' (shiftCube z (m' : ℤ) ∩ t • U) =
      shiftCube (0 : Vec d) (m' : ℤ) ∩ translateSet (-z) (t • U) := by
    rw [← lip_fine_translate_inter z m' (t • U)]
    ext x
    simp [mem_translateSet_iff_sub_mem, sub_eq_add_neg]
  have hae0 : ∀ᵐ x ∂volume.restrict (shiftCube (0 : Vec d) (m' : ℤ) ∩ translateSet (-z) (t • U)),
      |f (x + z)| ≤ Fr := by
    have haeD : ∀ᵐ x ∂volume.restrict (shiftCube z (m' : ℤ) ∩ t • U), |f x| ≤ Fr := by
      rw [hFr]; exact lip_fine_ae_abs_le hf_ne
    have := (hmp.restrict_preimage (hDm m')).quasiMeasurePreserving.ae haeD
    rwa [hpre] at this
  have hmeas0 : AEStronglyMeasurable (fun x => f (x + z))
      (volume.restrict (shiftCube (0 : Vec d) (m' : ℤ) ∩ translateSet (-z) (t • U))) := by
    have := (lip_fine_aesm_of_ne_top hf_ne).comp_quasiMeasurePreserving
      (hmp.restrict_preimage (hDm m')).quasiMeasurePreserving
    rw [hpre] at this
    exact this
  have hzero' : LocalizedZeroTraceFunctionOn
      (shiftCube (0 : Vec d) (m' : ℤ) ∩ translateSet (-z) (t • U))
      (shiftCube (0 : Vec d) (m' : ℤ)) (fun x => v0.toFun x - (fun x => g (x + z)) x) := by
    have := lip_fine_loc_translate z hzero
    rw [lip_fine_translate_inter z m' (t • U), lip_interior_translate_shiftCube z m'] at this
    rw [hv0f']
    exact this
  have hO := horigin (fun x => f (x + z)) (fun x => g (x + z)) Fr G1 G2 v0 hg'c hFr0 hG10 hG20
    hG1' hG2' hae0 hv0s hzero' hmeas0 _ rfl
  obtain ⟨hI, hII⟩ := hO
  rw [hv0f', hv0g'] at hI
  rw [hv0f'] at hII
  beta_reduce at hI hII
  rw [← lip_fine_translate_inter z m' (t • U), ← lip_fine_translate_inter z n (t • U)] at hI hII
  rw [lip_fine_lipL2_osc z _ (hDm m') u.toFun, lip_fine_lipL2_diff z _ u.toFun g,
    lip_fine_lipL2_osc z _ (hDm n) u.toFun, lip_fine_lipGradL2 z _ u.grad] at hI
  rw [lip_fine_lipL2_osc z _ (hDm m') u.toFun,
    lip_fine_lipL2_diff z (shiftCube z (m' : ℤ) ∩ t • U) u.toFun g,
    lip_fine_lipL2_diff z (shiftCube z (n : ℤ) ∩ t • U) u.toFun g] at hII
  have hII' : ¬ shiftCube z (n : ℤ) ⊆ t • U → ((3 : ℝ)⁻¹) ^ n *
      lipL2 (shiftCube z (n : ℤ) ∩ t • U) (fun x => u.toFun x - g x) ≤ _ := fun hn =>
    hII (fun h => hn ((lip_fine_subset_iff z n (t • U)).2 h))
  -- finiteness of the normalized norms
  have := hfin m'
  have := hfin n
  have hgL2 : MemLp g 2 (volume.restrict (shiftCube z (m' : ℤ) ∩ t • U)) := by
    obtain ⟨Cg, hCg⟩ := (isCompact_closedBall z ((3 : ℝ) ^ m' / 2)).exists_bound_of_continuousOn
      hg.continuous.continuousOn
    refine MemLp.of_bound hg.continuous.aestronglyMeasurable Cg ?_
    rw [ae_restrict_iff' (hDm m')]
    refine Filter.Eventually.of_forall fun x hx => hCg x ?_
    have := hx.1
    rw [lip_bdry_approx_shiftCube_eq_ball] at this
    exact Metric.ball_subset_closedBall this
  have hmem_osc : ∀ j : ℕ, j ≤ m' → MemLp (fun x => u.toFun x -
      ⨍ w in shiftCube z (j : ℤ) ∩ t • U, u.toFun w) 2
      (volume.restrict (shiftCube z (j : ℤ) ∩ t • U)) := by
    intro j hj
    have := hfin j
    have hsj : shiftCube z (j : ℤ) ∩ t • U ⊆ shiftCube z (m' : ℤ) ∩ t • U :=
      Set.inter_subset_inter_left _ (lip_bdry_approx_cube_mono z hj)
    exact (u.memL2.mono_measure (Measure.restrict_mono hsj le_rfl)).sub (memLp_const _)
  have hmem_diff : ∀ j : ℕ, j ≤ m' → MemLp (fun x => u.toFun x - g x) 2
      (volume.restrict (shiftCube z (j : ℤ) ∩ t • U)) := by
    intro j hj
    have hsj : shiftCube z (j : ℤ) ∩ t • U ⊆ shiftCube z (m' : ℤ) ∩ t • U :=
      Set.inter_subset_inter_left _ (lip_bdry_approx_cube_mono z hj)
    exact ((u.memL2.sub hgL2)).mono_measure (Measure.restrict_mono hsj le_rfl)
  have hmem_grad : MemLp (fun x => eucNorm (u.grad x)) 2
      (volume.restrict (shiftCube z (n : ℤ) ∩ t • U)) :=
    (memLp_eucNorm_grad u).mono_measure (Measure.restrict_mono hsub le_rfl)
  have e_grad := lip_lpBar_ne_top (hD0 n) hmem_grad
  have e_oscn := lip_lpBar_ne_top (hD0 n) (hmem_osc n hnm'.le)
  have e_oscm := lip_lpBar_ne_top (hD0 m') (hmem_osc m' le_rfl)
  have e_diffn := lip_lpBar_ne_top (hD0 n) (hmem_diff n hnm'.le)
  have e_diffm := lip_lpBar_ne_top (hD0 m') (hmem_diff m' le_rfl)
  have h3n : (3 : ℝ) ^ (-(n : ℝ)) = ((3 : ℝ)⁻¹) ^ n := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]
  have h3m : (3 : ℝ) ^ (-(m' : ℝ)) = ((3 : ℝ)⁻¹) ^ m' := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]
  -- the real numbers
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = lipGradL2 (shiftCube z (n : ℤ) ∩ t • U) u.grad := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = lipL2 (shiftCube z (n : ℤ) ∩ t • U)
      (fun x => u.toFun x - ⨍ w in shiftCube z (n : ℤ) ∩ t • U, u.toFun w) := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = lipL2 (shiftCube z (n : ℤ) ∩ t • U)
      (fun x => u.toFun x - g x) := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = lipL2 (shiftCube z (m' : ℤ) ∩ t • U)
      (fun x => u.toFun x - ⨍ w in shiftCube z (m' : ℤ) ∩ t • U, u.toFun w) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = lipL2 (shiftCube z (m' : ℤ) ∩ t • U)
      (fun x => u.toFun x - g x) := ⟨_, rfl⟩
  have hγ0 : 0 ≤ γ := by rw [hγ]; exact ENNReal.toReal_nonneg
  have hδ0 : 0 ≤ δ := by rw [hδ]; exact ENNReal.toReal_nonneg
  have hκ0 : 0 ≤ κ := by rw [hκ]; exact ENNReal.toReal_nonneg
  have hα0 : 0 ≤ α := by rw [hα]; exact ENNReal.toReal_nonneg
  have hβ0 : 0 ≤ β := by rw [hβ]; exact ENNReal.toReal_nonneg
  rw [← hγ, ← hδ, ← hα, ← hβ] at hI
  rw [← hκ, ← hβ, ← hα] at hII'
  have r_grad : lpBar (shiftCube z (n : ℤ) ∩ t • U) 2 (fun x => eucNorm (u.grad x)) =
      ENNReal.ofReal γ := by rw [hγ]; exact (ENNReal.ofReal_toReal e_grad).symm
  have r_oscn : lpBar (shiftCube z (n : ℤ) ∩ t • U) 2
      (fun x => u.toFun x - ⨍ w in shiftCube z (n : ℤ) ∩ t • U, u.toFun w) = ENNReal.ofReal δ := by
    rw [hδ]; exact (ENNReal.ofReal_toReal e_oscn).symm
  have r_diffn : lpBar (shiftCube z (n : ℤ) ∩ t • U) 2 (fun x => u.toFun x - g x) =
      ENNReal.ofReal κ := by rw [hκ]; exact (ENNReal.ofReal_toReal e_diffn).symm
  have r_oscm : lpBar (shiftCube z (m' : ℤ) ∩ t • U) 2
      (fun x => u.toFun x - ⨍ w in shiftCube z (m' : ℤ) ∩ t • U, u.toFun w) = ENNReal.ofReal α := by
    rw [hα]; exact (ENNReal.ofReal_toReal e_oscm).symm
  have r_diffm : lpBar (shiftCube z (m' : ℤ) ∩ t • U) 2 (fun x => u.toFun x - g x) =
      ENNReal.ofReal β := by rw [hβ]; exact (ENNReal.ofReal_toReal e_diffm).symm
  have hRreal : R = ENNReal.ofReal (K * ((3 : ℝ)⁻¹) ^ m' * (α + β) + K * σ⁻¹ * (3 : ℝ) ^ m' * Fr +
      K * ((m' : ℝ) - n) * G1 + K * (m : ℝ) ^ (-E) * (3 : ℝ) ^ m' * G2) := by
    rw [hR, r_oscm, r_diffm, hFre.symm, hG1e.symm, hG2e.symm, h3m]
    exact lip_fine_ofReal_sum hC0p.le hσ hFr0 hG10 hG20 hα0 hβ0 hnm'R.le
      (Real.rpow_nonneg hm0.le _)
  have hc1 : (Real.sqrt σ)⁻¹ * Real.sqrt nu ≤ 2 * ((Real.sqrt σ')⁻¹ * Real.sqrt nu) := by
    have := lip_inv_sqrt_le hσ hσ' (by linarith only [h2, hσ])
    nlinarith only [mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg nu)]
  have hinv : σ'⁻¹ ≤ 2 * σ⁻¹ := lip_inv_le hσ h1
  -- the bound of the original estimate by the target constant
  have hRo_le : 2 * (C0 * (((3 : ℝ)⁻¹) ^ m' * (α + β) + σ'⁻¹ * (3 : ℝ) ^ m' * Fr +
      ((m' : ℝ) - n) * G1 + (n : ℝ) ^ (-(E + 1)) * (3 : ℝ) ^ m' * G2)) ≤
      K * ((3 : ℝ)⁻¹) ^ m' * (α + β) + K * σ⁻¹ * (3 : ℝ) ^ m' * Fr +
        K * ((m' : ℝ) - n) * G1 + K * (m : ℝ) ^ (-E) * (3 : ℝ) ^ m' * G2 := by
    have c0 : 0 ≤ C0 := by linarith only [hC0]
    have p1 : 0 ≤ ((3 : ℝ)⁻¹) ^ m' * (α + β) :=
      mul_nonneg (pow_nonneg (by norm_num) _) (add_nonneg hα0 hβ0)
    have p2 : 0 ≤ (3 : ℝ) ^ m' * Fr := mul_nonneg (pow_nonneg (by norm_num) _) hFr0
    have p3 : 0 ≤ ((m' : ℝ) - n) * G1 := mul_nonneg hnm'R.le hG10
    have p4 : 0 ≤ (3 : ℝ) ^ m' * G2 := mul_nonneg (pow_nonneg (by norm_num) _) hG20
    have q2 : σ'⁻¹ * ((3 : ℝ) ^ m' * Fr) ≤ 2 * σ⁻¹ * ((3 : ℝ) ^ m' * Fr) :=
      mul_le_mul_of_nonneg_right hinv p2
    have q4 : (n : ℝ) ^ (-(E + 1)) * ((3 : ℝ) ^ m' * G2) ≤
        (m : ℝ) ^ (-E) * ((3 : ℝ) ^ m' * G2) := mul_le_mul_of_nonneg_right hnE p4
    have p5 : 0 ≤ (m : ℝ) ^ (-E) * ((3 : ℝ) ^ m' * G2) :=
      mul_nonneg (Real.rpow_nonneg hm0.le _) p4
    rw [hK]
    nlinarith only [mul_le_mul_of_nonneg_left q2 c0, mul_le_mul_of_nonneg_left q4 c0, p1, p3, c0,
      mul_nonneg c0 p1, mul_nonneg c0 p3, mul_nonneg c0 p5]
  rw [hRreal]
  refine ⟨?_, ?_⟩
  · have h3p : 0 ≤ ((3 : ℝ)⁻¹) ^ n := pow_nonneg (by norm_num) n
    have hc0 : 0 ≤ (Real.sqrt σ)⁻¹ * Real.sqrt nu :=
      mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    rw [r_grad, r_oscn, h3n, ← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul h3p,
      ← ENNReal.ofReal_add (mul_nonneg hc0 hγ0) (mul_nonneg h3p hδ0)]
    refine ENNReal.ofReal_le_ofReal ?_
    have s1 := mul_le_mul_of_nonneg_right hc1 hγ0
    have s2 : 0 ≤ ((3 : ℝ)⁻¹) ^ n * δ := mul_nonneg h3p hδ0
    nlinarith only [hI, hRo_le, s1, s2, hγ0, hδ0]
  · intro hn
    have h3p : 0 ≤ ((3 : ℝ)⁻¹) ^ n := pow_nonneg (by norm_num) n
    rw [r_diffn, h3n, ← ENNReal.ofReal_mul h3p]
    refine ENNReal.ofReal_le_ofReal ?_
    have := hII' hn
    have s2 : 0 ≤ ((3 : ℝ)⁻¹) ^ n * κ := mul_nonneg h3p hκ0
    have c0 : 0 ≤ C0 := by linarith only [hC0]
    nlinarith only [this, hRo_le, s2, hα0, hβ0, hFr0, hG10, hG20, c0, hC0, hnm'R]

end SuperdiffusionCLT.Section7
