/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Linfty.Prop

/-!
# The `L^∞` homogenization proposition: the pointwise core

For a fixed sample, `linf_pt_core` bounds the three terms of the proposition for the pair `(u, ū)`
with the general datum `g` by the bound for the pair `(v, v̄)` with a smooth datum `gt` plus the
datum errors, which are absorbed through the polynomial scale separation (`linf_real_bound`).
-/

@[expose] public section

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open scoped ENNReal Pointwise

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

/-- **The pointwise core** of the proposition for a fixed sample: for a domain `W` inside the cube
`3^n`, with the layer ratio bound, a smooth datum `gt` with `|gt - g| ≤ C_g 3^m ‖∇g‖_∞` and the
black-box bound for `(v, v̄)` of the smooth datum, the three terms for `(u, ū)` are at most the
bound for `(v, v̄)` plus `K δ log n 3^n ‖∇g‖_∞`. -/
theorem linf_pt_core [NeZero d] (Cf cv Cg : ℝ) (hCf : 1 ≤ Cf) (hcv : 0 ≤ cv) (hCg : 1 ≤ Cg) :
    ∃ K : ℝ, 0 < K ∧ ∀ {W : Set (Vec d)}, IsOpen W → IsBoundedDomain W → volume W ≠ 0 →
      ∀ {n m : ℕ}, W ⊆ axisCube (fun _ => -((3 : ℝ) ^ n / 2)) ((3 : ℝ) ^ n) →
      volume (boundaryLayer W (3 * (4 * (3 : ℝ) ^ m))) / volume W ≤
        ENNReal.ofReal (cv * ((3 : ℝ) ^ m / (3 : ℝ) ^ n)) →
      (n : ℝ) ^ 24 * (3 : ℝ) ^ m ≤ (3 : ℝ) ^ n →
      ∀ {ν ε ρ σ Cs : ℝ} (a : CoeffField d) (S : Mat d), 3 ≤ (n : ℝ) → 0 < ν → ν ≤ 1 →
        1 ≤ (n : ℝ) * ν → 0 < ε → ε ≤ 1 → 1 ≤ (n : ℝ) * ε ^ 2 → 0 < ρ → ρ < 1 → 1 ≤ σ →
        IsEllipticFieldOn ν ((ν + Cf * (n : ℝ) ^ (1 + ρ)) ^ 2 / ν) W (fun x => a x - S) →
        (∀ (w : H1Function W) (f : Vec d → ℝ),
          IsWeakSolutionOn a W w f (fun _ => 0) ↔
            IsWeakSolutionOn (fun x => a x - S) W w f (fun _ => 0)) →
        ∀ (f : Vec d → ℝ) (g : H1Function W) {F G' : ℝ}, 0 ≤ F → 0 ≤ G' →
          AEStronglyMeasurable f (volume.restrict W) → (∀ᵐ x ∂volume.restrict W, |f x| ≤ F) →
          (∀ᵐ x ∂volume.restrict W, eucNorm (g.grad x) ≤ G') →
        ∀ {gt : Vec d → ℝ}, ContDiff ℝ (⊤ : ℕ∞) gt →
          (∀ᵐ x ∂volume.restrict W, |gt x - g.toFun x| ≤ Cg * (3 : ℝ) ^ m * G') →
          (∀ x, ‖fderiv ℝ gt x‖ ≤ Cg * G') →
          (∀ x, ‖fderiv ℝ (fderiv ℝ gt) x‖ ≤ Cg * G' / (3 : ℝ) ^ m) →
        (∀ v vh : H1Function W, IsWeakSolutionOn a W v f (fun _ => 0) →
          MemH10 W (fun x => v.toFun x - gt x) →
          IsWeakSolutionOn (fun _ => σ • (1 : Mat d)) W vh f (fun _ => 0) →
          MemH10 W (fun x => vh.toFun x - gt x) →
          eLpNorm (fun x => v.toFun x - vh.toFun x) ⊤ (volume.restrict W) +
              hMinusOneVec W (fun x => v.grad x - vh.grad x) +
              hMinusOneVec W (fun x =>
                matVecMul (σ⁻¹ • (a x - S)) (v.grad x) - vh.grad x) ≤
            ENNReal.ofReal (Cs * deltaScale ε ρ (n : ℝ) *
              (σ⁻¹ * (3 : ℝ) ^ (2 * n) * F + Real.log (n : ℝ) * (3 : ℝ) ^ n * (Cg * G')))) →
        ∀ (u uhom : H1Function W), IsDirichletSolution a W f g u →
          IsDirichletSolution (fun _ => σ • (1 : Mat d)) W f g uhom →
          eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤ (volume.restrict W) +
              hMinusOneVec W (fun x => u.grad x - uhom.grad x) +
              hMinusOneVec W (fun x =>
                matVecMul (σ⁻¹ • (a x - S)) (u.grad x) - uhom.grad x) ≤
            ENNReal.ofReal (Cs * deltaScale ε ρ (n : ℝ) *
                (σ⁻¹ * (3 : ℝ) ^ (2 * n) * F + Real.log (n : ℝ) * (3 : ℝ) ^ n * (Cg * G'))) +
              ENNReal.ofReal (K * (deltaScale ε ρ (n : ℝ) * Real.log (n : ℝ) * (3 : ℝ) ^ n) * G') := by
  obtain ⟨C₁, hC₁, Hcmp⟩ := linf_compare (d := d)
  obtain ⟨K0, hK0, HK⟩ := linf_real_bound d C₁ Cf cv Cg hC₁.le hCf hCg
  have hsq0 : 0 ≤ Real.sqrt cv := Real.sqrt_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨(2 + 3 * d) * Cg + 2 * C₁ * Cg * Real.sqrt cv * (1 + Cf) ^ 4, by positivity, ?_⟩
  intro W hWo hWb hW0 n m hWL hlay hpow ν ε ρ σ Cs a S hn hν hν1 hνn hε hε1 hεn hρ hρ1 hσ hEll htr
    f g F G' hF hG' hfm hfF hgG gt hgt hgc hg1 hg2 hS u uhom hu huh
  have hWm : MeasurableSet W := hWo.measurableSet
  have hn0 : (0 : ℝ) < n := by linarith only [hn]
  have hT : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have h3m : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hσ0 : 0 < σ := by linarith only [hσ]
  have hGs0 : 0 ≤ Cg * G' := by positivity
  have hc0 : 0 ≤ Cg * (3 : ℝ) ^ m * G' := by positivity
  set Λ : ℝ := (ν + Cf * (n : ℝ) ^ (1 + ρ)) ^ 2 / ν with hΛdef
  have hνΛ : ν ≤ Λ := by
    obtain ⟨x₀, hx₀⟩ := nonempty_of_measure_ne_zero hW0
    exact (hEll.2 x₀ hx₀).2.1
  have hgt1 : ContDiff ℝ 1 gt := hgt.of_le (by exact_mod_cast le_top)
  have : IsFiniteMeasure (volume.restrict W) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 (volume_ne_top_of_isBoundedDomain hWb)⟩
  have hf2 : MemScalarL2 W f :=
    MemLp.of_bound hfm F (hfF.mono fun x hx => by rwa [Real.norm_eq_abs])
  obtain ⟨v, hv1, hv2⟩ := li1_dirichlet_exists hWo hWb hEll hf2 hgt1
  obtain ⟨vh, hvh1, hvh2⟩ := li1_dirichlet_exists hWo hWb
    (rc_isEllipticFieldOn_smul_one hσ0 hWm) hf2 hgt1
  have hu' : IsDirichletSolution (fun x => a x - S) W f g u := ⟨(htr u f).1 hu.1, hu.2⟩
  have hgG' : ∀ᵐ x ∂volume.restrict W, eucNorm (g.grad x) ≤ Cg * G' := by
    filter_upwards [hgG] with x hx
    nlinarith only [hx, hG', hCg]
  have e2 : 2 * (6 * (3 : ℝ) ^ m) = 3 * (4 * (3 : ℝ) ^ m) := by ring
  have cmp := Hcmp hWo hWb hW0 (fun _ => -((3 : ℝ) ^ n / 2)) hT hWL hν hνΛ hσ0 hEll g u uhom v vh
    hgt1 hu' huh hv1 hv2 hvh1 hvh2 (c := Cg * (3 : ℝ) ^ m * G') (G := Cg * G')
    (r := 6 * (3 : ℝ) ^ m) hc0 hGs0 (by positivity) hgc hgG' (fun x _ => hg1 x)
  rw [e2] at cmp
  have hES := hS v vh ((htr v f).2 hv1) hv2 hvh1 hvh2
  simp only [s12_matVecMul_smul_left] at hES ⊢
  -- the layer factor
  set η : ℝ := (3 : ℝ) ^ m / (3 : ℝ) ^ n with hη
  have hη0 : 0 ≤ η := by positivity
  set s : ℝ := Real.sqrt η with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = η := Real.sq_sqrt hη0
  have hlay' : (volume (boundaryLayer W (3 * (4 * (3 : ℝ) ^ m))) / volume W) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt cv * s) := by
    calc (volume (boundaryLayer W (3 * (4 * (3 : ℝ) ^ m))) / volume W) ^ (1 / 2 : ℝ)
        ≤ (ENNReal.ofReal (cv * η)) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hlay (by norm_num)
      _ = ENNReal.ofReal ((cv * η) ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
      _ = ENNReal.ofReal (Real.sqrt cv * s) := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_mul hcv]
  have hsn : s * (n : ℝ) ^ 12 ≤ 1 := by
    have h1 : η * (n : ℝ) ^ 24 ≤ 1 := by
      rw [hη, div_mul_eq_mul_div, div_le_one hT]
      linarith only [hpow]
    by_contra hcon
    have hcon' := not_le.1 hcon
    have : 1 < (s * (n : ℝ) ^ 12) ^ 2 := by nlinarith only [hcon']
    have e : (s * (n : ℝ) ^ 12) ^ 2 = η * (n : ℝ) ^ 24 := by rw [mul_pow, hs2]; ring
    linarith only [this, e, h1]
  -- the real inequality
  have hrc : Cg * (3 : ℝ) ^ m * G' ≤ Cg * s ^ 2 * (3 : ℝ) ^ n * G' := by
    rw [hs2, hη]
    apply le_of_eq
    field_simp
  have hGr : Cg * G' + Cg * (3 : ℝ) ^ m * G' / (6 * (3 : ℝ) ^ m) ≤ 2 * Cg * G' := by
    have : Cg * (3 : ℝ) ^ m * G' / (6 * (3 : ℝ) ^ m) = Cg * G' / 6 := by field_simp
    rw [this]; nlinarith only [hGs0]
  have hGr0 : 0 ≤ Cg * G' + Cg * (3 : ℝ) ^ m * G' / (6 * (3 : ℝ) ^ m) := by positivity
  have hreal := HK (n := (n : ℝ)) (ν := ν) (ε := ε) (ρ := ρ) (σ := σ) (Λ := Λ)
    (T := (3 : ℝ) ^ n) (G' := G') (c := Cg * (3 : ℝ) ^ m * G')
    (Gr := Cg * G' + Cg * (3 : ℝ) ^ m * G' / (6 * (3 : ℝ) ^ m)) (s := s) hn hν hν1 hνn hε hε1 hεn
    hρ hρ1 hσ hΛdef hT hG' hc0 hrc hGr0 hGr hs0 hsn
  -- the collection
  have hX0 : 0 ≤ C₁ * (3 : ℝ) ^ n * σ⁻¹ * Λ * (Λ / ν) *
      (Cg * G' + Cg * (3 : ℝ) ^ m * G' / (6 * (3 : ℝ) ^ m)) := by
    have hΛ0 : 0 ≤ Λ := hν.le.trans hνΛ
    positivity
  have hYs : 0 ≤ (2 + 3 * (d : ℝ)) * (Cg * (3 : ℝ) ^ m * G') := by positivity
  calc eLpNorm (fun x => u.toFun x - uhom.toFun x) ⊤ (volume.restrict W) +
          hMinusOneVec W (fun x => u.grad x - uhom.grad x) +
          hMinusOneVec W (fun x => σ⁻¹ • matVecMul (a x - S) (u.grad x) - uhom.grad x)
      ≤ ENNReal.ofReal (Cs * deltaScale ε ρ (n : ℝ) *
              (σ⁻¹ * (3 : ℝ) ^ (2 * n) * F + Real.log (n : ℝ) * (3 : ℝ) ^ n * (Cg * G'))) +
          ENNReal.ofReal ((2 + 3 * d) * (Cg * (3 : ℝ) ^ m * G')) +
          ENNReal.ofReal (C₁ * (3 : ℝ) ^ n * σ⁻¹ * Λ * (Λ / ν) *
            (Cg * G' + Cg * (3 : ℝ) ^ m * G' / (6 * (3 : ℝ) ^ m))) *
            ENNReal.ofReal (Real.sqrt cv * s) := by
        refine cmp.trans ?_
        gcongr
    _ = ENNReal.ofReal (Cs * deltaScale ε ρ (n : ℝ) *
              (σ⁻¹ * (3 : ℝ) ^ (2 * n) * F + Real.log (n : ℝ) * (3 : ℝ) ^ n * (Cg * G'))) +
          ENNReal.ofReal ((2 + 3 * d) * (Cg * (3 : ℝ) ^ m * G') +
            C₁ * (3 : ℝ) ^ n * σ⁻¹ * Λ * (Λ / ν) *
            (Cg * G' + Cg * (3 : ℝ) ^ m * G' / (6 * (3 : ℝ) ^ m)) * (Real.sqrt cv * s)) := by
        rw [← ENNReal.ofReal_mul hX0, add_assoc,
          ← ENNReal.ofReal_add hYs (mul_nonneg hX0 (mul_nonneg hsq0 hs0))]
    _ ≤ _ := by
        gcongr

end SuperdiffusionCLT.Section7
