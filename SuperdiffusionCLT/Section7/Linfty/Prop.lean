/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Linfty.DatumB
public import SuperdiffusionCLT.Section7.Lipschitz.InteriorHarm
public import SuperdiffusionCLT.Section7.Prereq.CenteringE
public import SuperdiffusionCLT.Section7.Analytic.Geometry.IndicatorMultiscaleB
public import SuperdiffusionCLT.Section7.Linfty.DetC
public import SuperdiffusionCLT.Section7.Linfty.Reduction
public import SuperdiffusionCLT.Section7.Linfty.Field
public import SuperdiffusionCLT.Section7.Linfty.ScaleChoice
public import SuperdiffusionCLT.Section7.Prereq.L2AssemblyG
public import SuperdiffusionCLT.Section7.Prereq.LinftyReductionC
public import SuperdiffusionCLT.Section7.Lipschitz.SigmaWindow
public import SuperdiffusionCLT.Section7.Prereq.WellPosedB
public import SuperdiffusionCLT.Section6.Lemma.AssemblyD

@[expose] public section

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff (ShellSeq)
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open scoped ENNReal Pointwise

/-!
# The `L^∞` homogenization proposition: from the smooth datum to the general datum

The deterministic comparison of the Dirichlet pair `(u, ū)` with datum `g` with the pair `(v, v̄)`
with the smooth datum `g̃` (`linf_compare`), the geometry of the dilates `R U` (`linf_geom`), and
the real inequality that absorbs the datum errors (`linf_real_bound`).
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}


/-- The weak norm of a flux dominated pointwise by a multiple of a gradient is bounded by the
normalized `L²` norm of that gradient, on a domain inside an axis cube. -/
theorem linf_hMinus_flux_le [NeZero d] :
    ∃ c : ℝ, 0 < c ∧ ∀ {W : Set (Vec d)}, IsOpen W → ∀ (z : Vec d) {L : ℝ}, 0 < L →
      W ⊆ axisCube z L → volume W ≠ 0 → ∀ (F : Vec d → Vec d) (w : H1Function W) {K : ℝ},
      0 ≤ K → (∀ i, MemLp (fun x => F x i) 2 (volume.restrict W)) →
      (∀ᵐ x ∂volume.restrict W, eucNorm (F x) ≤ K * eucNorm (w.grad x)) →
      hMinusOneVec W F ≤
        ENNReal.ofReal (c * L * d * K) * lpBar W 2 (fun x => eucNorm (w.grad x)) := by
  obtain ⟨c, hc, hP⟩ := li1_wMinusOneBar_two_le_lpBar (d := d)
  refine ⟨c, hc, fun {W} hWo z {L} hL hsub h0 F w {K} hK hF hpt => ?_⟩
  have hge : AEStronglyMeasurable (fun x => eucNorm (w.grad x)) (volume.restrict W) :=
    p13_continuous_eucNorm.comp_aestronglyMeasurable w.grad_memVectorL2.aestronglyMeasurable
  have hcomp : ∀ i, lpBar W 2 (fun x => F x i) ≤
      ENNReal.ofReal K * lpBar W 2 (fun x => eucNorm (w.grad x)) := by
    intro i
    unfold lpBar
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ((hF i).aestronglyMeasurable.smul_measure _) ?_ 2
    refine Measure.ae_smul_measure ?_ _
    filter_upwards [hpt] with x hx
    have e0 : ‖eucNorm (w.grad x)‖ = eucNorm (w.grad x) :=
      Real.norm_of_nonneg (Real.sqrt_nonneg _)
    rw [Real.norm_eq_abs, e0]
    exact (abs_le_eucNorm (F x) i).trans hx
  unfold hMinusOneVec
  calc ∑ i : Fin d, wMinusOneBar W 2 (fun x => F x i)
      ≤ ∑ _i : Fin d, ENNReal.ofReal (c * L) *
          (ENNReal.ofReal K * lpBar W 2 (fun x => eucNorm (w.grad x))) :=
        Finset.sum_le_sum fun i _ =>
          (hP hWo z hL hsub h0 _ (hF i)).trans (by gcongr; exact hcomp i)
    _ = ENNReal.ofReal (c * L * d * K) * lpBar W 2 (fun x => eucNorm (w.grad x)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        ring_nf

theorem linf_matVecMul_sub (A : Mat d) (v w : Vec d) :
    matVecMul A (v - w) = matVecMul A v - matVecMul A w := by
  funext i
  simp [matVecMul, mul_sub, Finset.sum_sub_distrib]

/-- **The comparison of the original pair `(u, ū)` with the smooth-datum pair `(v, v̄)`**: the three
terms of the proposition for `(u, ū)` are at most those for `(v, v̄)` plus the datum errors. -/
theorem linf_compare [NeZero d] :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ {W : Set (Vec d)}, IsOpen W → IsBoundedDomain W → volume W ≠ 0 →
      ∀ (z : Vec d) {L : ℝ}, 0 < L → W ⊆ axisCube z L →
      ∀ {ν Λ σ : ℝ} {b : CoeffField d}, 0 < ν → ν ≤ Λ → 0 < σ → IsEllipticFieldOn ν Λ W b →
      ∀ {f : Vec d → ℝ} (g u uh v vh : H1Function W) {gt : Vec d → ℝ}, ContDiff ℝ 1 gt →
      IsDirichletSolution b W f g u →
      IsDirichletSolution (fun _ => σ • (1 : Mat d)) W f g uh →
      IsWeakSolutionOn b W v f (fun _ => 0) → MemH10 W (fun x => v.toFun x - gt x) →
      IsWeakSolutionOn (fun _ => σ • (1 : Mat d)) W vh f (fun _ => 0) →
      MemH10 W (fun x => vh.toFun x - gt x) →
      ∀ {c G r : ℝ}, 0 ≤ c → 0 ≤ G → 0 < r →
        (∀ᵐ x ∂volume.restrict W, |gt x - g.toFun x| ≤ c) →
        (∀ᵐ x ∂volume.restrict W, eucNorm (g.grad x) ≤ G) →
        (∀ x ∈ W, ‖fderiv ℝ gt x‖ ≤ G) →
        eLpNorm (fun x => u.toFun x - uh.toFun x) ⊤ (volume.restrict W) +
            hMinusOneVec W (fun x => u.grad x - uh.grad x) +
            hMinusOneVec W (fun x => σ⁻¹ • matVecMul (b x) (u.grad x) - uh.grad x) ≤
          (eLpNorm (fun x => v.toFun x - vh.toFun x) ⊤ (volume.restrict W) +
              hMinusOneVec W (fun x => v.grad x - vh.grad x) +
              hMinusOneVec W (fun x => σ⁻¹ • matVecMul (b x) (v.grad x) - vh.grad x)) +
            ENNReal.ofReal ((2 + 3 * d) * c) +
          ENNReal.ofReal (C₁ * L * σ⁻¹ * Λ * (Λ / ν) * (G + c / r)) *
            (volume (boundaryLayer W (2 * r)) / volume W) ^ (1 / 2 : ℝ) := by
  obtain ⟨Cr, hCr, HR⟩ := linf_reduction (d := d)
  obtain ⟨cF, hcF, HF⟩ := linf_hMinus_flux_le (d := d)
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne d))
  refine ⟨cF * Cr * d, by positivity, ?_⟩
  intro W hWo hWb hW0 z L hL hWL ν Λ σ b hν hνΛ hσ hEll f g u uh v vh gt hgt hu huh hv mv hvh mvh
    c G r hc hG hr hgc hgG hgtG
  have hWm : MeasurableSet W := hWo.measurableSet
  have hΛ0 : 0 ≤ Λ := hν.le.trans hνΛ
  have hEllσ := rc_isEllipticFieldOn_smul_one hσ hWm
  obtain ⟨s1, s2⟩ := HR hWo hWb hW0 hν hEll g u v hgt hu hv mv hc hG hr hgc hgG hgtG
  obtain ⟨s3, -⟩ := HR hWo hWb hW0 hσ hEllσ g uh vh hgt huh hvh mvh hc hG hr hgc hgG hgtG
  -- the sup norms
  have hm : ∀ p q : H1Function W, AEStronglyMeasurable (fun x => p.toFun x - q.toFun x)
      (volume.restrict W) := fun p q =>
    p.memL2.aestronglyMeasurable.sub q.memL2.aestronglyMeasurable
  have hsup : ∀ p q : H1Function W, (∀ᵐ x ∂volume.restrict W, |p.toFun x - q.toFun x| ≤ c) →
      eLpNorm (fun x => p.toFun x - q.toFun x) ⊤ (volume.restrict W) ≤ ENNReal.ofReal c := by
    intro p q h
    rw [eLpNorm_exponent_top (hm p q)]
    exact eLpNormEssSup_le_of_ae_bound (h.mono fun x hx => by rwa [Real.norm_eq_abs])
  have hE1 := hsup u v s1
  have hE3 : eLpNorm (fun x => vh.toFun x - uh.toFun x) ⊤ (volume.restrict W) ≤
      ENNReal.ofReal c :=
    hsup vh uh (s3.mono fun x hx => by rwa [abs_sub_comm])
  have hT1 : eLpNorm (fun x => u.toFun x - uh.toFun x) ⊤ (volume.restrict W) ≤
      ENNReal.ofReal c + eLpNorm (fun x => v.toFun x - vh.toFun x) ⊤ (volume.restrict W) +
        ENNReal.ofReal c := by
    have e : (fun x => u.toFun x - uh.toFun x) = fun x =>
        ((u.toFun x - v.toFun x) + (v.toFun x - vh.toFun x)) + (vh.toFun x - uh.toFun x) := by
      funext x; ring
    rw [e]
    have h1 := eLpNorm_add_le (μ := volume.restrict W) (p := ⊤)
      (f := fun x => (u.toFun x - v.toFun x) + (v.toFun x - vh.toFun x))
      (g := fun x => vh.toFun x - uh.toFun x) le_top
    have h2 := eLpNorm_add_le (μ := volume.restrict W) (p := ⊤)
      (f := fun x => u.toFun x - v.toFun x) (g := fun x => v.toFun x - vh.toFun x) le_top
    refine le_trans h1 (add_le_add (le_trans h2 (add_le_add hE1 le_rfl)) hE3)
  -- the gradients
  have hg1 : hMinusOneVec W (fun x => u.grad x - v.grad x) ≤ ENNReal.ofReal (d * c) := by
    have := linf_hMinus_grad_le_sup hWo hWb hW0 (u - v) hc
      (by rw [H1Function.sub_toFun]; exact s1)
    rwa [H1Function.sub_grad] at this
  have hg3 : hMinusOneVec W (fun x => vh.grad x - uh.grad x) ≤ ENNReal.ofReal (d * c) := by
    have := linf_hMinus_grad_le_sup hWo hWb hW0 (vh - uh) hc
      (by rw [H1Function.sub_toFun]; exact s3.mono fun x hx => by rwa [abs_sub_comm])
    rwa [H1Function.sub_grad] at this
  have hPuv : s12_PairInt W (fun x => u.grad x - v.grad x) := by
    have := s12_pairInt_grad (u - v); rwa [H1Function.sub_grad] at this
  have hPvh : s12_PairInt W (fun x => v.grad x - vh.grad x) := by
    have := s12_pairInt_grad (v - vh); rwa [H1Function.sub_grad] at this
  have hPhu : s12_PairInt W (fun x => vh.grad x - uh.grad x) := by
    have := s12_pairInt_grad (vh - uh); rwa [H1Function.sub_grad] at this
  have hT2 : hMinusOneVec W (fun x => u.grad x - uh.grad x) ≤
      ENNReal.ofReal (d * c) + hMinusOneVec W (fun x => v.grad x - vh.grad x) +
        ENNReal.ofReal (d * c) := by
    have e : (fun x => u.grad x - uh.grad x) = fun x =>
        ((u.grad x - v.grad x) + (v.grad x - vh.grad x)) + (vh.grad x - uh.grad x) := by
      funext x; abel
    rw [e]
    refine (s12_hMinusOneVec_add_le W (s12_pairInt_add hPuv hPvh) hPhu).trans ?_
    exact add_le_add ((s12_hMinusOneVec_add_le W hPuv hPvh).trans (add_le_add hg1 le_rfl)) hg3
  -- the fluxes
  have hfl : ∀ w : H1Function W, MemVectorL2 W (fun x => matVecMul (b x) (w.grad x)) :=
    fun w => memVectorL2_matVecMul_of_isEllipticFieldOn hEll w.grad_memVectorL2
  have hPq : ∀ w : H1Function W, s12_PairInt W (fun x => σ⁻¹ • matVecMul (b x) (w.grad x)) := by
    intro w
    refine s12_pairInt_of_gradMemL2On fun i => ?_
    have h1 : MemLp (fun x => matVecMul (b x) (w.grad x) i) 2 (volume.restrict W) :=
      MeasureTheory.memLp_pi_iff.1 (hfl w) i
    exact h1.const_mul σ⁻¹
  have hPX1 : s12_PairInt W (fun x => σ⁻¹ • matVecMul (b x) (v.grad x) - vh.grad x) := by
    refine s12_pairInt_of_gradMemL2On fun i => ?_
    have h1 : MemLp (fun x => matVecMul (b x) (v.grad x) i) 2 (volume.restrict W) :=
      MeasureTheory.memLp_pi_iff.1 (hfl v) i
    exact (h1.const_mul σ⁻¹).sub (vh.gradMemL2 i)
  have hPX2 : s12_PairInt W (fun x => σ⁻¹ • matVecMul (b x) ((u - v).grad x)) := hPq (u - v)
  have hX2 : hMinusOneVec W (fun x => σ⁻¹ • matVecMul (b x) ((u - v).grad x)) ≤
      ENNReal.ofReal (cF * Cr * d * L * σ⁻¹ * Λ * (Λ / ν) * (G + c / r)) *
        (volume (boundaryLayer W (2 * r)) / volume W) ^ (1 / 2 : ℝ) := by
    have hK : 0 ≤ σ⁻¹ * Λ := mul_nonneg (inv_pos.2 hσ).le hΛ0
    have hpt : ∀ᵐ x ∂volume.restrict W,
        eucNorm (σ⁻¹ • matVecMul (b x) ((u - v).grad x)) ≤
          σ⁻¹ * Λ * eucNorm ((u - v).grad x) := by
      filter_upwards [ae_restrict_mem hWm] with x hx
      have h1 := linf_vecNormSq_matVecMul_le (hEll.2 x hx) ((u - v).grad x)
      rw [linf_eucNorm_smul, abs_of_pos (inv_pos.2 hσ), mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hσ).le
      unfold eucNorm
      rw [← Real.sqrt_sq hΛ0, ← Real.sqrt_mul (sq_nonneg Λ)]
      exact Real.sqrt_le_sqrt h1
    have hmem : ∀ i, MemLp (fun x => (σ⁻¹ • matVecMul (b x) ((u - v).grad x)) i) 2
        (volume.restrict W) := by
      intro i
      have h1 : MemLp (fun x => matVecMul (b x) ((u - v).grad x) i) 2 (volume.restrict W) :=
        MeasureTheory.memLp_pi_iff.1 (hfl (u - v)) i
      exact h1.const_mul σ⁻¹
    have h5 := HF hWo z hL hWL hW0 _ (u - v) hK hmem hpt
    refine h5.trans ?_
    have h6 : lpBar W 2 (fun x => eucNorm ((u - v).grad x)) ≤
        ENNReal.ofReal (Cr * (Λ / ν) * (G + c / r)) *
          (volume (boundaryLayer W (2 * r)) / volume W) ^ (1 / 2 : ℝ) := by
      rw [H1Function.sub_grad]; exact s2
    calc ENNReal.ofReal (cF * L * d * (σ⁻¹ * Λ)) * lpBar W 2 (fun x => eucNorm ((u - v).grad x))
        ≤ ENNReal.ofReal (cF * L * d * (σ⁻¹ * Λ)) *
          (ENNReal.ofReal (Cr * (Λ / ν) * (G + c / r)) *
            (volume (boundaryLayer W (2 * r)) / volume W) ^ (1 / 2 : ℝ)) := by gcongr
      _ = ENNReal.ofReal (cF * Cr * d * L * σ⁻¹ * Λ * (Λ / ν) * (G + c / r)) *
          (volume (boundaryLayer W (2 * r)) / volume W) ^ (1 / 2 : ℝ) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring
  have hT3 : hMinusOneVec W (fun x => σ⁻¹ • matVecMul (b x) (u.grad x) - uh.grad x) ≤
      hMinusOneVec W (fun x => σ⁻¹ • matVecMul (b x) (v.grad x) - vh.grad x) +
        ENNReal.ofReal (cF * Cr * d * L * σ⁻¹ * Λ * (Λ / ν) * (G + c / r)) *
          (volume (boundaryLayer W (2 * r)) / volume W) ^ (1 / 2 : ℝ) +
        ENNReal.ofReal (d * c) := by
    have e : (fun x => σ⁻¹ • matVecMul (b x) (u.grad x) - uh.grad x) = fun x =>
        ((σ⁻¹ • matVecMul (b x) (v.grad x) - vh.grad x) +
          σ⁻¹ • matVecMul (b x) ((u - v).grad x)) + (vh.grad x - uh.grad x) := by
      funext x
      rw [H1Function.sub_grad]
      simp only [linf_matVecMul_sub, smul_sub]
      abel
    rw [e]
    refine (s12_hMinusOneVec_add_le W (s12_pairInt_add hPX1 hPX2) hPhu).trans ?_
    exact add_le_add ((s12_hMinusOneVec_add_le W hPX1 hPX2).trans (add_le_add le_rfl hX2)) hg3
  -- the collection
  have hsum : ENNReal.ofReal c + ENNReal.ofReal c + ENNReal.ofReal (d * c) +
      ENNReal.ofReal (d * c) + ENNReal.ofReal (d * c) = ENNReal.ofReal ((2 + 3 * d) * c) := by
    have hdc : 0 ≤ (d : ℝ) * c := by positivity
    rw [← ENNReal.ofReal_add hc hc, ← ENNReal.ofReal_add (add_nonneg hc hc) hdc,
      ← ENNReal.ofReal_add (by positivity) hdc, ← ENNReal.ofReal_add (by positivity) hdc]
    congr 1; ring
  calc eLpNorm (fun x => u.toFun x - uh.toFun x) ⊤ (volume.restrict W) +
          hMinusOneVec W (fun x => u.grad x - uh.grad x) +
          hMinusOneVec W (fun x => σ⁻¹ • matVecMul (b x) (u.grad x) - uh.grad x)
      ≤ (ENNReal.ofReal c + eLpNorm (fun x => v.toFun x - vh.toFun x) ⊤ (volume.restrict W) +
          ENNReal.ofReal c) +
        (ENNReal.ofReal (d * c) + hMinusOneVec W (fun x => v.grad x - vh.grad x) +
          ENNReal.ofReal (d * c)) +
        (hMinusOneVec W (fun x => σ⁻¹ • matVecMul (b x) (v.grad x) - vh.grad x) +
          ENNReal.ofReal (cF * Cr * d * L * σ⁻¹ * Λ * (Λ / ν) * (G + c / r)) *
            (volume (boundaryLayer W (2 * r)) / volume W) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (d * c)) := add_le_add (add_le_add hT1 hT2) hT3
    _ = (eLpNorm (fun x => v.toFun x - vh.toFun x) ⊤ (volume.restrict W) +
            hMinusOneVec W (fun x => v.grad x - vh.grad x) +
            hMinusOneVec W (fun x => σ⁻¹ • matVecMul (b x) (v.grad x) - vh.grad x)) +
          (ENNReal.ofReal c + ENNReal.ofReal c + ENNReal.ofReal (d * c) +
            ENNReal.ofReal (d * c) + ENNReal.ofReal (d * c)) +
          ENNReal.ofReal (cF * Cr * d * L * σ⁻¹ * Λ * (Λ / ν) * (G + c / r)) *
            (volume (boundaryLayer W (2 * r)) / volume W) ^ (1 / 2 : ℝ) := by ring
    _ = _ := by rw [hsum]



/-- An open subset of the half-open unit cube lies in the open unit cube. -/
theorem linf_open_Q0 {U : Set (Vec d)} (hUo : IsOpen U) (hU0 : U ⊆ kc2_Q0 d) :
    U ⊆ Section6.engCube d 0 := by
  intro x hx
  have h1 : x ∈ interior (kc2_Q0 d) := (hUo.subset_interior_iff).2 hU0 hx
  rw [kc2_Q0, interior_pi_set Set.finite_univ] at h1
  rw [Section6.engCube, mem_openCubeSet_originCube_iff]
  intro i
  have h2 := h1 i (Set.mem_univ i)
  rw [interior_Ico] at h2
  simp only [Nat.cast_zero, zpow_zero, mul_one]
  exact ⟨h2.1, h2.2⟩

/-- Dilates by at most `3^n` of a subset of the open unit cube lie in the open cube of scale `n`. -/
theorem linf_dilate_engCube {U : Set (Vec d)} (hUo : IsOpen U) (hU0 : U ⊆ kc2_Q0 d) {n : ℕ}
    {R : ℝ} (hR0 : 0 < R) (hR : R ≤ (3 : ℝ) ^ n) : R • U ⊆ Section6.engCube d n := by
  rintro _ ⟨y, hy, rfl⟩
  have h := mem_openCubeSet_originCube_iff.1 (linf_open_Q0 hUo hU0 hy)
  rw [Section6.engCube, mem_openCubeSet_originCube_iff]
  intro i
  have hi := h i
  simp only [Nat.cast_zero, zpow_zero, mul_one] at hi
  rw [zpow_natCast]
  simp only [Pi.smul_apply, smul_eq_mul]
  constructor
  · nlinarith only [hi.1, hi.2, hR, hR0]
  · nlinarith only [hi.1, hi.2, hR, hR0]

/-- **Geometry of the dilate `R U`**, `3^n < 3 R ≤ 3^{n+1}`: open, inside the open cube of scale
`n`, bounded, of positive measure, with the layer ratio `c 3^{m-n}`. -/
theorem linf_geom [NeZero d] {U : Set (Vec d)} (hUs : IsSmoothBoundedDomain U)
    (hU0 : U ⊆ kc2_Q0 d) {r M₁ M₂ D : ℝ} (hU : IsUniformC11Domain U r M₁ M₂ D) :
    ∃ cv : ℝ, 0 < cv ∧ ∀ {n m : ℕ} {R : ℝ}, (3 : ℝ) ^ n < 3 * R → R ≤ (3 : ℝ) ^ n →
      12 * (3 : ℝ) ^ m ≤ (3 : ℝ) ^ n * (r / 3) →
      IsOpen (R • U) ∧ R • U ⊆ Section6.engCube d n ∧ IsBoundedDomain (R • U) ∧
        volume (R • U) ≠ 0 ∧
        volume (boundaryLayer (R • U) (3 * (4 * (3 : ℝ) ^ m))) / volume (R • U) ≤
          ENNReal.ofReal (cv * ((3 : ℝ) ^ m / (3 : ℝ) ^ n)) := by
  obtain ⟨cv, hcv, H⟩ := l2e_geom (d := d) (r / 3) M₁ (max D 0)
  refine ⟨cv, hcv, fun {n m R} h1 h2 h3 => ?_⟩
  have h3n : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hR0 : 0 < R := by linarith only [h1, h3n]
  have hlam0 : 1 / 3 < ((3 : ℝ) ^ n)⁻¹ * R := by
    rw [← div_eq_inv_mul, lt_div_iff₀ h3n]; linarith only [h1]
  have hlam1 : ((3 : ℝ) ^ n)⁻¹ * R ≤ 1 := by
    rw [← div_eq_inv_mul, div_le_one h3n]; exact h2
  have hunif := kc3_unif_smul hU hlam0 hlam1
  have hsm : ((3 : ℝ) ^ n)⁻¹ • (R • U) = (((3 : ℝ) ^ n)⁻¹ * R) • U := smul_smul _ _ _
  have hVne : (R • U).Nonempty := by
    obtain ⟨x, hx⟩ := hUs.2.1.nonempty
    exact ⟨R • x, Set.smul_mem_smul_set hx⟩
  obtain ⟨hUV, hV0, -, hlay⟩ := H (linf_dilate_engCube hUs.1 hU0 hR0 h2) (by rw [hsm]; exact hunif)
    hVne h3
  refine ⟨?_, linf_dilate_engCube hUs.1 hU0 hR0 h2, p14g_isBoundedDomain hUV, hV0, hlay⟩
  exact hUs.1.smul₀ hR0.ne'



/-- The scale `3^{⌈C log n⌉}` dominates `n^{24}` once `C ≥ 24`. -/
theorem linf_pow_le_three_pow {Cs : ℝ} (hCs : 24 ≤ Cs) {n : ℕ} (hn : 3 ≤ n) :
    (n : ℝ) ^ 24 ≤ (3 : ℝ) ^ ⌈Cs * Real.log (n : ℝ)⌉₊ := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith only [hn3]
  have hlog3 : (1 : ℝ) < Real.log 3 :=
    SuperdiffusionCLT.Section2.Estimates.Stream.one_lt_log_three
  have hlogn : 1 ≤ Real.log (n : ℝ) := le_trans hlog3.le (Real.log_le_log (by norm_num) hn3)
  have h1 : Cs * Real.log (n : ℝ) ≤ (⌈Cs * Real.log (n : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have h0 : (0 : ℝ) ≤ (⌈Cs * Real.log (n : ℝ)⌉₊ : ℝ) := Nat.cast_nonneg _
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  push_cast
  nlinarith only [h1, hlogn, hlog3, hCs, h0, mul_le_mul_of_nonneg_right hCs (by linarith only [hlogn] : (0 : ℝ) ≤ Real.log (n : ℝ))]

/-- **The real inequality of the reduction terms**: the datum errors are absorbed in the right-hand
side `δ log n 3^n ‖∇g‖_∞`. -/
theorem linf_real_bound (d : ℕ) (C₁ Cf cv Cg : ℝ) (hC₁ : 0 ≤ C₁) (hCf : 1 ≤ Cf)
    (hCg : 1 ≤ Cg) :
    ∃ K : ℝ, 0 < K ∧ ∀ {n ν ε ρ σ Λ T G' c Gr s : ℝ}, 3 ≤ n → 0 < ν → ν ≤ 1 → 1 ≤ n * ν →
      0 < ε → ε ≤ 1 → 1 ≤ n * ε ^ 2 → 0 < ρ → ρ < 1 → 1 ≤ σ →
      Λ = (ν + Cf * n ^ (1 + ρ)) ^ 2 / ν → 0 < T → 0 ≤ G' → 0 ≤ c → c ≤ Cg * s ^ 2 * T * G' →
      0 ≤ Gr → Gr ≤ 2 * Cg * G' → 0 ≤ s → s * n ^ 12 ≤ 1 →
        (2 + 3 * d) * c + C₁ * T * σ⁻¹ * Λ * (Λ / ν) * Gr * (Real.sqrt cv * s) ≤
          ((2 + 3 * d) * Cg + 2 * C₁ * Cg * Real.sqrt cv * (1 + Cf) ^ 4) *
            (deltaScale ε ρ n * Real.log n * T) * G' := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hsq0 : 0 ≤ Real.sqrt cv := Real.sqrt_nonneg _
  refine ⟨(2 + 3 * d) * Cg + 2 * C₁ * Cg * Real.sqrt cv * (1 + Cf) ^ 4, by positivity, ?_⟩
  intro n ν ε ρ σ Λ T G' c Gr s hn hν hν1 hνn hε hε1 hεn hρ hρ1 hσ hΛ hT hG hc hcs hGr hGr2 hs hsn
  have hn1 : (1 : ℝ) ≤ n := by linarith only [hn]
  have hnpos : (0 : ℝ) < n := by linarith only [hn]
  have hlog3 : (1 : ℝ) < Real.log 3 :=
    SuperdiffusionCLT.Section2.Estimates.Stream.one_lt_log_three
  have hlogn : 1 ≤ Real.log n := le_trans hlog3.le (Real.log_le_log (by norm_num) hn)
  -- the power of `n` against the scale
  have hs1 : s ≤ 1 := by
    have h12 : (1 : ℝ) ≤ n ^ 12 := one_le_pow₀ hn1
    nlinarith only [hsn, h12, hs]
  have hn11 : s * n ^ 11 ≤ 1 / n := by
    rw [le_div_iff₀ hnpos]
    have : s * n ^ 11 * n = s * n ^ 12 := by ring
    linarith only [this, hsn]
  -- `1/n ≤ δ log n`
  have hq : (1 : ℝ) / n ≤ deltaScale ε ρ n * Real.log n := by
    have hq1 : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ n ^ (-((1 - ρ) / 2)) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hρ])
    have hq2 : (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / n := by
      rw [← Real.rpow_add hnpos]
      norm_num [Real.rpow_neg_one]
    have hq3 : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ ε := by
      have hp0 : 0 < (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hnpos _
      by_contra hcon0
      have hcon := not_le.1 hcon0
      have h1 : ε * ε < (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
        mul_self_lt_mul_self hε.le hcon
      rw [hq2] at h1
      have h2 : 1 / (n : ℝ) ≤ ε ^ 2 := by
        rw [div_le_iff₀ hnpos]; nlinarith only [hεn]
      nlinarith only [h1, h2]
    have hp0 : 0 < (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hnpos _
    have hq4 : 1 / (n : ℝ) ≤ ε * (n : ℝ) ^ (-((1 - ρ) / 2)) := by
      rw [← hq2]
      calc (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 / 2 : ℝ))
          ≤ ε * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by gcongr
        _ ≤ ε * (n : ℝ) ^ (-((1 - ρ) / 2)) := by gcongr
    unfold deltaScale
    have hq5 : 0 ≤ ε * (n : ℝ) ^ (-((1 - ρ) / 2)) := by positivity
    nlinarith only [hq4, hq5, hlogn, mul_le_mul_of_nonneg_left hlogn hq5,
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogn hq5) (by linarith only [hlogn] : (0 : ℝ) ≤ Real.log n)]
  -- the ellipticity constant
  have hnr : (n : ℝ) ^ (1 + ρ) ≤ n ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hn1 (show 1 + ρ ≤ (2 : ℝ) by linarith only [hρ1])
    simpa [Real.rpow_two] using this
  have hnr0 : 0 ≤ (n : ℝ) ^ (1 + ρ) := by positivity
  have hn2 : (1 : ℝ) ≤ n ^ 2 := one_le_pow₀ hn1
  have hA : ν + Cf * (n : ℝ) ^ (1 + ρ) ≤ (1 + Cf) * n ^ 2 := by
    nlinarith only [hν1, hnr, hn2, hCf, mul_le_mul_of_nonneg_left hnr (by linarith only [hCf] : (0 : ℝ) ≤ Cf)]
  have hA0 : 0 ≤ ν + Cf * (n : ℝ) ^ (1 + ρ) := by positivity
  have hνi : ν⁻¹ ≤ n := by
    rw [inv_le_comm₀ hν hnpos]
    rw [inv_eq_one_div, div_le_iff₀ hnpos]
    linarith only [hνn]
  have hνi0 : 0 ≤ ν⁻¹ := inv_nonneg.2 hν.le
  have hΛ1 : Λ ≤ (1 + Cf) ^ 2 * n ^ 5 := by
    rw [hΛ, div_eq_mul_inv]
    calc (ν + Cf * (n : ℝ) ^ (1 + ρ)) ^ 2 * ν⁻¹
        ≤ ((1 + Cf) * n ^ 2) ^ 2 * n := by gcongr
      _ = (1 + Cf) ^ 2 * n ^ 5 := by ring
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; positivity
  have hΛ2 : Λ / ν ≤ (1 + Cf) ^ 2 * n ^ 6 := by
    rw [div_eq_mul_inv]
    calc Λ * ν⁻¹ ≤ ((1 + Cf) ^ 2 * n ^ 5) * n := by gcongr
      _ = (1 + Cf) ^ 2 * n ^ 6 := by ring
  have hΛ20 : 0 ≤ Λ / ν := by positivity
  have hprod : Λ * (Λ / ν) ≤ (1 + Cf) ^ 4 * n ^ 11 := by
    calc Λ * (Λ / ν) ≤ ((1 + Cf) ^ 2 * n ^ 5) * ((1 + Cf) ^ 2 * n ^ 6) := by gcongr
      _ = (1 + Cf) ^ 4 * n ^ 11 := by ring
  have hσi : σ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hσ
  have hσi0 : 0 ≤ σ⁻¹ := inv_nonneg.2 (by linarith only [hσ])
  have hP : σ⁻¹ * (Λ * (Λ / ν)) ≤ (1 + Cf) ^ 4 * n ^ 11 := by
    calc σ⁻¹ * (Λ * (Λ / ν)) ≤ 1 * (Λ * (Λ / ν)) := by gcongr
      _ ≤ _ := by rw [one_mul]; exact hprod
  have hP0 : 0 ≤ σ⁻¹ * (Λ * (Λ / ν)) := by positivity
  -- the two terms
  have hT1 : (2 + 3 * (d : ℝ)) * c ≤ (2 + 3 * d) * Cg * T * G' * (s * n ^ 11) := by
    have h1 : c ≤ Cg * T * G' * (s * n ^ 11) := by
      refine hcs.trans ?_
      have hn11' : (1 : ℝ) ≤ n ^ 11 := one_le_pow₀ hn1
      have : s ^ 2 ≤ s * n ^ 11 := by nlinarith only [hs1, hs, hn11', mul_le_mul_of_nonneg_left hn11' hs]
      calc Cg * s ^ 2 * T * G' = Cg * T * G' * s ^ 2 := by ring
        _ ≤ Cg * T * G' * (s * n ^ 11) := by gcongr
    calc (2 + 3 * (d : ℝ)) * c ≤ (2 + 3 * d) * (Cg * T * G' * (s * n ^ 11)) := by gcongr
      _ = _ := by ring
  have hT2 : C₁ * T * σ⁻¹ * Λ * (Λ / ν) * Gr * (Real.sqrt cv * s) ≤
      2 * C₁ * Cg * Real.sqrt cv * (1 + Cf) ^ 4 * T * G' * (s * n ^ 11) := by
    calc C₁ * T * σ⁻¹ * Λ * (Λ / ν) * Gr * (Real.sqrt cv * s)
        = C₁ * T * (σ⁻¹ * (Λ * (Λ / ν))) * Gr * (Real.sqrt cv * s) := by ring
      _ ≤ C₁ * T * ((1 + Cf) ^ 4 * n ^ 11) * (2 * Cg * G') * (Real.sqrt cv * s) := by gcongr
      _ = _ := by ring
  have hTG : 0 ≤ T * G' := by positivity
  calc (2 + 3 * (d : ℝ)) * c + C₁ * T * σ⁻¹ * Λ * (Λ / ν) * Gr * (Real.sqrt cv * s)
      ≤ ((2 + 3 * d) * Cg + 2 * C₁ * Cg * Real.sqrt cv * (1 + Cf) ^ 4) * T * G' * (s * n ^ 11) := by
        nlinarith only [hT1, hT2]
    _ ≤ ((2 + 3 * d) * Cg + 2 * C₁ * Cg * Real.sqrt cv * (1 + Cf) ^ 4) * T * G' *
          (deltaScale ε ρ n * Real.log n) := by
        exact mul_le_mul_of_nonneg_left (hn11.trans hq) (by positivity)
    _ = _ := by ring


end SuperdiffusionCLT.Section7
