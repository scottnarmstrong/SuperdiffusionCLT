/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Prereq.LinftyReductionB
public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.Boundary

/-!
# Boundary De Giorgi step for the `L^∞` homogenization estimate

For the weak solution `v` with smooth datum `g̃`, the function `ψ = v - g̃` lies in `H¹₀(W)` and
solves the zero-trace problem with flux datum `-a∇g̃` (`li1_reduction`); the boundary De Giorgi bound
applied to `ψ` and `-ψ` controls `|v - g̃|` on `W ∩ Q/2` by the `L²` norm on `W ∩ Q`.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem linf_dgb_neg {a : CoeffField d} {W : Set (Vec d)} {f : Vec d → ℝ} {g : Vec d → Vec d}
    {ψ : H10Function W} (h : IsWeakSolutionOn a W ψ.toH1Function f g) :
    IsWeakSolutionOn a W (-ψ).toH1Function (fun x => -f x) (fun x => -g x) := by
  intro φ
  have h1 := h φ
  have hf : (-ψ).toH1Function = -ψ.toH1Function := rfl
  rw [hf]
  have hg : (-ψ.toH1Function).grad = fun x => -ψ.toH1Function.grad x := by
    funext x
    simp
  rw [hg]
  simp only [matVecMul_neg, vecDot_neg_left, MeasureTheory.integral_neg, neg_mul, vecDot_neg_left]
  rw [h1]
  ring

/-- The flux datum `-a ∇g̃` is a.e. strongly measurable on `W ∩ Q`. -/
theorem linf_dgb_flux_meas {lam Lam : ℝ} {a : CoeffField d} {W Q : Set (Vec d)}
    (hEll : IsEllipticFieldOn lam Lam W a) {gt : Vec d → ℝ} (hgt : ContDiff ℝ 1 gt) :
    AEStronglyMeasurable
      (fun x => -(matVecMul (a x) (fun i => fderiv ℝ gt x (basisVec i))))
      (volume.restrict (W ∩ Q)) := by
  classical
  have hWm := measurableSet_of_isEllipticFieldOn hEll
  have hmono : volume.restrict (W ∩ Q) ≤ volume.restrict W :=
    Measure.restrict_mono Set.inter_subset_left le_rfl
  have hcoord : ∀ i j, AEMeasurable (fun x => a x i j) (volume.restrict (W ∩ Q)) := by
    intro i j
    have h1 : Measurable (fun x => if x ∈ W then a x i j else 0) :=
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hEll.1)
    have h2 : AEMeasurable (fun x => a x i j) (volume.restrict W) := by
      refine h1.aemeasurable.congr ?_
      filter_upwards [ae_restrict_mem hWm] with x hx
      simp [hx]
    exact h2.mono_measure hmono
  have hD : ∀ j, Continuous (fun x => fderiv ℝ gt x (basisVec j)) := fun j =>
    (hgt.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine (aemeasurable_pi_iff.2 fun i => ?_).aestronglyMeasurable
  simp only [matVecMul, Pi.neg_apply]
  exact (Finset.aemeasurable_fun_sum _ fun j _ => (hcoord i j).mul (hD j).measurable.aemeasurable).neg

/-- The Euclidean norm of the flux datum is at most `d² Λ G`. -/
theorem linf_dgb_flux_norm {lam Lam : ℝ} {a : CoeffField d} {W : Set (Vec d)}
    (hEll : IsEllipticFieldOn lam Lam W a) {gt : Vec d → ℝ} {G : ℝ} {x : Vec d} (hx : x ∈ W)
    (hG : ‖fderiv ℝ gt x‖ ≤ G) (hd : 1 ≤ d) :
    eucNorm (-(matVecMul (a x) (fun i => fderiv ℝ gt x (basisVec i)))) ≤
      (d : ℝ) ^ 2 * Lam * G := by
  obtain ⟨hlam, hlamLam, -, -⟩ := hEll.2 x hx
  have hLam : 0 ≤ Lam := hlam.le.trans hlamLam
  have hG0 : 0 ≤ G := (norm_nonneg _).trans hG
  have hD : ∀ j, |fderiv ℝ gt x (basisVec j)| ≤ G := by
    intro j
    have h1 : ‖fderiv ℝ gt x (basisVec j)‖ ≤ ‖fderiv ℝ gt x‖ * ‖basisVec j‖ :=
      (fderiv ℝ gt x).le_opNorm _
    have h2 : ‖basisVec (d := d) j‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
      by_cases h : i = j <;> simp [basisVec, h]
    rw [← Real.norm_eq_abs]
    calc _ ≤ ‖fderiv ℝ gt x‖ * ‖basisVec (d := d) j‖ := h1
      _ ≤ ‖fderiv ℝ gt x‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ ≤ G := by linarith only [hG]
  have hcomp : ∀ i, |(-(matVecMul (a x) (fun i => fderiv ℝ gt x (basisVec i)))) i| ≤
      (d : ℝ) * Lam * G := by
    intro i
    simp only [matVecMul, Pi.neg_apply, abs_neg]
    calc |∑ j, a x i j * fderiv ℝ gt x (basisVec j)| ≤ ∑ j, |a x i j * fderiv ℝ gt x (basisVec j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin d, Lam * G := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul (abs_apply_le_of_isEllipticFieldOn hEll hx i j) (hD j) (abs_nonneg _) hLam
      _ = (d : ℝ) * Lam * G := by simp [mul_assoc]
  unfold eucNorm
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  unfold vecNormSq vecDot
  calc ∑ i, (-(matVecMul (a x) (fun i => fderiv ℝ gt x (basisVec i)))) i *
        (-(matVecMul (a x) (fun i => fderiv ℝ gt x (basisVec i)))) i
      ≤ ∑ _i : Fin d, ((d : ℝ) * Lam * G) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← sq]
        exact sq_le_sq' (abs_le.1 (hcomp i)).1 (abs_le.1 (hcomp i)).2
    _ = (d : ℝ) * ((d : ℝ) * Lam * G) ^ 2 := by simp
    _ ≤ (d : ℝ) ^ 2 * ((d : ℝ) * Lam * G) ^ 2 := by
        exact mul_le_mul_of_nonneg_right (by nlinarith only [hd']) (sq_nonneg _)
    _ = ((d : ℝ) ^ 2 * Lam * G) ^ 2 := by ring


/-- Two-sided boundary bound, abstract form: a bound for `max (w, 0)` from the one-sided
De Giorgi estimate. -/
theorem linf_dgb_one_sided {C0 : ℝ} {lam Lam : ℝ} {a : CoeffField d} {W : Set (Vec d)}
    (hlam : 0 < lam) (hEll : IsEllipticFieldOn lam Lam W a)
    (z : Vec d) {L F G Bb : ℝ} (hL : 0 < L) (hF : 0 ≤ F) (hG : 0 ≤ G) (hBb : 0 ≤ Bb)
    (hpos : 0 ≤ C0 * (Lam / lam) ^ deGiorgiPower d) (f' : Vec d → ℝ) (g' : Vec d → Vec d) (w : H10Function W)
    (hfm : AEStronglyMeasurable f' (volume.restrict (W ∩ axisCube z L)))
    (hgm : AEStronglyMeasurable g' (volume.restrict (W ∩ axisCube z L)))
    (hf : ∀ᵐ x ∂volume.restrict (W ∩ axisCube z L), |f' x| ≤ F)
    (hg : ∀ x ∈ W ∩ axisCube z L, eucNorm (g' x) ≤ G)
    (hw : eLpNorm w.toH1Function.toFun 2 (volume.restrict (W ∩ axisCube z L)) ≤
      ENNReal.ofReal (L ^ ((d : ℝ) / 2) * Bb))
    (hmain : eLpNorm (fun x => max (w.toH1Function.toFun x) 0) ⊤
          (volume.restrict (W ∩ halfCube z L)) ≤
        ENNReal.ofReal (C0 * (Lam / lam) ^ deGiorgiPower d) *
          (ENNReal.ofReal (L ^ (-(d : ℝ) / 2)) *
              eLpNorm (fun x => max (w.toH1Function.toFun x) 0) 2
                (volume.restrict (W ∩ axisCube z L)) +
            ENNReal.ofReal (L ^ 2 / lam) * eLpNorm f' ⊤ (volume.restrict (W ∩ axisCube z L)) +
            ENNReal.ofReal (L / lam) *
              eLpNorm (fun x => eucNorm (g' x)) ⊤ (volume.restrict (W ∩ axisCube z L)))) :
    ∀ᵐ x ∂volume.restrict (W ∩ halfCube z L),
      max (w.toH1Function.toFun x) 0 ≤
        C0 * (Lam / lam) ^ deGiorgiPower d * (Bb + L ^ 2 / lam * F + L / lam * G) := by
  set μ := volume.restrict (W ∩ axisCube z L) with hμ
  have hwm : AEStronglyMeasurable w.toH1Function.toFun μ :=
    w.toH1Function.memL2.aestronglyMeasurable.mono_measure
      (Measure.restrict_mono Set.inter_subset_left le_rfl)
  have hmaxm : AEStronglyMeasurable (fun x => max (w.toH1Function.toFun x) 0) μ :=
    (hwm.aemeasurable.max aemeasurable_const).aestronglyMeasurable
  have e1 : eLpNorm (fun x => max (w.toH1Function.toFun x) 0) 2 μ ≤
      ENNReal.ofReal (L ^ ((d : ℝ) / 2) * Bb) := by
    refine le_trans (eLpNorm_mono_ae hmaxm (Filter.Eventually.of_forall fun x => ?_)) hw
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have e2 : eLpNorm f' ⊤ μ ≤ ENNReal.ofReal F := by
    rw [eLpNorm_exponent_top hfm]
    exact eLpNormEssSup_le_of_ae_bound (by simpa only [Real.norm_eq_abs] using hf)
  have hEm : AEStronglyMeasurable (fun x => eucNorm (g' x)) μ := by
    have hc : Continuous (fun y : Vec d => eucNorm y) := by
      unfold eucNorm vecNormSq vecDot
      fun_prop
    exact hc.comp_aestronglyMeasurable hgm
  have e3 : eLpNorm (fun x => eucNorm (g' x)) ⊤ μ ≤ ENNReal.ofReal G := by
    rw [eLpNorm_exponent_top hEm]
    refine eLpNormEssSup_le_of_ae_bound ?_
    have hmeas : MeasurableSet (W ∩ axisCube z L) :=
      (measurableSet_of_isEllipticFieldOn hEll).inter (isOpen_axisCube z L).measurableSet
    filter_upwards [ae_restrict_mem hmeas] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold eucNorm; exact Real.sqrt_nonneg _)]
    exact hg x hx
  have hL' : ENNReal.ofReal (L ^ (-(d : ℝ) / 2)) * ENNReal.ofReal (L ^ ((d : ℝ) / 2) * Bb) =
      ENNReal.ofReal Bb := by
    have h1 : L ^ (-(d : ℝ) / 2) * L ^ ((d : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add hL, show -(d : ℝ) / 2 + d / 2 = 0 by ring, Real.rpow_zero]
    rw [← ENNReal.ofReal_mul (by positivity), ← mul_assoc, h1, one_mul]
  have hbound : eLpNorm (fun x => max (w.toH1Function.toFun x) 0) ⊤
      (volume.restrict (W ∩ halfCube z L)) ≤
      ENNReal.ofReal (C0 * (Lam / lam) ^ deGiorgiPower d * (Bb + L ^ 2 / lam * F + L / lam * G)) := by
    refine hmain.trans ?_
    rw [ENNReal.ofReal_mul hpos]
    refine mul_le_mul' le_rfl ?_
    calc _ ≤ ENNReal.ofReal (L ^ (-(d : ℝ) / 2)) * ENNReal.ofReal (L ^ ((d : ℝ) / 2) * Bb) +
          ENNReal.ofReal (L ^ 2 / lam) * ENNReal.ofReal F +
            ENNReal.ofReal (L / lam) * ENNReal.ofReal G := by gcongr
      _ = _ := by
        rw [hL', ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add hBb (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have h2 := enorm_ae_le_eLpNormEssSup (fun x => max (w.toH1Function.toFun x) 0)
    (volume.restrict (W ∩ halfCube z L))
  have hmax2 : AEStronglyMeasurable (fun x => max (w.toH1Function.toFun x) 0)
      (volume.restrict (W ∩ halfCube z L)) := by
    exact hmaxm.mono_measure
      (Measure.restrict_mono (Set.inter_subset_inter_right _ (halfCube_subset z L)) le_rfl)
  rw [eLpNorm_exponent_top hmax2] at hbound
  have hB : 0 ≤ C0 * (Lam / lam) ^ deGiorgiPower d * (Bb + L ^ 2 / lam * F + L / lam * G) :=
    mul_nonneg hpos (by positivity)
  filter_upwards [h2] with x hx
  have h3 := hx.trans hbound
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (le_max_right _ _)] at h3
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 h3

/-- **Boundary De Giorgi step**: `|v - g̃|` on `W ∩ Q/2` from its `L²`
norm on `W ∩ Q`, for the Dirichlet solution with the smooth datum `g̃`. -/
theorem linf_dg_boundary [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {lam Lam : ℝ} {a : CoeffField d} {W : Set (Vec d)}, IsOpen W →
      IsBoundedDomain W → 0 < lam → lam ≤ Lam → IsEllipticFieldOn lam Lam W a →
      ∀ (f : Vec d → ℝ) (v : H1Function W) {gt : Vec d → ℝ}, ContDiff ℝ 1 gt →
      IsWeakSolutionOn a W v f (fun _ => 0) → MemH10 W (fun x => v.toFun x - gt x) →
      ∀ (z : Vec d) {L F G Bb : ℝ}, 0 < L → 0 ≤ F → 0 ≤ G → 0 ≤ Bb →
        AEStronglyMeasurable f (volume.restrict (W ∩ axisCube z L)) →
        (∀ᵐ x ∂volume.restrict (W ∩ axisCube z L), |f x| ≤ F) →
        (∀ x ∈ W ∩ axisCube z L, ‖fderiv ℝ gt x‖ ≤ G) →
        eLpNorm (fun x => v.toFun x - gt x) 2 (volume.restrict (W ∩ axisCube z L)) ≤
          ENNReal.ofReal (L ^ ((d : ℝ) / 2) * Bb) →
        ∀ᵐ x ∂volume.restrict (W ∩ halfCube z L),
          |v.toFun x - gt x| ≤
            C * (Lam / lam) ^ (deGiorgiPower d + 1) * (Bb + L ^ 2 / lam * F + L * G) := by
  obtain ⟨C0, hC0, H⟩ := deGiorgi_boundary_bound hd
  have hd1 : 1 ≤ d := by omega
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  refine ⟨C0 * (d : ℝ) ^ 2, by positivity, ?_⟩
  intro lam Lam a W hWo hWb hlam hlamLam hEll f v gt hgt hv hmem z L F G Bb hL hF hG hBb hfm hf
    hgt' hnorm
  obtain ⟨ψ, hψfun, hψ⟩ := (li1_reduction hWo hWb hEll hgt v).1 ⟨hv, hmem⟩
  have hψ' : IsWeakSolutionOn a W ψ.toH1Function f
      (fun x => -(matVecMul (a x) (fun i => fderiv ℝ gt x (basisVec i)))) := hψ
  have hψn := linf_dgb_neg hψ'
  have hgm := linf_dgb_flux_meas (Q := axisCube z L) hEll hgt
  have hgm' := hgm.neg
  have hflux : ∀ x ∈ W ∩ axisCube z L,
      eucNorm (-(matVecMul (a x) (fun i => fderiv ℝ gt x (basisVec i)))) ≤
        (d : ℝ) ^ 2 * Lam * G := fun x hx => linf_dgb_flux_norm hEll hx.1 (hgt' x hx) hd1
  have hflux' : ∀ x ∈ W ∩ axisCube z L,
      eucNorm (-(-(matVecMul (a x) (fun i => fderiv ℝ gt x (basisVec i))))) ≤
        (d : ℝ) ^ 2 * Lam * G := fun x hx => by
    have : eucNorm (-(-(matVecMul (a x) (fun i => fderiv ℝ gt x (basisVec i))))) =
        eucNorm (-(matVecMul (a x) (fun i => fderiv ℝ gt x (basisVec i)))) := by
      unfold eucNorm vecNormSq vecDot
      simp
    rw [this]
    exact hflux x hx
  have hq : 1 ≤ Lam / lam := by rw [le_div_iff₀ hlam]; linarith only [hlamLam]
  have hLam : 0 ≤ Lam := by linarith only [hlam, hlamLam]
  have hR : 0 ≤ C0 * (Lam / lam) ^ deGiorgiPower d := by
    have : 0 < Lam / lam := lt_of_lt_of_le one_pos hq
    positivity
  have hfm' : AEStronglyMeasurable (fun x => -f x) (volume.restrict (W ∩ axisCube z L)) := hfm.neg
  have hwψ : eLpNorm ψ.toH1Function.toFun 2 (volume.restrict (W ∩ axisCube z L)) ≤
      ENNReal.ofReal (L ^ ((d : ℝ) / 2) * Bb) := by
    rw [hψfun]; exact hnorm
  have hwψn : eLpNorm (-ψ).toH1Function.toFun 2 (volume.restrict (W ∩ axisCube z L)) ≤
      ENNReal.ofReal (L ^ ((d : ℝ) / 2) * Bb) := by
    have : (-ψ).toH1Function.toFun = fun x => -ψ.toH1Function.toFun x := by
      funext x
      change (-1 : ℝ) * ψ.toH1Function.toFun x = _
      ring
    rw [this]
    exact (eLpNorm_neg ψ.toH1Function.toFun 2 _).le.trans hwψ
  have hfn : ∀ᵐ x ∂volume.restrict (W ∩ axisCube z L), |-f x| ≤ F := by
    filter_upwards [hf] with x hx; rwa [abs_neg]
  have r1 := linf_dgb_one_sided hlam hEll z hL hF (by positivity) hBb
    hR f _ ψ hfm hgm hf hflux hwψ
    (H hWo hWb hEll z hL f _ hgm ψ hψ')
  have r2 := linf_dgb_one_sided hlam hEll z hL hF (by positivity) hBb
    hR (fun x => -f x) _ (-ψ) hfm' hgm' hfn hflux' hwψn
    (H hWo hWb hEll z hL _ _ hgm' (-ψ) hψn)
  filter_upwards [r1, r2] with x h1 h2
  have hneg : (-ψ).toH1Function.toFun x = -ψ.toH1Function.toFun x := by
    change (-1 : ℝ) * ψ.toH1Function.toFun x = _
    ring
  rw [hneg] at h2
  have hx : ψ.toH1Function.toFun x = v.toFun x - gt x := congrFun hψfun x
  rw [← hx]
  have hb : |ψ.toH1Function.toFun x| ≤ C0 * (Lam / lam) ^ deGiorgiPower d *
      (Bb + L ^ 2 / lam * F + L / lam * ((d : ℝ) ^ 2 * Lam * G)) :=
    abs_le.2 ⟨by linarith only [le_max_left (-ψ.toH1Function.toFun x) 0, h2],
      le_trans (le_max_left _ _) h1⟩
  refine hb.trans ?_
  have hqpos : 0 < Lam / lam := lt_of_lt_of_le one_pos hq
  have hrpow : (Lam / lam) ^ (deGiorgiPower d + 1) = (Lam / lam) ^ deGiorgiPower d * (Lam / lam) :=
    Real.rpow_add_one hqpos.ne' _
  have hk : 1 ≤ (d : ℝ) ^ 2 * (Lam / lam) := by
    have : (1 : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith only [hd']
    nlinarith only [this, hq]
  have hE : 0 ≤ L ^ 2 / lam * F := by positivity
  have hG2 : L / lam * ((d : ℝ) ^ 2 * Lam * G) = (d : ℝ) ^ 2 * (Lam / lam) * (L * G) := by
    field_simp
  rw [hG2, hrpow]
  have hmul : (Bb + L ^ 2 / lam * F) + (d : ℝ) ^ 2 * (Lam / lam) * (L * G) ≤
      (d : ℝ) ^ 2 * (Lam / lam) * (Bb + L ^ 2 / lam * F + L * G) := by
    have hP : 0 ≤ Bb + L ^ 2 / lam * F := by positivity
    nlinarith only [hk, hP]
  have hRn : 0 ≤ C0 * (Lam / lam) ^ deGiorgiPower d := hR
  calc C0 * (Lam / lam) ^ deGiorgiPower d * (Bb + L ^ 2 / lam * F + (d : ℝ) ^ 2 * (Lam / lam) * (L * G))
      ≤ C0 * (Lam / lam) ^ deGiorgiPower d *
        ((d : ℝ) ^ 2 * (Lam / lam) * (Bb + L ^ 2 / lam * F + L * G)) :=
        mul_le_mul_of_nonneg_left hmul hRn
    _ = _ := by ring

/-- Satisfiability: the zero solution on the unit ball with identity coefficients, zero datum and
zero right-hand side meets every non-law hypothesis of `linf_dg_boundary`. -/
example : ∀ᵐ x ∂volume.restrict (Section6.euclidBall (d := 2) 1 ∩ halfCube (0 : Vec 2) 1),
    |(0 : H1Function (Section6.euclidBall (d := 2) 1)).toFun x - (fun _ : Vec 2 => (0 : ℝ)) x| ≤
      (linf_dg_boundary (d := 2) le_rfl).choose * ((1 : ℝ) / 1) ^ (deGiorgiPower 2 + 1) *
        (0 + 1 ^ 2 / 1 * 0 + 1 * 0) := by
  have hz : IsWeakSolutionOn (fun _ => (1 : Mat 2)) (Section6.euclidBall (d := 2) 1)
      (0 : H1Function (Section6.euclidBall (d := 2) 1)) (fun _ => 0) (fun _ => 0) := by
    intro φ
    have h0 : ∀ x, (0 : H1Function (Section6.euclidBall (d := 2) 1)).grad x = 0 := fun _ => rfl
    simp [vecDot, matVecMul, h0]
  have hm : MemH10 (Section6.euclidBall (d := 2) 1) (fun x =>
      (0 : H1Function (Section6.euclidBall (d := 2) 1)).toFun x - (fun _ : Vec 2 => (0 : ℝ)) x) := by
    have : (fun x => (0 : H1Function (Section6.euclidBall (d := 2) 1)).toFun x -
        (fun _ : Vec 2 => (0 : ℝ)) x) = 0 := by
      funext x; simp
    rw [this]
    exact memH10_zero
  exact (linf_dg_boundary (d := 2) le_rfl).choose_spec.2 (Section6.isOpen_euclidBall (d := 2) 1)
    (isBoundedDomain_euclidBall one_pos) one_pos le_rfl isEllipticFieldOn_one_euclidBall
    (fun _ => 0) 0 contDiff_const hz hm 0 one_pos le_rfl le_rfl le_rfl
    aestronglyMeasurable_const (Filter.Eventually.of_forall fun x => by simp)
    (fun x _ => by simp) (by
      have : (fun x => (0 : H1Function (Section6.euclidBall (d := 2) 1)).toFun x -
        (fun _ : Vec 2 => (0 : ℝ)) x) = 0 := by funext x; simp
      rw [this]; simp)

end SuperdiffusionCLT.Section7
