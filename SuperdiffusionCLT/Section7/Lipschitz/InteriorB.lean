/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Engine.HarmonicAffineB
public import SuperdiffusionCLT.Section7.Lipschitz.Calc
public import SuperdiffusionCLT.Section7.Lipschitz.InteriorOriginC
public import SuperdiffusionCLT.Section7.Analytic.Geometry.DomainPoincareH
public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.IterationD

/-!
# From the frame of the centre to the interior estimate in `ℝ≥0∞`

Helpers for the interior Lipschitz estimate centred at `y`: the translated cube, the transfer of
weak solutions along an equality of sets, the translation of averages, and the passage from the
real-valued carrier `LipIntAt` to the `ℝ≥0∞` display.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section7

open Homogenization MeasureTheory
open scoped ENNReal Pointwise

variable {d : ℕ}

/-- The cube `y + □_n` seen from `y` is the origin cube. -/
theorem lip_interior_translate_shiftCube (y : Vec d) (n : ℕ) :
    translateSet (-y) (shiftCube y (n : ℤ)) = shiftCube 0 (n : ℤ) := by
  ext x
  rw [mem_translateSet_iff_sub_mem, sub_neg_eq_add]
  simp only [shiftCube, Set.mem_image]
  constructor
  · rintro ⟨z, hz, hzx⟩
    refine ⟨x, ?_, by simp⟩
    have : x = z := by
      have h2 : y + z = x + y := hzx
      have h3 : z = x := by
        have := add_left_cancel (a := y) (show y + z = y + x by rw [h2, add_comm])
        exact this
      exact h3.symm
    rw [this]; exact hz
  · rintro ⟨z, hz, hzx⟩
    refine ⟨z, hz, ?_⟩
    have : z = x := by simpa using hzx
    rw [this, add_comm]

/-- Weak solutions transfer along an equality of the underlying sets. -/
theorem lip_interior_congr_solution {a : CoeffField d} {W₁ W₂ : Set (Vec d)} (h : W₁ = W₂)
    {f : Vec d → ℝ} (v : H1Function W₁) (hv : IsWeakSolutionOn a W₁ v f (fun _ => 0)) :
    ∃ v' : H1Function W₂, v'.toFun = v.toFun ∧ v'.grad = v.grad ∧
      IsWeakSolutionOn a W₂ v' f (fun _ => 0) := by
  subst h
  exact ⟨v, rfl, rfl, hv⟩

/-- The average over a translated set. -/
theorem lip_interior_average_translate (y : Vec d) (S : Set (Vec d)) (hS : MeasurableSet S)
    (g : Vec d → ℝ) :
    ⨍ w in translateSet (-y) S, g (w + y) = ⨍ w in S, g w := by
  have hτ : MeasurableEmbedding (fun x : Vec d => x + y) := measurableEmbedding_addRight y
  have hT : translateSet (-y) S = (fun x : Vec d => x + y) ⁻¹' S := by
    ext x
    simp [mem_translateSet_iff_sub_mem, sub_eq_add_neg]
  have hmp : MeasurePreserving (fun x : Vec d => x + y) volume volume :=
    measurePreserving_add_right volume y
  simp only [average, integral_smul_measure]
  rw [hT, hmp.setIntegral_preimage_emb hτ g S]
  have : (volume ((fun x : Vec d => x + y) ⁻¹' S)) = volume S := by
    have := hmp.measure_preimage hS.nullMeasurableSet
    exact this
  simp only [Measure.restrict_apply_univ, this, ENNReal.toReal_inv]

theorem lip_interior_shiftCube_zero_subset [NeZero d] {n m : ℕ} (h : n ≤ m) :
    shiftCube (0 : Vec d) (n : ℤ) ⊆ shiftCube 0 (m : ℤ) := by
  rw [shiftCube_zero_eq_engCube, shiftCube_zero_eq_engCube,
    lip_interior_origin_engCube_eq_ball, lip_interior_origin_engCube_eq_ball]
  exact Metric.ball_subset_ball (by
    have : (3 : ℝ) ^ n ≤ 3 ^ m := pow_le_pow_right₀ (by norm_num) h
    linarith only [this])

theorem lip_interior_shiftCube_zero_vol [NeZero d] (n : ℕ) :
    volume (shiftCube (0 : Vec d) (n : ℤ)) ≠ 0 ∧ volume (shiftCube (0 : Vec d) (n : ℤ)) ≠ ⊤ := by
  rw [shiftCube_zero_eq_engCube]
  refine ⟨?_, Section6.eh_volume_engCube_ne_top n⟩
  intro h0
  have := Section6.eh_volume_engCube_pos (d := d) n
  rw [h0] at this
  simp at this

/-- The real inequality `LipIntAt` in the form of the `ℝ≥0∞` display, in the frame of the
centre. -/
theorem lip_interior_conv [NeZero d] {a : CoeffField d} {nu s C F : ℝ} (hs : 0 < s) (hC : 0 ≤ C)
    {n m : ℕ} (hnm : n ≤ m) (h : LipIntAt a nu s C 0 n m) (hF : 0 ≤ F) (f : Vec d → ℝ)
    (u : H1Function (shiftCube (0 : Vec d) (m : ℤ)))
    (hu : IsWeakSolutionOn a (shiftCube (0 : Vec d) (m : ℤ)) u f (fun _ => 0))
    (hfF : ∀ᵐ x ∂volume.restrict (shiftCube (0 : Vec d) (m : ℤ)), |f x| ≤ F) :
    ENNReal.ofReal ((Real.sqrt s)⁻¹ * Real.sqrt nu) *
          lpBar (shiftCube (0 : Vec d) (n : ℤ)) 2 (fun x => eucNorm (u.grad x)) +
        ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
          lpBar (shiftCube (0 : Vec d) (n : ℤ)) 2
            (fun x => u.toFun x - ⨍ w in shiftCube (0 : Vec d) (n : ℤ), u.toFun w) ≤
      ENNReal.ofReal (C * (3 : ℝ) ^ (-(m : ℝ))) *
          lpBar (shiftCube (0 : Vec d) (m : ℤ)) 2
            (fun x => u.toFun x - ⨍ w in shiftCube (0 : Vec d) (m : ℤ), u.toFun w) +
        ENNReal.ofReal (C * s⁻¹ * (3 : ℝ) ^ m) * ENNReal.ofReal F := by
  have hh := h f F u hu hF hfF
  have hsub := lip_interior_shiftCube_zero_subset (d := d) hnm
  obtain ⟨hn0, hnT⟩ := lip_interior_shiftCube_zero_vol (d := d) n
  obtain ⟨hm0, hmT⟩ := lip_interior_shiftCube_zero_vol (d := d) m
  have hmeas : ∀ k : ℕ, MeasurableSet (shiftCube (0 : Vec d) (k : ℤ)) := fun k =>
    rc_measurableSet_shiftCube _ _
  have hGn : MemLp (fun x => eucNorm (u.grad x)) 2
      (volume.restrict (shiftCube (0 : Vec d) (n : ℤ))) :=
    (memLp_eucNorm_grad u).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hfin : ∀ k : ℕ, IsFiniteMeasure (volume.restrict (shiftCube (0 : Vec d) (k : ℤ))) :=
    fun k => ⟨by
      rw [Measure.restrict_apply_univ]
      exact (lip_interior_shiftCube_zero_vol (d := d) k).2.lt_top⟩
  have hFn : MemLp (fun x => u.toFun x - ⨍ w in shiftCube (0 : Vec d) (n : ℤ), u.toFun w) 2
      (volume.restrict (shiftCube (0 : Vec d) (n : ℤ))) := by
    have := hfin n
    exact (u.memL2.mono_measure (Measure.restrict_mono hsub le_rfl)).sub (memLp_const _)
  have hFm : MemLp (fun x => u.toFun x - ⨍ w in shiftCube (0 : Vec d) (m : ℤ), u.toFun w) 2
      (volume.restrict (shiftCube (0 : Vec d) (m : ℤ))) := by
    have := hfin m
    exact u.memL2.sub (memLp_const _)
  have e1 := lip_lpBar_ne_top hn0 hGn
  have e2 := lip_lpBar_ne_top hn0 hFn
  have e3 := lip_lpBar_ne_top hm0 hFm
  have hsq : 0 ≤ (Real.sqrt s)⁻¹ * Real.sqrt nu := mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)
  have h3n : (3 : ℝ) ^ (-(n : ℝ)) = ((3 : ℝ)⁻¹) ^ n := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]
  have h3m : (3 : ℝ) ^ (-(m : ℝ)) = ((3 : ℝ)⁻¹) ^ m := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]
  have hr1 : lpBar (shiftCube (0 : Vec d) (n : ℤ)) 2 (fun x => eucNorm (u.grad x)) =
      ENNReal.ofReal (lipGradL2 (shiftCube (0 : Vec d) (n : ℤ)) u.grad) :=
    (ENNReal.ofReal_toReal e1).symm
  have hr2 : lpBar (shiftCube (0 : Vec d) (n : ℤ)) 2
      (fun x => u.toFun x - ⨍ w in shiftCube (0 : Vec d) (n : ℤ), u.toFun w) =
      ENNReal.ofReal (lipL2 (shiftCube (0 : Vec d) (n : ℤ))
        (fun x => u.toFun x - ⨍ w in shiftCube (0 : Vec d) (n : ℤ), u.toFun w)) :=
    (ENNReal.ofReal_toReal e2).symm
  have hr3 : lpBar (shiftCube (0 : Vec d) (m : ℤ)) 2
      (fun x => u.toFun x - ⨍ w in shiftCube (0 : Vec d) (m : ℤ), u.toFun w) =
      ENNReal.ofReal (lipL2 (shiftCube (0 : Vec d) (m : ℤ))
        (fun x => u.toFun x - ⨍ w in shiftCube (0 : Vec d) (m : ℤ), u.toFun w)) :=
    (ENNReal.ofReal_toReal e3).symm
  have g0 : 0 ≤ lipGradL2 (shiftCube (0 : Vec d) (n : ℤ)) u.grad := ENNReal.toReal_nonneg
  have l1 : 0 ≤ lipL2 (shiftCube (0 : Vec d) (n : ℤ))
      (fun x => u.toFun x - ⨍ w in shiftCube (0 : Vec d) (n : ℤ), u.toFun w) :=
    ENNReal.toReal_nonneg
  have l2 : 0 ≤ lipL2 (shiftCube (0 : Vec d) (m : ℤ))
      (fun x => u.toFun x - ⨍ w in shiftCube (0 : Vec d) (m : ℤ), u.toFun w) :=
    ENNReal.toReal_nonneg
  have hs1 : 0 ≤ s⁻¹ := inv_nonneg.2 hs.le
  have h3pos : (0 : ℝ) ≤ ((3 : ℝ)⁻¹) ^ n := by positivity
  have h3mpos : (0 : ℝ) ≤ ((3 : ℝ)⁻¹) ^ m := by positivity
  rw [hr1, hr2, hr3, h3n, h3m, ← ENNReal.ofReal_mul hsq, ← ENNReal.ofReal_mul h3pos,
    ← ENNReal.ofReal_mul (mul_nonneg hC h3mpos), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (mul_nonneg hsq g0) (mul_nonneg h3pos l1),
    ← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hC h3mpos) l2)
      (mul_nonneg (by positivity) hF)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : C * ((3 : ℝ)⁻¹) ^ m * lipL2 (shiftCube (0 : Vec d) (m : ℤ))
        (fun x => u.toFun x - ⨍ w in shiftCube (0 : Vec d) (m : ℤ), u.toFun w) +
      C * s⁻¹ * (3 : ℝ) ^ m * F = C * (((3 : ℝ)⁻¹) ^ m * lipL2 (shiftCube (0 : Vec d) (m : ℤ))
          (fun x => u.toFun x - ⨍ w in shiftCube (0 : Vec d) (m : ℤ), u.toFun w) +
        s⁻¹ * (3 : ℝ) ^ m * F) := by ring
  rw [e]
  exact hh

theorem lip_interior_isBounded_shiftCube (y : Vec d) (m : ℕ) :
    Bornology.IsBounded (shiftCube y (m : ℤ)) := by
  have hb := isBounded_openCubeSet (originCube d (m : ℤ))
  exact (IsometryEquiv.addLeft y).isometry.lipschitzWith.isBounded_image hb

/-- The interior estimate centred at `y`, from the estimate in the frame of the centre and the
transfer of the solution. -/
theorem lip_interior_main [NeZero d] {a : CoeffField d} {nu s C : ℝ} {y : Vec d} {m n : ℕ}
    (hC : 1 ≤ C) (hs : 0 < s) (hnm : n ≤ m) (h : LipIntAt a nu s C 0 n m) (f : Vec d → ℝ)
    (u : H1Function (shiftCube y (m : ℤ)))
    (hex : ∃ v : H1Function (translateSet (-y) (shiftCube y (m : ℤ))),
      (∀ x, v.toFun x = u.toFun (x + y)) ∧ (∀ x, v.grad x = u.grad (x + y)) ∧
      IsWeakSolutionOn a (translateSet (-y) (shiftCube y (m : ℤ))) v (fun x => f (x + y))
        (fun _ => 0)) :
    ENNReal.ofReal ((Real.sqrt s)⁻¹ * Real.sqrt nu) *
          lpBar (shiftCube y (n : ℤ)) 2 (fun x => eucNorm (u.grad x)) +
        ENNReal.ofReal ((3 : ℝ) ^ (-(n : ℝ))) *
          lpBar (shiftCube y (n : ℤ)) 2
            (fun x => u.toFun x - ⨍ w in shiftCube y (n : ℤ), u.toFun w) ≤
      ENNReal.ofReal (C * (3 : ℝ) ^ (-(m : ℝ))) *
          lpBar (shiftCube y (m : ℤ)) 2
            (fun x => u.toFun x - ⨍ w in shiftCube y (m : ℤ), u.toFun w) +
        ENNReal.ofReal (C * s⁻¹ * (3 : ℝ) ^ m) *
          eLpNorm f ⊤ (volume.restrict (shiftCube y (m : ℤ))) := by
  by_cases htop : eLpNorm f ⊤ (volume.restrict (shiftCube y (m : ℤ))) = ⊤
  · have hne : ENNReal.ofReal (C * s⁻¹ * (3 : ℝ) ^ m) ≠ 0 := by
      refine (ENNReal.ofReal_pos.2 ?_).ne'
      have : 0 < C := by linarith only [hC]
      positivity
    rw [htop, ENNReal.mul_top hne, add_top]
    exact le_top
  obtain ⟨v, hvf, hvg, hvs⟩ := hex
  obtain ⟨v', hv'f, hv'g, hv's⟩ := lip_interior_congr_solution
    (lip_interior_translate_shiftCube y m) v hvs
  have hF0 : 0 ≤ (eLpNorm f ⊤ (volume.restrict (shiftCube y (m : ℤ)))).toReal :=
    ENNReal.toReal_nonneg
  have hae : ∀ᵐ x ∂volume.restrict (shiftCube y (m : ℤ)),
      |f x| ≤ (eLpNorm f ⊤ (volume.restrict (shiftCube y (m : ℤ)))).toReal := by
    have hm : AEStronglyMeasurable f (volume.restrict (shiftCube y (m : ℤ))) := by
      by_contra hn
      exact htop (eLpNorm_of_not_aestronglyMeasurable hn)
    filter_upwards [enorm_ae_le_eLpNormEssSup f (volume.restrict (shiftCube y (m : ℤ)))] with x hx
    rw [← eLpNorm_exponent_top hm, ← ENNReal.ofReal_toReal htop, ← ofReal_norm,
      ENNReal.ofReal_le_ofReal_iff hF0, Real.norm_eq_abs] at hx
    exact hx
  have hmp : MeasurePreserving (fun x : Vec d => x + y) volume volume :=
    measurePreserving_add_right volume y
  have hpre : (fun x : Vec d => x + y) ⁻¹' shiftCube y (m : ℤ) = shiftCube 0 (m : ℤ) := by
    rw [← lip_interior_translate_shiftCube y m]
    ext x
    simp [mem_translateSet_iff_sub_mem, sub_eq_add_neg]
  have hae0 : ∀ᵐ x ∂volume.restrict (shiftCube (0 : Vec d) (m : ℤ)),
      |f (x + y)| ≤ (eLpNorm f ⊤ (volume.restrict (shiftCube y (m : ℤ)))).toReal := by
    have := (hmp.restrict_preimage (rc_measurableSet_shiftCube y (m : ℤ))).quasiMeasurePreserving.ae
      hae
    rwa [hpre] at this
  have hconv := lip_interior_conv hs (by linarith only [hC]) hnm h hF0 (fun x => f (x + y)) v' hv's
    hae0
  have hvf' : v'.toFun = fun x => u.toFun (x + y) := by rw [hv'f]; exact funext hvf
  have hvg' : v'.grad = fun x => u.grad (x + y) := by rw [hv'g]; exact funext hvg
  have k1 : ∀ k : ℕ, lpBar (shiftCube (0 : Vec d) (k : ℤ)) 2 (fun x => eucNorm (u.grad (x + y))) =
      lpBar (shiftCube y (k : ℤ)) 2 (fun x => eucNorm (u.grad x)) := fun k => by
    rw [← lip_interior_translate_shiftCube y k]
    exact lpBar_translateSet y _ 2 (fun x => eucNorm (u.grad x))
  have k2 : ∀ k : ℕ, lpBar (shiftCube (0 : Vec d) (k : ℤ)) 2
      (fun x => u.toFun (x + y) - ⨍ w in shiftCube (0 : Vec d) (k : ℤ), u.toFun (w + y)) =
      lpBar (shiftCube y (k : ℤ)) 2
        (fun x => u.toFun x - ⨍ w in shiftCube y (k : ℤ), u.toFun w) := fun k => by
    rw [← lip_interior_translate_shiftCube y k,
      lip_interior_average_translate y _ (rc_measurableSet_shiftCube y (k : ℤ)) u.toFun]
    exact lpBar_translateSet y _ 2 (fun x => u.toFun x - ⨍ w in shiftCube y (k : ℤ), u.toFun w)
  rw [hvf', hvg'] at hconv
  simp only [k1, k2] at hconv
  rwa [ENNReal.ofReal_toReal htop] at hconv

end SuperdiffusionCLT.Section7
