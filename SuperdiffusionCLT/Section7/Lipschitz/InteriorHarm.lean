/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Lipschitz.Carriers
public import SuperdiffusionCLT.Section7.Prereq.WellPosed
public import SuperdiffusionCLT.Section7.Prereq.RootCarriersApiB
public import SuperdiffusionCLT.Section7.Prereq.RootCarriersApiC
public import SuperdiffusionCLT.Section7.Root.ScalarComparison
public import SuperdiffusionCLT.Section6.Engine.HarmonicAffineC
public import SuperdiffusionCLT.Section2.Norms.CubeLp

/-!
# The interior harmonic approximation from the `L²` block: calculus and the Laplace comparison

Normalized `L²` calculus on subsets (`lip_int_harm_of_l2_lipL2_mono_set`, the triangle inequality),
the comparison of the Poisson solution `-sΔ ub = f` with the Laplace solution of the same trace
(`lip_int_harm_of_l2_energy`), the constant case, and the real arithmetic of the final bound.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7
variable {d : ℕ}

theorem lip_int_harm_of_l2_lpBar_eq {S : Set (Vec d)} (hS0 : volume S ≠ 0) (hS : volume S ≠ ⊤)
    {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict S)) :
    lpBar S 2 f = ENNReal.ofReal ((volume S).toReal⁻¹ ^ (1 / 2 : ℝ)) * eLpNorm f 2 (volume.restrict S) := by
  rw [rc_lpBar_two_eq S f hf.aestronglyMeasurable]
  congr 1
  rw [← ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) (by norm_num),
    ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hS0 hS), ENNReal.ofReal_toReal hS]

theorem lip_int_harm_of_l2_lpBar_lt_top {S : Set (Vec d)} (hS0 : volume S ≠ 0) (hS : volume S ≠ ⊤)
    {f : Vec d → ℝ} (hf : MemLp f 2 (volume.restrict S)) : lpBar S 2 f ≠ ⊤ := by
  rw [lip_int_harm_of_l2_lpBar_eq hS0 hS hf]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top

theorem lip_int_harm_of_l2_ofReal_lipL2 {S : Set (Vec d)} {f : Vec d → ℝ} (hS0 : volume S ≠ 0)
    (hS : volume S ≠ ⊤) (hf : MemLp f 2 (volume.restrict S)) :
    ENNReal.ofReal (lipL2 S f) = lpBar S 2 f :=
  ENNReal.ofReal_toReal (lip_int_harm_of_l2_lpBar_lt_top hS0 hS hf)

/-- Restriction to a subset costs the square root of the volume ratio. -/
theorem lip_int_harm_of_l2_lipL2_mono_set {S S' : Set (Vec d)} {f : Vec d → ℝ} {κ : ℝ}
    (hSS : S ⊆ S') (hS0 : volume S ≠ 0) (hS' : volume S' ≠ ⊤)
    (hvol : (volume S').toReal ≤ κ * (volume S).toReal) (hf : MemLp f 2 (volume.restrict S')) :
    lipL2 S f ≤ Real.sqrt κ * lipL2 S' f := by
  have hS : volume S ≠ ⊤ := ne_top_of_le_ne_top hS' (measure_mono hSS)
  have hS'0 : volume S' ≠ 0 := fun h => hS0 (le_antisymm (h ▸ measure_mono hSS) bot_le)
  have hf1 : MemLp f 2 (volume.restrict S) := hf.mono_measure (Measure.restrict_mono hSS le_rfl)
  have hm : 0 < (volume S).toReal := ENNReal.toReal_pos hS0 hS
  have hm' : 0 < (volume S').toReal := ENNReal.toReal_pos hS'0 hS'
  have hκ : 0 ≤ κ := by
    by_contra h
    push Not at h
    have := mul_neg_of_neg_of_pos h hm
    linarith only [this, hvol, hm'.le]
  have hN : (eLpNorm f 2 (volume.restrict S)).toReal ≤ (eLpNorm f 2 (volume.restrict S')).toReal :=
    ENNReal.toReal_mono hf.eLpNorm_ne_top
      (eLpNorm_mono_measure f (Measure.restrict_mono hSS le_rfl))
  have e1 : lipL2 S f = ((volume S).toReal⁻¹ ^ (1 / 2 : ℝ)) * (eLpNorm f 2 (volume.restrict S)).toReal := by
    unfold lipL2
    rw [lip_int_harm_of_l2_lpBar_eq hS0 hS hf1, ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (Real.rpow_nonneg (inv_nonneg.2 hm.le) _)]
  have e2 : lipL2 S' f = ((volume S').toReal⁻¹ ^ (1 / 2 : ℝ)) * (eLpNorm f 2 (volume.restrict S')).toReal := by
    unfold lipL2
    rw [lip_int_harm_of_l2_lpBar_eq hS'0 hS' hf, ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (Real.rpow_nonneg (inv_nonneg.2 hm'.le) _)]
  have hc : ((volume S).toReal⁻¹ ^ (1 / 2 : ℝ)) ≤ Real.sqrt κ * ((volume S').toReal⁻¹ ^ (1 / 2 : ℝ)) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul hκ]
    refine Real.sqrt_le_sqrt ?_
    rw [inv_eq_one_div, inv_eq_one_div, mul_one_div, div_le_div_iff₀ hm hm']
    linarith only [hvol]
  rw [e1, e2]
  calc ((volume S).toReal⁻¹ ^ (1 / 2 : ℝ)) * (eLpNorm f 2 (volume.restrict S)).toReal
      ≤ (Real.sqrt κ * ((volume S').toReal⁻¹ ^ (1 / 2 : ℝ))) * (eLpNorm f 2 (volume.restrict S')).toReal :=
        mul_le_mul hc hN ENNReal.toReal_nonneg (by positivity)
    _ = _ := by ring

theorem lip_int_harm_of_l2_lipL2_add_le {S : Set (Vec d)} {f g : Vec d → ℝ} (hS0 : volume S ≠ 0)
    (hS : volume S ≠ ⊤) (hf : MemLp f 2 (volume.restrict S)) (hg : MemLp g 2 (volume.restrict S)) :
    lipL2 S (fun x => f x + g x) ≤ lipL2 S f + lipL2 S g := by
  have hfg : MemLp (fun x => f x + g x) 2 (volume.restrict S) := hf.add hg
  have e : ∀ h : Vec d → ℝ, MemLp h 2 (volume.restrict S) → lipL2 S h =
      ((volume S).toReal⁻¹ ^ (1 / 2 : ℝ)) * (eLpNorm h 2 (volume.restrict S)).toReal := by
    intro h hh
    have hm : 0 < (volume S).toReal := ENNReal.toReal_pos hS0 hS
    unfold lipL2
    rw [lip_int_harm_of_l2_lpBar_eq hS0 hS hh, ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (Real.rpow_nonneg (inv_nonneg.2 hm.le) _)]
  rw [e _ hfg, e _ hf, e _ hg, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) _)
  rw [← ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩)
    (eLpNorm_add_le (p := 2) one_le_two)

theorem lip_int_harm_of_l2_lpBar_le_of_ae_bound {S : Set (Vec d)} (hS0 : volume S ≠ 0)
    (hS : volume S ≠ ⊤) (p : ℝ≥0∞) {f : Vec d → ℝ} {F : ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict S))
    (h : ∀ᵐ x ∂volume.restrict S, |f x| ≤ F) : lpBar S p f ≤ ENNReal.ofReal F := by
  unfold lpBar
  have hμ : (((volume S)⁻¹) • volume.restrict S) Set.univ = 1 := by
    rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hS0 hS
  have hae : ∀ᵐ x ∂(((volume S)⁻¹) • volume.restrict S), ‖f x‖ ≤ F := by
    filter_upwards [Measure.smul_absolutelyContinuous.ae_le h] with x hx
    rwa [Real.norm_eq_abs]
  have := eLpNorm_le_of_ae_bound (p := p) (hfm.smul_measure _) hae
  rwa [hμ, ENNReal.one_rpow, one_mul] at this

theorem lip_int_harm_of_l2_lpBar_openCube {E : Type*} [NormedAddCommGroup E] (Q : TriadicCube d)
    (p : ℝ≥0∞) (F : Vec d → E) :
    lpBar (openCubeSet Q) p F = SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q p F := by
  unfold lpBar SuperdiffusionCLT.Section2.Norms.cubeLpENorm normalizedCubeMeasure cubeMeasure
  have hv : volume (openCubeSet Q) = ENNReal.ofReal (cubeVolume Q) := by
    rw [volume_openCubeSet_eq_volume_cubeSet, ← cubeMeasure_apply_univ,
      cubeMeasure_apply_univ_eq]
  rw [hv, ENNReal.ofReal_inv_of_pos (cubeVolume_pos Q)]
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

theorem lip_int_harm_of_l2_lipL2_engCube [NeZero d] (n : ℕ) (f : Vec d → ℝ) :
    lipL2 (Section6.engCube d n) f = Section6.cubeL2 n f := by
  unfold lipL2 Section6.cubeL2
  rw [Section6.engCube, lip_int_harm_of_l2_lpBar_openCube,
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm_toReal_eq_cubeLpNorm]

theorem lip_int_harm_of_l2_lipGradL2_engCube [NeZero d] (n : ℕ) (F : Vec d → Vec d) :
    lipGradL2 (Section6.engCube d n) F = Section6.cubeGradL2 n F := by
  unfold lipGradL2 Section6.cubeGradL2
  rw [← lip_int_harm_of_l2_lipL2_engCube]
  rfl

theorem lip_int_harm_of_l2_vol_ne_zero (n : ℕ) : volume (Section6.engCube d n) ≠ 0 := by
  have := Section6.eh_volume_engCube_pos (d := d) n
  intro h
  rw [h] at this
  simp at this

theorem lip_int_harm_of_l2_vol_toReal (n : ℕ) :
    (volume (Section6.engCube d n)).toReal = ((3 : ℝ) ^ d) ^ n := by
  rw [Section6.eh_volume_engCube, ← pow_mul, ← pow_mul, mul_comm]

theorem lip_int_harm_of_l2_matVecMul_smul_one (s : ℝ) (v : Vec d) :
    matVecMul (s • (1 : Mat d)) v = s • v := by
  funext i
  simp [matVecMul, Matrix.smul_apply, Matrix.one_apply]

theorem lip_int_harm_of_l2_ell_one {U : Set (Vec d)} (hU : MeasurableSet U) :
    IsEllipticFieldOn (d := d) 1 1 U (fun _ => (1 : Mat d)) := by
  simpa using rc_isEllipticFieldOn_smul_one one_pos hU

/-- The difference of the Poisson and the Laplace solution with the same trace solves a Laplace
problem with the right-hand side `f / s`. -/
theorem lip_int_harm_of_l2_diff_weak {V : Set (Vec d)} (hV : IsOpen V) {s : ℝ} (hs : 0 < s)
    {f : Vec d → ℝ} (ub h : H1Function V) (wH : H10Function V)
    (hub : IsWeakSolutionOn (fun _ => s • (1 : Mat d)) V ub f (fun _ => 0))
    (hh : IsWeakSolutionOn (fun _ => (1 : Mat d)) V h (fun _ => 0) (fun _ => 0))
    (hwH : wH.toH1Function.toFun = fun x => ub.toFun x - h.toFun x) :
    IsWeakSolutionOn (fun _ => (1 : Mat d)) V wH.toH1Function (fun x => s⁻¹ * f x)
      (fun _ => 0) := by
  intro φ
  have hgrad := w0_h10_grad_ae hV h ub wH hwH
  have i1 : IntegrableOn (fun x => vecDot (ub.grad x) (φ.toH1Function.grad x)) V :=
    integrableOn_vecDot_of_memVectorL2 ub.grad_memVectorL2 φ.toH1Function.grad_memVectorL2
  have i2 : IntegrableOn (fun x => vecDot (h.grad x) (φ.toH1Function.grad x)) V :=
    integrableOn_vecDot_of_memVectorL2 h.grad_memVectorL2 φ.toH1Function.grad_memVectorL2
  have e1 := hub φ
  have e2 := hh φ
  simp only [lip_int_harm_of_l2_matVecMul_smul_one, vecDot_smul_left, vecDot_zero_left,
    integral_zero, add_zero, matVecMul_one, integral_const_mul] at e1 e2 ⊢
  have e3 : ∫ x in V, vecDot (wH.toH1Function.grad x) (φ.toH1Function.grad x) =
      (∫ x in V, vecDot (ub.grad x) (φ.toH1Function.grad x)) -
        ∫ x in V, vecDot (h.grad x) (φ.toH1Function.grad x) := by
    rw [← integral_sub i1 i2]
    refine integral_congr_ae ?_
    filter_upwards [hgrad] with x hx
    rw [hx, sub_eq_add_neg, vecDot_add_left, vecDot_neg_left, ← sub_eq_add_neg]
  have e4 : ∫ x in V, s⁻¹ * f x * φ.toH1Function.toFun x =
      s⁻¹ * ∫ x in V, f x * φ.toH1Function.toFun x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [e3, e4, e2, ← e1]
  field_simp
  ring

theorem lip_int_harm_of_l2_mem_engCube {n : ℕ} {x : Vec d} (hx : x ∈ Section6.engCube d n) (i : Fin d) :
    -((3 : ℝ) ^ n / 2) < x i ∧ x i < (3 : ℝ) ^ n / 2 := by
  have h := mem_openCubeSet_originCube_iff.1 hx i
  rw [zpow_natCast] at h
  constructor <;> linarith only [h.1, h.2]

theorem lip_int_harm_of_l2_engCube_subset_axis (n : ℕ) :
    Section6.engCube d n ⊆ axisCube (fun _ => -((3 : ℝ) ^ n / 2)) ((3 : ℝ) ^ n) := by
  intro x hx j _
  have h := lip_int_harm_of_l2_mem_engCube hx j
  constructor <;> linarith only [h.1, h.2]

theorem lip_int_harm_of_l2_isBoundedDomain {V : Set (Vec d)} {n : ℕ} (h : V ⊆ Section6.engCube d n) :
    IsBoundedDomain V := by
  refine ⟨(3 : ℝ) ^ n, by positivity, fun x hx i => ?_⟩
  have := lip_int_harm_of_l2_mem_engCube (h hx) i
  have hp : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  rw [abs_le]
  constructor <;> linarith only [this.1, this.2, hp]

/-- The Poisson solution is `c² 9^m F / s`-close in `L̲²` to the Laplace solution with the same
trace. -/
theorem lip_int_harm_of_l2_energy [NeZero d] :
    ∃ c : ℝ, 0 < c ∧ ∀ {V : Set (Vec d)}, IsOpen V → ∀ {m : ℕ}, V ⊆ Section6.engCube d m →
      volume V ≠ 0 → ∀ {s : ℝ}, 0 < s → ∀ (f : Vec d → ℝ) {F : ℝ}, 0 ≤ F →
      AEStronglyMeasurable f (volume.restrict V) → (∀ᵐ x ∂volume.restrict V, |f x| ≤ F) →
      ∀ (ub h : H1Function V),
        IsWeakSolutionOn (fun _ => s • (1 : Mat d)) V ub f (fun _ => 0) →
        IsWeakSolutionOn (fun _ => (1 : Mat d)) V h (fun _ => 0) (fun _ => 0) →
        MemH10 V (fun x => ub.toFun x - h.toFun x) →
          lipL2 V (fun x => ub.toFun x - h.toFun x) ≤ c ^ 2 * ((3 : ℝ) ^ m) ^ 2 * (s⁻¹ * F) := by
  obtain ⟨c, hc, hE⟩ := s12_energy (d := d)
  refine ⟨c, hc, ?_⟩
  intro V hV m hVm hV0 s hs f F hF hfm hfb ub h hub hh hm
  have hVt : volume V ≠ ⊤ := ne_top_of_le_ne_top (Section6.eh_volume_engCube_ne_top m)
    (measure_mono hVm)
  obtain ⟨wH, hwH⟩ := hm
  have hweak := lip_int_harm_of_l2_diff_weak hV hs ub h wH hub hh hwH
  have hL : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  obtain ⟨hw2, -⟩ := hE hV (fun _ => -((3 : ℝ) ^ m / 2)) hL
    (hVm.trans (lip_int_harm_of_l2_engCube_subset_axis m)) (fun x => s⁻¹ * f x) wH hweak
  have hfm' : AEStronglyMeasurable (fun x => s⁻¹ * f x) (volume.restrict V) := hfm.const_mul _
  have hfb' : ∀ᵐ x ∂volume.restrict V, |s⁻¹ * f x| ≤ s⁻¹ * F := by
    filter_upwards [hfb] with x hx
    rw [abs_mul, abs_of_pos (inv_pos.2 hs)]
    exact mul_le_mul_of_nonneg_left hx (inv_pos.2 hs).le
  have hfin : IsFiniteMeasure (volume.restrict V) := ⟨by simpa using hVt.lt_top⟩
  have hf2 : MemLp (fun x => s⁻¹ * f x) 2 (volume.restrict V) :=
    MemLp.of_bound hfm' (s⁻¹ * F) (hfb'.mono fun x hx => by rwa [Real.norm_eq_abs])
  have hwm : MemLp wH.toH1Function.toFun 2 (volume.restrict V) := wH.toH1Function.memL2
  have hlp := lip_int_harm_of_l2_lpBar_le_of_ae_bound hV0 hVt 2 hfm' hfb'
  have e1 : lpBar V 2 wH.toH1Function.toFun ≤
      ENNReal.ofReal ((c * (3 : ℝ) ^ m) ^ 2) * ENNReal.ofReal (s⁻¹ * F) := by
    rw [lip_int_harm_of_l2_lpBar_eq hV0 hVt hwm]
    calc _ ≤ ENNReal.ofReal ((volume V).toReal⁻¹ ^ (1 / 2 : ℝ)) *
          (ENNReal.ofReal ((c * (3 : ℝ) ^ m) ^ 2) * eLpNorm (fun x => s⁻¹ * f x) 2
            (volume.restrict V)) := mul_le_mul' le_rfl hw2
      _ = ENNReal.ofReal ((c * (3 : ℝ) ^ m) ^ 2) * lpBar V 2 (fun x => s⁻¹ * f x) := by
          rw [lip_int_harm_of_l2_lpBar_eq hV0 hVt hf2]; ring
      _ ≤ _ := mul_le_mul' le_rfl hlp
  have hfun : (fun x => ub.toFun x - h.toFun x) = wH.toH1Function.toFun := hwH.symm
  unfold lipL2
  rw [hfun]
  have hfin2 : ENNReal.ofReal ((c * (3 : ℝ) ^ m) ^ 2) * ENNReal.ofReal (s⁻¹ * F) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have := ENNReal.toReal_mono hfin2 e1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)] at this
  calc _ ≤ _ := this
    _ = _ := by ring

/-- The gradient part of the block, in terms of the Caccioppoli bound. -/
theorem lip_int_harm_of_l2_arith_grad {Cin δ r q P' P Gv Gc fl M N1 : ℝ} {A : ℕ}
    (hCin : 1 ≤ Cin) (hδ : 0 ≤ δ) (hr : 0 < r) (hq : 0 < q) (hP'0 : 0 ≤ P')
    (hP' : P' ≤ 2 ^ A * P) (H1 : P * r ≤ δ * q) (hN1 : 0 ≤ N1) (hGv : Gv ≤ N1 * Gc)
    (hfl : 0 ≤ fl) (hM : 0 ≤ M)
    (hCacc : q * Gc ≤ Cin * (r * fl + r⁻¹ * M)) :
    (Cin * δ * r⁻¹ * q + Cin * P') * Gv ≤
      N1 * (Cin ^ 2 * (1 + 2 ^ A)) * (δ * (fl + (r ^ 2)⁻¹ * M)) := by
  have hCin0 : 0 < Cin := by linarith only [hCin]
  have h2A : (1 : ℝ) ≤ 2 ^ A := one_le_pow₀ (by norm_num)
  set Bc : ℝ := Cin * δ * r⁻¹ + Cin * (P' / q) with hBc
  have hBc0 : 0 ≤ Bc := by positivity
  have hPq : P' / q ≤ 2 ^ A * (δ * r⁻¹) := by
    have h1 : P / q ≤ δ * r⁻¹ := by
      rw [div_le_iff₀ hq, mul_assoc, mul_comm r⁻¹ q, ← mul_assoc, ← div_eq_mul_inv,
        le_div_iff₀ hr]
      linarith only [H1]
    calc P' / q ≤ 2 ^ A * P / q := div_le_div_of_nonneg_right hP' hq.le
      _ = 2 ^ A * (P / q) := by ring
      _ ≤ 2 ^ A * (δ * r⁻¹) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hBc1 : Bc ≤ Cin * (1 + 2 ^ A) * (δ * r⁻¹) := by
    have : Cin * (P' / q) ≤ Cin * (2 ^ A * (δ * r⁻¹)) := mul_le_mul_of_nonneg_left hPq hCin0.le
    rw [hBc]
    linarith only [this]
  have e1 : (Cin * δ * r⁻¹ * q + Cin * P') = Bc * q := by
    rw [hBc]
    field_simp
  have hX : 0 ≤ r * fl + r⁻¹ * M := by positivity
  calc (Cin * δ * r⁻¹ * q + Cin * P') * Gv = Bc * (q * Gv) := by rw [e1]; ring
    _ ≤ Bc * (q * (N1 * Gc)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hGv hq.le) hBc0
    _ = N1 * (Bc * (q * Gc)) := by ring
    _ ≤ N1 * (Bc * (Cin * (r * fl + r⁻¹ * M))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hCacc hBc0) hN1
    _ ≤ N1 * ((Cin * (1 + 2 ^ A) * (δ * r⁻¹)) * (Cin * (r * fl + r⁻¹ * M))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hBc1 (by positivity)) hN1
    _ = N1 * (Cin ^ 2 * (1 + 2 ^ A)) * (δ * (fl + (r ^ 2)⁻¹ * M)) := by
        field_simp

/-- The real arithmetic of the interior harmonic approximation. -/
theorem lip_int_harm_of_l2_arith {Cin δ r q P' P Gv Gc fl F t T E N1 c2 : ℝ} {A : ℕ}
    (hCin : 1 ≤ Cin) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hr : 0 < r) (hq : 0 < q) (hP'0 : 0 ≤ P')
    (hP' : P' ≤ 2 ^ A * P) (H1 : P * r ≤ δ * q) (H2 : P * r ^ 2 ≤ 1)
    (hN1 : 0 ≤ N1) (hc2 : 0 ≤ c2) (hGv : Gv ≤ N1 * Gc) (hfl : 0 ≤ fl) (hF : 0 ≤ F)
    (ht : 0 < t) (hCacc : q * Gc ≤ Cin * (r * fl + r⁻¹ * (t * F)))
    (hblock : T ≤ (t / 3) * (Cin * δ * r⁻¹ * q * Gv + Cin * P' * (Gv + t / 3 * F)))
    (hE : E ≤ c2 * (t / 3) ^ 2 * ((r ^ 2)⁻¹ * F)) :
    T + E ≤ (N1 * (Cin ^ 2 * (1 + 2 ^ A)) + Cin * 2 ^ A + c2) * (δ * (t * fl)) +
      (N1 * (Cin ^ 2 * (1 + 2 ^ A)) + Cin * 2 ^ A + c2) * ((r ^ 2)⁻¹ * t ^ 2 * F) := by
  have hCin0 : 0 < Cin := by linarith only [hCin]
  have h2A : (1 : ℝ) ≤ 2 ^ A := one_le_pow₀ (by norm_num)
  have hg := lip_int_harm_of_l2_arith_grad (A := A) hCin hδ hr hq hP'0 hP' H1 hN1 hGv hfl
    (mul_nonneg ht.le hF) hCacc
  have hPs : P ≤ (r ^ 2)⁻¹ := by
    rw [← one_div, le_div_iff₀ (by positivity)]
    exact H2
  set W : ℝ := (r ^ 2)⁻¹ with hW
  have hW0 : 0 < W := by positivity
  set K0 : ℝ := N1 * (Cin ^ 2 * (1 + 2 ^ A)) with hK0
  have hK00 : 0 ≤ K0 := by positivity
  have hP'W : P' ≤ 2 ^ A * W :=
    hP'.trans (mul_le_mul_of_nonneg_left hPs (by positivity))
  have h1 : (t / 3) * (Cin * δ * r⁻¹ * q * Gv + Cin * P' * (Gv + t / 3 * F)) =
      (t / 3) * ((Cin * δ * r⁻¹ * q + Cin * P') * Gv) + (t / 3) * (Cin * P' * (t / 3 * F)) := by
    ring
  have h2 : (t / 3) * ((Cin * δ * r⁻¹ * q + Cin * P') * Gv) ≤
      (t / 3) * (K0 * (δ * (fl + W * (t * F)))) :=
    mul_le_mul_of_nonneg_left hg (by positivity)
  have h3 : (t / 3) * (Cin * P' * (t / 3 * F)) ≤ (t / 3) * (Cin * (2 ^ A * W) * (t / 3 * F)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP'W hCin0.le) (by positivity)
  have hX1 : 0 ≤ δ * (t * fl) := by positivity
  have hX2 : 0 ≤ W * t ^ 2 * F := by positivity
  have hT : T + E ≤ (K0 / 3) * (δ * (t * fl)) +
      (K0 / 3 * δ + Cin * 2 ^ A / 9 + c2 / 9) * (W * t ^ 2 * F) := by
    have e1 : T ≤ (K0 / 3) * (δ * (t * fl)) + (K0 / 3 * δ + Cin * 2 ^ A / 9) * (W * t ^ 2 * F) := by
      have := hblock
      rw [h1] at this
      calc T ≤ _ := this
        _ ≤ (t / 3) * (K0 * (δ * (fl + W * (t * F)))) + (t / 3) * (Cin * (2 ^ A * W) * (t / 3 * F)) :=
          add_le_add h2 h3
        _ = _ := by ring
    have e2 : E ≤ c2 / 9 * (W * t ^ 2 * F) := by
      calc E ≤ _ := hE
        _ = _ := by rw [hW]; ring
    linarith only [e1, e2]
  have hc1 : (K0 / 3) * (δ * (t * fl)) ≤
      (K0 + Cin * 2 ^ A + c2) * (δ * (t * fl)) := by
    refine mul_le_mul_of_nonneg_right ?_ hX1
    have : 0 ≤ Cin * 2 ^ A := by positivity
    linarith only [hK00, this, hc2]
  have hc2' : (K0 / 3 * δ + Cin * 2 ^ A / 9 + c2 / 9) * (W * t ^ 2 * F) ≤
      (K0 + Cin * 2 ^ A + c2) * (W * t ^ 2 * F) := by
    refine mul_le_mul_of_nonneg_right ?_ hX2
    have : 0 ≤ Cin * 2 ^ A := by positivity
    have h4 : K0 / 3 * δ ≤ K0 := by
      calc K0 / 3 * δ ≤ K0 / 3 * 1 := mul_le_mul_of_nonneg_left hδ1 (by positivity)
        _ ≤ K0 := by linarith only [hK00]
    linarith only [h4, this, hc2]
  linarith only [hT, hc1, hc2']

/-- The constant case: the mean value is a harmonic function with the full error. -/
theorem lip_int_harm_of_l2_const [NeZero d] {k : ℕ} (hk : 3 ≤ k)
    (u : H1Function (Section6.engCube d k)) :
    ∃ (w : Vec d → ℝ) (gw : Vec d → Vec d),
      Section6.IsSolOn (fun _ => (1 : Mat d)) (Section6.engCube d (k - 3)) w gw ∧
        Section6.cubeL2 (k - 3) (fun x => u.toFun x - w x) ≤
          Real.sqrt (((3 : ℝ) ^ d) ^ 3) * ((3 : ℝ) ^ k * Section6.cubeFlat k u.toFun) := by
  set c : ℝ := cubeAverage (originCube d (k : ℤ)) u.toFun with hc
  refine ⟨fun _ => c, fun _ => 0, ?_, ?_⟩
  · have := Section6.isSolOn_one_affine (d := d) (k - 3) c 0
    simpa [vecDot] using this
  · have hmem : MemLp (fun x => u.toFun x - c) 2 (volume.restrict (Section6.engCube d k)) :=
      u.memL2.sub (memLp_const c)
    have hsub : Section6.engCube d (k - 3) ⊆ Section6.engCube d k :=
      Section6.eh_engCube_mono (Nat.sub_le k 3)
    have hvol : (volume (Section6.engCube d k)).toReal ≤
        ((3 : ℝ) ^ d) ^ 3 * (volume (Section6.engCube d (k - 3))).toReal := by
      rw [lip_int_harm_of_l2_vol_toReal, lip_int_harm_of_l2_vol_toReal, ← pow_add]
      have : 3 + (k - 3) = k := by omega
      rw [this]
    have h := lip_int_harm_of_l2_lipL2_mono_set hsub (lip_int_harm_of_l2_vol_ne_zero (k - 3))
      (Section6.eh_volume_engCube_ne_top k) hvol hmem
    rw [lip_int_harm_of_l2_lipL2_engCube, lip_int_harm_of_l2_lipL2_engCube] at h
    have e : (3 : ℝ) ^ k * Section6.cubeFlat k u.toFun =
        Section6.cubeL2 k (fun x => u.toFun x - c) := by
      unfold Section6.cubeFlat
      rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ (by norm_num), one_pow, one_mul]
    rw [e]
    exact h

end SuperdiffusionCLT.Section7
