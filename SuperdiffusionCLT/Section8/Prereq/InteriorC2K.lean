/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section8.Prereq.InteriorC2J
public import SuperdiffusionCLT.Section8.Prereq.FieldDiffusion

/-!
# The pointwise equation

A `C²` function that solves `-∇·(a∇u) + μu = g` weakly in an open set `U`, with `a` of class `C²`
and `g` continuous, satisfies `divForm 1 a u = μ u - g` at every point of `U`.
-/

@[expose] public section

open MeasureTheory Filter Topology Homogenization
open scoped ENNReal

namespace SuperdiffusionCLT.Section8

variable {d : ℕ}

theorem intC2_integrable_cs_mul {μ : Measure (Vec d)} {ψ g : Vec d → ℝ} (hg : Integrable g μ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) : Integrable (fun x ↦ ψ x * g x) μ := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hψ
  exact hg.bdd_mul hψ.aestronglyMeasurable (Eventually.of_forall hC) (c := C)

theorem intC2_weak_unique {U : Set (Vec d)} (hU : IsOpen U) {u G1 G2 : Vec d → ℝ} {i : Fin d}
    (h1 : HasWeakPartialDerivOn U i u G1) (h2 : HasWeakPartialDerivOn U i u G2)
    (hl1 : Integrable G1 (volume.restrict U)) (hl2 : Integrable G2 (volume.restrict U)) :
    G1 =ᵐ[volume.restrict U] G2 := by
  have hzero := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume.restrict U)
    ((hl1.sub hl2).locallyIntegrable.locallyIntegrableOn U) (fun ψ hψ hψc hψs ↦ by
      have i1 := intC2_integrable_cs_mul hl1 hψ.continuous hψc
      have i2 := intC2_integrable_cs_mul hl2 hψ.continuous hψc
      have e : ∫ x, ψ x • (G1 x - G2 x) ∂(volume.restrict U) =
          (∫ x in U, G1 x * ψ x) - ∫ x in U, G2 x * ψ x := by
        rw [← integral_sub (by simpa only [mul_comm] using i1) (by simpa only [mul_comm] using i2)]
        exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only [smul_eq_mul]; ring)
      have a1 := h1 ψ hψ hψc hψs
      have a2 := h2 ψ hψ hψc hψs
      show ∫ x, ψ x • (G1 x - G2 x) ∂(volume.restrict U) = 0
      rw [e]
      linarith only [a1, a2])
  filter_upwards [hzero, ae_restrict_mem hU.measurableSet] with x hx hxU
  exact sub_eq_zero.1 (hx hxU)

theorem intC2_basisVec (i : Fin d) : basisVec i = (Pi.single i 1 : Vec d) := rfl

/-- **The pointwise equation.** -/
theorem intC2_pointwise {U : Set (Vec d)} (hU : IsOpen U) (hb : Bornology.IsBounded U)
    {a : CoeffField d} (ha : ∀ i j, ContDiff ℝ 2 fun y ↦ a y i j) {mu : ℝ} {g : Vec d → ℝ}
    (hg : Continuous g) {u : H1Function U} (hw : intC2_Weak a mu g U u)
    (hu2 : ContDiff ℝ 2 u.toFun) {x : Vec d} (hx : x ∈ U) :
    divForm 1 a u.toFun x = mu * u.toFun x - g x := by
  have hfin : IsFiniteMeasure (volume.restrict U) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hb.measure_lt_top⟩
  have hu1 : ContDiff ℝ 1 u.toFun := hu2.of_le (by norm_num)
  have hdu : ∀ i, Continuous fun y ↦ fderiv ℝ u.toFun y (basisVec i) := fun i ↦
    (hu1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hgrad : ∀ i, (fun y ↦ u.grad y i) =ᵐ[volume.restrict U]
      fun y ↦ fderiv ℝ u.toFun y (basisVec i) := fun i ↦ by
    refine intC2_weak_unique hU (u.hasWeakGradient i) (HasWeakPartialDerivOn.of_contDiff hu1)
      ((u.grad_memL2 i).integrable (by norm_num)) ?_
    obtain ⟨M, hM⟩ := intC2_bound_on hb (hdu i)
    exact (intC2_memLp_bdd hb hU.measurableSet (hdu i).aestronglyMeasurable hM 1).integrable le_rfl
  set F : Fin d → Vec d → ℝ := fun i y ↦ ∑ j, a y i j * fderiv ℝ u.toFun y (basisVec j) with hF
  have hF1 : ∀ i, ContDiff ℝ 1 (F i) := fun i ↦ by
    refine ContDiff.sum fun j _ ↦ ?_
    exact ((ha i j).of_le (by norm_num)).mul
      ((hu2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const)
  set D : Vec d → ℝ := fun y ↦ ∑ i, fderiv ℝ (F i) y (basisVec i) with hD
  have hDc : Continuous D := continuous_finsetSum _ fun i _ ↦
    ((hF1 i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDdiv : ∀ y, divForm 1 a u.toFun y = D y := fun y ↦ by
    simp only [divForm, hD, hF, one_mul, intC2_basisVec]
  have hzero : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ y, φ y • (-D y + mu * u.toFun y - g y) = 0 := fun φ hφ hφc hφs ↦ by
    have E := hw φ hφ hφc hφs
    have hφ0 : Continuous φ := hφ.continuous
    have hcsI : ∀ {f : Vec d → ℝ}, Continuous f → HasCompactSupport φ →
        Integrable (fun y ↦ f y * φ y) (volume.restrict U) := fun {f} hf hc ↦
      ((hf.mul hφ0).integrable_of_hasCompactSupport (μ := volume) hc.mul_left).restrict
    have hInt : ∀ i, Integrable (fun y ↦ F i y * fderiv ℝ φ y (basisVec i)) (volume.restrict U) :=
      fun i ↦ (((hF1 i).continuous.mul (intC2_d1_cont hφ i)).integrable_of_hasCompactSupport
        (μ := volume) ((intW2p_d1_cs hφc i).mul_left)).restrict
    have hIntD : ∀ i, Integrable (fun y ↦ fderiv ℝ (F i) y (basisVec i) * φ y)
        (volume.restrict U) := fun i ↦
      hcsI (((hF1 i).continuous_fderiv one_ne_zero).clm_apply continuous_const) hφc
    have A1 : ∫ y in U, vecDot (matVecMul (a y) (u.grad y))
        (fun i ↦ fderiv ℝ φ y (basisVec i)) =
        ∑ i, ∫ y in U, F i y * fderiv ℝ φ y (basisVec i) := by
      rw [← integral_finsetSum _ fun i _ ↦ hInt i]
      refine integral_congr_ae ?_
      filter_upwards [ae_all_iff.2 hgrad] with y hy
      simp only [vecDot, matVecMul, hF, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← hy j]
    have A2 : ∀ i, ∫ y in U, F i y * fderiv ℝ φ y (basisVec i) =
        -∫ y in U, fderiv ℝ (F i) y (basisVec i) * φ y := fun i ↦
      (HasWeakPartialDerivOn.of_contDiff (hF1 i)) φ hφ hφc hφs
    have A3 : ∫ y in U, D y * φ y = ∑ i, ∫ y in U, fderiv ℝ (F i) y (basisVec i) * φ y := by
      rw [← integral_finsetSum _ fun i _ ↦ hIntD i]
      refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
      simp only [hD, Finset.sum_mul]
    simp only [A2, Finset.sum_neg_distrib, ← A3] at A1
    have wh : ∫ y, φ y • (-D y + mu * u.toFun y - g y) =
        ∫ y in U, (-(D y * φ y) + mu * (u.toFun y * φ y) - g y * φ y) := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U)]
      · exact integral_congr_ae (Eventually.of_forall fun y ↦ by simp only [smul_eq_mul]; ring)
      · intro y hy
        rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hφs h)), zero_smul]
    have I1 := hcsI hDc hφc
    have I2 : Integrable (fun y ↦ u.toFun y * φ y) (volume.restrict U) := hcsI hu1.continuous hφc
    have I3 := hcsI hg hφc
    have I1' : Integrable (fun y ↦ -(D y * φ y)) (volume.restrict U) := I1.neg
    have K1 : Integrable (fun y ↦ -(D y * φ y) + mu * (u.toFun y * φ y)) (volume.restrict U) :=
      I1'.add (I2.const_mul mu)
    rw [wh, integral_sub K1 I3, integral_add I1' (I2.const_mul mu), integral_neg,
      integral_const_mul]
    linarith only [E, A1]
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (((hDc.neg.add (continuous_const.mul hu1.continuous)).sub hg).locallyIntegrable.locallyIntegrableOn U)
    hzero
  have heq : Set.EqOn (fun y ↦ -D y + mu * u.toFun y - g y) (fun _ ↦ 0) U :=
    Measure.eqOn_open_of_ae_eq (μ := volume) (by
      filter_upwards [(ae_restrict_iff' hU.measurableSet).2 hae] with y hy using hy)
      hU ((hDc.neg.add (continuous_const.mul hu1.continuous)).sub hg).continuousOn
      continuousOn_const
  have := heq hx
  simp only at this
  rw [hDdiv]
  linarith only [this]

/-- **Satisfiability witness.**  The constant field `a = Id` (`ν = 1`, zero skew part), `μ = 1`,
`g = 1`: the constant function `1` is a bounded continuous weak solution on the unit cube, so the
hypotheses of `intC2_contDiffAt` and `intC2_pointwise` are met. -/
example [NeZero d] (hd : 2 ≤ d) : ∃ u : H1Function (openCubeSet (originCube d 0)),
    intC2_Weak (fun _ ↦ (1 : Mat d)) 1 (fun _ ↦ (1 : ℝ)) (openCubeSet (originCube d 0)) u ∧
      (∀ x, u.toFun x = 1) ∧
      ContDiffAt ℝ 2 u.toFun 0 := by
  have hU : IsOpen (openCubeSet (originCube d 0)) := isOpen_openCubeSet _
  have hb : Bornology.IsBounded (openCubeSet (originCube d 0)) := isBounded_openCubeSet _
  have hfin : IsFiniteMeasure (volume.restrict (openCubeSet (originCube d 0))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hb.measure_lt_top⟩
  let u : H1Function (openCubeSet (originCube d 0)) :=
    { toFun := fun _ ↦ 1
      grad := fun _ ↦ 0
      memL2 := memLp_const _
      gradMemL2 := fun _ ↦ memLp_const _
      hasWeakGradient := fun i ↦ by
        intro φ hφ hc hs
        have h := (HasWeakPartialDerivOn.of_contDiff (U := openCubeSet (originCube d 0))
          (i := i) (contDiff_const (c := (1 : ℝ)))) φ hφ hc hs
        simpa using h }
  have hw : intC2_Weak (fun _ ↦ (1 : Mat d)) 1 (fun _ ↦ (1 : ℝ)) (openCubeSet (originCube d 0)) u := by
    intro φ hφ hc hs
    simp [u, vecDot, matVecMul]
  refine ⟨u, hw, fun x ↦ rfl, ?_⟩
  refine intC2_contDiffAt hd hU (a := fun _ ↦ (1 : Mat d)) (nu := 1) one_pos (fun y i j ↦ ?_)
    (fun i j ↦ contDiff_const) (mu := 1) (g := fun _ ↦ (1 : ℝ)) contDiff_const (M := 1) hw
    continuousOn_const (fun x _ ↦ by simp [u]) (x₀ := 0) (by
      rw [mem_openCubeSet_originCube_iff]
      intro i
      simp)
  by_cases h : i = j
  · subst h; simp; norm_num
  · simp [h, Ne.symm h]

end SuperdiffusionCLT.Section8
