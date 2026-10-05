/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.Defs
public import Homogenization.Sobolev.CubeEmbedding.LimitFiniteP
public import Homogenization.Sobolev.MatchedPair.ScaledPoincare
public import Homogenization.Sobolev.Foundations.PoincareW1p.OverlapCube
public import Homogenization.Sobolev.Foundations.MeanZero
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.AxisCubeHarmonicCovariance
public import Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ScalarPoissonHessian
public import SuperdiffusionCLT.Section2.Norms.CubeLp

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal NNReal Pointwise

/-!
# Cube scalar data: `s ∈ L^r` gives `∇ψ_s ∈ L^{r^*}`

For a zero-trace weak solution `ψ` of `-Δψ = s` on a centred triadic cube with
`s ∈ L̲² ∩ L̲^r`, `r < d`, each coordinate of `∇ψ` lies in `L̲^{r^*}`, `1/r^* = 1/r - 1/d`, with
`‖∂ᵢψ‖_{L̲^{r^*}} ≤ C 3^m ‖s‖_{L̲^r}` (`exists_cubeScalarData_gradLp_sobolev`).

Route: the Hessian estimate of CoarseGraining gives `∇²ψ ∈ L̲^r`; `∂ᵢψ` has mean zero (zero trace of
`ψ`), lies in `L²`, and has weak gradient `∇∂ᵢψ ∈ L^r`. A finite ladder of Sobolev embeddings
(`memLp_ladder`) puts `∂ᵢψ` in `L^{r^*}`, and the mean-zero `W^{1,r}` Poincaré inequality with the
Sobolev inequality of CoarseGraining gives the scale-free bound on axis cubes
(`axisCube_lpStar_of_gradLp`). `gradLp_of_weakHessian` is the assembly on any triadic cube, given a
weak Hessian in `L̲^r`; only the Hessian estimate itself is restricted to origin cubes.
-/

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem poincare_axisCube_w1p_ofReal {q : ℝ} (hq : 1 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Vec d) (L : ℝ), 0 < L →
      ∀ u : W1pFunction (axisCube z L) (ENNReal.ofReal q),
        MeanZeroOn (axisCube z L) u.toFun →
        u.valueLpSeminorm ≤ C * L * u.gradientCoordLpSeminormSum := by
  let hCunit : W1pPoincareEstimate (axisCube (0 : Vec d) 1) (ENNReal.ofReal q) :=
    w1pPoincareEstimate_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_axisCube (0 : Vec d) 1) hq
  refine ⟨hCunit.constant, hCunit.constant_nonneg, ?_⟩
  intro z L hL
  rw [axisCube_eq_translateSet_smul z L hL]
  intro u hmean
  let hCtrans : W1pPoincareEstimate
      (translateSet z (L • axisCube (0 : Vec d) 1)) (ENNReal.ofReal q) :=
    (hCunit.dilate hL ENNReal.ofReal_ne_top).translate z
  have h := hCtrans.bound_subAverage u hmean
  rw [u.subAverageLpSeminorm_eq_valueLpSeminorm_of_meanZero hmean] at h
  simp only [hCtrans, W1pPoincareEstimate.translate_constant,
    W1pPoincareEstimate.dilate_constant] at h
  linarith only [h]


theorem poincare_axisCube_w1p (r : FiniteLpExponent) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : Vec d) (L : ℝ), 0 < L →
      ∀ u : W1pFunction (axisCube z L) r.exponent,
        MeanZeroOn (axisCube z L) u.toFun →
        u.valueLpSeminorm ≤ C * L * u.gradientCoordLpSeminormSum := by
  have hq : 1 < r.exponent.toReal := by
    have hq' : (1 : ℝ≥0∞).toReal < r.exponent.toReal :=
      (ENNReal.toReal_lt_toReal (by norm_num) r.lt_top.ne).2 r.one_lt
    simpa using hq'
  have h := poincare_axisCube_w1p_ofReal (d := d) hq
  rwa [ENNReal.ofReal_toReal r.lt_top.ne] at h

theorem w1p_meanZero_sobolev (hd : 0 < d) (r : FiniteLpExponent)
    (hr : r.exponent.toReal < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : FiniteLpExponent,
      (q.exponent.toReal)⁻¹ = r.exponent.toReal⁻¹ - (d : ℝ)⁻¹ →
      ∀ (z : Vec d) (L : ℝ), 0 < L → ∀ u : W1pFunction (axisCube z L) r.exponent,
        MeanZeroOn (axisCube z L) u.toFun →
        eLpNorm u.toFun q.exponent (volume.restrict (axisCube z L)) ≤
          ENNReal.ofReal C * ∑ i : Fin d,
            eLpNorm (fun x => u.grad x i) r.exponent (volume.restrict (axisCube z L)) := by
  obtain ⟨Cs, hCs0, hCs⟩ := Homogenization.cubeSobolevEmbedding_finiteLp hd r hr
  obtain ⟨Cp, hCp0, hCp⟩ := poincare_axisCube_w1p (d := d) r
  refine ⟨(Cs : ℝ) * (1 + Cp), by positivity, ?_⟩
  intro q hq z L hL u hmean
  have h1 := hCs q hq z L hL u
  set M := volume.restrict (axisCube z L) with hM
  set S := ∑ i : Fin d, eLpNorm (fun x => u.grad x i) r.exponent M with hS
  have hSfin : ∀ i : Fin d, eLpNorm (fun x => u.grad x i) r.exponent M ≠ ⊤ :=
    fun i => (u.gradMemLp i).eLpNorm_ne_top
  have hSne : S ≠ ⊤ := ENNReal.sum_ne_top.2 fun i _ => hSfin i
  have hufin : eLpNorm u.toFun r.exponent M ≠ ⊤ := u.memLp.eLpNorm_ne_top
  have hpo := hCp z L hL u hmean
  have hsum : u.gradientCoordLpSeminormSum = S.toReal := by
    unfold W1pFunction.gradientCoordLpSeminormSum W1pFunction.gradCoordLpSeminorm
    rw [hS, ENNReal.toReal_sum (fun i _ => hSfin i)]
  have hPo : eLpNorm u.toFun r.exponent M ≤ ENNReal.ofReal (Cp * L) * S := by
    have hpo' : (eLpNorm u.toFun r.exponent M).toReal ≤ Cp * L * S.toReal := by
      have := hpo
      rw [hsum] at this
      exact this
    calc eLpNorm u.toFun r.exponent M
        = ENNReal.ofReal ((eLpNorm u.toFun r.exponent M).toReal) :=
          (ENNReal.ofReal_toReal hufin).symm
      _ ≤ ENNReal.ofReal (Cp * L * S.toReal) := ENNReal.ofReal_le_ofReal hpo'
      _ = ENNReal.ofReal (Cp * L) * S := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hSne]
  have he : ENNReal.ofReal L⁻¹ * ENNReal.ofReal (Cp * L) = ENNReal.ofReal Cp := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  calc eLpNorm u.toFun q.exponent M
      ≤ (Cs : ℝ≥0∞) * (S + ENNReal.ofReal L⁻¹ * eLpNorm u.toFun r.exponent M) := h1
    _ ≤ (Cs : ℝ≥0∞) * (S + ENNReal.ofReal L⁻¹ * (ENNReal.ofReal (Cp * L) * S)) := by gcongr
    _ = ENNReal.ofReal ((Cs : ℝ) * (1 + Cp)) * S := by
        rw [← mul_assoc, he, ENNReal.ofReal_mul (p := (Cs : ℝ)) (by positivity),
          ENNReal.ofReal_add (by norm_num) hCp0, ENNReal.ofReal_one,
          ENNReal.ofReal_coe_nnreal]
        ring


theorem memLp_sobolev_step (hd : 0 < d) (p q : FiniteLpExponent)
    (hp : p.exponent.toReal < d)
    (hq : (q.exponent.toReal)⁻¹ = p.exponent.toReal⁻¹ - (d : ℝ)⁻¹)
    (z : Vec d) (L : ℝ) (hL : 0 < L) (f : Vec d → ℝ) (g : Vec d → Vec d)
    (hw : HasWeakGradientOn (axisCube z L) f g)
    (hf : MemLp f p.exponent (volume.restrict (axisCube z L)))
    (hg : ∀ i, MemLp (fun x => g x i) p.exponent (volume.restrict (axisCube z L))) :
    MemLp f q.exponent (volume.restrict (axisCube z L)) := by
  let u : W1pFunction (axisCube z L) p.exponent := ⟨f, g, hf, hg, hw⟩
  obtain ⟨C, _, hC⟩ := Homogenization.cubeSobolevEmbedding_finiteLp hd p hp
  have h := hC q hq z L hL u
  refine lt_of_le_of_lt h ?_
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
  · exact (ENNReal.sum_lt_top.2 fun i _ => (hg i).eLpNorm_lt_top)
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.eLpNorm_lt_top


/-- The finite exponent with value `t > 1`. -/
noncomputable def mkExp (t : ℝ) (ht : 1 < t) : FiniteLpExponent :=
  ⟨ENNReal.ofReal t, by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith only [ht])).2 ht,
    ENNReal.ofReal_lt_top⟩

theorem mkExp_exponent (t : ℝ) (ht : 1 < t) : (mkExp t ht).exponent = ENNReal.ofReal t := rfl

theorem mkExp_toReal (t : ℝ) (ht : 1 < t) : (mkExp t ht).exponent.toReal = t :=
  ENNReal.toReal_ofReal (by linarith only [ht])

theorem exponent_eq_ofReal (r : FiniteLpExponent) :
    r.exponent = ENNReal.ofReal r.exponent.toReal :=
  (ENNReal.ofReal_toReal r.lt_top.ne).symm

theorem one_lt_toReal (r : FiniteLpExponent) : 1 < r.exponent.toReal := by
  have hq' : (1 : ℝ≥0∞).toReal < r.exponent.toReal :=
    (ENNReal.toReal_lt_toReal (by norm_num) r.lt_top.ne).2 r.one_lt
  simpa using hq'

theorem memLp_ladder_step (hd : 0 < d) (r : FiniteLpExponent)
    (hr : r.exponent.toReal < d) (z : Vec d) (L : ℝ) (hL : 0 < L) (f : Vec d → ℝ)
    (g : Vec d → Vec d) (hw : HasWeakGradientOn (axisCube z L) f g)
    (hg : ∀ i, MemLp (fun x => g x i) r.exponent (volume.restrict (axisCube z L)))
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hf : MemLp f (ENNReal.ofReal b⁻¹) (volume.restrict (axisCube z L))) :
    MemLp f (ENNReal.ofReal (max (r.exponent.toReal⁻¹ - (d : ℝ)⁻¹) (b - (d : ℝ)⁻¹))⁻¹)
      (volume.restrict (axisCube z L)) := by
  have hr1 := one_lt_toReal r
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set rr := r.exponent.toReal with hrr
  have hrinv : rr⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr1
  have hrpos : 0 < rr := by linarith only [hr1]
  have hdr : (d : ℝ)⁻¹ < rr⁻¹ := inv_strictAnti₀ hrpos hr
  have hbinv : 1 < b⁻¹ := (one_lt_inv₀ hb0).2 hb1
  have hrexp : r.exponent = ENNReal.ofReal rr := exponent_eq_ofReal r
  rcases le_or_gt rr⁻¹ b with hcase | hcase
  · -- the exponent `b⁻¹ ≤ r`
    have hbr : b⁻¹ ≤ rr := by
      rw [inv_le_comm₀ hb0 hrpos]; exact hcase
    have hbd : b⁻¹ < d := lt_of_le_of_lt hbr hr
    let p := mkExp b⁻¹ hbinv
    have hq1 : 0 < b - (d : ℝ)⁻¹ := by linarith only [hcase, hdr]
    have hq2 : 1 < (b - (d : ℝ)⁻¹)⁻¹ := (one_lt_inv₀ hq1).2 (by
      have : 0 < (d : ℝ)⁻¹ := inv_pos.2 hdpos
      linarith only [hb1, this])
    let q := mkExp (b - (d : ℝ)⁻¹)⁻¹ hq2
    have hpg : ∀ i, MemLp (fun x => g x i) p.exponent (volume.restrict (axisCube z L)) := by
      intro i
      refine (hg i).mono_exponent ?_
      rw [mkExp_exponent, hrexp]
      exact ENNReal.ofReal_le_ofReal hbr
    have hmax : max (rr⁻¹ - (d : ℝ)⁻¹) (b - (d : ℝ)⁻¹) = b - (d : ℝ)⁻¹ :=
      max_eq_right (by linarith only [hcase])
    rw [hmax]
    exact memLp_sobolev_step hd p q (by rw [mkExp_toReal]; exact hbd)
      (by rw [mkExp_toReal, mkExp_toReal, inv_inv, inv_inv]) z L hL f g hw hf hpg
  · have hrb : rr ≤ b⁻¹ := by
      rw [le_inv_comm₀ hrpos hb0]; exact hcase.le
    have hq1 : 0 < rr⁻¹ - (d : ℝ)⁻¹ := by linarith only [hdr]
    have hq2 : 1 < (rr⁻¹ - (d : ℝ)⁻¹)⁻¹ := (one_lt_inv₀ hq1).2 (by
      have : 0 < (d : ℝ)⁻¹ := inv_pos.2 hdpos
      linarith only [hrinv, this])
    let q := mkExp (rr⁻¹ - (d : ℝ)⁻¹)⁻¹ hq2
    have hfr : MemLp f r.exponent (volume.restrict (axisCube z L)) := by
      refine hf.mono_exponent ?_
      rw [hrexp]
      exact ENNReal.ofReal_le_ofReal hrb
    have hmax : max (rr⁻¹ - (d : ℝ)⁻¹) (b - (d : ℝ)⁻¹) = rr⁻¹ - (d : ℝ)⁻¹ :=
      max_eq_left (by linarith only [hcase])
    rw [hmax]
    exact memLp_sobolev_step hd r q hr
      (by rw [mkExp_toReal, inv_inv]) z L hL f g hw hfr hg


theorem max_ladder_eq (a x y : ℝ) (hy : 0 < y) :
    max a (max a x - y) = max a (x - y) := by
  rcases le_total a x with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h]
    have h1 : x - y ≤ a := by linarith only [h, hy]
    rw [max_eq_left h1]
    exact max_eq_left (by linarith only [hy])

theorem memLp_ladder (hd : 0 < d) (r : FiniteLpExponent)
    (hr : r.exponent.toReal < d) (z : Vec d) (L : ℝ) (hL : 0 < L) (f : Vec d → ℝ)
    (g : Vec d → Vec d) (hw : HasWeakGradientOn (axisCube z L) f g)
    (hg : ∀ i, MemLp (fun x => g x i) r.exponent (volume.restrict (axisCube z L)))
    (hf2 : MemLp f 2 (volume.restrict (axisCube z L))) :
    MemLp f (ENNReal.ofReal (r.exponent.toReal⁻¹ - (d : ℝ)⁻¹)⁻¹)
      (volume.restrict (axisCube z L)) := by
  have hr1 := one_lt_toReal r
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set rr := r.exponent.toReal with hrr
  have hrinv : rr⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr1
  have hrpos : 0 < rr := by linarith only [hr1]
  have hdr : (d : ℝ)⁻¹ < rr⁻¹ := inv_strictAnti₀ hrpos hr
  have hdinv : 0 < (d : ℝ)⁻¹ := inv_pos.2 hdpos
  set a := rr⁻¹ - (d : ℝ)⁻¹ with ha
  have ha0 : 0 < a := by linarith only [hdr]
  have ha1 : a < 1 := by linarith only [hrinv, hdinv]
  have key : ∀ k : ℕ, MemLp f (ENNReal.ofReal (max a (1 / 2 - (k : ℝ) * (d : ℝ)⁻¹))⁻¹)
      (volume.restrict (axisCube z L)) := by
    intro k
    induction k with
    | zero =>
      refine hf2.mono_exponent ?_
      have h12 : (1 / 2 : ℝ) ≤ max a (1 / 2 - ((0 : ℕ) : ℝ) * (d : ℝ)⁻¹) := by
        simp
      have hpos : 0 < (1 / 2 : ℝ) := by norm_num
      have : (max a (1 / 2 - ((0 : ℕ) : ℝ) * (d : ℝ)⁻¹))⁻¹ ≤ 2 := by
        have := inv_anti₀ hpos h12
        simpa using this
      calc ENNReal.ofReal (max a (1 / 2 - ((0 : ℕ) : ℝ) * (d : ℝ)⁻¹))⁻¹
          ≤ ENNReal.ofReal 2 := ENNReal.ofReal_le_ofReal this
        _ = 2 := by simp
    | succ k ih =>
      set b := max a (1 / 2 - (k : ℝ) * (d : ℝ)⁻¹) with hb
      have hb0 : 0 < b := lt_of_lt_of_le ha0 (le_max_left _ _)
      have hb1 : b < 1 := max_lt ha1 (by
        have : 0 ≤ (k : ℝ) * (d : ℝ)⁻¹ := by positivity
        linarith only [this])
      have hstep := memLp_ladder_step hd r hr z L hL f g hw hg hb0 hb1 ih
      have heq : max a (b - (d : ℝ)⁻¹) = max a (1 / 2 - ((k + 1 : ℕ) : ℝ) * (d : ℝ)⁻¹) := by
        rw [hb, max_ladder_eq a _ _ hdinv]
        have h1 : 1 / 2 - (k : ℝ) * (d : ℝ)⁻¹ - (d : ℝ)⁻¹ =
            1 / 2 - ((k + 1 : ℕ) : ℝ) * (d : ℝ)⁻¹ := by
          push_cast
          ring
        rw [h1]
      rw [← heq]
      exact hstep
  have hk := key d
  have hlast : max a (1 / 2 - (d : ℝ) * (d : ℝ)⁻¹) = a := by
    rw [mul_inv_cancel₀ hdpos.ne']
    exact max_eq_left (by linarith only [ha0])
  rwa [hlast] at hk


/-- On an axis cube, a mean-zero `L²` function whose weak gradient lies in `L^r` lies in
`L^{r^*}`, with an absolute (scale-free) bound by the `L^r` norms of the gradient. -/
theorem axisCube_lpStar_of_gradLp (hd : 0 < d) (r : FiniteLpExponent)
    (hr : r.exponent.toReal < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : FiniteLpExponent,
      (q.exponent.toReal)⁻¹ = r.exponent.toReal⁻¹ - (d : ℝ)⁻¹ →
      ∀ (z : Vec d) (L : ℝ), 0 < L → ∀ (f : Vec d → ℝ) (g : Vec d → Vec d),
        HasWeakGradientOn (axisCube z L) f g →
        (∀ i, MemLp (fun x => g x i) r.exponent (volume.restrict (axisCube z L))) →
        MemLp f 2 (volume.restrict (axisCube z L)) →
        ∫ x in axisCube z L, f x = 0 →
        MemLp f q.exponent (volume.restrict (axisCube z L)) ∧
          eLpNorm f q.exponent (volume.restrict (axisCube z L)) ≤
            ENNReal.ofReal C * ∑ i : Fin d,
              eLpNorm (fun x => g x i) r.exponent (volume.restrict (axisCube z L)) := by
  obtain ⟨C, hC0, hC⟩ := w1p_meanZero_sobolev hd r hr
  refine ⟨C, hC0, ?_⟩
  intro q hq z L hL f g hw hg hf2 hmean
  have hr1 := one_lt_toReal r
  have hq1 := one_lt_toReal q
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hladder := memLp_ladder hd r hr z L hL f g hw hg hf2
  have hqexp : q.exponent = ENNReal.ofReal (r.exponent.toReal⁻¹ - (d : ℝ)⁻¹)⁻¹ := by
    rw [← hq, inv_inv]
    exact exponent_eq_ofReal q
  have hfq : MemLp f q.exponent (volume.restrict (axisCube z L)) := by
    rw [hqexp]; exact hladder
  have hrq : r.exponent ≤ q.exponent := by
    refine (ENNReal.toReal_le_toReal r.lt_top.ne q.lt_top.ne).1 ?_
    have hrpos : 0 < r.exponent.toReal := by linarith only [hr1]
    have hqpos : 0 < q.exponent.toReal := by linarith only [hq1]
    have hlt : (q.exponent.toReal)⁻¹ ≤ r.exponent.toReal⁻¹ := by
      rw [hq]
      have : 0 < (d : ℝ)⁻¹ := inv_pos.2 hdpos
      linarith only [this]
    exact (inv_le_inv₀ hqpos hrpos).1 hlt
  have hfr : MemLp f r.exponent (volume.restrict (axisCube z L)) := hfq.mono_exponent hrq
  let u : W1pFunction (axisCube z L) r.exponent := ⟨f, g, hfr, hg, hw⟩
  exact ⟨hfq, hC q hq z L hL u hmean⟩


/-! ## Normalized cube norms -/

theorem eLpNorm_ofReal_smul {c : ℝ} (hc : 0 < c) (f : Vec d → ℝ) (p : ℝ≥0∞)
    (μ : Measure (Vec d)) :
    eLpNorm f p (ENNReal.ofReal c • μ) = ENNReal.ofReal (c ^ p.toReal⁻¹) * eLpNorm f p μ := by
  rw [eLpNorm_smul_measure_of_ne_zero (by simpa using hc)]
  simp [smul_eq_mul, one_div, ENNReal.toReal_inv, ENNReal.ofReal_rpow_of_pos hc]

theorem cubeScalar_normalizedCubeMeasure_eq_smul (Q : TriadicCube d) :
    normalizedCubeMeasure Q =
      ENNReal.ofReal ((Homogenization.cubeVolume Q)⁻¹) • volume.restrict (openCubeSet Q) := by
  rw [normalizedCubeMeasure, cubeMeasure, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

theorem cubeVolume_pos' (Q : TriadicCube d) : 0 < Homogenization.cubeVolume Q := by
  unfold Homogenization.cubeVolume cubeScaleFactor
  positivity

theorem cubeScaleFactor_pos' (Q : TriadicCube d) : 0 < cubeScaleFactor Q := by
  unfold cubeScaleFactor
  positivity

theorem eLpNorm_normalized (Q : TriadicCube d) (f : Vec d → ℝ) (p : ℝ≥0∞) :
    eLpNorm f p (normalizedCubeMeasure Q) =
      ENNReal.ofReal ((Homogenization.cubeVolume Q)⁻¹ ^ p.toReal⁻¹) *
        eLpNorm f p (volume.restrict (openCubeSet Q)) := by
  rw [cubeScalar_normalizedCubeMeasure_eq_smul]
  exact eLpNorm_ofReal_smul (inv_pos.2 (cubeVolume_pos' Q)) f p _

theorem eLpNorm_restrict_eq (Q : TriadicCube d) (f : Vec d → ℝ) (p : ℝ≥0∞) :
    eLpNorm f p (volume.restrict (openCubeSet Q)) =
      ENNReal.ofReal ((Homogenization.cubeVolume Q) ^ p.toReal⁻¹) *
        eLpNorm f p (normalizedCubeMeasure Q) := by
  have hV := cubeVolume_pos' Q
  have h : volume.restrict (openCubeSet Q) =
      ENNReal.ofReal (Homogenization.cubeVolume Q) • normalizedCubeMeasure Q := by
    rw [cubeScalar_normalizedCubeMeasure_eq_smul, smul_smul, ← ENNReal.ofReal_mul hV.le,
      mul_inv_cancel₀ hV.ne', ENNReal.ofReal_one, one_smul]
  rw [h]
  exact eLpNorm_ofReal_smul hV f p _

theorem memLp_restrict_of_normalized (Q : TriadicCube d) {f : Vec d → ℝ} {p : ℝ≥0∞}
    (h : MemLp f p (normalizedCubeMeasure Q)) :
    MemLp f p (volume.restrict (openCubeSet Q)) := by
  unfold MemLp at *
  rw [eLpNorm_restrict_eq]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h

theorem memLp_normalized_of_restrict (Q : TriadicCube d) {f : Vec d → ℝ} {p : ℝ≥0∞}
    (h : MemLp f p (volume.restrict (openCubeSet Q))) :
    MemLp f p (normalizedCubeMeasure Q) := by
  unfold MemLp at *
  rw [eLpNorm_normalized]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h


theorem scale_identity (hd : 0 < d) (L a b : ℝ) (hL : 0 < L)
    (hab : b = a - (d : ℝ)⁻¹) :
    ((L ^ d)⁻¹ ^ b) * (L ^ d) ^ a = L := by
  have hV : 0 < L ^ d := by positivity
  rw [Real.inv_rpow hV.le, ← div_eq_inv_mul, ← Real.rpow_sub hV, hab]
  have : a - (a - (d : ℝ)⁻¹) = (d : ℝ)⁻¹ := by ring
  rw [this]
  exact Real.pow_rpow_inv_natCast hL.le hd.ne'

/-- Assembly on any triadic cube: a zero-trace `H¹` function whose gradient has a weak Hessian
in `L̲^r` has gradient in `L̲^{r^*}`, with the scale factor `3^m` of the cube. -/
theorem gradLp_of_weakHessian (hd : 0 < d) (r : FiniteLpExponent)
    (hr : r.exponent.toReal < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : FiniteLpExponent,
      (q.exponent.toReal)⁻¹ = r.exponent.toReal⁻¹ - (d : ℝ)⁻¹ →
      ∀ (Q : TriadicCube d) (u : H10Function (openCubeSet Q))
        (H : HasWeakHessianOn (openCubeSet Q) u.toH1Function),
        (∀ i j, MemLp (H.hess i j) r.exponent (normalizedCubeMeasure Q)) →
        ∀ i : Fin d,
          MemLp (fun x => u.toH1Function.grad x i) q.exponent (normalizedCubeMeasure Q) ∧
            Section2.Norms.cubeLpENorm Q q.exponent (fun x => u.toH1Function.grad x i) ≤
              ENNReal.ofReal (C * cubeScaleFactor Q) *
                ∑ j : Fin d, Section2.Norms.cubeLpENorm Q r.exponent (H.hess i j) := by
  obtain ⟨C0, hC0, hC⟩ := axisCube_lpStar_of_gradLp hd r hr
  refine ⟨C0, hC0, ?_⟩
  intro q hq Q u H hH i
  have hL := cubeScaleFactor_pos' Q
  have hU := CubeCalderonZygmund.openCubeSet_eq_axisCube_triadicCube Q
  set L := cubeScaleFactor Q with hLdef
  set z := CubeCalderonZygmund.triadicCubeAxisCorner Q with hz
  have hw : HasWeakGradientOn (axisCube z L) (fun x => u.toH1Function.grad x i)
      (fun x j => H.hess i j x) := by
    rw [← hU]; exact fun j => H.weak_second i j
  have hg : ∀ j, MemLp (fun x => H.hess i j x) r.exponent (volume.restrict (axisCube z L)) := by
    intro j; rw [← hU]; exact memLp_restrict_of_normalized Q (hH i j)
  have hf2 : MemLp (fun x => u.toH1Function.grad x i) 2 (volume.restrict (axisCube z L)) := by
    rw [← hU]; exact u.toH1Function.gradMemL2 i
  have hfin : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) := by
    rw [hU]; infer_instance
  have hmean : ∫ x in axisCube z L, u.toH1Function.grad x i = 0 := by
    rw [← hU]
    have h := H1Function.integral_mul_zeroTrace_gradCoord_eq_neg_integral_gradCoord_mul
      (H1Function.const (U := openCubeSet Q) 1) u i
    simpa using h
  obtain ⟨hmem, hbd⟩ := hC q hq z L hL _ _ hw hg hf2 hmean
  rw [← hU] at hmem hbd
  refine ⟨memLp_normalized_of_restrict Q hmem, ?_⟩
  unfold Section2.Norms.cubeLpENorm
  rw [eLpNorm_normalized]
  have hV : Homogenization.cubeVolume Q = L ^ d := rfl
  have hsum : ∑ j : Fin d, eLpNorm (fun x => H.hess i j x) r.exponent
      (volume.restrict (openCubeSet Q)) =
      ENNReal.ofReal ((L ^ d) ^ r.exponent.toReal⁻¹) *
        ∑ j : Fin d, eLpNorm (H.hess i j) r.exponent (normalizedCubeMeasure Q) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eLpNorm_restrict_eq, hV]
  calc ENNReal.ofReal ((Homogenization.cubeVolume Q)⁻¹ ^ q.exponent.toReal⁻¹) *
        eLpNorm (fun x => u.toH1Function.grad x i) q.exponent (volume.restrict (openCubeSet Q))
      ≤ ENNReal.ofReal ((Homogenization.cubeVolume Q)⁻¹ ^ q.exponent.toReal⁻¹) *
        (ENNReal.ofReal C0 * ∑ j : Fin d, eLpNorm (fun x => H.hess i j x) r.exponent
          (volume.restrict (openCubeSet Q))) := by gcongr
    _ = ENNReal.ofReal (C0 * L) *
          ∑ j : Fin d, eLpNorm (H.hess i j) r.exponent (normalizedCubeMeasure Q) := by
        rw [hsum, hV, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        have := scale_identity hd L r.exponent.toReal⁻¹ q.exponent.toReal⁻¹ hL (by rw [hq])
        linear_combination C0 * this


theorem abs_hess_le_norm (A : Vec d → HilbertMat d) (i j : Fin d) (x : Vec d) :
    |HilbertMat.toMat (A x) i j| ≤ ‖A x‖ := by
  have h := HilbertMat.abs_apply_sub_apply_le_norm (A x) (0 : HilbertMat d) i j
  simpa using h

/-- **Scalar data on origin cubes.** If `u ∈ H¹₀` of a centred triadic cube solves `-Δu = s` with
`s ∈ L̲² ∩ L̲^r`, `r < d`, then each coordinate of `∇u` lies in `L̲^{r^*}` with
`‖∂ᵢu‖_{L̲^{r^*}} ≤ C 3^m ‖s‖_{L̲^r}`. -/
theorem exists_cubeScalarData_gradLp_sobolev (hd : 2 ≤ d) (r q : FiniteLpExponent)
    (hr : r.exponent.toReal < d)
    (hq : (q.exponent.toReal)⁻¹ = r.exponent.toReal⁻¹ - (d : ℝ)⁻¹) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (m : ℤ) (s : Vec d → ℝ),
      MemLp s 2 (normalizedCubeMeasure (originCube d m)) →
      MemLp s r.exponent (normalizedCubeMeasure (originCube d m)) →
      ∀ u : H10Function (openCubeSet (originCube d m)),
        CubeDirichletWeakPoissonProblem (originCube d m) u s →
        ∀ i : Fin d,
          MemLp (fun x => u.toH1Function.grad x i) q.exponent
              (normalizedCubeMeasure (originCube d m)) ∧
            Section2.Norms.cubeLpENorm (originCube d m) q.exponent
                (fun x => u.toH1Function.grad x i) ≤
              C * ENNReal.ofReal (cubeScaleFactor (originCube d m)) *
                Section2.Norms.cubeLpENorm (originCube d m) r.exponent s := by
  have hd0 : 0 < d := by omega
  let _ : NeZero d := ⟨by omega⟩
  obtain ⟨C0, hC0, hC⟩ := gradLp_of_weakHessian hd0 r hr
  obtain ⟨Ccz, hCcz, hCz⟩ :=
    CubeCalderonZygmund.exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le d r
  refine ⟨ENNReal.ofReal C0 * (d : ℝ≥0∞) * Ccz,
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.natCast_lt_top d)) hCcz,
    ?_⟩
  intro m s hs2 hsr u hu i
  obtain ⟨H, hHmem, hHb⟩ := hCz m s hs2 hsr u hu
  have hent : ∀ i j, eLpNorm (H.hess i j) r.exponent (normalizedCubeMeasure (originCube d m)) ≤
      eLpNorm (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) r.exponent
        (normalizedCubeMeasure (originCube d m)) := by
    intro i j
    have hmeas : AEStronglyMeasurable (H.hess i j) (normalizedCubeMeasure (originCube d m)) := by
      rw [cubeScalar_normalizedCubeMeasure_eq_smul]
      exact (H.hess_memL2 i j).aestronglyMeasurable.smul_measure _
    refine eLpNorm_mono hmeas fun x => ?_
    have h := abs_hess_le_norm (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) i j x
    simpa [Real.norm_eq_abs] using h
  have hmem : ∀ i j, MemLp (H.hess i j) r.exponent
      (normalizedCubeMeasure (originCube d m)) := fun i j =>
    lt_of_le_of_lt (hent i j) hHmem
  obtain ⟨hm, hb⟩ := hC q hq (originCube d m) u H hmem i
  refine ⟨hm, hb.trans ?_⟩
  have hsum : ∑ j : Fin d, Section2.Norms.cubeLpENorm (originCube d m) r.exponent (H.hess i j) ≤
      (d : ℝ≥0∞) * (Ccz * Section2.Norms.cubeLpENorm (originCube d m) r.exponent s) := by
    calc _ ≤ ∑ _j : Fin d, (Ccz * Section2.Norms.cubeLpENorm (originCube d m) r.exponent s) :=
          Finset.sum_le_sum fun j _ => (hent i j).trans hHb
      _ = _ := by simp
  have hLeq : ENNReal.ofReal (C0 * cubeScaleFactor (originCube d m)) =
      ENNReal.ofReal C0 * ENNReal.ofReal (cubeScaleFactor (originCube d m)) :=
    ENNReal.ofReal_mul hC0
  calc ENNReal.ofReal (C0 * cubeScaleFactor (originCube d m)) *
        ∑ j : Fin d, Section2.Norms.cubeLpENorm (originCube d m) r.exponent (H.hess i j)
      ≤ ENNReal.ofReal (C0 * cubeScaleFactor (originCube d m)) *
        ((d : ℝ≥0∞) * (Ccz * Section2.Norms.cubeLpENorm (originCube d m) r.exponent s)) := by
        gcongr
    _ = _ := by rw [hLeq]; ring


/-- Satisfiability: in dimension `3`, `r = 3/2`, `q = 3 = r^*`, the hypotheses of
`exists_cubeScalarData_gradLp_sobolev` are met by `s = 0`, `u = 0`, on every origin cube. -/
example : ∃ (r q : FiniteLpExponent), r.exponent.toReal < (3 : ℕ) ∧
    (q.exponent.toReal)⁻¹ = r.exponent.toReal⁻¹ - ((3 : ℕ) : ℝ)⁻¹ ∧
    ∀ m : ℤ, ∃ u : H10Function (openCubeSet (originCube 3 m)),
      CubeDirichletWeakPoissonProblem (originCube 3 m) u (fun _ => 0) ∧
      MemLp (fun _ : Vec 3 => (0 : ℝ)) 2 (normalizedCubeMeasure (originCube 3 m)) ∧
      MemLp (fun _ : Vec 3 => (0 : ℝ)) r.exponent (normalizedCubeMeasure (originCube 3 m)) := by
  refine ⟨mkExp (3 / 2) (by norm_num), mkExp 3 (by norm_num), ?_, ?_, ?_⟩
  · rw [mkExp_toReal]; norm_num
  · rw [mkExp_toReal, mkExp_toReal]; norm_num
  · intro m
    refine ⟨0, ?_, by simp, by simp⟩
    intro φ
    have h0 : ∀ x, (H10Function.toH1Function (0 : H10Function (openCubeSet (originCube 3 m)))).grad x
        = 0 := fun _ => rfl
    simp [vecDot, h0]

end SuperdiffusionCLT.Section7

