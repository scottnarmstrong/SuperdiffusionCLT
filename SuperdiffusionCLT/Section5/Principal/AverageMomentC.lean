/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Principal.AverageMomentB
public import SuperdiffusionCLT.Section5.Response.GradientL8

/-!
# The pointwise bound behind `e.principal.uz`

For one sample `ω` and fields `∇w_D, ∇w_N` in `L²(cu_K)`, the average over the subcubes `z + cu_n` of
`|e_{D,z}|⁸ + |e_{N,z}|⁸ + |shom⁻¹ hbar_z|⁸` is at most `C(d)` times
`1 + ‖∇w_D‖⁸_{L̲⁸} + ‖∇w_N‖⁸_{L̲⁸} + shom⁻⁸ ‖k_m - k_{m-h}‖⁸_{L̲⁸}` on `cu_K`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization Homogenization.Book.Ch02 MeasureTheory
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open scoped ENNReal

variable {d : ℕ}

theorem ennreal_add_pow_eight_le (x y : ℝ≥0∞) : (x + y) ^ (8 : ℕ) ≤ 2 ^ 7 * (x ^ (8 : ℕ) + y ^ (8 : ℕ)) := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow x y (p := 8) (by norm_num)
  have e1 : ∀ z : ℝ≥0∞, z ^ (8 : ℝ) = z ^ (8 : ℕ) := fun z => by
    rw [← ENNReal.rpow_natCast]; norm_num
  rw [e1, e1, e1] at h
  have e2 : (2 : ℝ≥0∞) ^ ((8 : ℝ) - 1) = 2 ^ 7 := by
    rw [show (8 : ℝ) - 1 = ((7 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  rwa [e2] at h

theorem vecNorm_add_le_pm (u v : Vec d) : vecNorm (u + v) ≤ vecNorm u + vecNorm v := by
  have h : HilbertVec.ofVec (u + v) = HilbertVec.ofVec u + HilbertVec.ofVec v :=
    map_add (HilbertVec.linearEquivVec d).symm u v
  rw [vecNorm_eq_norm_ofVec, vecNorm_eq_norm_ofVec, vecNorm_eq_norm_ofVec, h]
  exact norm_add_le _ _

theorem subcubeAvg_const_pm {Kc n : ℕ} (hn : n ≤ Kc) (c : ℝ≥0∞) :
    subcubeAvg (d := d) Kc n (fun _ => c) = c := by
  unfold subcubeAvg
  rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc]
  have h0 : ((descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ)).card : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast card_descendantsAtScale_ne_zero hn
  rw [ENNReal.inv_mul_cancel h0 (ENNReal.natCast_ne_top _), one_mul]

theorem memVectorL2_add_pm {U : Set (Vec d)} {f g : Vec d → Vec d} (hf : MemVectorL2 U f)
    (hg : MemVectorL2 U g) : MemVectorL2 U (fun x => f x + g x) := by
  unfold MemVectorL2 at *
  exact hf.add hg

/-- One sub-cube: `|e_D|⁸ + |e_N|⁸ + |s hbar|⁸` against the two Jensen quantities. -/
theorem ofReal_uz_summand_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    {AD AN C : ℝ≥0∞} (hAD : ENNReal.ofReal a ≤ 1 + AD) (hAN : ENNReal.ofReal b ≤ 1 + AN)
    (hC : ENNReal.ofReal c ≤ C) :
    ENNReal.ofReal (a ^ 8 + b ^ 8 + c ^ 8) ≤
      2 ^ 7 * (1 + AD ^ (8 : ℕ)) + 2 ^ 7 * (1 + AN ^ (8 : ℕ)) + C ^ (8 : ℕ) := by
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_pow ha,
    ENNReal.ofReal_pow hb, ENNReal.ofReal_pow hc]
  refine add_le_add (add_le_add ?_ ?_) (pow_le_pow_left' hC 8)
  · refine (pow_le_pow_left' hAD 8).trans ?_
    simpa using ennreal_add_pow_eight_le 1 AD
  · refine (pow_le_pow_left' hAN 8).trans ?_
    simpa using ennreal_add_pow_eight_le 1 AN

theorem continuous_finiteShellIncrement_pm (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)
    (l L : ℕ) :
    Continuous (fun x : Vec d =>
      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L x) := by
  have hfun : (fun x : Vec d =>
      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega l L x) =
      fun x => ∑ k ∈ Finset.Ioc l L, (omega k) x := by
    funext x
    rw [SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement_apply]
    rfl
  rw [hfun]
  exact continuous_finsetSum _ fun k _ => (omega k).1.1.continuous

theorem principalGauge_eq_volumeAverageMat_incr (m h : ℕ) (R : TriadicCube d)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) :
    principalGauge m h R omega = volumeAverageMat (cubeSet R) (fun y =>
      SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega (m - h) m y) := by
  rw [principalGauge_eq_average]
  congr 1
  funext y
  exact (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement_apply_eq_streamCutoff_sub
    omega (Nat.sub_le m h) y).symm

theorem hshellFlux_eq_smul_incr [NeZero d] (nu : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (m h : ℕ) (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) (e : Vec d) :
    hshellFlux nu P m h omega e = fun x =>
      (sigmaBarInfinite nu (m - h) P)⁻¹ •
        matVecMul (SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega (m - h) m x) e := by
  funext x
  rw [hshellFlux, SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement_apply_eq_streamCutoff_sub
    omega (Nat.sub_le m h) x]

section MatNorm

open scoped Matrix.Norms.L2Operator

theorem matrixOperatorNorm_smul_pm (c : ℝ) (A : Mat d) :
    matrixOperatorNorm (c • A) = |c| * matrixOperatorNorm A := by
  have h := norm_smul c A
  rw [Real.norm_eq_abs] at h
  exact h

theorem cubeLpENorm_pow_eight_eq {Q : TriadicCube d} {f : Vec d → Mat d} (hf : Continuous f) :
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8 f ^ (8 : ℕ) =
      ∫⁻ x, ENNReal.ofReal (matrixOperatorNorm (f x)) ^ (8 : ℕ) ∂normalizedCubeMeasure Q := by
  have hm : AEStronglyMeasurable f (normalizedCubeMeasure Q) := hf.aestronglyMeasurable
  have h1 : SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8 f =
      avgRootENorm Q 8 f := by
    have := avgRootENorm_eq_cubeLpENorm Q (p := 8) (by norm_num) hm
    rw [show ENNReal.ofReal 8 = 8 by norm_num] at this
    exact this.symm
  rw [h1]
  have h2 := avgPowENorm_eq_rootENorm_rpow Q (p := 8) (by norm_num) f
  have h3 : avgRootENorm Q 8 f ^ (8 : ℕ) = avgRootENorm Q 8 f ^ (8 : ℝ) := by
    rw [← ENNReal.rpow_natCast]; norm_num
  rw [h3, ← h2]
  unfold avgPowENorm
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.rpow_natCast, Nat.cast_ofNat,
    SuperdiffusionCLT.Section2.Norms.enorm_matrixOperatorNorm f x]

theorem subcubeAvg_cubeLpENorm_pow_eight_le {Kc n : ℕ} (hn : n ≤ Kc) {f : Vec d → Mat d}
    (hf : Continuous f) :
    subcubeAvg Kc n (fun Q => SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8 f ^ (8 : ℕ)) ≤
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 8 f ^ (8 : ℕ) := by
  have h : subcubeAvg Kc n (fun Q =>
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8 f ^ (8 : ℕ)) =
      subcubeAvg Kc n (fun Q => ∫⁻ x, ENNReal.ofReal (matrixOperatorNorm (f x)) ^ (8 : ℕ)
        ∂normalizedCubeMeasure Q) := by
    unfold subcubeAvg
    congr 1
    exact Finset.sum_congr rfl fun Q _ => cubeLpENorm_pow_eight_eq hf
  rw [h, subcubeAvg_lintegral_normalizedCubeMeasure hn
    (fun x => ENNReal.ofReal (matrixOperatorNorm (f x)) ^ (8 : ℕ)), cubeLpENorm_pow_eight_eq hf]

end MatNorm

section MatNorm2

open scoped Matrix.Norms.L2Operator

/-- **`e.principal.uz`, pointwise in the sample.** With `e_{D,z} = e' + (∇w_D)_{z+cu_n}`,
`e_{N,z} = e + (∇w_N + shom⁻¹ hshell e')_{z+cu_n}`, `principalGauge` the cube average of
`k_m - k_{m-h}`,
`|e|, |e'| ≤ 1`: the average over `z + cu_n ⊆ cu_K` of `|e_D|⁸ + |e_N|⁸ + |shom⁻¹ hbar_z|⁸` is at most
`(2¹⁵ + d¹⁶)(1 + ‖∇w_D‖⁸ + ‖∇w_N‖⁸ + shom⁻⁸ ‖k_m - k_{m-h}‖⁸)` with `L̲⁸(cu_K)` norms. -/
theorem principal_uz_pointwise [NeZero d] {nu : ℝ}
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d))
    (m h : ℕ) {Kc n : ℕ} (hn : n ≤ Kc) (hσ : 0 < sigmaBarInfinite nu (m - h) P)
    (omega : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d) {e e' : Vec d}
    (he : vecNorm e ≤ 1) (he' : vecNorm e' ≤ 1) {gD gN0 : Vec d → Vec d}
    (hgD : MemVectorL2 (openCubeSet (originCube d (Kc : ℤ))) gD)
    (hgN0 : MemVectorL2 (openCubeSet (originCube d (Kc : ℤ))) gN0) :
    subcubeAvg Kc n (fun Q => ENNReal.ofReal
        (vecNorm (principalED Q e' gD) ^ 8 +
          vecNorm (principalEN Q e (fun y => gN0 y + hshellFlux nu P m h omega e' y)) ^ 8 +
          matrixOperatorNorm ((sigmaBarInfinite nu (m - h) P)⁻¹ • principalGauge m h Q omega) ^ 8)) ≤
      ((2 : ℝ≥0∞) ^ 15 + ((d : ℝ≥0∞) * d) ^ 8) *
        (1 + vecCubeLpENorm (originCube d (Kc : ℤ)) 8 gD ^ (8 : ℕ) +
          vecCubeLpENorm (originCube d (Kc : ℤ)) 8 gN0 ^ (8 : ℕ) +
          ENNReal.ofReal (sigmaBarInfinite nu (m - h) P)⁻¹ ^ (8 : ℕ) *
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 8
              (fun x => SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega (m - h) m x)
              ^ (8 : ℕ)) := by
  classical
  have hk : (n : ℤ) ≤ (originCube d (Kc : ℤ)).scale := by
    show (n : ℤ) ≤ (Kc : ℤ)
    exact_mod_cast hn
  set incr : Vec d → Mat d := fun x =>
    SuperdiffusionCLT.Section2.Cutoff.finiteShellIncrement omega (m - h) m x with hincr
  have hcont : Continuous incr := continuous_finiteShellIncrement_pm omega _ _
  set s : ℝ≥0∞ := ENNReal.ofReal (sigmaBarInfinite nu (m - h) P)⁻¹ with hs
  set gN : Vec d → Vec d := fun y => gN0 y + hshellFlux nu P m h omega e' y with hgNdef
  have hflux : Continuous (hshellFlux nu P m h omega e') := by
    rw [hshellFlux_eq_smul_incr]
    exact Continuous.const_smul (pm_continuous_matVecMul_field hcont e') (sigmaBarInfinite nu (m - h) P)⁻¹
  have hgN : MemVectorL2 (openCubeSet (originCube d (Kc : ℤ))) gN :=
    memVectorL2_add_pm hgN0
      (SuperdiffusionCLT.Section3.Setup.memVectorL2_of_continuous _ hflux)
  have he'sq : vecNormSq e' ≤ 1 := by
    rw [← vecNorm_sq_eq_vecNormSq]
    nlinarith only [he', vecNorm_nonneg e']
  have hLN : vecCubeLpENorm (originCube d (Kc : ℤ)) 8 gN ≤
      vecCubeLpENorm (originCube d (Kc : ℤ)) 8 gN0 +
        s * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 8 incr := by
    refine (vecCubeLpENorm_add_le (by norm_num)
      (SuperdiffusionCLT.Section3.Terms.aestronglyMeasurable_hilbertifyVecField_of_memVectorL2
        hgN0)
      (SuperdiffusionCLT.Section3.Terms.aestronglyMeasurable_hilbertifyVecField_of_memVectorL2
        (SuperdiffusionCLT.Section3.Setup.memVectorL2_of_continuous _ hflux))).trans ?_
    refine add_le_add le_rfl ?_
    have := vecCubeLpENorm_hshellFlux_le nu P m h omega he'sq (originCube d (Kc : ℤ)) 8
    rwa [Real.enorm_eq_ofReal (inv_nonneg.2 hσ.le)] at this
  -- the pointwise bound for each subcube
  have hcube : ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      ENNReal.ofReal
        (vecNorm (principalED Q e' gD) ^ 8 + vecNorm (principalEN Q e gN) ^ 8 +
          matrixOperatorNorm ((sigmaBarInfinite nu (m - h) P)⁻¹ • principalGauge m h Q omega) ^ 8) ≤
      (2 ^ 7 * (1 + ENNReal.ofReal (vecNorm (volumeAverageVec (cubeSet Q) gD)) ^ (8 : ℕ)) +
        2 ^ 7 * (1 + ENNReal.ofReal (vecNorm (volumeAverageVec (cubeSet Q) gN)) ^ (8 : ℕ))) +
        (s * (((d : ℝ≥0∞) * d) *
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8 incr)) ^ (8 : ℕ) := by
    intro Q hQ
    refine ofReal_uz_summand_le (vecNorm_nonneg _) (vecNorm_nonneg _)
      (by rw [matrixOperatorNorm_smul_pm]; exact mul_nonneg (abs_nonneg _) (matrixOperatorNorm_nonneg _))
      ?_ ?_ ?_
    · unfold principalED
      refine (ENNReal.ofReal_le_ofReal (vecNorm_add_le_pm _ _)).trans ?_
      refine ENNReal.ofReal_add_le.trans ?_
      refine add_le_add ?_ le_rfl
      calc ENNReal.ofReal (vecNorm e') ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal he'
        _ = 1 := ENNReal.ofReal_one
    · unfold principalEN
      refine (ENNReal.ofReal_le_ofReal (vecNorm_add_le_pm _ _)).trans ?_
      refine ENNReal.ofReal_add_le.trans ?_
      refine add_le_add ?_ le_rfl
      calc ENNReal.ofReal (vecNorm e) ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal he
        _ = 1 := ENNReal.ofReal_one
    · rw [matrixOperatorNorm_smul_pm, principalGauge_eq_volumeAverageMat_incr,
        abs_of_nonneg (inv_nonneg.2 hσ.le), ENNReal.ofReal_mul (inv_nonneg.2 hσ.le)]
      exact mul_le_mul' le_rfl (ofReal_matrixOperatorNorm_volumeAverageMat_le hn hQ hcont)
  set Kn : ℝ≥0∞ := SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 8 incr
    with hKn
  set Jd : ℝ≥0∞ := vecCubeLpENorm (originCube d (Kc : ℤ)) 8 gD with hJd
  set Jn : ℝ≥0∞ := vecCubeLpENorm (originCube d (Kc : ℤ)) 8 gN0 with hJn
  set D : ℝ≥0∞ := ((d : ℝ≥0∞) * d) ^ 8 with hD
  have hX1 : subcubeAvg Kc n (fun Q =>
      ENNReal.ofReal (vecNorm (volumeAverageVec (cubeSet Q) gD)) ^ (8 : ℕ)) ≤ Jd ^ (8 : ℕ) :=
    subcubeAvg_ofReal_vecNorm_volumeAverageVec_pow_eight_le hn hgD
  have hX2 : subcubeAvg Kc n (fun Q =>
      ENNReal.ofReal (vecNorm (volumeAverageVec (cubeSet Q) gN)) ^ (8 : ℕ)) ≤
        2 ^ 7 * (Jn ^ (8 : ℕ) + (s * Kn) ^ (8 : ℕ)) := by
    refine (subcubeAvg_ofReal_vecNorm_volumeAverageVec_pow_eight_le hn hgN).trans ?_
    exact (pow_le_pow_left' hLN 8).trans (ennreal_add_pow_eight_le _ _)
  have hX3 : subcubeAvg Kc n (fun Q =>
      SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8 incr ^ (8 : ℕ)) ≤ Kn ^ (8 : ℕ) :=
    subcubeAvg_cubeLpENorm_pow_eight_le hn hcont
  have hmono : subcubeAvg Kc n (fun Q => ENNReal.ofReal
        (vecNorm (principalED Q e' gD) ^ 8 + vecNorm (principalEN Q e gN) ^ 8 +
          matrixOperatorNorm ((sigmaBarInfinite nu (m - h) P)⁻¹ • principalGauge m h Q omega) ^ 8)) ≤
      subcubeAvg Kc n (fun Q =>
        (2 ^ 7 * (1 + ENNReal.ofReal (vecNorm (volumeAverageVec (cubeSet Q) gD)) ^ (8 : ℕ)) +
          2 ^ 7 * (1 + ENNReal.ofReal (vecNorm (volumeAverageVec (cubeSet Q) gN)) ^ (8 : ℕ))) +
          (s * ((d : ℝ≥0∞) * d)) ^ (8 : ℕ) *
            (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8 incr ^ (8 : ℕ))) := by
    unfold subcubeAvg
    refine mul_le_mul' le_rfl (Finset.sum_le_sum fun Q hQ => (hcube Q hQ).trans (le_of_eq ?_))
    ring
  refine hmono.trans ?_
  have hA : subcubeAvg Kc n (fun Q =>
        (2 ^ 7 * (1 + ENNReal.ofReal (vecNorm (volumeAverageVec (cubeSet Q) gD)) ^ (8 : ℕ)) +
          2 ^ 7 * (1 + ENNReal.ofReal (vecNorm (volumeAverageVec (cubeSet Q) gN)) ^ (8 : ℕ))) +
          (s * ((d : ℝ≥0∞) * d)) ^ (8 : ℕ) *
            (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8 incr ^ (8 : ℕ))) =
      (2 ^ 7 * (1 + subcubeAvg Kc n (fun Q =>
          ENNReal.ofReal (vecNorm (volumeAverageVec (cubeSet Q) gD)) ^ (8 : ℕ))) +
        2 ^ 7 * (1 + subcubeAvg Kc n (fun Q =>
          ENNReal.ofReal (vecNorm (volumeAverageVec (cubeSet Q) gN)) ^ (8 : ℕ)))) +
        (s * ((d : ℝ≥0∞) * d)) ^ (8 : ℕ) * subcubeAvg Kc n (fun Q =>
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8 incr ^ (8 : ℕ)) := by
    rw [subcubeAvg_add, subcubeAvg_add, subcubeAvg_const_mul, subcubeAvg_const_mul,
      subcubeAvg_const_mul, subcubeAvg_add, subcubeAvg_add, subcubeAvg_const_pm hn]
  rw [hA]
  have hc1 : (2 : ℝ≥0∞) ^ 8 ≤ 2 ^ 15 + D := le_add_right (pow_le_pow_right₀ (by norm_num) (by norm_num))
  have hc2 : (2 : ℝ≥0∞) ^ 7 ≤ 2 ^ 15 + D := le_add_right (pow_le_pow_right₀ (by norm_num) (by norm_num))
  have hc3 : (2 : ℝ≥0∞) ^ 14 ≤ 2 ^ 15 + D := le_add_right (pow_le_pow_right₀ (by norm_num) (by norm_num))
  have hc4 : (2 : ℝ≥0∞) ^ 14 + D ≤ 2 ^ 15 + D :=
    add_le_add (pow_le_pow_right₀ (by norm_num) (by norm_num)) le_rfl
  calc (2 ^ 7 * (1 + subcubeAvg Kc n (fun Q =>
          ENNReal.ofReal (vecNorm (volumeAverageVec (cubeSet Q) gD)) ^ (8 : ℕ))) +
        2 ^ 7 * (1 + subcubeAvg Kc n (fun Q =>
          ENNReal.ofReal (vecNorm (volumeAverageVec (cubeSet Q) gN)) ^ (8 : ℕ)))) +
        (s * ((d : ℝ≥0∞) * d)) ^ (8 : ℕ) * subcubeAvg Kc n (fun Q =>
          SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8 incr ^ (8 : ℕ))
      ≤ (2 ^ 7 * (1 + Jd ^ (8 : ℕ)) + 2 ^ 7 * (1 + 2 ^ 7 * (Jn ^ (8 : ℕ) + (s * Kn) ^ (8 : ℕ)))) +
        (s * ((d : ℝ≥0∞) * d)) ^ (8 : ℕ) * Kn ^ (8 : ℕ) := by
        gcongr
    _ = 2 ^ 8 * 1 + 2 ^ 7 * Jd ^ (8 : ℕ) + 2 ^ 14 * Jn ^ (8 : ℕ) +
        (2 ^ 14 + D) * (s ^ (8 : ℕ) * Kn ^ (8 : ℕ)) := by
        rw [hD]; ring
    _ ≤ (2 ^ 15 + D) * 1 + (2 ^ 15 + D) * Jd ^ (8 : ℕ) + (2 ^ 15 + D) * Jn ^ (8 : ℕ) +
        (2 ^ 15 + D) * (s ^ (8 : ℕ) * Kn ^ (8 : ℕ)) := by
        gcongr
    _ = (2 ^ 15 + D) * (1 + Jd ^ (8 : ℕ) + Jn ^ (8 : ℕ) + s ^ (8 : ℕ) * Kn ^ (8 : ℕ)) := by ring

end MatNorm2

end SuperdiffusionCLT.Section5
