/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Response.NeumannOscillationOsc
public import SuperdiffusionCLT.Section5.Response.NeumannOscillationDelta
public import SuperdiffusionCLT.Section5.Response.GradientL8

/-!
# The moment chain of `e.crude.Fz.bound`

The expectation of the subcube average of the fourth powers of the oscillations of
`∇w_{D,e}` and of `∇w_{N,e'} + hshell e'` is bounded by the sum of three kinds of terms:
the Hessian and shell-Jacobian terms (Poincaré on the subcubes, `L⁸` size by the measurable
majorant), and the gap term (interpolation between the energy gap and the `L⁸` gradient bound).
The bound is stated with the interpolation parameter `t` and the energy-gap bound `X0` free;
`NeumannOscillation.lean` chooses `t` and does the scale arithmetic.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The Dirichlet responses of the shell flux have a family of weak Hessians. -/
theorem exists_hessian_family [NeZero d] (hd : 2 ≤ d) (nu : ℝ)
    (P : ProbabilityMeasure (ShellSeq d)) (m h Kc : ℕ) (e : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))))
    (hwD : ∀ omega, IsCubeDirichletResponse (originCube d (Kc : ℤ))
      (hshellFlux nu P m h omega e) (wD omega)) :
    Nonempty (∀ omega, HasWeakHessianOn (openCubeSet (originCube d (Kc : ℤ)))
      (wD omega).toH1Function) :=
  ⟨fun omega => Classical.choice
    (exists_hasWeakHessianOn_dirichletResponse hd omega (Nat.sub_le m h)
      ((sigmaBarInfinite nu (m - h) P)⁻¹ • e) (wD omega)
      (by
        have hw := hwD omega
        rw [responseData_hshellFlux_eq_dirichletRhsField] at hw
        exact hw))⟩

theorem continuous_hshellFlux_jac [NeZero d] (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d))
    (m h : ℕ) (omega : ShellSeq d) (e : Vec d) (i j : Fin d) :
    Continuous (fun x => fderiv ℝ (fun y => hshellFlux nu P m h omega e y i) x (basisVec j)) :=
  ((contDiff_hshellFlux_apply nu P m h omega e i).continuous_fderiv (by simp)).clm_apply
    continuous_const

theorem continuous_hshellFlux_osc [NeZero d] (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d))
    (m h : ℕ) (omega : ShellSeq d) (e : Vec d) : Continuous (hshellFlux nu P m h omega e) :=
  continuous_pi fun i => (contDiff_hshellFlux_apply nu P m h omega e i).continuous

/-- **The moment chain of `e.crude.Fz.bound`**, with the interpolation parameter `t` and the
energy-gap bound `X0` free. -/
theorem crude_Fz_chain [NeZero d] (hd : 2 ≤ d) :
    ∃ Cos Cmaj Cgr : ℝ, 0 < Cos ∧ 0 < Cmaj ∧ 1 ≤ Cgr ∧
    ∀ (nu : ℝ), 0 < nu → nu ≤ 1 →
    ∀ (P : ProbabilityMeasure (ShellSeq d)), ShellLawPrefix d P → ShellLawJ2 d P →
      ShellLawJ3 d P → ShellLawJ1Restriction d P → ShellLawJ4 d P →
    ∀ m h Kc : ℕ, 1 ≤ h → 400 * h ≤ m → 100 * m ≤ Kc →
    ∀ e e' : Vec d, vecNormSq e ≤ 1 → vecNormSq e' ≤ 1 →
    ∀ n : ℕ, n ≤ Kc →
    ∀ (wD : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ))))
      (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ))))
      (wD' : ShellSeq d → H10Function (openCubeSet (originCube d (Kc : ℤ)))),
    (∀ omega, IsCubeDirichletResponse (originCube d (Kc : ℤ))
      (hshellFlux nu P m h omega e) (wD omega)) →
    (∀ omega, IsCubeNeumannResponse (originCube d (Kc : ℤ))
      (hshellFlux nu P m h omega e') (wN omega)) →
    (∀ omega, IsCubeDirichletResponse (originCube d (Kc : ℤ))
      (hshellFlux nu P m h omega e') (wD' omega)) →
    ∀ X0 : ℝ,
    ∫⁻ omega, vecCubeLpENorm (originCube d (Kc : ℤ)) 2
        (fun x => (wN omega).toH1Function.grad x - (wD' omega).toH1Function.grad x) ^ (2 : ℕ)
        ∂P.toMeasure ≤ ENNReal.ofReal X0 →
    ∀ {t : ℝ}, 0 < t →
    subcubeAvg Kc n (fun Q => ∫⁻ omega,
        ((vecCubeLpENorm Q 4 (fun x => (wD omega).toH1Function.grad x -
            volumeAverageVec (cubeSet Q) (wD omega).toH1Function.grad)) ^ 4 +
          (vecCubeLpENorm Q 4 (fun x => ((wN omega).toH1Function.grad x +
              hshellFlux nu P m h omega e' x) -
            volumeAverageVec (cubeSet Q) (fun y => (wN omega).toH1Function.grad y +
              hshellFlux nu P m h omega e' y))) ^ 4) ∂P.toMeasure) ≤
      ENNReal.ofReal (((Cos * (3 : ℝ) ^ n) ^ 4) * ((Cmaj * (sigmaBarInfinite nu (m - h) P)⁻¹) *
          (Real.sqrt d * (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)))) ^ 4) +
        1024 * (ENNReal.ofReal (((Cos * (3 : ℝ) ^ n) ^ 4) *
            ((Cmaj * (sigmaBarInfinite nu (m - h) P)⁻¹) *
              (Real.sqrt d * (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)))) ^ 4) +
          ENNReal.ofReal (((Cos * (3 : ℝ) ^ n) ^ 4) * ((sigmaBarInfinite nu (m - h) P)⁻¹ *
            (Real.sqrt d * (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)))) ^ 4)) +
        1024 * (ENNReal.ofReal (2 * t / 3) * ENNReal.ofReal X0 +
          ENNReal.ofReal (1 / (3 * t ^ 2)) *
            (128 * ENNReal.ofReal ((Cgr * (sigmaBarInfinite nu (m - h) P)⁻¹ *
              (h : ℝ) ^ ((1 : ℝ) / 2)) ^ 8))) := by
  obtain ⟨Cos, hCos, hosc⟩ := osc_pointwise (d := d)
  obtain ⟨Cm0, hCm0, hmaj⟩ := hessian_le_majorant hd
  obtain ⟨Cgr, hCgr1, hgrad⟩ := response_gradient_L8 d hd
  refine ⟨Cos, Cm0 + 1, Cgr, hCos, by linarith only [hCm0], hCgr1, ?_⟩
  intro nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 m h Kc hh h400 h100 e e' he he' n hn wD wN wD' hwD hwN
    hwD' X0 hX0 t ht
  have hσ : 0 < sigmaBarInfinite nu (m - h) P :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu (m - h) hPre hJ2 hJ3 hJ4
  set si : ℝ := (sigmaBarInfinite nu (m - h) P)⁻¹ with hsi
  have hsi0 : 0 < si := inv_pos.2 hσ
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd0)
  have h3 : 0 < (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)) := by positivity
  set Be : ℝ := Real.sqrt d * (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)) with hBe
  have hBe0 : 0 < Be := mul_pos hsqrt h3
  obtain ⟨HD0⟩ := exists_hessian_family hd nu P m h Kc e wD hwD
  obtain ⟨HD1⟩ := exists_hessian_family hd nu P m h Kc e' wD' hwD'
  have hL2e : ∀ omega, MemVectorL2 (openCubeSet (originCube d (Kc : ℤ))) (hshellFlux nu P m h omega e) := fun omega =>
    memVectorL2_of_continuous (Kc : ℤ) (continuous_hshellFlux_osc nu P m h omega e)
  choose wNe hwNe using fun omega => exists_isCubeNeumannResponse (originCube d (Kc : ℤ)) (hL2e omega)
  have hS := fun omega Q hQ => hosc hn (wD omega).toH1Function (wD' omega).toH1Function
    (wN omega).toH1Function (HD0 omega) (HD1 omega) (hshellFlux nu P m h omega e')
    (fun i => contDiff_hshellFlux_apply nu P m h omega e' i) Q hQ
  set cos4 : ℝ≥0∞ := ENNReal.ofReal ((Cos * (3 : ℝ) ^ n) ^ 4) with hcos4
  let H0 : ShellSeq d → Vec d → HilbertMat d := fun omega x =>
    HilbertMat.ofMat (fun i j => (HD0 omega).hess i j x)
  let H1 : ShellSeq d → Vec d → HilbertMat d := fun omega x =>
    HilbertMat.ofMat (fun i j => (HD1 omega).hess i j x)
  let Jf : ShellSeq d → Vec d → HilbertMat d := fun omega x =>
    HilbertMat.ofMat (fun i j => fderiv ℝ (fun y => hshellFlux nu P m h omega e' y i) x (basisVec j))
  let δf : ShellSeq d → Vec d → Vec d := fun omega x =>
    (wN omega).toH1Function.grad x - (wD' omega).toH1Function.grad x
  let Φ : TriadicCube d → ShellSeq d → ℝ≥0∞ := fun Q omega =>
    cos4 * (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4 (H0 omega)) ^ 4 +
      1024 * (cos4 * (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4 (H1 omega)) ^ 4 +
        (vecCubeLpENorm Q 4 (δf omega)) ^ 4 +
        cos4 * (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4 (Jf omega)) ^ 4)
  have hS' : ∀ omega, ∀ Q ∈ descendantsAtScale (originCube d (Kc : ℤ)) (n : ℤ),
      (vecCubeLpENorm Q 4 (fun x => (wD omega).toH1Function.grad x -
          volumeAverageVec (cubeSet Q) (wD omega).toH1Function.grad)) ^ 4 +
        (vecCubeLpENorm Q 4 (fun x => ((wN omega).toH1Function.grad x +
            hshellFlux nu P m h omega e' x) -
          volumeAverageVec (cubeSet Q) (fun y => (wN omega).toH1Function.grad y +
            hshellFlux nu P m h omega e' y))) ^ 4 ≤ Φ Q omega :=
    fun omega Q hQ => hS omega Q hQ
  -- the sample-wise partition identity
  have hΨ : ∀ omega, subcubeAvg Kc n (fun Q => Φ Q omega) =
      cos4 * (SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 4
          (H0 omega)) ^ 4 +
        1024 * (cos4 * (SuperdiffusionCLT.Section2.Norms.cubeLpENorm
            (originCube d (Kc : ℤ)) 4 (H1 omega)) ^ 4 +
          (vecCubeLpENorm (originCube d (Kc : ℤ)) 4 (δf omega)) ^ 4 +
          cos4 * (SuperdiffusionCLT.Section2.Norms.cubeLpENorm
            (originCube d (Kc : ℤ)) 4 (Jf omega)) ^ 4) := by
    intro omega
    have m0 : AEStronglyMeasurable (H0 omega)
        (volume.restrict (openCubeSet (originCube d (Kc : ℤ)))) :=
      aestronglyMeasurable_hilbertMat_of_entries fun i j =>
        ((HD0 omega).hess_memL2 i j).aestronglyMeasurable
    have m1 : AEStronglyMeasurable (H1 omega)
        (volume.restrict (openCubeSet (originCube d (Kc : ℤ)))) :=
      aestronglyMeasurable_hilbertMat_of_entries fun i j =>
        ((HD1 omega).hess_memL2 i j).aestronglyMeasurable
    have m3 : AEStronglyMeasurable (Jf omega)
        (volume.restrict (openCubeSet (originCube d (Kc : ℤ)))) :=
      aestronglyMeasurable_hilbertMat_of_entries fun i j =>
        (continuous_hshellFlux_jac nu P m h omega e' i j).aestronglyMeasurable
    have mδ : AEStronglyMeasurable (hilbertifyVecField (δf omega))
        (volume.restrict (openCubeSet (originCube d (Kc : ℤ)))) :=
      (memHilbertVectorL2_hilbertifyVecField
        ((wN omega).toH1Function.grad_memVectorL2.sub
          (wD' omega).toH1Function.grad_memVectorL2)).aestronglyMeasurable
    have := subcubeAvg_combo (Kc := Kc) (n := n) cos4 cos4 cos4
      (fun Q => (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4 (H0 omega)) ^ 4)
      (fun Q => (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4 (H1 omega)) ^ 4)
      (fun Q => (vecCubeLpENorm Q 4 (δf omega)) ^ 4)
      (fun Q => (SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 4 (Jf omega)) ^ 4)
    refine this.trans ?_
    rw [subcubeAvg_pow_four_cubeLpENorm hn _ m0, subcubeAvg_pow_four_cubeLpENorm hn _ m1,
      subcubeAvg_pow_four_cubeLpENorm hn _ m3]
    have e4 := subcubeAvg_pow_four_cubeLpENorm hn _ mδ
    exact congrArg₂ (· + ·) rfl (congrArg (1024 * ·) (congrArg₂ (· + ·)
      (congrArg₂ (· + ·) rfl e4) rfl))
  -- the majorants
  have hab : m - h ≤ m := Nat.sub_le m h
  have hvn : ∀ p : Vec d, vecNormSq p ≤ 1 → vecNorm p ≤ 1 := fun p hp => by
    have hsq := Homogenization.Book.Ch02.vecNorm_sq_eq_vecNormSq p
    exact (pow_le_one_iff_of_nonneg (vecNorm_nonneg p) two_ne_zero).1 (hsq ▸ hp)
  have hZ8 : ∀ p : Vec d, vecNormSq p ≤ 1 →
      ∫⁻ omega, (shellJacMajorant (originCube d (Kc : ℤ)) (m - h) m
        (Real.sqrt d * vecNorm p) omega) ^ 8 ∂P.toMeasure ≤ ENNReal.ofReal (Be ^ 8) := by
    intro p hp
    refine le_ofReal_pow_eight_of_rpow_le hBe0.le ?_
    refine (lintegral_shellJacMajorant_le hPre hJ3 (originCube d (Kc : ℤ)) (m - h) m
      (mul_nonneg hsqrt.le (vecNorm_nonneg p))).trans (ENNReal.ofReal_le_ofReal ?_)
    have hsum := sum_Ioc_inv_three_pow_le hab
    have h3' : (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)) = ((3 : ℝ) ^ (m - h))⁻¹ := by
      rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
    have hvp := hvn p hp
    have hs0 : 0 ≤ ∑ k ∈ Finset.Ioc (m - h) m, ((3 : ℝ) ^ k)⁻¹ :=
      Finset.sum_nonneg fun k _ => by positivity
    calc 2 * (Real.sqrt d * vecNorm p) * ∑ k ∈ Finset.Ioc (m - h) m, ((3 : ℝ) ^ k)⁻¹
        ≤ 2 * (Real.sqrt d * 1) * (((3 : ℝ) ^ (m - h))⁻¹ / 2) := by
          gcongr
      _ = Be := by rw [hBe, h3']; ring
  set Ze : ShellSeq d → ℝ≥0∞ := shellJacMajorant (originCube d (Kc : ℤ)) (m - h) m
    (Real.sqrt d * vecNorm e) with hZe
  set Ze' : ShellSeq d → ℝ≥0∞ := shellJacMajorant (originCube d (Kc : ℤ)) (m - h) m
    (Real.sqrt d * vecNorm e') with hZe'
  have hZem : Measurable Ze := measurable_shellJacMajorant _ _ _ _
  have hZe'm : Measurable Ze' := measurable_shellJacMajorant _ _ _ _
  have hCmaj : 0 < (Cm0 + 1) * si := mul_pos (by linarith only [hCm0]) hsi0
  have hint1 : ∫⁻ omega, (ENNReal.ofReal ((Cm0 + 1) * si) * Ze omega) ^ 4 ∂P.toMeasure ≤
      ENNReal.ofReal ((((Cm0 + 1) * si) * Be) ^ 4) :=
    lintegral_const_mul_pow_four_le Ze hCmaj hBe0 (hZ8 e he)
  have hint2 : ∫⁻ omega, (ENNReal.ofReal ((Cm0 + 1) * si) * Ze' omega) ^ 4 ∂P.toMeasure ≤
      ENNReal.ofReal ((((Cm0 + 1) * si) * Be) ^ 4) :=
    lintegral_const_mul_pow_four_le Ze' hCmaj hBe0 (hZ8 e' he')
  have hint3 : ∫⁻ omega, (ENNReal.ofReal si * Ze' omega) ^ 4 ∂P.toMeasure ≤
      ENNReal.ofReal ((si * Be) ^ 4) :=
    lintegral_const_mul_pow_four_le Ze' hsi0 hBe0 (hZ8 e' he')
  -- the pointwise domination of the Hessian and shell terms by the majorants
  have hp0 : ∀ omega, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm
      (originCube d (Kc : ℤ)) 4 (H0 omega)) ^ 4 ≤
      (ENNReal.ofReal ((Cm0 + 1) * si) * Ze omega) ^ 4 := fun omega => by
    refine pow_le_pow_left' ?_ 4
    refine (cubeLpENorm_mono_exponent _ (by norm_num : (4 : ℝ≥0∞) ≤ 8) _).trans ?_
    refine (hmaj nu hnu P hPre hJ2 hJ3 hJ4 m h Kc e (wD omega) (wNe omega) omega (hwD omega)
      (hwNe omega) (HD0 omega)).trans ?_
    gcongr
    linarith only
  have hp1 : ∀ omega, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm
      (originCube d (Kc : ℤ)) 4 (H1 omega)) ^ 4 ≤
      (ENNReal.ofReal ((Cm0 + 1) * si) * Ze' omega) ^ 4 := fun omega => by
    refine pow_le_pow_left' ?_ 4
    refine (cubeLpENorm_mono_exponent _ (by norm_num : (4 : ℝ≥0∞) ≤ 8) _).trans ?_
    refine (hmaj nu hnu P hPre hJ2 hJ3 hJ4 m h Kc e' (wD' omega) (wN omega) omega (hwD' omega)
      (hwN omega) (HD1 omega)).trans ?_
    gcongr
    linarith only
  have hp3 : ∀ omega, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm
      (originCube d (Kc : ℤ)) 4 (Jf omega)) ^ 4 ≤ (ENNReal.ofReal si * Ze' omega) ^ 4 :=
    fun omega => by
    refine pow_le_pow_left' ?_ 4
    refine (cubeLpENorm_mono_exponent _ (by norm_num : (4 : ℝ≥0∞) ≤ 8) _).trans ?_
    have hjac := cubeLpENorm_hshellFlux_jac nu P m h omega e' (originCube d (Kc : ℤ)) 8
    rw [Real.enorm_eq_ofReal hsi0.le] at hjac
    refine hjac.le.trans ?_
    exact mul_le_mul' le_rfl (cubeLpENorm_streamJac_le_majorant omega hab e' _)
  -- the gap term
  have hXm := measurable_gap_energy nu P m h Kc e' wN wD' hwN hwD'
  have hgp := lintegral_gap_pow_four_le (Kc := Kc) P.toMeasure
    (fun omega => (wD' omega).toH1Function.grad) (fun omega => (wN omega).toH1Function.grad)
    (fun omega => (wD' omega).toH1Function.grad_memVectorL2)
    (fun omega => (wN omega).toH1Function.grad_memVectorL2) hXm ht
  have hCg0 : 0 ≤ Cgr * si * (h : ℝ) ^ ((1 : ℝ) / 2) :=
    mul_nonneg (mul_nonneg (by linarith only [hCgr1]) hsi0.le) (Real.rpow_nonneg (by positivity) _)
  have hY := le_ofReal_pow_eight_of_rpow_le hCg0
    (hgrad nu hnu hnu1 P hPre hJ2 hJ3 hJ1 hJ4 m h Kc hh h400 h100 e' he' wD' wN hwD' hwN)
  have hb : ∫⁻ omega, (vecCubeLpENorm (originCube d (Kc : ℤ)) 4 (δf omega)) ^ 4 ∂P.toMeasure ≤
      ENNReal.ofReal (2 * t / 3) * ENNReal.ofReal X0 +
        ENNReal.ofReal (1 / (3 * t ^ 2)) *
          (128 * ENNReal.ofReal ((Cgr * si * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ 8)) :=
    hgp.trans (add_le_add (mul_le_mul' le_rfl hX0) (mul_le_mul' le_rfl (mul_le_mul' le_rfl hY)))
  -- the splitting of the sample integral
  set c0 : ℝ≥0∞ := ENNReal.ofReal ((Cm0 + 1) * si) with hc0
  set M : ShellSeq d → ℝ≥0∞ := fun omega =>
    cos4 * (c0 * Ze omega) ^ 4 + 1024 * (cos4 * (c0 * Ze' omega) ^ 4 +
      cos4 * (ENNReal.ofReal si * Ze' omega) ^ 4) with hM
  have hf0 : Measurable fun omega => cos4 * (c0 * Ze omega) ^ 4 :=
    ((hZem.const_mul c0).pow_const 4).const_mul cos4
  have hf1 : Measurable fun omega => cos4 * (c0 * Ze' omega) ^ 4 :=
    ((hZe'm.const_mul c0).pow_const 4).const_mul cos4
  have hf3 : Measurable fun omega => cos4 * (ENNReal.ofReal si * Ze' omega) ^ 4 :=
    ((hZe'm.const_mul (ENNReal.ofReal si)).pow_const 4).const_mul cos4
  have hcos4fin : cos4 ≠ ∞ := ENNReal.ofReal_ne_top
  have h1024 : (1024 : ℝ≥0∞) ≠ ∞ := by norm_num
  have hMint : ∫⁻ omega, M omega ∂P.toMeasure ≤
      cos4 * ENNReal.ofReal ((((Cm0 + 1) * si) * Be) ^ 4) +
        1024 * (cos4 * ENNReal.ofReal ((((Cm0 + 1) * si) * Be) ^ 4) +
          cos4 * ENNReal.ofReal ((si * Be) ^ 4)) := by
    simp only [hM]
    rw [lintegral_add_left hf0, lintegral_const_mul' _ _ h1024,
      lintegral_add_left hf1, lintegral_const_mul' _ _ hcos4fin, lintegral_const_mul' _ _ hcos4fin,
      lintegral_const_mul' _ _ hcos4fin]
    gcongr
  have hMm : Measurable M := hf0.add (((hf1.add hf3).const_mul 1024))
  have hΨle : ∀ omega, subcubeAvg Kc n (fun Q => Φ Q omega) ≤
      M omega + 1024 * (vecCubeLpENorm (originCube d (Kc : ℤ)) 4 (δf omega)) ^ 4 := by
    intro omega
    rw [hΨ omega]
    calc _ ≤ cos4 * (c0 * Ze omega) ^ 4 + 1024 * (cos4 * (c0 * Ze' omega) ^ 4 +
          (vecCubeLpENorm (originCube d (Kc : ℤ)) 4 (δf omega)) ^ 4 +
          cos4 * (ENNReal.ofReal si * Ze' omega) ^ 4) :=
          add_le_add (mul_le_mul' le_rfl (hp0 omega)) (mul_le_mul' le_rfl
            (add_le_add (add_le_add (mul_le_mul' le_rfl (hp1 omega)) le_rfl)
              (mul_le_mul' le_rfl (hp3 omega))))
      _ = _ := by simp only [hM]; ring
  calc _ ≤ subcubeAvg Kc n (fun Q => ∫⁻ omega, Φ Q omega ∂P.toMeasure) :=
        subcubeAvg_mono_on_osc fun Q hQ => lintegral_mono fun omega => hS' omega Q hQ
    _ ≤ ∫⁻ omega, subcubeAvg Kc n (fun Q => Φ Q omega) ∂P.toMeasure :=
        subcubeAvg_lintegral_le_osc _ hn _
    _ ≤ ∫⁻ omega, (M omega + 1024 * (vecCubeLpENorm (originCube d (Kc : ℤ)) 4 (δf omega)) ^ 4)
          ∂P.toMeasure := lintegral_mono hΨle
    _ = ∫⁻ omega, M omega ∂P.toMeasure + 1024 *
          ∫⁻ omega, (vecCubeLpENorm (originCube d (Kc : ℤ)) 4 (δf omega)) ^ 4 ∂P.toMeasure := by
        rw [lintegral_add_left hMm, lintegral_const_mul' _ _ h1024]
    _ ≤ (cos4 * ENNReal.ofReal ((((Cm0 + 1) * si) * Be) ^ 4) +
        1024 * (cos4 * ENNReal.ofReal ((((Cm0 + 1) * si) * Be) ^ 4) +
          cos4 * ENNReal.ofReal ((si * Be) ^ 4))) + 1024 * (ENNReal.ofReal (2 * t / 3) *
            ENNReal.ofReal X0 + ENNReal.ofReal (1 / (3 * t ^ 2)) *
          (128 * ENNReal.ofReal ((Cgr * si * (h : ℝ) ^ ((1 : ℝ) / 2)) ^ 8))) :=
        add_le_add hMint (mul_le_mul' le_rfl hb)
    _ = _ := by
        have hq : 0 ≤ (Cos * (3 : ℝ) ^ n) ^ 4 := by positivity
        rw [hcos4, ← ENNReal.ofReal_mul hq, ← ENNReal.ofReal_mul hq]

end

end SuperdiffusionCLT.Section5
