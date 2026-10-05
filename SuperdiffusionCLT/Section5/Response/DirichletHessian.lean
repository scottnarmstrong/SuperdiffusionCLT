/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Carriers.BlockOffset
public import SuperdiffusionCLT.Section5.Response.ResponseData
public import SuperdiffusionCLT.Section5.Response.DerivativeMomentsB
public import SuperdiffusionCLT.Frozen.Section3.ResponseFieldsAprioriOrderOne
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume

/-!
# The Dirichlet Hessian clause of `lem.response`

display `e.response.hess.l8`, Dirichlet half:
for every family of weak Hessians `HD ω` of the Dirichlet responses `w_D(ω)` of the flux
`shom_{m-h}^{-1} hshell e` on `cu_K`,

`E[‖∇²w_D‖_{L̲⁸}⁸]^{1/8} ≤ C shom_{m-h}^{-1} 3^{-(m-h)}`.

The clause is universal over supplied weak Hessians: the a priori clause
(`Frozen.Section3.responseFields_apriori_orderOne`, clause 2) bounds a supplied Hessian by
`C ‖∇F‖_{L̲⁸}` and asserts no existence. The Jacobian of the flux is the classical one, and its
`L⁸(P; L̲⁸(cu_K))` size is bounded in `DerivativeMomentsB` by `J3` and stationarity,
independently of `K`. There is no Neumann Hessian clause.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open scoped ENNReal

variable {d : ℕ}

/-- The geometric tail of the derivative scales: `∑_{k ∈ (a,b]} 3^{-k} = (3^{-a} - 3^{-b})/2`. -/
theorem sum_Ioc_inv_three_pow {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Finset.Ioc a b, ((3 : ℝ) ^ k)⁻¹ = (((3 : ℝ) ^ a)⁻¹ - ((3 : ℝ) ^ b)⁻¹) / 2 := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      rw [Finset.sum_Ioc_succ_top hab, ih]
      have h3 : ((3 : ℝ) ^ (b + 1))⁻¹ = ((3 : ℝ) ^ b)⁻¹ / 3 := by
        rw [pow_succ, mul_inv, div_eq_mul_inv]
      rw [h3]
      ring

theorem sum_Ioc_inv_three_pow_le {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Finset.Ioc a b, ((3 : ℝ) ^ k)⁻¹ ≤ ((3 : ℝ) ^ a)⁻¹ / 2 := by
  rw [sum_Ioc_inv_three_pow hab]
  have : (0 : ℝ) ≤ ((3 : ℝ) ^ b)⁻¹ := by positivity
  linarith only [this]

/-- **The Dirichlet Hessian clause of `lem.response`** (`e.response.hess.l8`, Dirichlet half): for
every family of weak Hessians `HD ω` of `w_D(ω)`,
`E[‖∇²w_D‖_{L̲⁸}⁸]^{1/8} ≤ C shom_{m-h}^{-1} 3^{-(m-h)}`. -/
theorem response_hessian_L8 (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
        ∀ (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)),
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawPrefix d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ2 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ3 d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ1Restriction d P →
          SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4 d P →
          ∀ m h Kc : ℕ, 1 ≤ h → 400 * h ≤ m → 100 * m ≤ Kc →
          ∀ e : Vec d, vecNormSq e ≤ 1 →
          ∀ (wD : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
                H10Function (openCubeSet (originCube d (Kc : ℤ))))
            (wN : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
                H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ)))),
            (∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
              (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wD omega)) →
            (∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse
              (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wN omega)) →
          (∀ HD : ∀ omega, HasWeakHessianOn (openCubeSet (originCube d (Kc : ℤ)))
                (wD omega).toH1Function,
            (∫⁻ omega, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                (originCube d (Kc : ℤ)) 8
                (fun x => HilbertMat.ofMat (fun i j => (HD omega).hess i j x))) ^ (8 : ℕ)
                ∂P.toMeasure) ^ ((1 : ℝ) / 8) ≤
              ENNReal.ofReal (C * (sigmaBarInfinite nu (m - h) P)⁻¹ *
                (3 : ℝ) ^ (-((m - h : ℕ) : ℝ))))
  := by
  obtain ⟨Cap, hCapTop, hAp⟩ :=
    SuperdiffusionCLT.Frozen.Section3.responseFields_apriori_orderOne d hd
  refine ⟨max 1 (Cap.toReal * Real.sqrt d), le_max_left _ _, ?_⟩
  intro nu hnu hnu1 P hPre hJ2 hJ3 _hJ1 hJ4 m h Kc _hh _h400 _h100 e he wD wN hwD hwN HD
  have hσ : 0 < sigmaBarInfinite nu (m - h) P :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu (m - h) hPre hJ2 hJ3 hJ4
  have hab : m - h ≤ m := Nat.sub_le m h
  set σi : ℝ := (sigmaBarInfinite nu (m - h) P)⁻¹ with hσi
  have hσinn : 0 ≤ σi := inv_nonneg.2 hσ.le
  have hdiff : ∀ omega i, ContDiff ℝ 1 (fun y => hshellFlux nu P m h omega e y i) := by
    intro omega i
    have h1 := SuperdiffusionCLT.Section3.ResponseFields.contDiff_streamFlux_apply
      omega hab e i
    have h2 : (fun y => hshellFlux nu P m h omega e y i) = fun y =>
        σi * matVecMul (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega m y -
          SuperdiffusionCLT.Frozen.Section2.streamCutoff omega (m - h) y) e i := by
      funext y
      simp [hshellFlux, hσi]
    rw [h2]
    exact contDiff_const.mul h1
  set DF : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d → Fin d → Vec d → Vec d :=
    fun omega i x j => fderiv ℝ (fun y => hshellFlux nu P m h omega e y i) x (basisVec j)
    with hDF
  have hDFweak : ∀ omega i, HasWeakGradientOn (openCubeSet (originCube d (Kc : ℤ)))
      (fun x => hshellFlux nu P m h omega e x i) (DF omega i) := fun omega i =>
    HasWeakGradientOn.of_contDiff (hdiff omega i)
  have hDFeq : ∀ omega i x j, DF omega i x j =
      σi * SuperdiffusionCLT.Section3.ResponseFields.streamFluxWeakGradient omega (m - h) m e
        i x j := by
    intro omega i x j
    have h1 := SuperdiffusionCLT.Section3.ResponseFields.contDiff_streamFlux_apply
      omega hab e i
    have h2 : (fun y => hshellFlux nu P m h omega e y i) = fun y =>
        σi * matVecMul (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega m y -
          SuperdiffusionCLT.Frozen.Section2.streamCutoff omega (m - h) y) e i := by
      funext y
      simp [hshellFlux, hσi]
    simp only [hDF]
    rw [h2, fderiv_const_mul (h1.differentiable (by norm_num) x)]
    rfl
  have hjac : ∀ omega, SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 8
      (fun x => HilbertMat.ofMat (fun i j => DF omega i x j)) =
      ‖σi‖ₑ * SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 8
        (fun x => HilbertMat.ofMat (fun i j =>
          SuperdiffusionCLT.Section3.ResponseFields.streamFluxWeakGradient omega (m - h) m e
            i x j)) := by
    intro omega
    rw [← SuperdiffusionCLT.Section2.Norms.cubeLpENorm_const_smul]
    congr 1
    funext x
    ext i j
    simp [hDFeq]
  have hcap : Cap * ENNReal.ofReal σi = ENNReal.ofReal (Cap.toReal * σi) := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hCapTop.ne]
  have hpt : ∀ omega, SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 8
      (fun x => HilbertMat.ofMat (fun i j => (HD omega).hess i j x)) ≤
      ENNReal.ofReal (Cap.toReal * σi) *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 8
          (fun x => HilbertMat.ofMat (fun i j =>
            SuperdiffusionCLT.Section3.ResponseFields.streamFluxWeakGradient omega (m - h) m e
              i x j)) := by
    intro omega
    have h1 := (hAp Kc (hshellFlux nu P m h omega e) (wD omega) (wN omega) (hwD omega)
      (hwN omega)).2.1 (DF omega) (HD omega) (hDFweak omega)
    refine h1.trans ?_
    rw [hjac omega, Real.enorm_eq_ofReal hσinn, ← mul_assoc, hcap]
  have hrpow : ∀ x : ℝ≥0∞, x ^ (8 : ℝ) = x ^ (8 : ℕ) := fun x => by
    exact_mod_cast ENNReal.rpow_natCast x 8
  have hJ := lintegral_cubeLpENorm_streamFluxWeakGradient_le hPre hJ3 hab e
    (originCube d (Kc : ℤ))
  have hvn : Homogenization.Book.Ch02.vecNorm e ≤ 1 := by
    have hsq := Homogenization.Book.Ch02.vecNorm_sq_eq_vecNormSq e
    exact (pow_le_one_iff_of_nonneg (Homogenization.Book.Ch02.vecNorm_nonneg e)
      two_ne_zero).1 (hsq ▸ he)
  have hK : 0 ≤ Cap.toReal * σi := mul_nonneg ENNReal.toReal_nonneg hσinn
  have hone : (1 : ℝ) / 8 = (((8 : ℕ) : ℝ))⁻¹ := by norm_num
  have hlint : ∫⁻ omega, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 8
        (fun x => HilbertMat.ofMat (fun i j => (HD omega).hess i j x))) ^ (8 : ℕ) ∂P.toMeasure ≤
      ENNReal.ofReal (Cap.toReal * σi) ^ (8 : ℕ) *
        ∫⁻ omega, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 8
          (fun x => HilbertMat.ofMat (fun i j =>
            SuperdiffusionCLT.Section3.ResponseFields.streamFluxWeakGradient omega (m - h) m e
              i x j))) ^ (8 : ℕ) ∂P.toMeasure := by
    rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
    refine lintegral_mono fun omega => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ bot_le (hpt omega) 8
  calc (∫⁻ omega, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 8
        (fun x => HilbertMat.ofMat (fun i j => (HD omega).hess i j x))) ^ (8 : ℕ) ∂P.toMeasure) ^
        ((1 : ℝ) / 8)
      ≤ (ENNReal.ofReal (Cap.toReal * σi) ^ (8 : ℕ) *
        ∫⁻ omega, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 8
          (fun x => HilbertMat.ofMat (fun i j =>
            SuperdiffusionCLT.Section3.ResponseFields.streamFluxWeakGradient omega (m - h) m e
              i x j))) ^ (8 : ℕ) ∂P.toMeasure) ^ ((1 : ℝ) / 8) :=
        ENNReal.rpow_le_rpow hlint (by norm_num)
    _ = ENNReal.ofReal (Cap.toReal * σi) *
        (∫⁻ omega, (SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 8
          (fun x => HilbertMat.ofMat (fun i j =>
            SuperdiffusionCLT.Section3.ResponseFields.streamFluxWeakGradient omega (m - h) m e
              i x j))) ^ (8 : ℕ) ∂P.toMeasure) ^ ((1 : ℝ) / 8) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), hone,
          ENNReal.pow_rpow_inv_natCast (by norm_num)]
    _ ≤ ENNReal.ofReal (Cap.toReal * σi) *
        ENNReal.ofReal (2 * (Real.sqrt d * Homogenization.Book.Ch02.vecNorm e) *
          ∑ k ∈ Finset.Ioc (m - h) m, ((3 : ℝ) ^ k)⁻¹) := mul_le_mul_right hJ _
    _ ≤ ENNReal.ofReal (max 1 (Cap.toReal * Real.sqrt d) * σi * (3 : ℝ) ^ (-((m - h : ℕ) : ℝ))) := by
        rw [← ENNReal.ofReal_mul hK]
        refine ENNReal.ofReal_le_ofReal ?_
        have hsum := sum_Ioc_inv_three_pow_le hab
        have hs0 : 0 ≤ ∑ k ∈ Finset.Ioc (m - h) m, ((3 : ℝ) ^ k)⁻¹ :=
          Finset.sum_nonneg fun k _ => by positivity
        have h3 : (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)) = ((3 : ℝ) ^ (m - h))⁻¹ := by
          rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
        have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
        have hstep : 2 * (Real.sqrt d * Homogenization.Book.Ch02.vecNorm e) *
            ∑ k ∈ Finset.Ioc (m - h) m, ((3 : ℝ) ^ k)⁻¹ ≤
            Real.sqrt d * ((3 : ℝ) ^ (m - h))⁻¹ := by
          calc 2 * (Real.sqrt d * Homogenization.Book.Ch02.vecNorm e) *
              ∑ k ∈ Finset.Ioc (m - h) m, ((3 : ℝ) ^ k)⁻¹
              ≤ 2 * (Real.sqrt d * 1) * (((3 : ℝ) ^ (m - h))⁻¹ / 2) := by
                gcongr
            _ = Real.sqrt d * ((3 : ℝ) ^ (m - h))⁻¹ := by ring
        calc Cap.toReal * σi * (2 * (Real.sqrt d * Homogenization.Book.Ch02.vecNorm e) *
              ∑ k ∈ Finset.Ioc (m - h) m, ((3 : ℝ) ^ k)⁻¹)
            ≤ Cap.toReal * σi * (Real.sqrt d * ((3 : ℝ) ^ (m - h))⁻¹) :=
              mul_le_mul_of_nonneg_left hstep hK
          _ = (Cap.toReal * Real.sqrt d) * σi * (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)) := by
              rw [h3]; ring
          _ ≤ max 1 (Cap.toReal * Real.sqrt d) * σi * (3 : ℝ) ^ (-((m - h : ℕ) : ℝ)) := by
              gcongr
              exact le_max_right _ _

/-- **Satisfiability witness.** The non-law hypotheses of the clause are met together: the scale
conditions at `(m, h, K) = (400, 1, 40000)`, a direction `e` with `|e|² ≤ 1`, and Dirichlet and
Neumann responses of the shell flux with a family of weak Hessians for every sample. -/
example [NeZero d] (hd : 2 ≤ d) (nu : ℝ)
    (P : MeasureTheory.ProbabilityMeasure (SuperdiffusionCLT.Section2.Cutoff.ShellSeq d)) :
    ∃ m h Kc : ℕ, 1 ≤ h ∧ 400 * h ≤ m ∧ 100 * m ≤ Kc ∧
      ∃ e : Vec d, vecNormSq e ≤ 1 ∧
        ∃ (wD : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
              H10Function (openCubeSet (originCube d (Kc : ℤ))))
          (wN : SuperdiffusionCLT.Section2.Cutoff.ShellSeq d →
              H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ)))),
          (∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
            (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wD omega)) ∧
          (∀ omega, SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse
            (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) (wN omega)) ∧
          Nonempty (∀ omega, HasWeakHessianOn (openCubeSet (originCube d (Kc : ℤ)))
            (wD omega).toH1Function) := by
  refine ⟨400, 1, 40000, by norm_num, by norm_num, by norm_num, 0, ?_, ?_⟩
  · simp [vecNormSq, vecDot]
  · exact exists_response_data hd nu P 400 1 40000 0

end SuperdiffusionCLT.Section5
