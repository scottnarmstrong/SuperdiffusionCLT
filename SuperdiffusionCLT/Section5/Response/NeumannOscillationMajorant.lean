/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section5.Response.DirichletHessian
public import SuperdiffusionCLT.Section5.Response.NeumannOscillationMoments
public import SuperdiffusionCLT.Frozen.Section3.ResponseFieldsAprioriOrderOne
public import SuperdiffusionCLT.Frozen.Assumptions.ShellLawJ4
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume

/-!
# A measurable majorant for the Hessian and the shell Jacobian

The moment bounds of `e.crude.Fz.bound` add several `L⁸`-controlled quantities inside one sample
integral.  The Dirichlet Hessian norm is not known to be measurable in the sample, so it is
dominated pointwise (by the a priori clause) by the measurable majorant
`shellJacMajorant`, the sum of the shell derivative sizes, whose `L⁸(P)` size is controlled by
`J3` and stationarity (`DerivativeMoments`).  The Jacobian of the shell flux itself is dominated by
the same majorant (`DerivativeMomentsB`).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section5

open Homogenization MeasureTheory Homogenization.Book.Ch02
open SuperdiffusionCLT.Section2.Annealed (sigmaBarInfinite)
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The measurable majorant `c ∑_{k ∈ (a,b]} ‖∇ j_k‖_{L̲⁸(Q)}` of the Jacobian of `(k_b - k_a) p`. -/
def shellJacMajorant (Q : TriadicCube d) (a b : ℕ) (c : ℝ) (omega : ShellSeq d) : ℝ≥0∞ :=
  ENNReal.ofReal c * ∑ k ∈ Finset.Ioc a b,
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8 (shellDerivSize k omega)

theorem measurable_shellJacMajorant (Q : TriadicCube d) (a b : ℕ) (c : ℝ) :
    Measurable (shellJacMajorant Q a b c) :=
  measurable_const.mul (Finset.measurable_sum _ fun k _ => measurable_cubeLpENorm_shellDerivSize k Q)

/-- The Jacobian of `(k_b - k_a) p` is dominated by the majorant with `c = √d |p|`. -/
theorem cubeLpENorm_streamJac_le_majorant (omega : ShellSeq d) {a b : ℕ} (hab : a ≤ b) (p : Vec d)
    (Q : TriadicCube d) :
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8
        (fun x => HilbertMat.ofMat (fun i j => streamFluxWeakGradient omega a b p i x j)) ≤
      shellJacMajorant Q a b (Real.sqrt d * vecNorm p) omega :=
  cubeLpENorm_streamFluxWeakGradient_le omega hab p Q

/-- **The `L⁸(P)` size of the majorant**, `‖Z‖_{L⁸(P)} ≤ 2 c ∑_{k ∈ (a,b]} 3^{-k}`. -/
theorem lintegral_shellJacMajorant_le {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ3 : ShellLawJ3 d P) (Q : TriadicCube d) (a b : ℕ) {c : ℝ}
    (hc : 0 ≤ c) :
    (∫⁻ omega, (shellJacMajorant Q a b c omega) ^ (8 : ℕ) ∂P.toMeasure) ^ ((1 : ℝ) / 8) ≤
      ENNReal.ofReal (2 * c * ∑ k ∈ Finset.Ioc a b, ((3 : ℝ) ^ k)⁻¹) := by
  set f : ℕ → ShellSeq d → ℝ≥0∞ := fun k omega =>
    ENNReal.ofReal c * SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q 8
      (shellDerivSize k omega) with hf
  have hrpow : ∀ x : ℝ≥0∞, x ^ (8 : ℝ) = x ^ (8 : ℕ) := fun x => by
    exact_mod_cast ENNReal.rpow_natCast x 8
  have hZ : ∀ omega, shellJacMajorant Q a b c omega = ∑ k ∈ Finset.Ioc a b, f k omega :=
    fun omega => Finset.mul_sum _ _ _
  have hone : (1 : ℝ) / 8 = (((8 : ℕ) : ℝ))⁻¹ := by norm_num
  calc (∫⁻ omega, (shellJacMajorant Q a b c omega) ^ (8 : ℕ) ∂P.toMeasure) ^ ((1 : ℝ) / 8)
      = (∫⁻ omega, (∑ k ∈ Finset.Ioc a b, f k omega) ^ (8 : ℝ) ∂P.toMeasure) ^ ((1 : ℝ) / 8) := by
        congr 1
        refine lintegral_congr fun omega => ?_
        rw [hrpow, hZ]
    _ ≤ ∑ k ∈ Finset.Ioc a b, (∫⁻ omega, (f k omega) ^ (8 : ℝ) ∂P.toMeasure) ^ ((1 : ℝ) / 8) :=
        lintegral_rpow_finsetSum_le _ f
          (fun k _ => measurable_const.mul (measurable_cubeLpENorm_shellDerivSize k Q))
          (by norm_num)
    _ ≤ ∑ k ∈ Finset.Ioc a b, ENNReal.ofReal (c * (2 * ((3 : ℝ) ^ k)⁻¹)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have h1 : ∫⁻ omega, (f k omega) ^ (8 : ℝ) ∂P.toMeasure ≤
            (ENNReal.ofReal c * ENNReal.ofReal (2 * ((3 : ℝ) ^ k)⁻¹)) ^ (8 : ℕ) := by
          simp_rw [hrpow, hf, mul_pow]
          rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
          exact mul_le_mul_right (lintegral_cubeLpENorm_shellDerivSize_pow_le hPrefix hJ3 k Q) _
        rw [ENNReal.ofReal_mul hc, hone]
        calc (∫⁻ omega, (f k omega) ^ (8 : ℝ) ∂P.toMeasure) ^ (((8 : ℕ) : ℝ)⁻¹)
            ≤ ((ENNReal.ofReal c * ENNReal.ofReal (2 * ((3 : ℝ) ^ k)⁻¹)) ^ (8 : ℕ)) ^
                (((8 : ℕ) : ℝ)⁻¹) :=
              ENNReal.rpow_le_rpow h1 (by positivity)
          _ = _ := by
              rw [ENNReal.pow_rpow_inv_natCast (by norm_num)]
    _ = ENNReal.ofReal (2 * c * ∑ k ∈ Finset.Ioc a b, ((3 : ℝ) ^ k)⁻¹) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity), ← Finset.mul_sum]
        congr 1
        rw [← Finset.mul_sum]
        ring

/-! ## The classical Jacobian of the shell flux -/

theorem hshellFlux_apply_eq [NeZero d] (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d)) (m h : ℕ)
    (omega : ShellSeq d) (e : Vec d) (y : Vec d) (i : Fin d) :
    hshellFlux nu P m h omega e y i =
      (sigmaBarInfinite nu (m - h) P)⁻¹ * matVecMul
        (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega m y -
          SuperdiffusionCLT.Frozen.Section2.streamCutoff omega (m - h) y) e i := by
  simp [hshellFlux]

theorem contDiff_hshellFlux_apply [NeZero d] (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d))
    (m h : ℕ) (omega : ShellSeq d) (e : Vec d) (i : Fin d) :
    ContDiff ℝ 1 (fun y => hshellFlux nu P m h omega e y i) := by
  have h1 := contDiff_streamFlux_apply omega (Nat.sub_le m h) e i
  have h2 : (fun y => hshellFlux nu P m h omega e y i) = fun y =>
      (sigmaBarInfinite nu (m - h) P)⁻¹ * matVecMul
        (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega m y -
          SuperdiffusionCLT.Frozen.Section2.streamCutoff omega (m - h) y) e i :=
    funext fun y => hshellFlux_apply_eq nu P m h omega e y i
  rw [h2]
  exact contDiff_const.mul h1

theorem fderiv_hshellFlux_apply [NeZero d] (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d))
    (m h : ℕ) (omega : ShellSeq d) (e : Vec d) (i j : Fin d) (x : Vec d) :
    fderiv ℝ (fun y => hshellFlux nu P m h omega e y i) x (basisVec j) =
      (sigmaBarInfinite nu (m - h) P)⁻¹ * streamFluxWeakGradient omega (m - h) m e i x j := by
  have h1 := contDiff_streamFlux_apply omega (Nat.sub_le m h) e i
  have h2 : (fun y => hshellFlux nu P m h omega e y i) = fun y =>
      (sigmaBarInfinite nu (m - h) P)⁻¹ * matVecMul
        (SuperdiffusionCLT.Frozen.Section2.streamCutoff omega m y -
          SuperdiffusionCLT.Frozen.Section2.streamCutoff omega (m - h) y) e i :=
    funext fun y => hshellFlux_apply_eq nu P m h omega e y i
  rw [h2, fderiv_const_mul (h1.differentiable (by norm_num) x)]
  rfl

theorem cubeLpENorm_hshellFlux_jac [NeZero d] (nu : ℝ) (P : ProbabilityMeasure (ShellSeq d))
    (m h : ℕ) (omega : ShellSeq d) (e : Vec d) (Q : TriadicCube d) (q : ℝ≥0∞) :
    SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q q (fun x => HilbertMat.ofMat
        (fun i j => fderiv ℝ (fun y => hshellFlux nu P m h omega e y i) x (basisVec j))) =
      ‖(sigmaBarInfinite nu (m - h) P)⁻¹‖ₑ *
        SuperdiffusionCLT.Section2.Norms.cubeLpENorm Q q (fun x => HilbertMat.ofMat
          (fun i j => streamFluxWeakGradient omega (m - h) m e i x j)) := by
  rw [← SuperdiffusionCLT.Section2.Norms.cubeLpENorm_const_smul]
  congr 1
  funext x
  ext i j
  simp [fderiv_hshellFlux_apply]

/-! ## The pointwise majorant of the Dirichlet Hessian -/

/-- **The Hessian of the Dirichlet response is dominated pointwise by the majorant**: the
a priori clause bounds any supplied weak Hessian by `C ‖∇ flux‖_{L̲⁸}`, and the Jacobian of the
flux is dominated by `shellJacMajorant`. -/
theorem hessian_le_majorant [NeZero d] (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (nu : ℝ), 0 < nu → ∀ (P : ProbabilityMeasure (ShellSeq d)),
        ShellLawPrefix d P → ShellLawJ2 d P → ShellLawJ3 d P → ShellLawJ4 d P →
        ∀ (m h Kc : ℕ) (e : Vec d)
          (wD : H10Function (openCubeSet (originCube d (Kc : ℤ))))
          (wN : H1MeanZeroFunction (openCubeSet (originCube d (Kc : ℤ))))
          (omega : ShellSeq d),
          IsCubeDirichletResponse (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) wD →
          IsCubeNeumannResponse (originCube d (Kc : ℤ)) (hshellFlux nu P m h omega e) wN →
          ∀ HD : HasWeakHessianOn (openCubeSet (originCube d (Kc : ℤ))) wD.toH1Function,
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 8
                (fun x => HilbertMat.ofMat (fun i j => HD.hess i j x)) ≤
              ENNReal.ofReal (C * (sigmaBarInfinite nu (m - h) P)⁻¹) *
                shellJacMajorant (originCube d (Kc : ℤ)) (m - h) m
                  (Real.sqrt d * vecNorm e) omega := by
  obtain ⟨Cap, hCapTop, hAp⟩ :=
    SuperdiffusionCLT.Frozen.Section3.responseFields_apriori_orderOne d hd
  refine ⟨Cap.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro nu hnu P hPre hJ2 hJ3 hJ4 m h Kc e wD wN omega hwD hwN HD
  have hσ : 0 < sigmaBarInfinite nu (m - h) P :=
    SuperdiffusionCLT.Section2.Annealed.sigmaBarInfinite_pos hnu (m - h) hPre hJ2 hJ3 hJ4
  set σi : ℝ := (sigmaBarInfinite nu (m - h) P)⁻¹ with hσi
  have hσinn : 0 ≤ σi := inv_nonneg.2 hσ.le
  have hab : m - h ≤ m := Nat.sub_le m h
  set DF : Fin d → Vec d → Vec d :=
    fun i x j => fderiv ℝ (fun y => hshellFlux nu P m h omega e y i) x (basisVec j) with hDF
  have hDFweak : ∀ i, HasWeakGradientOn (openCubeSet (originCube d (Kc : ℤ)))
      (fun x => hshellFlux nu P m h omega e x i) (DF i) := fun i =>
    HasWeakGradientOn.of_contDiff (contDiff_hshellFlux_apply nu P m h omega e i)
  have h1 := (hAp Kc (hshellFlux nu P m h omega e) wD wN hwD hwN).2.1 DF HD hDFweak
  have hcap : Cap * ENNReal.ofReal σi = ENNReal.ofReal (Cap.toReal * σi) := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hCapTop.ne]
  refine h1.trans ?_
  have hjac := cubeLpENorm_hshellFlux_jac nu P m h omega e (originCube d (Kc : ℤ)) 8
  rw [Real.enorm_eq_ofReal hσinn] at hjac
  have hDFeq : SuperdiffusionCLT.Section2.Norms.cubeLpENorm (originCube d (Kc : ℤ)) 8
      (fun x => HilbertMat.ofMat (fun i j => DF i x j)) =
      ENNReal.ofReal σi * SuperdiffusionCLT.Section2.Norms.cubeLpENorm
        (originCube d (Kc : ℤ)) 8 (fun x => HilbertMat.ofMat
          (fun i j => streamFluxWeakGradient omega (m - h) m e i x j)) := hjac
  rw [hDFeq, ← mul_assoc, hcap]
  exact mul_le_mul_right (cubeLpENorm_streamJac_le_majorant omega hab e _) _

end

end SuperdiffusionCLT.Section5
