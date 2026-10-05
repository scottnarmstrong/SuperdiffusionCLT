/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellHminusEndpointOrderOneB
public import SuperdiffusionCLT.Sobolev.CubeSmoothDensityH2B
public import SuperdiffusionCLT.Section3.Terms.RHSTerm1InputsF

/-!
# Step 2 of `l.RHS.term1` in the order-one hatted carrier

Step 2 of the proof of `l.RHS.term1`, in the **order-one** carrier
`Section2.Norms.vecHatNegENormOrderOne` and in the scaled normalization: the printed left factor
`‖∇w‖_{H̲¹(cu_m)}` becomes `‖∇w‖_{L̲²(cu_m)} + 3^m‖∇²w‖_{L̲²(cu_m)}` and the printed
`Ĥ̲^{-1}` norm becomes `3^{-m}` times its un-normalized value, so the factor `3^m`
cancels in the product and the printed rate is unchanged.

Two defective inputs of the order-zero plumbing disappear.
The order-zero duality bridge needs `hH1Dominates`
(`‖∇w‖_{L̲²(cu_m)} ≤ ‖∇w‖_{H̲¹(cu_m)}`), false at the printed normalization;
`duality_bridge` needs nothing of the sort, because the printed left factor
*is* the admissible test level of the smooth approximants of `∇w`.  And `hConc`,
the printed multiscale line, is proved here in the honest `ℓ¹` form
rather than carried; only the per-scale
concentration line stays a hypothesis.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open scoped ENNReal
open SuperdiffusionCLT.Section2.Norms
  (euclideanGradientJacobian vecHatTestH1ENorm vecHatNegENormOrderOne)

noncomputable section

variable {d : ℕ}

/-! ## Cube-level memberships -/

private theorem memLpTwoHilbertify {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) :
    MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q) := by
  rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
  exact (memHilbertVectorL2_hilbertifyVecField hF).smul_measure ENNReal.ofReal_ne_top

private theorem memLpHessianHilbertMat (Q : TriadicCube d)
    {v : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) v) :
    MemLp (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) 2
      (normalizedCubeMeasure Q) := by
  rw [MeasureTheory.memLp_piLp_iff]
  intro i
  rw [MeasureTheory.memLp_piLp_iff]
  intro j
  simpa only [Function.comp_apply, HilbertMat.ofMat, HilbertVec.ofVec,
    PiLp.toLp_apply] using H.hess_memLp_normalizedCubeMeasure Q i j

private theorem threePowScalePos (Q : TriadicCube d) :
    (0 : ℝ) < (3 : ℝ) ^ ((Q.scale : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _

/-! ## The smooth order-one test potential of a response field -/

private theorem matrixFrobeniusMagnitudeSubEqNorm (M N : Mat d) :
    matrixFrobeniusMagnitude (fun i j => M i j - N i j)
      = ‖HilbertMat.ofMat M - HilbertMat.ofMat N‖ := by
  refine (matrixFrobeniusMagnitude_eq_norm_hilbertMat_ofMat _).trans ?_
  congr 1

/-- **The smooth order-one test potential attached to a response field.**

An `H¹` function `a` on the interior of a triadic cube carrying a weak Hessian
`H` has, for every `eps > 0`, a smooth mean-zero potential `g` with

`‖∇g‖_{L̲²(Q)} + 3^{scale Q}‖∇²g‖_{L̲²(Q)} ≤
  ‖∇a‖_{L̲²(Q)} + 3^{scale Q}‖H‖_{L̲²(Q)} + (1 + 3^{scale Q}) eps`

and `‖∇a − ∇g‖_{L̲²(Q)} ≤ eps`: `g` is admissible for `vecHatNegENormOrderOne Q` at a
level converging to the printed left factor of the duality display, while its
gradient converges to `∇a` in `L̲²(Q)`.  Nothing is carried: the approximants are
the mean-zero convex smoothings of `Sobolev.exists_cubeH2MeanZeroSmoothApprox`,
and the two triangle inequalities turn their two convergences into the level. -/
theorem exists_orderOneTestPotential_of_weakHessian {Q : TriadicCube d}
    {a : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) a)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ g : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ volumeAverage (cubeSet Q) g = 0 ∧
      vecHatTestH1ENorm Q g ≤
        ENNReal.ofReal ((vecCubeLpENorm Q 2 a.grad).toReal +
          (3 : ℝ) ^ ((Q.scale : ℝ)) * (Section2.Norms.cubeLpENorm Q 2
            (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))).toReal +
          (1 + (3 : ℝ) ^ ((Q.scale : ℝ))) * eps) ∧
      vecCubeLpENorm Q 2 (fun x => a.grad x - euclideanGradient g x) ≤
        ENNReal.ofReal eps := by
  obtain ⟨g, hgc, hgmean, hgclose, hgjac⟩ :=
    Sobolev.exists_cubeH2MeanZeroSmoothApprox H eps heps
  rw [Section2.Norms.vecGradient_eq_euclideanGradient] at hgclose hgjac
  have hAmem : MemLp (hilbertifyVecField a.grad) 2 (normalizedCubeMeasure Q) :=
    memLpTwoHilbertify a.grad_memVectorL2
  have hHmem := memLpHessianHilbertMat Q H
  have hEcont : Continuous (hilbertifyVecField (euclideanGradient g)) :=
    continuous_hilbertifyVecField (continuous_euclideanGradient' hgc)
  have hDmem : MemLp (hilbertifyVecField (fun x => euclideanGradient g x - a.grad x))
      2 (normalizedCubeMeasure Q) := by
    exact lt_of_le_of_lt hgclose ENNReal.ofReal_lt_top
  -- the gradient half of the level
  have hgrad : vecCubeLpENorm Q 2 (euclideanGradient g) ≤
      vecCubeLpENorm Q 2 a.grad + ENNReal.ofReal eps := by
    have heq : (fun x => (euclideanGradient g x - a.grad x) + a.grad x)
        = euclideanGradient g := by
      funext x
      funext i
      show (euclideanGradient g x i - a.grad x i) + a.grad x i = euclideanGradient g x i
      ring
    have htri := vecCubeLpENorm_add_le (Q := Q) (q := 2)
      (F := fun x => euclideanGradient g x - a.grad x) (G := a.grad) (by norm_num)
      hDmem.aestronglyMeasurable hAmem.aestronglyMeasurable
    rw [heq] at htri
    exact le_trans htri (le_trans (le_of_eq (add_comm _ _)) (add_le_add le_rfl hgclose))
  -- the Hessian half of the level
  have hjaceq : Section2.Norms.jacobianDistENorm Q (euclideanGradient g)
        (fun x i j => H.hess i j x) =
      Section2.Norms.cubeLpENorm Q 2 (fun x =>
        HilbertMat.ofMat (euclideanGradientJacobian g x) -
          HilbertMat.ofMat (fun i j => H.hess i j x)) := by
    unfold Section2.Norms.jacobianDistENorm
    unfold Section2.Norms.cubeLpENorm
    have hRm : AEStronglyMeasurable (fun x =>
        HilbertMat.ofMat (euclideanGradientJacobian g x) -
          HilbertMat.ofMat (fun i j => H.hess i j x)) (normalizedCubeMeasure Q) :=
      ((continuous_euclideanGradientJacobian hgc).aestronglyMeasurable).sub
        hHmem.aestronglyMeasurable
    have hpt : ∀ x, matrixFrobeniusMagnitude (fun i j =>
        euclideanGradient (fun y => (euclideanGradient g y) i) x j - H.hess i j x) =
        ‖HilbertMat.ofMat (euclideanGradientJacobian g x) -
          HilbertMat.ofMat (fun i j => H.hess i j x)‖ := fun x =>
      matrixFrobeniusMagnitudeSubEqNorm
        (euclideanGradientJacobian g x) (fun i j => H.hess i j x)
    refine eLpNorm_congr_norm_ae ?_ hRm (ae_of_all _ fun x => ?_)
    · have h2 := hRm.norm
      refine h2.congr (ae_of_all _ fun x => ?_)
      exact (hpt x).symm
    · rw [Real.norm_eq_abs]
      exact (abs_of_nonneg (matrixFrobeniusMagnitude_nonneg _)).trans (hpt x)
  have hgjac' : Section2.Norms.cubeLpENorm Q 2 (fun x =>
      HilbertMat.ofMat (euclideanGradientJacobian g x) -
        HilbertMat.ofMat (fun i j => H.hess i j x)) ≤ ENNReal.ofReal eps := by
    rw [← hjaceq]
    exact hgjac
  have hJmem : MemLp (fun x =>
      HilbertMat.ofMat (euclideanGradientJacobian g x) -
        HilbertMat.ofMat (fun i j => H.hess i j x)) 2 (normalizedCubeMeasure Q) :=
    lt_of_le_of_lt hgjac' ENNReal.ofReal_lt_top
  have hjac : Section2.Norms.cubeLpENorm Q 2
        (fun x => HilbertMat.ofMat (euclideanGradientJacobian g x)) ≤
      Section2.Norms.cubeLpENorm Q 2
          (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) +
        ENNReal.ofReal eps := by
    have heq : ((fun x =>
          HilbertMat.ofMat (euclideanGradientJacobian g x) -
            HilbertMat.ofMat (fun i j => H.hess i j x)) +
        fun x => HilbertMat.ofMat (fun i j => H.hess i j x))
        = fun x => HilbertMat.ofMat (euclideanGradientJacobian g x) := by
      funext x
      show (HilbertMat.ofMat (euclideanGradientJacobian g x) -
        HilbertMat.ofMat (fun i j => H.hess i j x)) +
          HilbertMat.ofMat (fun i j => H.hess i j x) = _
      abel
    have htri := Section2.Norms.cubeLpENorm_add_le (Q := Q) (q := 2)
      (f := fun x => HilbertMat.ofMat (euclideanGradientJacobian g x) -
        HilbertMat.ofMat (fun i j => H.hess i j x))
      (g := fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) (by norm_num)
      hJmem.aestronglyMeasurable hHmem.aestronglyMeasurable
    rw [heq] at htri
    exact le_trans htri (le_trans (le_of_eq (add_comm _ _)) (add_le_add le_rfl hgjac'))
  -- assembling the level
  have hAfin : vecCubeLpENorm Q 2 a.grad ≠ ⊤ := hAmem.eLpNorm_lt_top.ne
  have hHfin : Section2.Norms.cubeLpENorm Q 2
      (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) ≠ ⊤ :=
    hHmem.eLpNorm_lt_top.ne
  have hsc : (0 : ℝ) ≤ (3 : ℝ) ^ ((Q.scale : ℝ)) := (threePowScalePos Q).le
  set A : ℝ := (vecCubeLpENorm Q 2 a.grad).toReal with hAdef
  set B : ℝ := (Section2.Norms.cubeLpENorm Q 2
    (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))).toReal with hBdef
  have hA0 : (0 : ℝ) ≤ A := ENNReal.toReal_nonneg
  have hB0 : (0 : ℝ) ≤ B := ENNReal.toReal_nonneg
  have hAval : vecCubeLpENorm Q 2 a.grad = ENNReal.ofReal A :=
    (ENNReal.ofReal_toReal hAfin).symm
  have hBval : Section2.Norms.cubeLpENorm Q 2
      (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) = ENNReal.ofReal B :=
    (ENNReal.ofReal_toReal hHfin).symm
  refine ⟨g, hgc, by rw [volumeAverage_cubeSet_eq_cubeAverage, hgmean], ?_, ?_⟩
  · rw [Section2.Norms.vecHatTestH1ENorm]
    refine le_trans (add_le_add hgrad (mul_le_mul' le_rfl hjac)) (le_of_eq ?_)
    rw [hAval, hBval, ← ENNReal.ofReal_add hA0 heps.le,
      ← ENNReal.ofReal_add hB0 heps.le, ← ENNReal.ofReal_mul hsc,
      ← ENNReal.ofReal_add (by linarith only [hA0, heps.le])
        (mul_nonneg hsc (by linarith only [hB0, heps.le]))]
    congr 1
    ring
  · have hneg : (fun x => a.grad x - euclideanGradient g x)
        = fun x => -(euclideanGradient g x - a.grad x) := by
      funext x
      funext i
      show a.grad x i - euclideanGradient g x i = -(euclideanGradient g x i - a.grad x i)
      ring
    rw [hneg, vecCubeLpENorm_neg]
    exact hgclose

/-! ## The duality display of Step 2 -/

/-- **The Step-2 duality display, in the order-one carrier.**

`|⨍_Q ∇w·F| ≤ (‖∇w‖_{L̲²(Q)} + 3^{scale Q}‖∇²w‖_{L̲²(Q)}) ‖F‖_{Ĥ̲^{-1}(Q)}`,

the printed duality display of Step 2 in the scaled normalization;
the left factor is `3^{scale Q}‖∇w‖_{H̲¹(Q)}` for the `H̲¹` carrier
`RHSTerm1Inputs.vecCubeH1ENorm`.

The only hypotheses are the `L̲²(Q)` membership of `F` — the standing
integrability datum of the duality — and the weak Hessian of the response.  In
particular the `hH1Dominates` hypothesis of the order-zero duality bridge is gone: at the
order-one test class the printed left factor *is* the admissible level of the
smooth approximants of `∇w`, so no comparison between `‖∇w‖_{L̲²}` and
`‖∇w‖_{H̲¹}` is needed. -/
theorem ofReal_abs_volumeAverage_vecDot_grad_le {Q : TriadicCube d}
    {F : Vec d → Vec d}
    (hF : MemLp (hilbertifyVecField F) 2 (normalizedCubeMeasure Q))
    {a : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) a) :
    ENNReal.ofReal |volumeAverage (openCubeSet Q)
        (fun x => vecDot (a.grad x) (F x))| ≤
      ENNReal.ofReal ((3 : ℝ) ^ ((Q.scale : ℝ))) *
          vecCubeH1ENorm Q a.grad (fun x => fun i j => H.hess i j x) *
        vecHatNegENormOrderOne Q F := by
  classical
  have hGmem : MemLp (hilbertifyVecField a.grad) 2 (normalizedCubeMeasure Q) :=
    memLpTwoHilbertify a.grad_memVectorL2
  have hHmem := memLpHessianHilbertMat Q H
  have hsc : (0 : ℝ) < (3 : ℝ) ^ ((Q.scale : ℝ)) := threePowScalePos Q
  set A : ℝ := (vecCubeLpENorm Q 2 a.grad).toReal with hAdef
  set B : ℝ := (Section2.Norms.cubeLpENorm Q 2
    (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))).toReal with hBdef
  have hA0 : (0 : ℝ) ≤ A := ENNReal.toReal_nonneg
  have hB0 : (0 : ℝ) ≤ B := ENNReal.toReal_nonneg
  have hAval : vecCubeLpENorm Q 2 a.grad = ENNReal.ofReal A :=
    (ENNReal.ofReal_toReal hGmem.eLpNorm_lt_top.ne).symm
  have hBval : Section2.Norms.cubeLpENorm Q 2
      (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) = ENNReal.ofReal B :=
    (ENNReal.ofReal_toReal hHmem.eLpNorm_lt_top.ne).symm
  -- the left factor, in real form
  have hleft : ENNReal.ofReal ((3 : ℝ) ^ ((Q.scale : ℝ))) *
      vecCubeH1ENorm Q a.grad (fun x => fun i j => H.hess i j x) =
      ENNReal.ofReal (A + (3 : ℝ) ^ ((Q.scale : ℝ)) * B) := by
    erw [vecCubeH1ENorm_eq]
    rw [hAval, hBval, mul_add, ← mul_assoc,
      ← ENNReal.ofReal_mul hsc.le, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      add_neg_cancel, Real.rpow_zero, ENNReal.ofReal_one, one_mul,
      ← ENNReal.ofReal_mul hsc.le, ← ENNReal.ofReal_add hA0
        (mul_nonneg hsc.le hB0)]
  -- the hatted norm is finite
  have hVne : vecHatNegENormOrderOne Q F ≠ ⊤ :=
    ne_top_of_le_ne_top hF.eLpNorm_lt_top.ne
      (Section2.Norms.vecHatNegENormOrderOne_le_vecCubeLpENorm hF)
  set Vr : ℝ := (vecHatNegENormOrderOne Q F).toReal with hVrdef
  have hVr0 : (0 : ℝ) ≤ Vr := ENNReal.toReal_nonneg
  have hVval : vecHatNegENormOrderOne Q F = ENNReal.ofReal Vr :=
    (ENNReal.ofReal_toReal hVne).symm
  -- the pairing, on the closed cube and in the order of the supremum
  have hswap : (fun x : Vec d => vecDot (a.grad x) (F x))
      = fun x : Vec d => vecDot (F x) (a.grad x) :=
    funext fun x => vecDot_comm _ _
  -- the estimate at every positive slack, then the limit
  have hreal : |volumeAverage (cubeSet Q) (fun x => vecDot (F x) (a.grad x))| ≤
      (A + (3 : ℝ) ^ ((Q.scale : ℝ)) * B) * Vr := by
    refine le_of_forall_pos_le_add fun delta hdelta => ?_
    have hone : (0 : ℝ) < 1 + (3 : ℝ) ^ ((Q.scale : ℝ)) := by linarith only [hsc]
    set c : ℝ := A + (3 : ℝ) ^ ((Q.scale : ℝ)) * B + delta / (Vr + 1) with hcdef
    have hc : (0 : ℝ) < c := by
      have h1 : (0 : ℝ) < delta / (Vr + 1) := by positivity
      have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ ((Q.scale : ℝ)) * B := mul_nonneg hsc.le hB0
      rw [hcdef]; linarith only [hA0, h1, h2]
    have hDense : ∀ eps : ℝ, 0 < eps → ∃ g : Vec d → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) g ∧ volumeAverage (cubeSet Q) g = 0 ∧
          vecHatTestH1ENorm Q g ≤ ENNReal.ofReal c ∧
          vecCubeLpENorm Q 2 (fun x => a.grad x - euclideanGradient g x) ≤
            ENNReal.ofReal eps := by
      intro eps heps
      have hstep : (0 : ℝ) < min eps (delta / (Vr + 1) / (1 + (3 : ℝ) ^ ((Q.scale : ℝ)))) :=
        lt_min heps (by positivity)
      obtain ⟨g, hgc, hgm, hglev, hgcl⟩ :=
        exists_orderOneTestPotential_of_weakHessian H hstep
      refine ⟨g, hgc, hgm, le_trans hglev (ENNReal.ofReal_le_ofReal ?_),
        le_trans hgcl (ENNReal.ofReal_le_ofReal (min_le_left _ _))⟩
      have hmin : min eps (delta / (Vr + 1) / (1 + (3 : ℝ) ^ ((Q.scale : ℝ)))) ≤
          delta / (Vr + 1) / (1 + (3 : ℝ) ^ ((Q.scale : ℝ))) := min_le_right _ _
      have hmul := mul_le_mul_of_nonneg_left hmin hone.le
      rw [mul_div_cancel₀ _ hone.ne'] at hmul
      rw [hcdef]
      linarith only [hmul]
    have hkey := Section2.Norms.ofReal_abs_volumeAverage_vecDot_le_vecHatNegENormOrderOne_mul
      hc hF hGmem hDense
    rw [hVval, ← ENNReal.ofReal_mul hc.le] at hkey
    have hreal' : |volumeAverage (cubeSet Q) (fun x => vecDot (F x) (a.grad x))| ≤
        c * Vr := by
      refine (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hkey
    have hexp : c * Vr = (A + (3 : ℝ) ^ ((Q.scale : ℝ)) * B) * Vr +
        delta / (Vr + 1) * Vr := by rw [hcdef]; ring
    have hsmall : delta / (Vr + 1) * Vr ≤ delta := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith only [hdelta.le, hVr0]
    linarith only [hreal', hexp, hsmall]
  rw [hleft, hVval, ← ENNReal.ofReal_mul (by positivity),
    ← volumeAverage_cubeSet_eq_openCubeSet, hswap]
  exact ENNReal.ofReal_le_ofReal hreal

/-! ## `hDuality` in its exact shape -/

private theorem threePowOriginCubeScale (d k : ℕ) :
    (3 : ℝ) ^ (((originCube d (k : ℤ)).scale : ℝ)) = (3 : ℝ) ^ ((k : ℝ)) := by
  show (3 : ℝ) ^ ((((k : ℤ)) : ℝ)) = (3 : ℝ) ^ ((k : ℝ))
  norm_num

/-- **`hDuality` of the second-step decomposition, in its exact shape.**

`|⨍_{cu_m} ∇w·(a_ℓ∇ũ_n − q̃)| ≤
  (3^m ‖∇w‖_{H̲¹(cu_m)}) ‖a_ℓ∇ũ_n − q̃‖_{Ĥ̲^{-1}(cu_m)}`

in the order-one carrier, for every sample.  The two inputs are the weak Hessian
`HD` of the response (with its Jacobian slot pinned by `hJac`) and the
`L̲²(cu_m)` membership `hMemLp` of the localized centred flux.  The defective
input `hH1Dominates` of the order-zero duality bridge is gone. -/
theorem duality_bridge (nu : ℝ) (S : ScaleSelection)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (HD : ∀ omega : ShellSeq d,
      HasWeakHessianOn (openCubeSet (originCube d (S.m : ℤ)))
        (w omega).toH1Function)
    (uTildeGlued : ShellSeq d → Vec d → Vec d) (qTilde : Vec d)
    (JacGradW : ShellSeq d → Vec d → Mat d)
    (hJac : JacGradW =
      fun omega => fun x : Vec d => ((fun i j => (HD omega).hess i j x) : Mat d))
    (hMemLp : ∀ omega : ShellSeq d,
      MemLp (hilbertifyVecField (fun x =>
          matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (uTildeGlued omega x) - qTilde)) 2
        (normalizedCubeMeasure (originCube d (S.m : ℤ)))) :
    ∀ omega : ShellSeq d,
      ENNReal.ofReal |volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot ((w omega).toH1Function.grad x)
            (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                (uTildeGlued omega x) - qTilde))| ≤
        ENNReal.ofReal ((3 : ℝ) ^ ((S.m : ℝ))) *
            vecCubeH1ENorm (originCube d (S.m : ℤ))
              (w omega).toH1Function.grad (JacGradW omega) *
          vecHatNegENormOrderOne (originCube d (S.m : ℤ))
            (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (uTildeGlued omega x) - qTilde) := by
  subst hJac
  intro omega
  have h := ofReal_abs_volumeAverage_vecDot_grad_le (hMemLp omega) (HD omega)
  rwa [threePowOriginCubeScale] at h

/-! ## The second display of Step 2, in the scaled carrier -/

/-! ## The multiscale decomposition of the third display of Step 2 -/

/-! ## Elementary passages used by the assembled Step-2 node -/

/-- The absolute value of a real Bochner integral is at most the truncated
Lebesgue integral of the absolute value. -/
theorem abs_integral_le_toReal_lintegral_abs {alpha : Type*} [MeasurableSpace alpha]
    {mu : Measure alpha} {f : alpha → ℝ} :
    |∫ x, f x ∂mu| ≤ (∫⁻ x, ENNReal.ofReal |f x| ∂mu).toReal := by
  by_cases hint : MeasureTheory.Integrable f mu
  · have h2 : ∫ x, |f x| ∂mu = (∫⁻ x, ENNReal.ofReal |f x| ∂mu).toReal :=
      integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
        hint.abs.aestronglyMeasurable
    exact h2 ▸ abs_integral_le_integral_abs
  · rw [integral_undef hint]
    simp

end

end SuperdiffusionCLT.Section3.Terms
