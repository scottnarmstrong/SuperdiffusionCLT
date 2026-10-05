/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm1StepTwoOrderOne
public import SuperdiffusionCLT.Section3.Terms.RHSTerm3OscInputs
public import SuperdiffusionCLT.Sobolev.CubeSmoothDensityH2B

/-!
# The `H̲¹`/`Ĥ̲⁻¹` duality of `e.RHS.term3.B`

The first display of the
proof of `e.RHS.term3.B`:

```
\begin{multline*}
\fint_{z+\cu_n}
\bigl( \nabla w - (\nabla w )_{z+\cu_n} \bigr) \cdot \a_{L'} ( \nabla u_m - \nabla u_{n,z} )
\\
\leq
\bigl[ \nabla w - (\nabla w )_{z+\cu_n}   \bigr]_{\underline{H}^1(z+\cu_n)}
\| \a_{L'} ( \nabla u_m - \nabla u_{n,z} ) \|_{\Hminusul(z+\cu_n)}
\,.
\end{multline*}
```

**Which norms, and over which domain.**  Both sides are taken on the one
translated cube `z + cu_n`.  The left side is the normalized average over that
cube of the scalar pairing of the *centered* gradient `∇w − (∇w)_{z+cu_n}` with
the flux `a_{L'}(∇u_m − ∇u_{n,z})`.  The right side is the product of the
`H̲¹(z + cu_n)` size of the centered gradient with the hatted negative norm
`‖·‖_{Ĥ̲⁻¹(z + cu_n)}` (the macro `\Hminusul`) of the flux.  Note
that the printed first factor is a *seminorm* `[·]_{H̲¹}`, while the second is a
full norm; the pairing is against gradients.

**The pinned carrier.**  The reading of the second factor is fixed as follows:
on a vector field, `‖·‖_{Ĥ̲⁻¹(U)}` is the
*order-one* negative norm in the
scaled normalization — the supremum of `⨍_U F·∇g` over smooth mean-zero `g` with
`‖∇g‖_{L̲²(U)} + |U|^{1/d}‖∇²g‖_{L̲²(U)} ≤ 1`.  That is the carrier
`Section2.Norms.vecHatNegENormOrderOne`, whose test quantity is
`Section2.Norms.vecHatTestH1ENorm Q g = ‖∇g‖_{L̲²(Q)} + 3^{scale Q}‖∇²g‖_{L̲²(Q)}`.
Each negative norm is read as this full-norm/mean-zero-test
form; the order-zero carrier `Section3.ResponseFields.vecHatNegENorm` (test
`‖∇g‖_{L̲²} ≤ 1`) is superseded and is not used here.

The printed first factor reads in the scaled
convention as in Step 2 of `l.RHS.term1`, the same
duality: the dual partner of `‖F‖_{Ĥ̲⁻¹}` is the `H̲¹` size of the *potential*
whose gradient pairs with `F`.  At the centered potential `w − ℓ`, `∇ℓ =
(∇w)_{z+cu_n}`, this is

`[∇w − (∇w)_{z+cu_n}]_{H̲¹(z+cu_n)} = ‖∇w − (∇w)_{z+cu_n}‖_{L̲²(Q)}
+ 3^{scale Q}‖∇²w‖_{L̲²(Q)}`,

the coercive `3^{-scale Q}‖·‖_{L̲²}` summand of the full `H̲¹` norm being absent
because the print writes the seminorm.

## Main results

* `exists_centeredOrderOneTestPotential`: the smooth mean-zero order-one test
  potential attached to a *centered* gradient field.  For every `eps > 0` there
  is a smooth mean-zero `g` with
  `vecHatTestH1ENorm Q g ≤ ‖∇a − (∇a)_Q‖_{L̲²(Q)} + 3^{scale Q}‖H‖_{L̲²(Q)}
  + (1 + 3^{scale Q}) eps` and `‖(∇a − (∇a)_Q) − ∇g‖_{L̲²(Q)} ≤ eps`.  This is
  the density input the order-one duality needs; it is *proved*, not carried.

## The gap this exposes

The `_hCS` binder of the term-3.B assembly bounds the same pairing
by the `L̲²` size of the centered gradient times the flux negative norm, i.e. by
the `L̲²` summand *alone*.  The duality proved here
carries the second summand `3^{scale R}‖∇²w‖_{L̲²(R)}` as well, so the
constant of the duality display is at least the `L̲²` summand.  Reading the printed
first factor as the `L̲²` summand alone would
therefore *strictly strengthen* the printed display at the pinned carrier, and
that strengthening is not proved here; the `_hCS` binder is left as it
stands.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section3.ResponseFields
open scoped ENNReal
open SuperdiffusionCLT.Section2.Norms
  (euclideanGradientJacobian)

noncomputable section

variable {d : ℕ}

/-! ## Shifting a smoothing by a linear potential -/

/-- The Euclidean gradient is unchanged by a constant vertical shift. -/
theorem euclideanGradient_sub_const' {h : Vec d → ℝ} (κ : ℝ) :
    euclideanGradient (fun x => h x - κ) = euclideanGradient h := by
  funext x i
  simp only [euclideanGradient, euclideanCoordDeriv]
  rw [fderiv_sub_const]

/-- Subtracting the linear potential `x ↦ c·x` and a constant shifts the
gradient by `c` and leaves everything else alone. -/
theorem euclideanGradient_sub_vecDot_sub_const {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (c : Vec d) (κ : ℝ) :
    euclideanGradient (fun x => g x - vecDot c x - κ)
      = fun x => euclideanGradient g x - c := by
  rw [euclideanGradient_sub_const' κ, euclideanGradient_sub_vecDot_const hg c]

/-- The Jacobian of the gradient is unchanged by the shift
`g ↦ g − c·x − κ`: the shifted gradient differs from `∇g` by the constant `c`,
whose Jacobian vanishes. -/
theorem euclideanGradientJacobian_sub_vecDot_sub_const {g : Vec d → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (c : Vec d) (κ : ℝ) :
    euclideanGradientJacobian (fun x => g x - vecDot c x - κ)
      = euclideanGradientJacobian g := by
  funext x i j
  have hrow : (fun y : Vec d => euclideanGradient (fun z => g z - vecDot c z - κ) y i)
      = fun y : Vec d => euclideanGradient g y i - c i := by
    funext y
    rw [euclideanGradient_sub_vecDot_sub_const hg c κ]
    rfl
  show euclideanCoordDeriv j
      (fun y : Vec d => euclideanGradient (fun z => g z - vecDot c z - κ) y i) x
    = euclideanCoordDeriv j (fun y : Vec d => euclideanGradient g y i) x
  rw [hrow]
  simp only [euclideanCoordDeriv, fderiv_sub_const]

/-! ## Private helpers -/

private theorem threePowScalePos (Q : TriadicCube d) :
    (0 : ℝ) < (3 : ℝ) ^ ((Q.scale : ℝ)) :=
  Real.rpow_pos_of_pos (by norm_num) _

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

private theorem matrixFrobeniusMagnitudeSubEqNorm (M N : Mat d) :
    matrixFrobeniusMagnitude (fun i j => M i j - N i j)
      = ‖HilbertMat.ofMat M - HilbertMat.ofMat N‖ := by
  refine (matrixFrobeniusMagnitude_eq_norm_hilbertMat_ofMat _).trans ?_
  congr 1

/-! ## The smooth order-one test potential of a centered gradient -/

/-- **The smooth order-one test potential attached to a centered gradient.**

An `H¹` function `a` on the interior of a triadic cube carrying a weak Hessian
`H` has, for every `eps > 0`, a smooth mean-zero potential `g` with

`‖∇g‖_{L̲²(Q)} + 3^{scale Q}‖∇²g‖_{L̲²(Q)} ≤
  ‖∇a − (∇a)_Q‖_{L̲²(Q)} + 3^{scale Q}‖H‖_{L̲²(Q)} + (1 + 3^{scale Q}) eps`

and `‖(∇a − (∇a)_Q) − ∇g‖_{L̲²(Q)} ≤ eps`.  The approximants are the mean-zero
convex smoothings of `Sobolev.exists_cubeH2MeanZeroSmoothApprox`, shifted by the
linear potential `x ↦ (∇a)_Q·x` (which moves the gradient and nothing else) and
re-centered.  Nothing is carried. -/
theorem exists_centeredOrderOneTestPotential {Q : TriadicCube d}
    {a : H1Function (openCubeSet Q)} (H : HasWeakHessianOn (openCubeSet Q) a)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ g : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ volumeAverage (cubeSet Q) g = 0 ∧
      Section2.Norms.vecHatTestH1ENorm Q g ≤
        ENNReal.ofReal ((vecCubeLpENorm Q 2
            (fun x => a.grad x - volumeAverageVec (openCubeSet Q) a.grad)).toReal +
          (3 : ℝ) ^ ((Q.scale : ℝ)) * (Section2.Norms.cubeLpENorm Q 2
            (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))).toReal +
          (1 + (3 : ℝ) ^ ((Q.scale : ℝ))) * eps) ∧
      vecCubeLpENorm Q 2 (fun x =>
          (a.grad x - volumeAverageVec (openCubeSet Q) a.grad)
            - euclideanGradient g x) ≤ ENNReal.ofReal eps := by
  obtain ⟨g₀, hg₀c, hg₀mean, hg₀close, hg₀jac⟩ :=
    Sobolev.exists_cubeH2MeanZeroSmoothApprox H eps heps
  rw [vecGradient_eq_euclideanGradient] at hg₀close hg₀jac
  set c : Vec d := volumeAverageVec (openCubeSet Q) a.grad with hcdef
  set A : ℝ := (vecCubeLpENorm Q 2 (fun x => a.grad x - c)).toReal with hAdef
  set B : ℝ := (Section2.Norms.cubeLpENorm Q 2
    (fun x => HilbertMat.ofMat (fun i j => H.hess i j x))).toReal with hBdef
  have hcmem : MemLp (hilbertifyVecField (fun x => a.grad x - c)) 2
      (normalizedCubeMeasure Q) := memLp_hilbertifyVecField_grad_sub_const a c
  have hHmem := memLpHessianHilbertMat Q H
  have hAmem := memLpTwoHilbertify a.grad_memVectorL2
  have hA0 : (0 : ℝ) ≤ A := ENNReal.toReal_nonneg
  have hB0 : (0 : ℝ) ≤ B := ENNReal.toReal_nonneg
  have hsc0 : (0 : ℝ) ≤ (3 : ℝ) ^ ((Q.scale : ℝ)) := (threePowScalePos Q).le
  have hAval : vecCubeLpENorm Q 2 (fun x => a.grad x - c) = ENNReal.ofReal A :=
    (ENNReal.ofReal_toReal hcmem.eLpNorm_lt_top.ne).symm
  have hBval : Section2.Norms.cubeLpENorm Q 2
      (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) = ENNReal.ofReal B :=
    (ENNReal.ofReal_toReal hHmem.eLpNorm_lt_top.ne).symm
  have hDmem : MemLp (hilbertifyVecField
      (fun x => euclideanGradient g₀ x - a.grad x)) 2 (normalizedCubeMeasure Q) := by
    exact lt_of_le_of_lt hg₀close ENNReal.ofReal_lt_top
  -- the gradient half of the level, at the centered field
  have hgrad : vecCubeLpENorm Q 2 (fun x => euclideanGradient g₀ x - c) ≤
      vecCubeLpENorm Q 2 (fun x => a.grad x - c) + ENNReal.ofReal eps := by
    have htri := vecCubeLpENorm_add_le (Q := Q) (q := 2)
      (F := fun x => euclideanGradient g₀ x - a.grad x) (G := fun x => a.grad x - c)
      (by norm_num) hDmem.aestronglyMeasurable hcmem.aestronglyMeasurable
    calc vecCubeLpENorm Q 2 (fun x => euclideanGradient g₀ x - c)
        = vecCubeLpENorm Q 2
            (fun x => (euclideanGradient g₀ x - a.grad x) + (a.grad x - c)) := by
          congr 1
          funext x i
          show euclideanGradient g₀ x i - c i
            = (euclideanGradient g₀ x i - a.grad x i) + (a.grad x i - c i)
          ring
      _ ≤ vecCubeLpENorm Q 2 (fun x => euclideanGradient g₀ x - a.grad x) +
            vecCubeLpENorm Q 2 (fun x => a.grad x - c) := htri
      _ ≤ ENNReal.ofReal eps + vecCubeLpENorm Q 2 (fun x => a.grad x - c) :=
          add_le_add hg₀close le_rfl
      _ = vecCubeLpENorm Q 2 (fun x => a.grad x - c) + ENNReal.ofReal eps := add_comm _ _
  -- the Hessian half of the level
  have hJm : MeasureTheory.AEStronglyMeasurable (fun x =>
      HilbertMat.ofMat (euclideanGradientJacobian g₀ x) -
        HilbertMat.ofMat (fun i j => H.hess i j x)) (normalizedCubeMeasure Q) :=
    ((SuperdiffusionCLT.Section2.Estimates.Stream.continuous_euclideanGradientJacobian
        hg₀c).aestronglyMeasurable).sub hHmem.aestronglyMeasurable
  have hjaceq : Section2.Norms.jacobianDistENorm Q (euclideanGradient g₀)
        (fun x i j => H.hess i j x) =
      Section2.Norms.cubeLpENorm Q 2 (fun x =>
        HilbertMat.ofMat (euclideanGradientJacobian g₀ x) -
          HilbertMat.ofMat (fun i j => H.hess i j x)) := by
    unfold Section2.Norms.jacobianDistENorm
    rw [Section2.Norms.cubeLpENorm,
      Section2.Norms.cubeLpENorm]
    have hpt : ∀ x, matrixFrobeniusMagnitude
        (fun i j => euclideanGradient (fun y => euclideanGradient g₀ y i) x j -
          H.hess i j x) = ‖HilbertMat.ofMat (euclideanGradientJacobian g₀ x) -
        HilbertMat.ofMat (fun i j => H.hess i j x)‖ := fun x =>
      matrixFrobeniusMagnitudeSubEqNorm
        (euclideanGradientJacobian g₀ x) (fun i j => H.hess i j x)
    have hfm : MeasureTheory.AEStronglyMeasurable (fun x => matrixFrobeniusMagnitude
        (fun i j => euclideanGradient (fun y => euclideanGradient g₀ y i) x j -
          H.hess i j x)) (normalizedCubeMeasure Q) := by
      have := hJm.norm
      simpa only [← hpt] using this
    refine eLpNorm_congr_norm_ae hfm hJm (ae_of_all _ fun x => ?_)
    refine (Real.norm_of_nonneg (matrixFrobeniusMagnitude_nonneg _)).trans ?_
    exact hpt x
  have hgjac' : Section2.Norms.cubeLpENorm Q 2 (fun x =>
      HilbertMat.ofMat (euclideanGradientJacobian g₀ x) -
        HilbertMat.ofMat (fun i j => H.hess i j x)) ≤ ENNReal.ofReal eps := by
    rw [← hjaceq]
    exact hg₀jac
  have hJmem : MemLp (fun x =>
      HilbertMat.ofMat (euclideanGradientJacobian g₀ x) -
        HilbertMat.ofMat (fun i j => H.hess i j x)) 2 (normalizedCubeMeasure Q) :=
    lt_of_le_of_lt hgjac' ENNReal.ofReal_lt_top
  have hjac : Section2.Norms.cubeLpENorm Q 2
        (fun x => HilbertMat.ofMat (euclideanGradientJacobian g₀ x)) ≤
      Section2.Norms.cubeLpENorm Q 2
          (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) +
        ENNReal.ofReal eps := by
    have htri := Section2.Norms.cubeLpENorm_add_le (Q := Q) (q := 2)
      (f := fun x => HilbertMat.ofMat (euclideanGradientJacobian g₀ x) -
        HilbertMat.ofMat (fun i j => H.hess i j x))
      (g := fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) (by norm_num)
      hJmem.aestronglyMeasurable hHmem.aestronglyMeasurable
    calc Section2.Norms.cubeLpENorm Q 2
          (fun x => HilbertMat.ofMat (euclideanGradientJacobian g₀ x))
        = Section2.Norms.cubeLpENorm Q 2 (fun x =>
            (HilbertMat.ofMat (euclideanGradientJacobian g₀ x) -
              HilbertMat.ofMat (fun i j => H.hess i j x)) +
              HilbertMat.ofMat (fun i j => H.hess i j x)) := by
          congr 1
          funext x
          abel
      _ ≤ Section2.Norms.cubeLpENorm Q 2 (fun x =>
              HilbertMat.ofMat (euclideanGradientJacobian g₀ x) -
                HilbertMat.ofMat (fun i j => H.hess i j x)) +
            Section2.Norms.cubeLpENorm Q 2
              (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) := htri
      _ ≤ ENNReal.ofReal eps + Section2.Norms.cubeLpENorm Q 2
              (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) :=
          add_le_add hgjac' le_rfl
      _ = Section2.Norms.cubeLpENorm Q 2
              (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) +
            ENNReal.ofReal eps := add_comm _ _
  set κ : ℝ := volumeAverage (cubeSet Q) (fun x => g₀ x - vecDot c x) with hκdef
  refine ⟨fun x => g₀ x - vecDot c x - κ, ?_, ?_, ?_, ?_⟩
  · exact (hg₀c.sub (contDiff_vecDot_const c)).sub contDiff_const
  · rw [hκdef]
    exact volumeAverage_sub_self_eq_zero Q
      ((hg₀c.sub (contDiff_vecDot_const c)).continuous)
  · rw [Section2.Norms.vecHatTestH1ENorm,
      euclideanGradient_sub_vecDot_sub_const hg₀c c κ,
      euclideanGradientJacobian_sub_vecDot_sub_const hg₀c c κ]
    refine le_trans (add_le_add hgrad (mul_le_mul' le_rfl hjac)) (le_of_eq ?_)
    rw [hAval, hBval, ← ENNReal.ofReal_add hA0 heps.le,
      ← ENNReal.ofReal_add hB0 heps.le, ← ENNReal.ofReal_mul hsc0,
      ← ENNReal.ofReal_add (by linarith only [hA0, heps.le])
        (mul_nonneg hsc0 (by linarith only [hB0, heps.le]))]
    congr 1
    ring
  · have hneg : (fun x => (a.grad x - c) - euclideanGradient (fun y => g₀ y - vecDot c y - κ) x)
        = fun x => -(euclideanGradient g₀ x - a.grad x) := by
      funext x
      funext i
      rw [euclideanGradient_sub_vecDot_sub_const hg₀c c κ]
      show (a.grad x - c) i - (euclideanGradient g₀ x - c) i
        = -(euclideanGradient g₀ x - a.grad x) i
      simp only [Pi.sub_apply]
      ring
    rw [hneg, vecCubeLpENorm_neg]
    exact hg₀close

end

end SuperdiffusionCLT.Section3.Terms
