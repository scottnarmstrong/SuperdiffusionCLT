/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.HminusOneOrderOne

/-!
# The order-one `Ĥ̲^{-1}` estimate of Step 4, and the order-one a priori bound

`HminusOneOrderOne.lean` produces, for a mean-zero `L̲²` datum `z` on `cu_M`, the
pair `(ψ, θ)` of cube Poisson potentials with their gradient and Hessian bounds.
This module pairs the harmonic-part gradient `∇ψ − ∇θ` with the flux through the
order-one duality of
`SuperdiffusionCLT.Section2.Norms.vecHatNegENormOrderOne` and delivers

`3^{-M}‖v − (v)_{cu_M}‖_{L̲²(cu_M)} ≤ C(d) ‖G‖_{Ĥ̲^{-1}(cu_M)}`,

the first of the two standard estimates of Step 4 of the proof of
`l.abstract.response.fields`, in the order-one carrier.  That is the hypothesis
`hHm1` of `AprioriAssemblyC.lean`, so with `CHm`, `hCHm` and `hHm1`
removed the order-one a priori statement is `responseFields_apriori_orderOne_of_clauses`.

## The estimate

Write `u` for the prescribed-flux Neumann response of `G` and `w` for its
Dirichlet response, `v = u − w`, `z = v − (v)_{cu_M}`.  With `ψ` the mean-zero
Neumann potential of `z` and `θ` its zero-trace part,

`‖z‖²_{L̲²} = ⨍ ∇v·∇ψ = ⨍ ∇u·∇ψ − ⨍ ∇u·∇θ`,

the second step because `⨍ ∇v·∇θ = 0` (the difference of the two responses is
harmonic) and `⨍ ∇w·∇ψ = ⨍ ∇w·∇θ` (the defining equation of `θ`).  Both `ψ` and
`θ` are `H²` on the cube, so each is approximated in the order-one test class by
a smooth mean-zero potential `g` at the level
`‖∇ψ‖_{L̲²} + 3^M‖∇²ψ‖_{L̲²}`; the pairing `⨍ ∇u·∇g` equals `−⨍ G·∇g` by the
Neumann equation and is therefore at most that level times
`‖G‖_{Ĥ̲^{-1}(cu_M)}`.  The two approximation errors are paired against `∇u`
alone and disappear in the limit.  The cube bounds
`‖∇ψ‖_{L̲²} ≤ C 3^M‖z‖_{L̲²}` and `‖∇²ψ‖_{L̲²} ≤ C‖z‖_{L̲²}`, and the same two for
`θ`, turn the level into `C 3^M‖z‖_{L̲²}`, and dividing by `‖z‖_{L̲²}` gives the
display.

No integrability hypothesis on the flux `G` is needed anywhere: `G` is only ever
paired with a *smooth* test gradient, through
`volumeAverage_vecGradientPairingDensity_eq_of_isCubeNeumannResponse` and the
definition of `vecHatNegENormOrderOne`.

## Main results

* `hminusOneResponseConst`: the constant, explicit in `d`.
* `hminusOne_response_difference_bridge`: the display, in the exact shape of the
  `hHm1` binder of `AprioriAssemblyC.lean`.

-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section3
namespace ResponseFields

open Homogenization
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The pairing estimate at one approximation scale -/

/-- **The core of the order-one estimate.** If the squared `L̲²` size of the
response difference equals `⨍ ∇u·∇ψ − ⨍ ∇u·∇θ`, and if `∇ψ` and `∇θ` are each
approximated to within `eps` by a smooth order-one test gradient at the levels
`c₁` and `c₂`, then that squared size is at most `(c₁+c₂)‖G‖_{Ĥ̲^{-1}(Q)}` up to
`2‖∇u‖_{L̲²(Q)} eps`.  The two pairings against the smooth gradients pass through
the Neumann equation `hpair`, so no integrability of `G` is used. -/
private theorem sq_le_add_of_approx {Q : TriadicCube d} {G gu gp gt : Vec d → Vec d}
    (hpair : ∀ g : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
      volumeAverage (cubeSet Q) (vecGradientPairingDensity G g) =
        -volumeAverage (cubeSet Q)
          (fun x => vecDot (gu x) (euclideanGradient g x)))
    (hgu : MemLp (hilbertifyVecField gu) 2 (normalizedCubeMeasure Q))
    {n Vr c1 c2 eps : ℝ} (heps : 0 < eps) (hVr : 0 ≤ Vr)
    (hV : Section2.Norms.vecHatNegENormOrderOne Q G = ENNReal.ofReal Vr)
    (hn : n ^ 2 = volumeAverage (cubeSet Q) (fun x => vecDot (gu x) (gp x)) -
      volumeAverage (cubeSet Q) (fun x => vecDot (gu x) (gt x)))
    (happrox1 : ∃ g : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧
      volumeAverage (cubeSet Q) g = 0 ∧
      Section2.Norms.vecHatTestH1ENorm Q g ≤ ENNReal.ofReal c1 ∧
      MemLp (hilbertifyVecField (euclideanGradient g)) 2 (normalizedCubeMeasure Q) ∧
      MemLp (hilbertifyVecField (fun x => euclideanGradient g x - gp x)) 2
        (normalizedCubeMeasure Q) ∧
      vecCubeLpENorm Q 2 (fun x => euclideanGradient g x - gp x) ≤
        ENNReal.ofReal eps)
    (happrox2 : ∃ g : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧
      volumeAverage (cubeSet Q) g = 0 ∧
      Section2.Norms.vecHatTestH1ENorm Q g ≤ ENNReal.ofReal c2 ∧
      MemLp (hilbertifyVecField (euclideanGradient g)) 2 (normalizedCubeMeasure Q) ∧
      MemLp (hilbertifyVecField (fun x => euclideanGradient g x - gt x)) 2
        (normalizedCubeMeasure Q) ∧
      vecCubeLpENorm Q 2 (fun x => euclideanGradient g x - gt x) ≤
        ENNReal.ofReal eps)
    (hc1 : 0 < c1) (hc2 : 0 < c2) :
    n ^ 2 ≤ (c1 + c2) * Vr + 2 * (vecCubeLpENorm Q 2 gu).toReal * eps := by
  obtain ⟨g1, hg1c, hg1m, hg1lev, hE1, hD1, hcl1⟩ := happrox1
  obtain ⟨g2, hg2c, hg2m, hg2lev, hE2, hD2, hcl2⟩ := happrox2
  have hsplit : ∀ (b : Vec d → Vec d) (g : Vec d → ℝ),
      MemLp (hilbertifyVecField (euclideanGradient g)) 2 (normalizedCubeMeasure Q) →
      MemLp (hilbertifyVecField (fun x => euclideanGradient g x - b x)) 2
        (normalizedCubeMeasure Q) →
      volumeAverage (cubeSet Q) (fun x => vecDot (gu x) (b x)) =
        volumeAverage (cubeSet Q)
            (fun x => vecDot (gu x) (euclideanGradient g x)) -
          volumeAverage (cubeSet Q)
            (fun x => vecDot (gu x) (euclideanGradient g x - b x)) := by
    intro b g hEm hDm
    have hfun : ∀ x : Vec d, vecDot (gu x) (b x) =
        vecDot (gu x) (euclideanGradient g x - (euclideanGradient g x - b x)) := by
      intro x
      refine congrArg (vecDot (gu x)) ?_
      funext i
      show b x i = euclideanGradient g x i - (euclideanGradient g x i - b x i)
      ring
    rw [congrArg (volumeAverage (cubeSet Q)) (funext hfun),
      volumeAverage_vecDot_sub_right hgu hEm hDm]
  have hbound : ∀ (g : Vec d → ℝ) (c : ℝ), 0 < c → ContDiff ℝ (⊤ : ℕ∞) g →
      volumeAverage (cubeSet Q) g = 0 →
      Section2.Norms.vecHatTestH1ENorm Q g ≤ ENNReal.ofReal c →
      |volumeAverage (cubeSet Q)
          (fun x => vecDot (gu x) (euclideanGradient g x))| ≤ c * Vr := by
    intro g c hc hgc hgm hlev
    have h := Section2.Norms.ofReal_abs_volumeAverage_pairing_le_vecHatNegENormOrderOne_mul
      G hc hgc hgm hlev
    rw [hV, ← ENNReal.ofReal_mul hc.le] at h
    have h2 : |volumeAverage (cubeSet Q) (vecGradientPairingDensity G g)| ≤ c * Vr :=
      (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc.le hVr)).1 h
    rw [hpair g hgc, abs_neg] at h2
    exact h2
  have herr : ∀ (b : Vec d → Vec d) (g : Vec d → ℝ),
      MemLp (hilbertifyVecField (fun x => euclideanGradient g x - b x)) 2
        (normalizedCubeMeasure Q) →
      vecCubeLpENorm Q 2 (fun x => euclideanGradient g x - b x) ≤
        ENNReal.ofReal eps →
      |volumeAverage (cubeSet Q)
          (fun x => vecDot (gu x) (euclideanGradient g x - b x))| ≤
        (vecCubeLpENorm Q 2 gu).toReal * eps := by
    intro b g hDm hcl
    refine le_trans (Section2.Norms.abs_volumeAverage_vecDot_le_mul hgu hDm) ?_
    exact mul_le_mul_of_nonneg_left
      (ENNReal.toReal_le_of_le_ofReal heps.le hcl) ENNReal.toReal_nonneg
  have h1 := (abs_le.1 (hbound g1 c1 hc1 hg1c hg1m hg1lev)).2
  have h2 := (abs_le.1 (hbound g2 c2 hc2 hg2c hg2m hg2lev)).1
  have h3 := (abs_le.1 (herr gp g1 hD1 hcl1)).1
  have h4 := (abs_le.1 (herr gt g2 hD2 hcl2)).2
  rw [hn, hsplit gp g1 hE1 hD1, hsplit gt g2 hE2 hD2]
  linarith only [h1, h2, h3, h4]

/-! ## The identity behind the estimate -/

/-- **`‖v − (v)_Q‖²_{L̲²(Q)} = ⨍ ∇u·∇ψ − ⨍ ∇u·∇θ`.**  Testing the Neumann
potential at the centred response difference gives `⨍ ∇ψ·∇v`; the difference of
the two responses is harmonic, so `⨍ ∇v·∇θ = 0`, and the defining equation of
`θ` gives `⨍ ∇w·∇ψ = ⨍ ∇w·∇θ`. -/
private theorem sq_response_difference_eq {Q : TriadicCube d}
    {G : Vec d → Vec d} {u : H1MeanZeroFunction (openCubeSet Q)}
    {w : H10Function (openCubeSet Q)}
    (hN : IsCubeNeumannResponse Q G u) (hD : IsCubeDirichletResponse Q G w)
    {ψ : H1MeanZeroFunction (openCubeSet Q)} {θ : H10Function (openCubeSet Q)}
    (hψeq : ∀ φ : H1MeanZeroFunction (openCubeSet Q),
      ∫ x in openCubeSet Q, vecDot (ψ.toH1Function.grad x) (φ.toH1Function.grad x) =
        ∫ x in openCubeSet Q,
          (u.toH1Function - w.toH1Function).subAverage.toFun x * φ.toH1Function x)
    (hθeq : ∀ φ : H10Function (openCubeSet Q),
      ∫ x in openCubeSet Q, vecDot (θ.toH1Function.grad x) (φ.toH1Function.grad x) =
        ∫ x in openCubeSet Q,
          vecDot (ψ.toH1Function.grad x) (φ.toH1Function.grad x)) :
    (Section2.Norms.cubeLpENorm Q 2
        (u.toH1Function - w.toH1Function).subAverage.toFun).toReal ^ 2 =
      volumeAverage (cubeSet Q)
          (fun x => vecDot (u.toH1Function.grad x) (ψ.toH1Function.grad x)) -
        volumeAverage (cubeSet Q)
          (fun x => vecDot (u.toH1Function.grad x) (θ.toH1Function.grad x)) := by
  have hgu := memLp_two_hilbertify u.toH1Function.grad_memVectorL2
  have hgw := memLp_two_hilbertify w.toH1Function.grad_memVectorL2
  have hgp := memLp_two_hilbertify ψ.toH1Function.grad_memVectorL2
  have hgt := memLp_two_hilbertify θ.toH1Function.grad_memVectorL2
  have hzmem : MemLp (u.toH1Function - w.toH1Function).subAverage.toFun 2
      (normalizedCubeMeasure Q) :=
    memLp_two_normalizedCubeMeasure_of_memScalarL2
      (u.toH1Function - w.toH1Function).subAverage.memL2
  have hgradeq : ∀ x : Vec d,
      ((u.toH1Function - w.toH1Function).toMeanZero).toH1Function.grad x =
        u.toH1Function.grad x - w.toH1Function.grad x := by
    intro x
    rw [H1Function.toMeanZero_grad, H1Function.sub_grad]
  have hkey : ∫ x in openCubeSet Q,
      vecDot (ψ.toH1Function.grad x)
        (u.toH1Function.grad x - w.toH1Function.grad x) =
      ∫ x in openCubeSet Q,
        (u.toH1Function - w.toH1Function).subAverage.toFun x *
          (u.toH1Function - w.toH1Function).subAverage.toFun x :=
    calc ∫ x in openCubeSet Q, vecDot (ψ.toH1Function.grad x)
            (u.toH1Function.grad x - w.toH1Function.grad x)
        = ∫ x in openCubeSet Q, vecDot (ψ.toH1Function.grad x)
            (((u.toH1Function - w.toH1Function).toMeanZero).toH1Function.grad x) :=
          setIntegral_congr_fun (measurableSet_openCubeSet Q)
            (fun x _ => by rw [hgradeq x])
      _ = ∫ x in openCubeSet Q,
            (u.toH1Function - w.toH1Function).subAverage.toFun x *
              ((u.toH1Function - w.toH1Function).toMeanZero).toH1Function x :=
          hψeq ((u.toH1Function - w.toH1Function).toMeanZero)
      _ = _ := rfl
  have hsq : (Section2.Norms.cubeLpENorm Q 2
        (u.toH1Function - w.toH1Function).subAverage.toFun).toReal ^ 2 =
      volumeAverage (cubeSet Q) (fun x => vecDot (ψ.toH1Function.grad x)
        (u.toH1Function.grad x - w.toH1Function.grad x)) := by
    rw [← volumeAverage_mul_self_eq_sq hzmem]
    exact (volumeAverage_congr_setIntegral hkey).symm
  rw [hsq, volumeAverage_vecDot_sub_right hgp hgu hgw]
  -- the harmonicity of the response difference
  have hcongr : ∫ x in openCubeSet Q,
      vecDot ((u.toH1Function - w.toH1Function).grad x) (θ.toH1Function.grad x) =
      ∫ x in openCubeSet Q,
        vecDot (u.toH1Function.grad x - w.toH1Function.grad x)
          (θ.toH1Function.grad x) :=
    setIntegral_congr_fun (measurableSet_openCubeSet Q)
      (fun x _ => by rw [H1Function.sub_grad])
  have hharm0 := hcongr.symm.trans
    (setIntegral_vecDot_grad_responseDifference_eq_zero hD hN θ)
  have hharm : volumeAverage (cubeSet Q)
      (fun x => vecDot (u.toH1Function.grad x - w.toH1Function.grad x)
        (θ.toH1Function.grad x)) = 0 := by
    rw [volumeAverage_cubeSet_eq_openCubeSet, volumeAverage, hharm0, mul_zero]
  have ec := volumeAverage_vecDot_sub_left hgu hgw hgt
  rw [hharm] at ec
  have ea : volumeAverage (cubeSet Q)
      (fun x => vecDot (θ.toH1Function.grad x) (w.toH1Function.grad x)) =
      volumeAverage (cubeSet Q)
        (fun x => vecDot (ψ.toH1Function.grad x) (w.toH1Function.grad x)) :=
    volumeAverage_congr_setIntegral (hθeq w)
  have eb : volumeAverage (cubeSet Q)
      (fun x => vecDot (w.toH1Function.grad x) (θ.toH1Function.grad x)) =
      volumeAverage (cubeSet Q)
        (fun x => vecDot (θ.toH1Function.grad x) (w.toH1Function.grad x)) :=
    congrArg (volumeAverage (cubeSet Q)) (funext fun x => vecDot_comm' _ _)
  have e1 : volumeAverage (cubeSet Q)
      (fun x => vecDot (ψ.toH1Function.grad x) (u.toH1Function.grad x)) =
      volumeAverage (cubeSet Q)
        (fun x => vecDot (u.toH1Function.grad x) (ψ.toH1Function.grad x)) :=
    congrArg (volumeAverage (cubeSet Q)) (funext fun x => vecDot_comm' _ _)
  linarith only [ea, eb, ec, e1]

/-! ## The constant -/

/-- **The constant of the order-one `Ĥ̲^{-1}` estimate**: twice
the dimensional cube Poincaré-Wirtinger constant, plus the dimensional Neumann
and Dirichlet cube `H²` constants, plus one.  The Dirichlet summand
`cubeDirichletHessianConst` is a `Classical.choose` constant of the upstream
existential; the summand `1` only keeps the constant away from zero. -/
def hminusOneResponseConst (d : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * (originCubeMeanZeroH1CoerciveEstimate d 0).constant +
      originCubeNeumannW22CalderonZygmundConstant d +
      (cubeDirichletHessianConst d).toReal) + 1

theorem hminusOneResponseConst_lt_top (d : ℕ) : hminusOneResponseConst d < ⊤ :=
  ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.one_lt_top⟩

theorem hminusOneResponseConst_ne_zero (d : ℕ) : hminusOneResponseConst d ≠ 0 := by
  intro h
  rw [hminusOneResponseConst, add_eq_zero] at h
  exact one_ne_zero h.2

private theorem le_toReal_hminusOneResponseConst (d : ℕ) :
    2 * (originCubeMeanZeroH1CoerciveEstimate d 0).constant +
        originCubeNeumannW22CalderonZygmundConstant d +
        (cubeDirichletHessianConst d).toReal ≤
      (hminusOneResponseConst d).toReal := by
  have hnn : 0 ≤ 2 * (originCubeMeanZeroH1CoerciveEstimate d 0).constant +
      originCubeNeumannW22CalderonZygmundConstant d +
      (cubeDirichletHessianConst d).toReal := by
    have h1 : (0 : ℝ) ≤ (originCubeMeanZeroH1CoerciveEstimate d 0).constant :=
      (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
    have h2 : (0 : ℝ) ≤ originCubeNeumannW22CalderonZygmundConstant d :=
      originCubeNeumannW22CalderonZygmundConstant_nonneg d
    have h3 : (0 : ℝ) ≤ (cubeDirichletHessianConst d).toReal := ENNReal.toReal_nonneg
    linarith only [h1, h2, h3]
  rw [hminusOneResponseConst, ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.one_ne_top,
    ENNReal.toReal_ofReal hnn, ENNReal.toReal_one]
  linarith only []

private theorem toReal_hminusOneResponseConst_pos (d : ℕ) :
    0 < (hminusOneResponseConst d).toReal := by
  have h1 : (0 : ℝ) ≤ (originCubeMeanZeroH1CoerciveEstimate d 0).constant :=
    (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
  have h2 : (0 : ℝ) ≤ originCubeNeumannW22CalderonZygmundConstant d :=
    originCubeNeumannW22CalderonZygmundConstant_nonneg d
  have h3 : (0 : ℝ) ≤ (cubeDirichletHessianConst d).toReal := ENNReal.toReal_nonneg
  have h4 := le_toReal_hminusOneResponseConst d
  have hnn : 0 ≤ 2 * (originCubeMeanZeroH1CoerciveEstimate d 0).constant +
      originCubeNeumannW22CalderonZygmundConstant d +
      (cubeDirichletHessianConst d).toReal := by linarith only [h1, h2, h3]
  have hone : (1 : ℝ) ≤ (hminusOneResponseConst d).toReal := by
    rw [hminusOneResponseConst, ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.one_ne_top,
      ENNReal.toReal_ofReal hnn, ENNReal.toReal_one]
    linarith only [hnn]
  linarith only [hone]

private theorem toReal_le_toReal_mul {X Y C : ℝ≥0∞} (hC : C ≠ ⊤) (hY : Y ≠ ⊤)
    (h : X ≤ C * Y) : X.toReal ≤ C.toReal * Y.toReal := by
  have hfin : C * Y ≠ ⊤ := (ENNReal.mul_lt_top hC.lt_top hY.lt_top).ne
  have hmono := ENNReal.toReal_mono hfin h
  rwa [ENNReal.toReal_mul] at hmono

/-! ## The order-one `Ĥ̲^{-1}` estimate of Step 4 -/

/-- **The first of the two standard estimates of Step 4, in the
order-one hatted negative norm**: with `u` the prescribed-flux Neumann response
of `G` on `cu_M` and `w` its Dirichlet response,

`3^{-M}‖(u − w) − (u − w)_{cu_M}‖_{L̲²(cu_M)} ≤ C(d) ‖G‖_{Ĥ̲^{-1}(cu_M)}`.

This is the exact shape of the hypothesis `hHm1` of
`exists_responseDifferenceL2Clause_orderOne`, at `CHm := hminusOneResponseConst d`.
The flux `G` carries no integrability hypothesis: it is only ever paired with a
smooth test gradient. -/
theorem hminusOne_response_difference_bridge (hd : 2 ≤ d) :
    ∀ (M : ℕ) (G : Vec d → Vec d)
      (u : H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ))))
      (w : H10Function (openCubeSet (originCube d (M : ℤ)))),
      IsCubeNeumannResponse (originCube d (M : ℤ)) G u →
      IsCubeDirichletResponse (originCube d (M : ℤ)) G w →
      ENNReal.ofReal ((cubeScaleFactor (originCube d (M : ℤ)))⁻¹) *
          Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 2
            (u.toH1Function - w.toH1Function).subAverage.toFun ≤
        hminusOneResponseConst d *
          Section2.Norms.vecHatNegENormOrderOne (originCube d (M : ℤ)) G := by
  have : NeZero d := ⟨by omega⟩
  intro M G u w hN hD
  have hzmem : MemLp (u.toH1Function - w.toH1Function).subAverage.toFun 2
      (normalizedCubeMeasure (originCube d (M : ℤ))) :=
    memLp_two_normalizedCubeMeasure_of_memScalarL2
      (u.toH1Function - w.toH1Function).subAverage.memL2
  have hint0 : ∫ x in openCubeSet (originCube d (M : ℤ)),
      (u.toH1Function - w.toH1Function).subAverage.toFun x = 0 :=
    H1Function.meanZeroOn_subAverage (u.toH1Function - w.toH1Function)
  have hzmean : cubeAverage (originCube d (M : ℤ))
      (u.toH1Function - w.toH1Function).subAverage.toFun = 0 := by
    show (cubeVolume (originCube d (M : ℤ)))⁻¹ *
      ∫ x in cubeSet (originCube d (M : ℤ)),
        (u.toH1Function - w.toH1Function).subAverage.toFun x = 0
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet, hint0, mul_zero]
  obtain ⟨ψ, θ, Hpsi, Hth, hψeq, hθeq, hpg, htg, hph, hth⟩ :=
    exists_cubeHarmonicPartPotential (M : ℤ) hzmem hzmean
  have hscale : 0 < cubeScaleFactor (originCube d (M : ℤ)) := by
    rw [cubeScaleFactor]
    positivity
  have hzfin : Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 2
      (u.toH1Function - w.toH1Function).subAverage.toFun ≠ ⊤ :=
    hzmem.eLpNorm_lt_top.ne
  have hgu := memLp_two_hilbertify u.toH1Function.grad_memVectorL2
  have hn := sq_response_difference_eq hN hD hψeq hθeq
  by_cases hVtop : Section2.Norms.vecHatNegENormOrderOne (originCube d (M : ℤ)) G = ⊤
  · rw [hVtop, ENNReal.mul_top (hminusOneResponseConst_ne_zero d)]
    exact le_top
  · set n : ℝ := (Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 2
      (u.toH1Function - w.toH1Function).subAverage.toFun).toReal with hndef
    set Vr : ℝ := (Section2.Norms.vecHatNegENormOrderOne (originCube d (M : ℤ)) G).toReal
      with hVrdef
    set K : ℝ := (hminusOneResponseConst d).toReal with hKdef
    set Nu : ℝ := (vecCubeLpENorm (originCube d (M : ℤ)) 2
      u.toH1Function.grad).toReal with hNudef
    have hV : Section2.Norms.vecHatNegENormOrderOne (originCube d (M : ℤ)) G =
        ENNReal.ofReal Vr := (ENNReal.ofReal_toReal hVtop).symm
    have hn0 : (0 : ℝ) ≤ n := ENNReal.toReal_nonneg
    have hVr0 : (0 : ℝ) ≤ Vr := ENNReal.toReal_nonneg
    have hNu0 : (0 : ℝ) ≤ Nu := ENNReal.toReal_nonneg
    have hK0 : (0 : ℝ) < K := toReal_hminusOneResponseConst_pos d
    -- the four cube bounds, in real form
    have hA : (vecCubeLpENorm (originCube d (M : ℤ)) 2 ψ.toH1Function.grad).toReal ≤
        (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
          cubeScaleFactor (originCube d (M : ℤ)) * n := by
      have h := toReal_le_toReal_mul ENNReal.ofReal_ne_top hzfin hpg
      rwa [ENNReal.toReal_ofReal
        (mul_nonneg (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
          hscale.le)] at h
    have hB : (vecCubeLpENorm (originCube d (M : ℤ)) 2 θ.toH1Function.grad).toReal ≤
        (originCubeMeanZeroH1CoerciveEstimate d 0).constant *
          cubeScaleFactor (originCube d (M : ℤ)) * n := by
      have h := toReal_le_toReal_mul ENNReal.ofReal_ne_top hzfin htg
      rwa [ENNReal.toReal_ofReal
        (mul_nonneg (originCubeMeanZeroH1CoerciveEstimate d 0).constant_nonneg
          hscale.le)] at h
    have hCh : (Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 2
        (fun x => HilbertMat.ofMat (fun i j => Hpsi.hess i j x))).toReal ≤
        originCubeNeumannW22CalderonZygmundConstant d * n := by
      have h := toReal_le_toReal_mul ENNReal.ofReal_ne_top hzfin hph
      rwa [ENNReal.toReal_ofReal
        (originCubeNeumannW22CalderonZygmundConstant_nonneg d)] at h
    have hDh : (Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 2
        (fun x => HilbertMat.ofMat (fun i j => Hth.hess i j x))).toReal ≤
        (cubeDirichletHessianConst d).toReal * n :=
      toReal_le_toReal_mul (cubeDirichletHessianConst_lt_top d).ne hzfin hth
    have hsum : ((vecCubeLpENorm (originCube d (M : ℤ)) 2 ψ.toH1Function.grad).toReal +
          cubeScaleFactor (originCube d (M : ℤ)) *
            (Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 2
              (fun x => HilbertMat.ofMat (fun i j => Hpsi.hess i j x))).toReal) +
        ((vecCubeLpENorm (originCube d (M : ℤ)) 2 θ.toH1Function.grad).toReal +
          cubeScaleFactor (originCube d (M : ℤ)) *
            (Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 2
              (fun x => HilbertMat.ofMat (fun i j => Hth.hess i j x))).toReal) ≤
        cubeScaleFactor (originCube d (M : ℤ)) * K * n := by
      have h3 := mul_le_mul_of_nonneg_left hCh hscale.le
      have h4 := mul_le_mul_of_nonneg_left hDh hscale.le
      have h6 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_toReal_hminusOneResponseConst d) hscale.le) hn0
      linarith only [hA, hB, h3, h4, h6]
    -- the estimate at one approximation scale
    have hkey : ∀ eps : ℝ, 0 < eps →
        n ^ 2 ≤ cubeScaleFactor (originCube d (M : ℤ)) * K * n * Vr +
          eps * ((2 + 2 * cubeScaleFactor (originCube d (M : ℤ))) * Vr + 2 * Nu + 1) := by
      intro eps heps
      obtain ⟨g1, hg1c, hg1m, hg1lev, hE1, hD1, hcl1⟩ :=
        exists_orderOneTestPotential Hpsi heps
      obtain ⟨g2, hg2c, hg2m, hg2lev, hE2, hD2, hcl2⟩ :=
        exists_orderOneTestPotential Hth heps
      refine le_trans (sq_le_add_of_approx
        (fun g hg =>
          volumeAverage_vecGradientPairingDensity_eq_of_isCubeNeumannResponse hN hg)
        hgu heps hVr0 hV hn ⟨g1, hg1c, hg1m, hg1lev, hE1, hD1, hcl1⟩
        ⟨g2, hg2c, hg2m, hg2lev, hE2, hD2, hcl2⟩ ?_ ?_) ?_
      · have h1 : (0 : ℝ) ≤
            (vecCubeLpENorm (originCube d (M : ℤ)) 2 ψ.toH1Function.grad).toReal :=
          ENNReal.toReal_nonneg
        have h2 : (0 : ℝ) ≤ cubeScaleFactor (originCube d (M : ℤ)) *
            (Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 2
              (fun x => HilbertMat.ofMat (fun i j => Hpsi.hess i j x))).toReal :=
          mul_nonneg hscale.le ENNReal.toReal_nonneg
        have h3 : 0 < (1 + cubeScaleFactor (originCube d (M : ℤ))) * eps :=
          mul_pos (by linarith only [hscale]) heps
        linarith only [h1, h2, h3]
      · have h1 : (0 : ℝ) ≤
            (vecCubeLpENorm (originCube d (M : ℤ)) 2 θ.toH1Function.grad).toReal :=
          ENNReal.toReal_nonneg
        have h2 : (0 : ℝ) ≤ cubeScaleFactor (originCube d (M : ℤ)) *
            (Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 2
              (fun x => HilbertMat.ofMat (fun i j => Hth.hess i j x))).toReal :=
          mul_nonneg hscale.le ENNReal.toReal_nonneg
        have h3 : 0 < (1 + cubeScaleFactor (originCube d (M : ℤ))) * eps :=
          mul_pos (by linarith only [hscale]) heps
        linarith only [h1, h2, h3]
      · have hmul := mul_le_mul_of_nonneg_right hsum hVr0
        linarith only [hmul, heps.le]
    -- the limit
    have hS : 0 < (2 + 2 * cubeScaleFactor (originCube d (M : ℤ))) * Vr + 2 * Nu + 1 := by
      have h1 : (0 : ℝ) ≤ (2 + 2 * cubeScaleFactor (originCube d (M : ℤ))) * Vr :=
        mul_nonneg (by linarith only [hscale]) hVr0
      linarith only [h1, hNu0]
    have hfinal : n ^ 2 ≤ cubeScaleFactor (originCube d (M : ℤ)) * K * n * Vr := by
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      have h := hkey (δ / ((2 + 2 * cubeScaleFactor (originCube d (M : ℤ))) * Vr +
        2 * Nu + 1)) (div_pos hδ hS)
      rwa [div_mul_cancel₀ δ hS.ne'] at h
    rcases eq_or_lt_of_le hn0 with hzero | hpos
    · have hzeq : Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 2
          (u.toH1Function - w.toH1Function).subAverage.toFun = 0 := by
        rw [← ENNReal.ofReal_toReal hzfin, ← hndef, ← hzero, ENNReal.ofReal_zero]
      rw [hzeq, mul_zero]
      exact zero_le
    · have hdiv : n ≤ cubeScaleFactor (originCube d (M : ℤ)) * K * Vr := by
        refine le_of_mul_le_mul_right ?_ hpos
        calc n * n = n ^ 2 := by ring
          _ ≤ cubeScaleFactor (originCube d (M : ℤ)) * K * n * Vr := hfinal
          _ = cubeScaleFactor (originCube d (M : ℤ)) * K * Vr * n := by ring
      have hres : (cubeScaleFactor (originCube d (M : ℤ)))⁻¹ * n ≤ K * Vr := by
        have h1 := mul_le_mul_of_nonneg_left hdiv (le_of_lt (inv_pos.2 hscale))
        have h2 : (cubeScaleFactor (originCube d (M : ℤ)))⁻¹ *
            (cubeScaleFactor (originCube d (M : ℤ)) * K * Vr) = K * Vr := by
          field_simp
        rwa [h2] at h1
      have hzval : Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 2
          (u.toH1Function - w.toH1Function).subAverage.toFun = ENNReal.ofReal n :=
        (ENNReal.ofReal_toReal hzfin).symm
      have hKval : hminusOneResponseConst d = ENNReal.ofReal K :=
        (ENNReal.ofReal_toReal (hminusOneResponseConst_lt_top d).ne).symm
      rw [hzval, hV, hKval, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.2 hscale)),
        ← ENNReal.ofReal_mul hK0.le]
      exact ENNReal.ofReal_le_ofReal hres

end

end ResponseFields
end Section3
end SuperdiffusionCLT
