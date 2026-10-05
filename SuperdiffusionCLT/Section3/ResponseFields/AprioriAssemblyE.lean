/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.ResponseFields.AprioriAssemblyD
public import SuperdiffusionCLT.Section3.ResponseFields.HhalfEndpointB

/-!
# The a priori response estimates without a junk binder

The four estimates of `l.abstract.response.fields` in the paper are its deterministic
half. The clauses are assembled from bridges, which
`HarmonicInterpolationB.lean`, `HhalfDilationB.lean`, `JunkBranchB.lean` and
`HhalfEndpointB.lean` discharge, except for one junk hypothesis on the Hessian clause
(the junk binder for the second conjunct), whose case split is not the junk branch of that
conjunct: it demands the Hessian estimate *with constant one* on a branch where the
weak-Jacobian witness, and not the flux, is the non-measurable datum, and where
that is a sharp-constant claim.

This module repairs that case split and re-runs the assembly.

## The repaired case split

Write `U = cu_M` for the open cube and `DF` for the weak-Jacobian witness. The
right-hand side of `e.abstract.response.W28` is `‖DF‖_{L̲⁸(U)}`.

1. `‖DF‖_{L̲⁸(U)} = ⊤`: the estimate is empty.
2. Some pairing `∫_U F·∇φ`, `φ ∈ H¹₀(U)`, is not integrable. Then every pairing
   of `∇w_D` against a test gradient vanishes, so `∇w_D = 0` almost everywhere
   and every weak Hessian of `w_D` vanishes almost everywhere: the left-hand
   side is `0`. This is the junk branch proper, carried by the bad test function
   instead of by the non-measurability of `F`.
3. Every pairing is integrable. Then `F` is measurable on `U` and locally
   integrable there, and the Calderón-Zygmund endpoint is applied to the honest
   witness `honestJacobian U DF` of `AprioriAssemblyD.lean`, which is measurable,
   is again a weak Jacobian of `F`, and is dominated by `DF` entry by entry, so
   `eLpNorm` monotonicity finishes with the endpoint's own constant.

## The flux is not assumed square integrable

The Dirichlet Hessian endpoint of `Sobolev/DirichletW2pDivergence.lean` assumes
`F ∈ L̲²(cu_M)`, which branch 3 does not provide: passing from local integrability to `L̲²` is the
Sobolev embedding of the cube, and the Poincaré layer available here
(`CoerciveH1`, `PoincareLp*`, `PoincareW1p`) is stated for `H1Function` and
`W1pFunction` carriers, which already presuppose that membership.

It is not needed. The `L̲²` size of the flux entered only through the bridge to
the scalar Poisson problem, that is, through the `H¹₀` closure of the by-parts
identity `∫_U F·∇φ = −∫_U (∇·F) φ`. Here that closure comes from the response
equation instead: along the smooth approximation package of an `H¹₀` test
function both sides are continuous — the left because `∇w_D ∈ L²(U)`, the right
because `∇·F ∈ L²(U)` — and at a smooth compactly supported approximant the
identity is the definition of the weak Jacobian, every pairing being an honest
integral because the flux is locally integrable. That is
`cubeDirichletWeakPoissonProblem_of_locallyIntegrableOn`, and
`exists_cubeDirichletResponseW28Estimate_of_locallyIntegrableOn` is the endpoint
rebuilt on it from CoarseGraining's scalar Poisson Hessian estimate.

## The assembly

`responseFields_apriori_orderZero_of_clauses` assembles the four clauses with the second clause
taken from `exists_dirichletHessianL8Clause'`, and the three other bridges supplied as
follows —

* clause 1 from `exists_responseGradientL8Clause` with `junkL8_bridge`;
* clause 3 from `exists_dirichletHsClause` with `dirichlet_hhalf_bridge` at the
  constant `hhalfEndpointConst d hd`, the differentiated endpoint
  `hhalf_endpoint_bridge` and the junk branch `junkHalf_bridge`;
* clause 4 from `exists_responseDifferenceL2Clause` with the Step 3 bridge
  `harmonic_interpolation_bridge` and the junk branch `junkND_bridge`.

The conclusion is the statement
`SuperdiffusionCLT.Frozen.Section3.responseFields_apriori_orderZero` verbatim, and
there is no hypothesis beyond `2 ≤ d`.
-/

@[expose] public section

namespace SuperdiffusionCLT
namespace Section3
namespace ResponseFields

open Homogenization
open MeasureTheory
open scoped ENNReal

noncomputable section

section Repair

variable {d : ℕ}

/-! ## The scalar Poisson problem of a locally integrable flux -/

/-- **A Dirichlet response of a locally integrable flux with an `L²` weak
Jacobian solves the scalar Poisson problem with datum `∇·F`.**

`Sobolev/DirichletW2pDivergence.lean` proves this from `F ∈ L̲²(Q)`, which the
`H¹₀` closure of the by-parts identity needs. Here the flux is only locally
integrable, and the closure is obtained instead from the response equation
itself: both sides of the Poisson identity are continuous along the `H¹₀`
approximation package, the left-hand side because `∇w ∈ L²(Q)` and the
right-hand side because `∇·F ∈ L²(Q)`, and they agree on the smooth compactly
supported approximants, where the by-parts identity is the definition of the
weak Jacobian and every pairing is an honest integral. -/
theorem cubeDirichletWeakPoissonProblem_of_locallyIntegrableOn {Q : TriadicCube d}
    {F : Vec d → Vec d} {DF : Fin d → Vec d → Vec d}
    {w : H10Function (openCubeSet Q)}
    (hFloc : ∀ i, LocallyIntegrableOn (fun x => F x i) (openCubeSet Q) volume)
    (hDF : ∀ i j, MemScalarL2 (openCubeSet Q) (fun x => DF i x j))
    (hweak : ∀ i, HasWeakGradientOn (openCubeSet Q) (fun x => F x i) (DF i))
    (hw : IsCubeDirichletResponse Q F w) :
    CubeDirichletWeakPoissonProblem Q w (Sobolev.weakDivergence DF) := by
  intro φ
  have happroxL2 : ∀ n : ℕ, MemScalarL2 (openCubeSet Q) (φ.approx n) := fun n =>
    memScalarL2_of_contDiff_hasCompactSupport _ (φ.approx_smooth n)
      (φ.approx_hasCompactSupport n)
  have hgradL2 : ∀ (n : ℕ) (i : Fin d), MemScalarL2 (openCubeSet Q)
      (fun x => euclideanCoordDeriv i (φ.approx n) x) := fun n i =>
    memScalarL2_euclideanCoordDeriv_of_contDiff_hasCompactSupport _ i
      (φ.approx_smooth n) (φ.approx_hasCompactSupport n)
  have hdivL2 : MemScalarL2 (openCubeSet Q) (Sobolev.weakDivergence DF) := by
    have hsum := memLp_finsetSum' (μ := volumeMeasureOn (openCubeSet Q)) (p := (2 : ℝ≥0∞))
      (Finset.univ : Finset (Fin d))
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hDF i i)
    have hfun : (∑ i : Fin d, fun x : Vec d => DF i x i) = Sobolev.weakDivergence DF := by
      funext x
      simp only [Finset.sum_apply, Sobolev.weakDivergence]
    rwa [hfun] at hsum
  -- the smooth approximants, packaged as `H¹₀` test functions
  set ψ : ℕ → H10Function (openCubeSet Q) := fun n =>
    H10Function.ofContDiff (isOpen_openCubeSet Q) (φ.approx_smooth n)
      (φ.approx_hasCompactSupport n) (φ.approx_support_subset n) with hψdef
  have hψgrad : ∀ (n : ℕ) (x : Vec d) (i : Fin d),
      (ψ n).toH1Function.grad x i = euclideanCoordDeriv i (φ.approx n) x := fun _ _ _ => rfl
  have hψfun : ∀ n : ℕ, (ψ n).toH1Function.toFun = φ.approx n := fun _ => rfl
  -- Step 1: the identity at each smooth approximant
  have hstep : ∀ n : ℕ,
      ∫ x in openCubeSet Q, vecDot (w.toH1Function.grad x) ((ψ n).toH1Function.grad x) =
        ∫ x in openCubeSet Q, Sobolev.weakDivergence DF x * φ.approx n x := by
    intro n
    have hFint : ∀ i : Fin d, IntegrableOn
        (fun x => F x i * euclideanCoordDeriv i (φ.approx n) x) (openCubeSet Q) volume := by
      intro i
      refine integrableOn_mul_of_locallyIntegrableOn (measurableSet_openCubeSet Q)
        (hFloc i) ?_ ?_ ?_
      · exact ((φ.approx_smooth n).continuous_fderiv (by simp)).clm_apply continuous_const
      · exact hasCompactSupport_euclideanCoordDeriv (φ.approx_hasCompactSupport n) i
      · exact (tsupport_euclideanCoordDeriv_subset_tsupport i (φ.approx n)).trans
          (φ.approx_support_subset n)
    have hDint : ∀ i : Fin d,
        IntegrableOn (fun x => DF i x i * φ.approx n x) (openCubeSet Q) volume :=
      fun i => (hDF i i).integrable_mul (happroxL2 n)
    have hsplitF : ∫ x in openCubeSet Q, vecDot (F x) ((ψ n).toH1Function.grad x) =
        ∑ i : Fin d, ∫ x in openCubeSet Q,
          F x i * euclideanCoordDeriv i (φ.approx n) x := by
      rw [← integral_finsetSum _ fun i _ => hFint i]
      rfl
    have hbyparts : ∀ i : Fin d,
        ∫ x in openCubeSet Q, F x i * euclideanCoordDeriv i (φ.approx n) x =
          -∫ x in openCubeSet Q, DF i x i * φ.approx n x := fun i =>
      hweak i i (φ.approx n) (φ.approx_smooth n) (φ.approx_hasCompactSupport n)
        (φ.approx_support_subset n)
    have hRHS : ∫ x in openCubeSet Q, Sobolev.weakDivergence DF x * φ.approx n x =
        ∑ i : Fin d, ∫ x in openCubeSet Q, DF i x i * φ.approx n x := by
      rw [← integral_finsetSum _ fun i _ => hDint i]
      refine setIntegral_congr_fun (measurableSet_openCubeSet Q) fun x _ => ?_
      simp only [Sobolev.weakDivergence, Finset.sum_mul]
    rw [hw (ψ n), hsplitF, hRHS]
    simp_rw [hbyparts]
    rw [Finset.sum_neg_distrib, neg_neg]
  -- Step 2: both sides are continuous along the approximation
  have hleftcoord : ∀ i : Fin d, Filter.Tendsto
      (fun n => ∫ x in openCubeSet Q,
        w.toH1Function.grad x i * euclideanCoordDeriv i (φ.approx n) x)
      Filter.atTop
      (nhds (∫ x in openCubeSet Q,
        w.toH1Function.grad x i * φ.toH1Function.grad x i)) := by
    intro i
    refine tendsto_integral_mul_of_tendsto_toScalarL2 (w.toH1Function.gradMemL2 i)
      (fun n => hgradL2 n i) (φ.toH1Function.gradMemL2 i) ?_
    refine tendsto_toScalarL2_of_tendsto_eLpNorm (fun n => hgradL2 n i)
      (φ.toH1Function.gradMemL2 i) ?_
    simpa only [euclideanCoordDeriv] using φ.tendsto_approx_grad i
  have hleft : Filter.Tendsto
      (fun n => ∫ x in openCubeSet Q,
        vecDot (w.toH1Function.grad x) ((ψ n).toH1Function.grad x))
      Filter.atTop
      (nhds (∫ x in openCubeSet Q,
        vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x))) := by
    have hsum : ∀ n : ℕ, ∫ x in openCubeSet Q,
        vecDot (w.toH1Function.grad x) ((ψ n).toH1Function.grad x) =
        ∑ i : Fin d, ∫ x in openCubeSet Q,
          w.toH1Function.grad x i * euclideanCoordDeriv i (φ.approx n) x := by
      intro n
      have hint : ∀ i : Fin d, IntegrableOn
          (fun x => w.toH1Function.grad x i * euclideanCoordDeriv i (φ.approx n) x)
          (openCubeSet Q) volume := fun i =>
        (w.toH1Function.gradMemL2 i).integrable_mul (hgradL2 n i)
      rw [← integral_finsetSum _ fun i _ => hint i]
      rfl
    have hlim : ∫ x in openCubeSet Q,
        vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x) =
        ∑ i : Fin d, ∫ x in openCubeSet Q,
          w.toH1Function.grad x i * φ.toH1Function.grad x i := by
      have hint : ∀ i : Fin d, IntegrableOn
          (fun x => w.toH1Function.grad x i * φ.toH1Function.grad x i)
          (openCubeSet Q) volume := fun i =>
        (w.toH1Function.gradMemL2 i).integrable_mul (φ.toH1Function.gradMemL2 i)
      rw [← integral_finsetSum _ fun i _ => hint i]
      rfl
    rw [hlim]
    exact Filter.Tendsto.congr (fun n => (hsum n).symm)
      (tendsto_finsetSum Finset.univ fun i _ => hleftcoord i)
  have hright : Filter.Tendsto
      (fun n => ∫ x in openCubeSet Q, Sobolev.weakDivergence DF x * φ.approx n x)
      Filter.atTop
      (nhds (∫ x in openCubeSet Q,
        Sobolev.weakDivergence DF x * φ.toH1Function x)) :=
    tendsto_integral_mul_of_tendsto_toScalarL2 hdivL2 happroxL2 φ.toH1Function.memL2
      (tendsto_toScalarL2_of_tendsto_eLpNorm happroxL2 φ.toH1Function.memL2
        φ.tendsto_approx)
  exact tendsto_nhds_unique (Filter.Tendsto.congr hstep hleft) hright

/-! ## The Dirichlet Hessian endpoint for a locally integrable flux -/

/-- **The Dirichlet half of `e.abstract.response.W28` for a locally integrable
flux**: with a constant depending on `d` alone,

> `‖∇²w_D‖_{L̲⁸(cu_M)} ≤ C ‖∇F‖_{L̲⁸(cu_M)}`,

for every centred cube, every flux locally integrable on it whose weak Jacobian
is `L̲² ∩ L̲⁸(cu_M)`, every Dirichlet response and every weak-Hessian witness.

This is the Dirichlet Hessian endpoint of `Sobolev/DirichletW2pDivergence.lean` with the
hypothesis `F ∈ L̲²(cu_M)` replaced by local integrability: the only place the `L̲²` size
of the flux entered was the bridge to the scalar Poisson problem, which
`cubeDirichletWeakPoissonProblem_of_locallyIntegrableOn` supplies without it.
Everything below the bridge — CoarseGraining's scalar Poisson Hessian
Calderón-Zygmund endpoint and the a.e. uniqueness of weak second derivatives —
is unchanged. -/
theorem exists_cubeDirichletResponseW28Estimate_of_locallyIntegrableOn (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (M : ℕ) (F : Vec d → Vec d) (DF : Fin d → Vec d → Vec d)
        (wD : H10Function (openCubeSet (originCube d (M : ℤ))))
        (HD : HasWeakHessianOn (openCubeSet (originCube d (M : ℤ)))
          wD.toH1Function),
        (∀ i, LocallyIntegrableOn (fun x => F x i)
          (openCubeSet (originCube d (M : ℤ))) volume) →
        MemLp (fun x => HilbertMat.ofMat (fun i j => DF i x j)) 2
            (normalizedCubeMeasure (originCube d (M : ℤ))) →
        MemLp (fun x => HilbertMat.ofMat (fun i j => DF i x j)) 8
            (normalizedCubeMeasure (originCube d (M : ℤ))) →
        (∀ i, HasWeakGradientOn (openCubeSet (originCube d (M : ℤ)))
          (fun x => F x i) (DF i)) →
        IsCubeDirichletResponse (originCube d (M : ℤ)) F wD →
        Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 8
            (fun x => HilbertMat.ofMat (fun i j => HD.hess i j x)) ≤
          C * Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 8
            (fun x => HilbertMat.ofMat (fun i j => DF i x j)) := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨C, hCtop, hC⟩ :=
    CubeCalderonZygmund.exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le
      d { exponent := 8, one_lt := by norm_num, lt_top := by norm_num }
  refine ⟨(d : ℝ≥0∞) * C, ENNReal.mul_lt_top (ENNReal.natCast_lt_top d) hCtop, ?_⟩
  intro M F DF wD HD hFloc hDF2 hDF8 hweak hw
  have hDFcoord : ∀ i j : Fin d,
      MemScalarL2 (openCubeSet (originCube d (M : ℤ))) (fun x => DF i x j) := by
    intro i j
    refine memL2On_openCubeSet_of_memLp_normalizedCubeMeasure (originCube d (M : ℤ)) ?_
    have hcomp := (HilbertMat.entryL i j).comp_memLp' hDF2
    exact hcomp
  obtain ⟨H, -, hbound⟩ := hC (M : ℤ) (Sobolev.weakDivergence DF)
    (Sobolev.memLp_weakDivergence hDF2) (Sobolev.memLp_weakDivergence hDF8) wD
    (cubeDirichletWeakPoissonProblem_of_locallyIntegrableOn hFloc hDFcoord hweak hw)
  calc Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 8
        (fun x => HilbertMat.ofMat (fun i j => HD.hess i j x))
      = Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 8
          (fun x => HilbertMat.ofMat (fun i j => H.hess i j x)) :=
        Sobolev.cubeLpENorm_hessianHilbertMat_congr HD H 8
    _ ≤ C * Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 8
          (Sobolev.weakDivergence DF) := hbound
    _ ≤ C * ((d : ℝ≥0∞) * Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 8
          (fun x => HilbertMat.ofMat (fun i j => DF i x j))) := by
        gcongr
        exact Sobolev.cubeLpENorm_weakDivergence_le (originCube d (M : ℤ)) 8 DF
    _ = (d : ℝ≥0∞) * C * Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 8
          (fun x => HilbertMat.ofMat (fun i j => DF i x j)) := by
        ring

/-! ## `e.abstract.response.W28`, the Dirichlet summand, without a junk binder -/

/-- **The Hessian clause of `l.abstract.response.fields`**
(`e.abstract.response.W28`) for the
Dirichlet response alone, universally over weak-Hessian witnesses, in the shape
of the second conjunct of the statement `responseFields_apriori_orderZero`.

This is the Hessian clause with its junk hypothesis removed and
the case split repaired. Three branches, and nothing is assumed:

* an infinite `L̲⁸(cu_M)` Jacobian size, where the right-hand side is `⊤`;
* a flux with one non-integrable test pairing, where `∇w_D`, hence every weak
  Hessian of `w_D`, vanishes almost everywhere and the left-hand side is `0`;
* a flux with only integrable test pairings, where the flux is locally
  integrable on the cube and `exists_cubeDirichletResponseW28Estimate_of_locallyIntegrableOn`
  applies to the honest witness `honestJacobian`, which is measurable, is again
  a weak Jacobian of the flux, and is dominated by `DF` entry by entry. -/
theorem exists_dirichletHessianL8Clause' (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (M : ℕ) (F : Vec d → Vec d)
        (wD : H10Function (openCubeSet (originCube d (M : ℤ)))),
        IsCubeDirichletResponse (originCube d (M : ℤ)) F wD →
        ∀ (DF : Fin d → Vec d → Vec d)
          (HD : HasWeakHessianOn (openCubeSet (originCube d (M : ℤ)))
            wD.toH1Function),
          (∀ i, HasWeakGradientOn (openCubeSet (originCube d (M : ℤ)))
            (fun x => F x i) (DF i)) →
          Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 8
              (fun x => HilbertMat.ofMat (fun i j => HD.hess i j x)) ≤
            C * Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 8
              (fun x => HilbertMat.ofMat (fun i j => DF i x j)) := by
  obtain ⟨C, hCtop, hC⟩ := exists_cubeDirichletResponseW28Estimate_of_locallyIntegrableOn hd
  refine ⟨C + 1, ENNReal.add_lt_top.2 ⟨hCtop, ENNReal.one_lt_top⟩, ?_⟩
  intro M F wD hD DF HD hweak
  by_cases htop : Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 8
      (fun x => HilbertMat.ofMat (fun i j => DF i x j)) = ⊤
  · rw [htop, ENNReal.mul_top (by simp : C + 1 ≠ 0)]
    exact le_top
  by_cases hbad : ∃ φ₀ : H10Function (openCubeSet (originCube d (M : ℤ))),
      ¬ IntegrableOn (fun x => vecDot (F x) (φ₀.toH1Function.grad x))
        (openCubeSet (originCube d (M : ℤ)))
  · rw [cubeLpENorm_hess_eq_zero_of_grad_ae_eq_zero HD
      (grad_ae_eq_zero_of_exists_bad_test hbad hD)]
    exact zero_le
  push Not at hbad
  have hFloc : ∀ i, LocallyIntegrableOn (fun x => F x i)
      (openCubeSet (originCube d (M : ℤ))) volume := fun i =>
    locallyIntegrableOn_of_forall_integrableOn_vecDot_grad hbad i
  have hweakh := hasWeakJacobianOn_honestJacobian
    (isOpen_openCubeSet (originCube d (M : ℤ))) hFloc hweak
  have hle := cubeLpENorm_honestJacobian_le (originCube d (M : ℤ)) 8 DF
  have hmeas : AEStronglyMeasurable
      (fun x => HilbertMat.ofMat
        (fun i j => honestJacobian (openCubeSet (originCube d (M : ℤ))) DF i x j))
      (normalizedCubeMeasure (originCube d (M : ℤ))) := by
    rw [normalizedCubeMeasure_eq_smul_volume_restrict_openCubeSet]
    exact (aestronglyMeasurable_honestJacobianHilbertMat
      (openCubeSet (originCube d (M : ℤ))) DF).smul_measure _
  have hmem8 : MemLp
      (fun x => HilbertMat.ofMat
        (fun i j => honestJacobian (openCubeSet (originCube d (M : ℤ))) DF i x j)) 8
      (normalizedCubeMeasure (originCube d (M : ℤ))) :=
    lt_of_le_of_lt hle (lt_top_iff_ne_top.2 htop)
  have hmem2 : MemLp
      (fun x => HilbertMat.ofMat
        (fun i j => honestJacobian (openCubeSet (originCube d (M : ℤ))) DF i x j)) 2
      (normalizedCubeMeasure (originCube d (M : ℤ))) :=
    memLp_normalizedCubeMeasure_mono (by norm_num) hmem8
  calc Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 8
        (fun x => HilbertMat.ofMat (fun i j => HD.hess i j x))
      ≤ C * Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 8
          (fun x => HilbertMat.ofMat
            (fun i j => honestJacobian (openCubeSet (originCube d (M : ℤ))) DF i x j)) :=
        hC M F (honestJacobian (openCubeSet (originCube d (M : ℤ))) DF) wD HD hFloc
          hmem2 hmem8 hweakh hD
    _ ≤ (C + 1) * Section2.Norms.cubeLpENorm (originCube d (M : ℤ)) 8
          (fun x => HilbertMat.ofMat (fun i j => DF i x j)) := by
        gcongr
        exact le_self_add

end Repair

/-! ## The a priori response estimates -/

/-- **The a priori response estimates.** The
conclusion is the statement
`SuperdiffusionCLT.Frozen.Section3.responseFields_apriori_orderZero` verbatim.

There is no hypothesis beyond `2 ≤ d`: the junk binder of the Hessian clause is gone,
replaced by the repaired case split of `exists_dirichletHessianL8Clause'`. -/
theorem responseFields_apriori_orderZero_of_clauses (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (M : ℕ) (F : Vec d → Vec d)
        (wD : H10Function (openCubeSet (originCube d (M : ℤ))))
        (wN : H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ)))),
        SuperdiffusionCLT.Section3.ResponseFields.IsCubeDirichletResponse
          (originCube d (M : ℤ)) F wD →
        SuperdiffusionCLT.Section3.ResponseFields.IsCubeNeumannResponse
          (originCube d (M : ℤ)) F wN →
        (SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
                (originCube d (M : ℤ)) 8 wD.toH1Function.grad +
              SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
                (originCube d (M : ℤ)) 8 wN.toH1Function.grad ≤
            C * SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
              (originCube d (M : ℤ)) 8 F) ∧
        (∀ (DF : Fin d → Vec d → Vec d)
            (HD : HasWeakHessianOn (openCubeSet (originCube d (M : ℤ)))
              wD.toH1Function),
            (∀ i, HasWeakGradientOn (openCubeSet (originCube d (M : ℤ)))
              (fun x => F x i) (DF i)) →
            SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                (originCube d (M : ℤ)) 8
                (fun x => HilbertMat.ofMat (fun i j => HD.hess i j x)) ≤
            C * SuperdiffusionCLT.Section2.Norms.cubeLpENorm
                (originCube d (M : ℤ)) 8
                (fun x => HilbertMat.ofMat (fun i j => DF i x j))) ∧
        (SuperdiffusionCLT.Section2.Norms.cubeHsENorm
                (originCube d (M : ℤ)) (1 / 2)
                (hilbertifyVecField wD.toH1Function.grad) ≤
            C * SuperdiffusionCLT.Section2.Norms.cubeHsENorm
                (originCube d (M : ℤ)) (1 / 2)
                (hilbertifyVecField F)) ∧
        (SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
              (originCube d (M : ℤ)) 2
              (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) ≤
            C * (SuperdiffusionCLT.Section3.ResponseFields.vecHatNegENorm
                  (originCube d (M : ℤ))
                  (fun x => F x - volumeAverageVec
                    (cubeSet (originCube d (M : ℤ))) F)) ^ ((1 : ℝ) / 5) *
                (SuperdiffusionCLT.Section3.ResponseFields.vecCubeLpENorm
                  (originCube d (M : ℤ)) 4
                  (fun x => F x - volumeAverageVec
                    (cubeSet (originCube d (M : ℤ))) F)) ^ ((4 : ℝ) / 5) +
              C * ‖HilbertVec.ofVec (volumeAverageVec
                  (cubeSet (originCube d (M : ℤ))) F)‖ₑ)
    := by
  obtain ⟨C1, hC1top, hC1⟩ := exists_responseGradientL8Clause hd junkL8_bridge
  obtain ⟨C2, hC2top, hC2⟩ := exists_dirichletHessianL8Clause' hd
  obtain ⟨C3, hC3top, hC3⟩ := exists_dirichletHsClause
    (dirichletHhalfConst d hd (hhalfEndpointConst d hd))
    (dirichletHhalfConst_lt_top d hd (hhalfEndpointConst d hd))
    (dirichlet_hhalf_bridge d hd (hhalfEndpointConst d hd)
      (hhalfEndpointConst_nonneg d hd) (hhalf_endpoint_bridge d hd) junkHalf_bridge)
  obtain ⟨C4, hC4top, hC4⟩ := exists_responseDifferenceL2Clause hd
    (harmonicInterpolationConst d) (harmonicInterpolationConst_lt_top d)
    (harmonic_interpolation_bridge d) junkND_bridge
  refine ⟨C1 + C2 + C3 + C4, ?_, ?_⟩
  · exact ENNReal.add_lt_top.2
      ⟨ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨hC1top, hC2top⟩, hC3top⟩, hC4top⟩
  have hle1 : C1 ≤ C1 + C2 + C3 + C4 :=
    le_trans (le_trans le_self_add le_self_add) le_self_add
  have hle2 : C2 ≤ C1 + C2 + C3 + C4 :=
    le_trans (le_trans le_add_self le_self_add) le_self_add
  have hle3 : C3 ≤ C1 + C2 + C3 + C4 := le_trans le_add_self le_self_add
  have hle4 : C4 ≤ C1 + C2 + C3 + C4 := le_add_self
  intro M F wD wN hD hN
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine le_trans (hC1 M F wD wN hD hN) ?_
    gcongr
  · intro DF HD hweak
    refine le_trans (hC2 M F wD hD DF HD hweak) ?_
    gcongr
  · refine le_trans (hC3 M F wD hD) ?_
    gcongr
  · refine le_trans (hC4 M F wD wN hD hN) ?_
    exact add_le_add (mul_le_mul' (mul_le_mul' hle4 le_rfl) le_rfl)
      (mul_le_mul' hle4 le_rfl)

end

end ResponseFields
end Section3
end SuperdiffusionCLT
