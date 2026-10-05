/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.EllsepDrift
public import Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.SmoothLimit

/-!
# The weak divergence of a vector field, and its integration by parts

The paper needs only the *divergence* of
the skew flux `(k_{L'} − k_ℓ)∇u_m`, never its full Jacobian.  The
integration by parts `Sobolev/DirichletW2pDivergence.setIntegral_vecDot_zeroTrace_grad_eq_neg`
states its conclusion in terms of `weakDivergence DF` alone, but its *proof*
splits the pairing coordinatewise and applies the `H¹`-versus-`H¹₀`
identity to each component `F i` packaged with the whole Jacobian row `DF i`.
So it cannot be fed a divergence-only datum, and every supplier of a
weak Jacobian of `K ∇u` consumes a weak Hessian of `u`, which
is not available for the cube maximizer.

This module removes the Jacobian from the chain.  It defines the weak
divergence as a predicate tested against smooth compactly supported functions,
derives it from a weak Jacobian, and closes the test class up to `H¹₀` — the
step that `H10Function` makes available for free, since that carrier *bundles*
its own smooth compactly supported approximating sequence together with `L²`
convergence of the values and of every coordinate derivative.

## The skew cancellation

Write `f = ∇·K` in the row convention `(∇·K) j = ∑ᵢ ∂ᵢ K i j` of the footnote of the
paper.  For a smooth test function `φ` compactly supported in the cube:

1. the `C¹`-multiplier weak product rule
   `Section3/Terms/EllsepDrift.hasWeakGradientOn_mul_of_contDiff_one`, applied to
   the multiplier `K i j` and the `H¹` function `u` in direction `j`, and tested
   against the *coordinate derivative* `∂ᵢφ` — again a smooth compactly
   supported test — gives
   `∫ (K i j ∂ⱼu) ∂ᵢφ = −∫ (K i j) u ∂ⱼ∂ᵢφ − ∫ u (∂ⱼ K i j) ∂ᵢφ`;
2. summing over `i, j`, the first family cancels because `K` is antisymmetric
   and `∇²φ` is symmetric, and the second is `∫ u (f·∇φ)` because the row sums
   of `∇K` are `−f`, again by antisymmetry.  So `∫ (K∇u)·∇φ = ∫ u (f·∇φ)`;
3. the same product rule with the `C¹` multiplier `f i` in direction `i`, tested
   against `φ`, turns that into `−∫ (f·∇u) φ − ∫ u (∇·f) φ`;
4. `∇·f = ∑ᵢⱼ ∂ᵢ∂ⱼ K i j = 0`, again by antisymmetry of `K` and symmetry of the
   second derivative of a `C²` function.

`u ∈ H¹` is used exactly twice, once in each product rule, and no weak Hessian
of `u` appears anywhere.  The matrix field must be `C²`, not merely `C¹`, for
step 4.

## Main results

* `HasWeakDivergenceOn` — the predicate `∫_U F·∇φ = −∫_U G φ` for smooth
  compactly supported `φ`.
* `setIntegral_vecDot_zeroTrace_grad_eq_neg_of_hasWeakDivergenceOn` — the
  integration by parts against an `H¹₀` test, from the weak divergence alone.
* `matFieldDivergence` — the classical divergence of a matrix field.
* `hasWeakDivergenceOn_matVecMul_of_skew` — the skew cancellation.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Sobolev

noncomputable section

variable {d : ℕ}

/-! ## The weak divergence as a test-function predicate -/

/-- **The weak divergence of a vector field on `U`.**  `G` is a weak divergence
of `F` on `U` when `∫_U F·∇φ = −∫_U G φ` for every smooth test function `φ`
compactly supported in `U`.  This is the divergence half of
`Homogenization.HasWeakGradientOn`, and unlike a weak Jacobian it survives for a
skew flux `K ∇u` with `u` merely in `H¹`. -/
def HasWeakDivergenceOn (U : Set (Vec d)) (F : Vec d → Vec d) (G : Vec d → ℝ) :
    Prop :=
  ∀ φ : Vec d → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) φ →
    HasCompactSupport φ →
    tsupport φ ⊆ U →
    ∫ x in U, vecDot (F x) (euclideanGradient φ x) ∂volume =
      -∫ x in U, G x * φ x ∂volume

/-- The `L²` datum of a coordinate derivative of a smooth compactly supported
test function.  It is a copy of the same step inside
`Section3/Terms/EllsepDrift.lean`, which keeps it private. -/
theorem memL2On_euclideanCoordDeriv (U : Set (Vec d)) {φ : Vec d → ℝ} (i : Fin d)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) :
    MemL2On U (fun x => euclideanCoordDeriv i φ x) := by
  have hcont : Continuous (fun x : Vec d => euclideanCoordDeriv i φ x) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcsi : HasCompactSupport (fun x : Vec d => euclideanCoordDeriv i φ x) := by
    simpa [euclideanCoordDeriv] using hcs.fderiv_apply (𝕜 := ℝ) (basisVec i)
  exact (hcont.memLp_of_hasCompactSupport hcsi).restrict U

/-- The pairing of a coordinatewise `L²` field with the gradient of a test
function splits into the sum of its coordinate integrals. -/
private theorem setIntegralVecDotGradSum {U : Set (Vec d)} {F : Vec d → Vec d}
    (hF : ∀ i : Fin d, MemL2On U (fun x => F x i)) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) :
    ∫ x in U, vecDot (F x) (euclideanGradient φ x) ∂volume =
      ∑ i : Fin d, ∫ x in U, F x i * euclideanCoordDeriv i φ x ∂volume := by
  show ∫ x in U, (∑ i : Fin d, F x i * euclideanCoordDeriv i φ x) ∂volume = _
  exact MeasureTheory.integral_finsetSum _
    (fun i _ => (hF i).integrable_mul (memL2On_euclideanCoordDeriv U i hφ hcs))

/-! ## The integration by parts against an `H¹₀` test -/

/-- The smooth compactly supported approximants of an `H¹₀` function are
square-integrable. -/
private theorem approxMemL2 {U : Set (Vec d)} (φ : H10Function U) (n : ℕ) :
    MemL2On U (φ.approx n) :=
  ((φ.approx_smooth n).continuous.memLp_of_hasCompactSupport
    (φ.approx_hasCompactSupport n)).restrict U

/-- **Integration by parts for a weak divergence against a zero-trace test.**
`∫_U F·∇φ = −∫_U (∇·F) φ` for every `φ ∈ H¹₀(U)`, from the weak divergence
alone.  This is the Hessian-free replacement for
`Sobolev/DirichletW2pDivergence.setIntegral_vecDot_zeroTrace_grad_eq_neg`: the
test class is enlarged from smooth compact tests to `H¹₀` through the
approximating sequence bundled in `H10Function`, both sides being continuous
along it because `F` and `G` are square-integrable. -/
theorem setIntegral_vecDot_zeroTrace_grad_eq_neg_of_hasWeakDivergenceOn
    {U : Set (Vec d)} {F : Vec d → Vec d} {G : Vec d → ℝ}
    (hF : ∀ i : Fin d, MemL2On U (fun x => F x i)) (hG : MemL2On U G)
    (hdiv : HasWeakDivergenceOn U F G) (φ : H10Function U) :
    ∫ x in U, vecDot (F x) (φ.toH1Function.grad x) ∂volume =
      -∫ x in U, G x * φ.toH1Function x ∂volume := by
  have hseq : ∀ n : ℕ,
      (∑ i : Fin d, ∫ x in U, F x i * euclideanCoordDeriv i (φ.approx n) x ∂volume)
        = -∫ x in U, G x * φ.approx n x ∂volume := by
    intro n
    rw [← setIntegralVecDotGradSum hF (φ.approx_smooth n) (φ.approx_hasCompactSupport n)]
    exact hdiv (φ.approx n) (φ.approx_smooth n) (φ.approx_hasCompactSupport n)
      (φ.approx_support_subset n)
  -- the left-hand side converges coordinatewise
  have hleftCoord : ∀ i : Fin d,
      Filter.Tendsto
        (fun n => ∫ x in U, F x i * euclideanCoordDeriv i (φ.approx n) x ∂volume)
        Filter.atTop (nhds (∫ x in U, F x i * φ.toH1Function.grad x i ∂volume)) := by
    intro i
    refine tendsto_integral_mul_of_tendsto_toScalarL2 (hF i)
      (fun n => memL2On_euclideanCoordDeriv U i (φ.approx_smooth n) (φ.approx_hasCompactSupport n))
      (φ.toH1Function.gradMemL2 i) ?_
    refine tendsto_toScalarL2_of_tendsto_eLpNorm
      (fun n => memL2On_euclideanCoordDeriv U i (φ.approx_smooth n) (φ.approx_hasCompactSupport n))
      (φ.toH1Function.gradMemL2 i) ?_
    simpa only [euclideanCoordDeriv] using φ.tendsto_approx_grad i
  have hleft : Filter.Tendsto
      (fun n => ∑ i : Fin d,
        ∫ x in U, F x i * euclideanCoordDeriv i (φ.approx n) x ∂volume)
      Filter.atTop
      (nhds (∑ i : Fin d, ∫ x in U, F x i * φ.toH1Function.grad x i ∂volume)) :=
    tendsto_finsetSum _ fun i _ => hleftCoord i
  have hright : Filter.Tendsto
      (fun n => -∫ x in U, G x * φ.approx n x ∂volume) Filter.atTop
      (nhds (-∫ x in U, G x * φ.toH1Function x ∂volume)) :=
    (tendsto_integral_mul_of_tendsto_toScalarL2 hG (fun n => approxMemL2 φ n)
      φ.toH1Function.memL2
      (tendsto_toScalarL2_of_tendsto_eLpNorm (fun n => approxMemL2 φ n)
        φ.toH1Function.memL2 φ.tendsto_approx)).neg
  have hlim : (∑ i : Fin d, ∫ x in U, F x i * φ.toH1Function.grad x i ∂volume)
      = -∫ x in U, G x * φ.toH1Function x ∂volume :=
    tendsto_nhds_unique
      (hleft.congr' (Filter.EventuallyEq.of_eq (funext hseq))) hright
  rw [← hlim]
  show ∫ x in U, (∑ i : Fin d, F x i * φ.toH1Function.grad x i) ∂volume = _
  exact MeasureTheory.integral_finsetSum _
    (fun i _ => (hF i).integrable_mul (φ.toH1Function.gradMemL2 i))

/-! ## Two pieces of classical calculus -/

/-- **The coordinate reading of a second Frechet derivative.**  For a `C²`
scalar field, differentiating the `j`-th coordinate derivative in the `i`-th
direction evaluates the second derivative at the pair of basis vectors. -/
theorem fderiv_coordDeriv_eq_sndFDeriv {h : Vec d → ℝ} (hh : ContDiff ℝ 2 h)
    (x : Vec d) (i j : Fin d) :
    (fderiv ℝ (fun y : Vec d => euclideanCoordDeriv j h y) x) (basisVec i) =
      (fderiv ℝ (fderiv ℝ h) x) (basisVec i) (basisVec j) := by
  have hdiff : DifferentiableAt ℝ (fderiv ℝ h) x :=
    ((hh.fderiv_right (m := 1) le_rfl).differentiable (by simp)) x
  have hcomp : HasFDerivAt (fun y : Vec d => euclideanCoordDeriv j h y)
      ((ContinuousLinearMap.apply ℝ ℝ (basisVec j)).comp (fderiv ℝ (fderiv ℝ h) x)) x :=
    (ContinuousLinearMap.apply ℝ ℝ (basisVec j)).hasFDerivAt.comp x hdiff.hasFDerivAt
  rw [hcomp.fderiv]
  rfl

/-- **Symmetry of the second derivative of a `C²` scalar field.** -/
theorem sndFDeriv_symm {h : Vec d → ℝ} (hh : ContDiff ℝ 2 h) (x v w : Vec d) :
    (fderiv ℝ (fderiv ℝ h) x) v w = (fderiv ℝ (fderiv ℝ h) x) w v :=
  second_derivative_symmetric (f' := fderiv ℝ h)
    (fun y => (hh.differentiable (by norm_num)).differentiableAt.hasFDerivAt)
    (((hh.fderiv_right (m := 1) le_rfl).differentiable (by simp)) x).hasFDerivAt v w

/-- **A doubly indexed antisymmetric array sums to zero.** -/
theorem sum_sum_eq_zero_of_antisymm {T : Fin d → Fin d → ℝ}
    (hT : ∀ i j : Fin d, T i j = -T j i) :
    ∑ i : Fin d, ∑ j : Fin d, T i j = 0 := by
  have hcomm : ∑ i : Fin d, ∑ j : Fin d, T i j = ∑ i : Fin d, ∑ j : Fin d, T j i :=
    Finset.sum_comm
  have hneg : ∑ i : Fin d, ∑ j : Fin d, T j i
      = -∑ i : Fin d, ∑ j : Fin d, T i j := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => hT j i
  have h := hcomm.trans hneg
  linarith only [h]

/-! ## The divergence of a matrix field -/

/-- **The divergence of a matrix field**, in the row convention
`(∇·A) j = ∑ᵢ ∂ᵢ A i j` that `Section2/Cutoff/Drift.lean` fixes for the drift of
the stream matrix. -/
def matFieldDivergence (K : Vec d → Mat d) (x : Vec d) : Vec d :=
  fun j => ∑ i : Fin d, euclideanCoordDeriv i (fun y : Vec d => K y i j) x

/-- A coordinate derivative of a `C²` scalar field is `C¹`. -/
private theorem contDiffOneCoordDeriv {h : Vec d → ℝ} (hh : ContDiff ℝ 2 h)
    (j : Fin d) : ContDiff ℝ 1 (fun x : Vec d => euclideanCoordDeriv j h x) :=
  (hh.fderiv_right (m := 1) le_rfl).clm_apply contDiff_const

/-- A coordinate derivative of a `C¹` scalar field is continuous. -/
private theorem continuousCoordDeriv {g : Vec d → ℝ} (hg : ContDiff ℝ 1 g)
    (i : Fin d) : Continuous (fun x : Vec d => euclideanCoordDeriv i g x) :=
  (hg.continuous_fderiv (by simp)).clm_apply continuous_const

/-- The divergence of a `C²` matrix field is `C¹`. -/
private theorem contDiffOneDivergence {K : Vec d → Mat d}
    (hK : ∀ i j : Fin d, ContDiff ℝ 2 (fun x : Vec d => K x i j)) (j : Fin d) :
    ContDiff ℝ 1 (fun x : Vec d => matFieldDivergence K x j) :=
  ContDiff.sum fun i _ => contDiffOneCoordDeriv (hK i j) i

/-- Antisymmetry passes to the coordinate derivatives of the entries. -/
private theorem coordDerivSkew {K : Vec d → Mat d}
    (hskew : ∀ (x : Vec d) (i j : Fin d), K x i j = -K x j i) (x : Vec d)
    (i j : Fin d) :
    euclideanCoordDeriv j (fun y : Vec d => K y i j) x =
      -euclideanCoordDeriv j (fun y : Vec d => K y j i) x := by
  have hfun : (fun y : Vec d => K y i j) = fun y : Vec d => -(K y j i) :=
    funext fun y => hskew y i j
  have hneg : fderiv ℝ (fun y : Vec d => -K y j i) x =
      -fderiv ℝ (fun y : Vec d => K y j i) x := fderiv_neg
  show (fderiv ℝ (fun y : Vec d => K y i j) x) (basisVec j) =
    -((fderiv ℝ (fun y : Vec d => K y j i) x) (basisVec j))
  rw [hfun, hneg]
  rfl

/-- **The row sums of the Jacobian of an antisymmetric matrix field are minus
its divergence.** -/
private theorem rowSumEqNegDivergence {K : Vec d → Mat d}
    (hskew : ∀ (x : Vec d) (i j : Fin d), K x i j = -K x j i) (x : Vec d)
    (i : Fin d) :
    ∑ j : Fin d, euclideanCoordDeriv j (fun y : Vec d => K y i j) x =
      -matFieldDivergence K x i := by
  show ∑ j : Fin d, euclideanCoordDeriv j (fun y : Vec d => K y i j) x =
    -∑ j : Fin d, euclideanCoordDeriv j (fun y : Vec d => K y j i) x
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => coordDerivSkew hskew x i j

/-- The second derivative of an antisymmetric `C²` matrix field is
antisymmetric in the entry indices. -/
private theorem sndFDerivEntrySkew {K : Vec d → Mat d}
    (hK : ∀ i j : Fin d, ContDiff ℝ 2 (fun x : Vec d => K x i j))
    (hskew : ∀ (x : Vec d) (i j : Fin d), K x i j = -K x j i) (x : Vec d)
    (a b : Fin d) :
    (fderiv ℝ (fderiv ℝ (fun y : Vec d => K y b a)) x) (basisVec a) (basisVec b) =
      -(fderiv ℝ (fderiv ℝ (fun y : Vec d => K y a b)) x) (basisVec b)
        (basisVec a) := by
  have hfun : (fun y : Vec d => K y b a) = fun y : Vec d => -(K y a b) :=
    funext fun y => hskew y b a
  have hneg : fderiv ℝ (fderiv ℝ (fun y : Vec d => K y b a)) x =
      -(fderiv ℝ (fderiv ℝ (fun y : Vec d => K y a b)) x) := by
    rw [hfun, show (fderiv ℝ (fun y : Vec d => -(K y a b)))
        = fun y : Vec d => -(fderiv ℝ (fun z : Vec d => K z a b) y) from
      funext fun y => fderiv_neg]
    exact fderiv_neg
  rw [hneg]
  show -((fderiv ℝ (fderiv ℝ (fun y : Vec d => K y a b)) x) (basisVec a)
      (basisVec b)) = _
  rw [sndFDeriv_symm (hK a b) x (basisVec a) (basisVec b)]

/-- **The divergence of an antisymmetric `C²` matrix field is itself
divergence-free.** -/
private theorem sumCoordDerivDivergenceEqZero {K : Vec d → Mat d}
    (hK : ∀ i j : Fin d, ContDiff ℝ 2 (fun x : Vec d => K x i j))
    (hskew : ∀ (x : Vec d) (i j : Fin d), K x i j = -K x j i) (x : Vec d) :
    ∑ j : Fin d,
        euclideanCoordDeriv j (fun y : Vec d => matFieldDivergence K y j) x = 0 := by
  have hentry : ∀ j : Fin d,
      euclideanCoordDeriv j (fun y : Vec d => matFieldDivergence K y j) x =
        ∑ i : Fin d, (fderiv ℝ (fderiv ℝ (fun y : Vec d => K y i j)) x)
          (basisVec j) (basisVec i) := by
    intro j
    show (fderiv ℝ (fun y : Vec d => ∑ i : Fin d,
        euclideanCoordDeriv i (fun z : Vec d => K z i j) y) x) (basisVec j) = _
    rw [fderiv_fun_sum (fun i _ =>
      ((contDiffOneCoordDeriv (hK i j) i).differentiable (by simp)).differentiableAt),
      sum_apply]
    exact Finset.sum_congr rfl fun i _ =>
      fderiv_coordDeriv_eq_sndFDeriv (hK i j) x j i
  rw [Finset.sum_congr rfl fun j _ => hentry j]
  exact sum_sum_eq_zero_of_antisymm fun a b => sndFDerivEntrySkew hK hskew x a b

/-! ## The `L²` data of the flux and its pieces -/

/-- An entry of a `C²` matrix field times a coordinate of an `H¹` gradient is
square-integrable on the cube. -/
theorem memL2On_entry_mul_gradCoord (Q : TriadicCube d) {K : Vec d → Mat d}
    (hK : ∀ i j : Fin d, ContDiff ℝ 2 (fun x : Vec d => K x i j))
    (u : H1Function (openCubeSet Q)) (i j : Fin d) :
    MemL2On (openCubeSet Q) (fun x => K x i j * u.grad x j) :=
  (memLpOn_openCubeSet_of_continuous (p := ⊤) Q (hK i j).continuous).fun_mul
    (u.gradMemL2 j)

/-- The value of an `H¹` function times a coordinate derivative of an entry of a
`C²` matrix field is square-integrable on the cube. -/
private theorem memL2OnValueEntryDeriv (Q : TriadicCube d) {K : Vec d → Mat d}
    (hK : ∀ i j : Fin d, ContDiff ℝ 2 (fun x : Vec d => K x i j))
    (u : H1Function (openCubeSet Q)) (i j : Fin d) :
    MemL2On (openCubeSet Q)
      (fun x => u.toFun x * euclideanCoordDeriv j (fun y : Vec d => K y i j) x) :=
  u.memL2.fun_mul (memLpOn_openCubeSet_of_continuous (p := ⊤) Q
    (contDiffOneCoordDeriv (hK i j) j).continuous)

/-- An entry of a `C²` matrix field times the value of an `H¹` function is
square-integrable on the cube. -/
private theorem memL2OnEntryValue (Q : TriadicCube d) {K : Vec d → Mat d}
    (hK : ∀ i j : Fin d, ContDiff ℝ 2 (fun x : Vec d => K x i j))
    (u : H1Function (openCubeSet Q)) (i j : Fin d) :
    MemL2On (openCubeSet Q) (fun x => K x i j * u.toFun x) :=
  (memLpOn_openCubeSet_of_continuous (p := ⊤) Q (hK i j).continuous).fun_mul u.memL2

/-! ## The three summed families -/

/-- **The pair identity**: the `C¹`-multiplier product rule applied to the
multiplier `K i j` and the `H¹` function `u` in direction `j`, tested against the
coordinate derivative `∂ᵢφ`. -/
private theorem skewPairIdentity (Q : TriadicCube d) {K : Vec d → Mat d}
    (hK : ∀ i j : Fin d, ContDiff ℝ 2 (fun x : Vec d => K x i j))
    (u : H1Function (openCubeSet Q)) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ openCubeSet Q) (i j : Fin d) :
    (∫ x in openCubeSet Q,
        (K x i j * u.grad x j) * euclideanCoordDeriv i φ x ∂volume) +
      ∫ x in openCubeSet Q,
        (u.toFun x * euclideanCoordDeriv j (fun y : Vec d => K y i j) x) *
          euclideanCoordDeriv i φ x ∂volume =
      -∫ x in openCubeSet Q, (K x i j * u.toFun x) *
        euclideanCoordDeriv j (euclideanCoordDeriv i φ) x ∂volume := by
  have hDL2 : MemL2On (openCubeSet Q) (fun x => euclideanCoordDeriv i φ x) :=
    memL2On_euclideanCoordDeriv (openCubeSet Q) i hφ hcs
  have hsplit : ∫ x in openCubeSet Q, (K x i j * u.grad x j +
        u.toFun x * euclideanCoordDeriv j (fun y : Vec d => K y i j) x) *
        euclideanCoordDeriv i φ x ∂volume =
      (∫ x in openCubeSet Q,
          (K x i j * u.grad x j) * euclideanCoordDeriv i φ x ∂volume) +
        ∫ x in openCubeSet Q,
          (u.toFun x * euclideanCoordDeriv j (fun y : Vec d => K y i j) x) *
            euclideanCoordDeriv i φ x ∂volume := by
    rw [show (fun x : Vec d => (K x i j * u.grad x j +
          u.toFun x * euclideanCoordDeriv j (fun y : Vec d => K y i j) x) *
          euclideanCoordDeriv i φ x)
        = fun x : Vec d => (K x i j * u.grad x j) * euclideanCoordDeriv i φ x +
          (u.toFun x * euclideanCoordDeriv j (fun y : Vec d => K y i j) x) *
            euclideanCoordDeriv i φ x from funext fun x => add_mul _ _ _]
    exact MeasureTheory.integral_add
      ((memL2On_entry_mul_gradCoord Q hK u i j).integrable_mul hDL2)
      ((memL2OnValueEntryDeriv Q hK u i j).integrable_mul hDL2)
  have hw : (∫ x in openCubeSet Q, (K x i j * u.toFun x) *
        euclideanCoordDeriv j (euclideanCoordDeriv i φ) x ∂volume) =
      -∫ x in openCubeSet Q, (K x i j * u.grad x j +
        u.toFun x * euclideanCoordDeriv j (fun y : Vec d => K y i j) x) *
        euclideanCoordDeriv i φ x ∂volume :=
    hasWeakGradientOn_mul_of_contDiff_one Q ((hK i j).of_le (by norm_num)) u j
      (euclideanCoordDeriv i φ) (contDiff_euclideanCoordDeriv hφ i)
      (hasCompactSupport_euclideanCoordDeriv hcs i)
      ((tsupport_euclideanCoordDeriv_subset_tsupport i φ).trans hsub)
  rw [← hsplit, hw, neg_neg]

/-- The flux pairing is the doubly indexed sum of the pair identities'
first terms. -/
private theorem fluxPairingSum (Q : TriadicCube d) {K : Vec d → Mat d}
    (hK : ∀ i j : Fin d, ContDiff ℝ 2 (fun x : Vec d => K x i j))
    (u : H1Function (openCubeSet Q)) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) :
    ∫ x in openCubeSet Q,
        vecDot (matVecMul (K x) (u.grad x)) (euclideanGradient φ x) ∂volume =
      ∑ i : Fin d, ∑ j : Fin d, ∫ x in openCubeSet Q,
        (K x i j * u.grad x j) * euclideanCoordDeriv i φ x ∂volume := by
  have hint : ∀ i j : Fin d, IntegrableOn (fun x : Vec d =>
      (K x i j * u.grad x j) * euclideanCoordDeriv i φ x)
      (openCubeSet Q) volume := fun i j =>
    (memL2On_entry_mul_gradCoord Q hK u i j).integrable_mul
      (memL2On_euclideanCoordDeriv (openCubeSet Q) i hφ hcs)
  have hpt : (fun x : Vec d =>
        vecDot (matVecMul (K x) (u.grad x)) (euclideanGradient φ x))
      = fun x : Vec d => ∑ i : Fin d, ∑ j : Fin d,
        (K x i j * u.grad x j) * euclideanCoordDeriv i φ x := by
    funext x
    show ∑ i : Fin d, (∑ j : Fin d, K x i j * u.grad x j) *
      euclideanCoordDeriv i φ x = _
    exact Finset.sum_congr rfl fun i _ => Finset.sum_mul _ _ _
  rw [hpt, MeasureTheory.integral_finsetSum _ (fun i _ =>
    MeasureTheory.integrable_finsetSum _ (fun j _ => hint i j))]
  exact Finset.sum_congr rfl fun i _ =>
    MeasureTheory.integral_finsetSum _ (fun j _ => hint i j)

/-- The doubly indexed sum of the pair identities' second terms is the pairing
of the value with the divergence, with a sign. -/
private theorem valueDivergencePairingSum (Q : TriadicCube d) {K : Vec d → Mat d}
    (hK : ∀ i j : Fin d, ContDiff ℝ 2 (fun x : Vec d => K x i j))
    (hskew : ∀ (x : Vec d) (i j : Fin d), K x i j = -K x j i)
    (u : H1Function (openCubeSet Q)) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) :
    ∑ i : Fin d, ∑ j : Fin d, ∫ x in openCubeSet Q,
        (u.toFun x * euclideanCoordDeriv j (fun y : Vec d => K y i j) x) *
          euclideanCoordDeriv i φ x ∂volume =
      -∫ x in openCubeSet Q,
        u.toFun x * vecDot (matFieldDivergence K x) (euclideanGradient φ x) ∂volume := by
  have hint : ∀ i j : Fin d, IntegrableOn (fun x : Vec d =>
      (u.toFun x * euclideanCoordDeriv j (fun y : Vec d => K y i j) x) *
        euclideanCoordDeriv i φ x) (openCubeSet Q) volume := fun i j =>
    (memL2OnValueEntryDeriv Q hK u i j).integrable_mul
      (memL2On_euclideanCoordDeriv (openCubeSet Q) i hφ hcs)
  have hpt : (fun x : Vec d => ∑ i : Fin d, ∑ j : Fin d,
        (u.toFun x * euclideanCoordDeriv j (fun y : Vec d => K y i j) x) *
          euclideanCoordDeriv i φ x)
      = fun x : Vec d => -(u.toFun x *
          vecDot (matFieldDivergence K x) (euclideanGradient φ x)) := by
    funext x
    have hrow : ∀ i : Fin d, ∑ j : Fin d,
        (u.toFun x * euclideanCoordDeriv j (fun y : Vec d => K y i j) x) *
          euclideanCoordDeriv i φ x =
        -(u.toFun x * (matFieldDivergence K x i * euclideanCoordDeriv i φ x)) := by
      intro i
      rw [← Finset.sum_mul, ← Finset.mul_sum, rowSumEqNegDivergence hskew x i]
      ring
    calc ∑ i : Fin d, ∑ j : Fin d,
          (u.toFun x * euclideanCoordDeriv j (fun y : Vec d => K y i j) x) *
            euclideanCoordDeriv i φ x
        = ∑ i : Fin d,
            -(u.toFun x * (matFieldDivergence K x i * euclideanCoordDeriv i φ x)) :=
          Finset.sum_congr rfl fun i _ => hrow i
      _ = -(u.toFun x * vecDot (matFieldDivergence K x) (euclideanGradient φ x)) := by
          rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
          rfl
  have hsum : ∑ i : Fin d, ∑ j : Fin d, ∫ x in openCubeSet Q,
        (u.toFun x * euclideanCoordDeriv j (fun y : Vec d => K y i j) x) *
          euclideanCoordDeriv i φ x ∂volume =
      ∫ x in openCubeSet Q, (∑ i : Fin d, ∑ j : Fin d,
        (u.toFun x * euclideanCoordDeriv j (fun y : Vec d => K y i j) x) *
          euclideanCoordDeriv i φ x) ∂volume := by
    rw [MeasureTheory.integral_finsetSum _ (fun i _ =>
      MeasureTheory.integrable_finsetSum _ (fun j _ => hint i j))]
    exact Finset.sum_congr rfl fun i _ =>
      (MeasureTheory.integral_finsetSum _ (fun j _ => hint i j)).symm
  rw [hsum, hpt, MeasureTheory.integral_neg]

/-- The doubly indexed sum of the pair identities' right-hand sides vanishes:
`K` is antisymmetric and the Hessian of a smooth test function is symmetric. -/
private theorem hessianPairingSum (Q : TriadicCube d) {K : Vec d → Mat d}
    (hK : ∀ i j : Fin d, ContDiff ℝ 2 (fun x : Vec d => K x i j))
    (hskew : ∀ (x : Vec d) (i j : Fin d), K x i j = -K x j i)
    (u : H1Function (openCubeSet Q)) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) :
    ∑ i : Fin d, ∑ j : Fin d, ∫ x in openCubeSet Q, (K x i j * u.toFun x) *
        euclideanCoordDeriv j (euclideanCoordDeriv i φ) x ∂volume = 0 := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le ENat.LEInfty.out
  have hint : ∀ i j : Fin d, IntegrableOn (fun x : Vec d => (K x i j * u.toFun x) *
      euclideanCoordDeriv j (euclideanCoordDeriv i φ) x)
      (openCubeSet Q) volume := fun i j =>
    (memL2OnEntryValue Q hK u i j).integrable_mul
      (memL2On_euclideanCoordDeriv (openCubeSet Q) j
        (contDiff_euclideanCoordDeriv hφ i)
        (hasCompactSupport_euclideanCoordDeriv hcs i))
  have hpt : ∀ x : Vec d, ∑ i : Fin d, ∑ j : Fin d, (K x i j * u.toFun x) *
      euclideanCoordDeriv j (euclideanCoordDeriv i φ) x = 0 := by
    intro x
    refine sum_sum_eq_zero_of_antisymm fun i j => ?_
    have hsym : euclideanCoordDeriv i (euclideanCoordDeriv j φ) x =
        euclideanCoordDeriv j (euclideanCoordDeriv i φ) x := by
      show (fderiv ℝ (fun y : Vec d => euclideanCoordDeriv j φ y) x) (basisVec i) =
        (fderiv ℝ (fun y : Vec d => euclideanCoordDeriv i φ y) x) (basisVec j)
      rw [fderiv_coordDeriv_eq_sndFDeriv hφ2 x i j,
        fderiv_coordDeriv_eq_sndFDeriv hφ2 x j i]
      exact sndFDeriv_symm hφ2 x (basisVec i) (basisVec j)
    rw [hskew x j i, hsym]
    ring
  have hsum : ∑ i : Fin d, ∑ j : Fin d, ∫ x in openCubeSet Q,
        (K x i j * u.toFun x) *
          euclideanCoordDeriv j (euclideanCoordDeriv i φ) x ∂volume =
      ∫ x in openCubeSet Q, (∑ i : Fin d, ∑ j : Fin d, (K x i j * u.toFun x) *
        euclideanCoordDeriv j (euclideanCoordDeriv i φ) x) ∂volume := by
    rw [MeasureTheory.integral_finsetSum _ (fun i _ =>
      MeasureTheory.integrable_finsetSum _ (fun j _ => hint i j))]
    exact Finset.sum_congr rfl fun i _ =>
      (MeasureTheory.integral_finsetSum _ (fun j _ => hint i j)).symm
  have hzero : ∫ x in openCubeSet Q, (∑ i : Fin d, ∑ j : Fin d,
      (K x i j * u.toFun x) *
        euclideanCoordDeriv j (euclideanCoordDeriv i φ) x) ∂volume = 0 := by
    simp only [hpt]
    exact MeasureTheory.integral_zero _ _
  exact hsum.trans hzero

/-! ## Moving the divergence back onto the gradient -/

/-- **The second integration by parts**, with the `C¹` multiplier `f i = (∇·K) i`
and the `H¹` function `u`.  The correction term vanishes because the divergence
of an antisymmetric `C²` matrix field is itself divergence-free. -/
private theorem divergencePartsIdentity (Q : TriadicCube d) {K : Vec d → Mat d}
    (hK : ∀ i j : Fin d, ContDiff ℝ 2 (fun x : Vec d => K x i j))
    (hskew : ∀ (x : Vec d) (i j : Fin d), K x i j = -K x j i)
    (u : H1Function (openCubeSet Q)) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ)
    (hsub : tsupport φ ⊆ openCubeSet Q) :
    ∫ x in openCubeSet Q,
        u.toFun x * vecDot (matFieldDivergence K x) (euclideanGradient φ x) ∂volume =
      -∫ x in openCubeSet Q,
        vecDot (matFieldDivergence K x) (u.grad x) * φ x ∂volume := by
  have hφL2 : MemL2On (openCubeSet Q) φ :=
    (hφ.continuous.memLp_of_hasCompactSupport hcs).restrict (openCubeSet Q)
  have hvalue : ∀ i : Fin d, MemL2On (openCubeSet Q)
      (fun x => matFieldDivergence K x i * u.toFun x) := fun i =>
    (memLpOn_openCubeSet_of_continuous (p := ⊤) Q
      (contDiffOneDivergence hK i).continuous).fun_mul u.memL2
  have hgrad : ∀ i : Fin d, MemL2On (openCubeSet Q)
      (fun x => matFieldDivergence K x i * u.grad x i) := fun i =>
    (memLpOn_openCubeSet_of_continuous (p := ⊤) Q
      (contDiffOneDivergence hK i).continuous).fun_mul (u.gradMemL2 i)
  have hcorr : ∀ i : Fin d, MemL2On (openCubeSet Q)
      (fun x => u.toFun x *
        euclideanCoordDeriv i (fun y : Vec d => matFieldDivergence K y i) x) := fun i =>
    u.memL2.fun_mul (memLpOn_openCubeSet_of_continuous (p := ⊤) Q
      (continuousCoordDeriv (contDiffOneDivergence hK i) i))
  have hpair : ∀ i : Fin d,
      (∫ x in openCubeSet Q,
          (matFieldDivergence K x i * u.toFun x) * euclideanCoordDeriv i φ x ∂volume) =
        -((∫ x in openCubeSet Q,
            (matFieldDivergence K x i * u.grad x i) * φ x ∂volume) +
          ∫ x in openCubeSet Q, (u.toFun x *
            euclideanCoordDeriv i (fun y : Vec d => matFieldDivergence K y i) x) *
            φ x ∂volume) := by
    intro i
    have hw : (∫ x in openCubeSet Q,
          (matFieldDivergence K x i * u.toFun x) * euclideanCoordDeriv i φ x ∂volume) =
        -∫ x in openCubeSet Q, (matFieldDivergence K x i * u.grad x i +
          u.toFun x *
            euclideanCoordDeriv i (fun y : Vec d => matFieldDivergence K y i) x) *
          φ x ∂volume :=
      hasWeakGradientOn_mul_of_contDiff_one Q (contDiffOneDivergence hK i) u i φ
        hφ hcs hsub
    have hadd : ∫ x in openCubeSet Q, (matFieldDivergence K x i * u.grad x i +
          u.toFun x *
            euclideanCoordDeriv i (fun y : Vec d => matFieldDivergence K y i) x) *
          φ x ∂volume =
        (∫ x in openCubeSet Q,
            (matFieldDivergence K x i * u.grad x i) * φ x ∂volume) +
          ∫ x in openCubeSet Q, (u.toFun x *
            euclideanCoordDeriv i (fun y : Vec d => matFieldDivergence K y i) x) *
            φ x ∂volume := by
      rw [show (fun x : Vec d => (matFieldDivergence K x i * u.grad x i +
            u.toFun x *
              euclideanCoordDeriv i (fun y : Vec d => matFieldDivergence K y i) x) *
            φ x)
          = fun x : Vec d => (matFieldDivergence K x i * u.grad x i) * φ x +
            (u.toFun x *
              euclideanCoordDeriv i (fun y : Vec d => matFieldDivergence K y i) x) *
              φ x from funext fun x => add_mul _ _ _]
      exact MeasureTheory.integral_add ((hgrad i).integrable_mul hφL2)
        ((hcorr i).integrable_mul hφL2)
    rw [hw, hadd]
  -- the three sums
  have hptLeft : (fun x : Vec d =>
        u.toFun x * vecDot (matFieldDivergence K x) (euclideanGradient φ x))
      = fun x : Vec d => ∑ i : Fin d,
        (matFieldDivergence K x i * u.toFun x) * euclideanCoordDeriv i φ x := by
    funext x
    show u.toFun x * ∑ i : Fin d,
      matFieldDivergence K x i * euclideanCoordDeriv i φ x = _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hleft : ∫ x in openCubeSet Q,
        u.toFun x * vecDot (matFieldDivergence K x) (euclideanGradient φ x) ∂volume =
      ∑ i : Fin d, ∫ x in openCubeSet Q,
        (matFieldDivergence K x i * u.toFun x) * euclideanCoordDeriv i φ x ∂volume := by
    rw [hptLeft]
    exact MeasureTheory.integral_finsetSum _
      (fun i _ => (hvalue i).integrable_mul
        (memL2On_euclideanCoordDeriv (openCubeSet Q) i hφ hcs))
  have hright : ∫ x in openCubeSet Q,
        vecDot (matFieldDivergence K x) (u.grad x) * φ x ∂volume =
      ∑ i : Fin d, ∫ x in openCubeSet Q,
        (matFieldDivergence K x i * u.grad x i) * φ x ∂volume := by
    rw [show (fun x : Vec d =>
          vecDot (matFieldDivergence K x) (u.grad x) * φ x)
        = fun x : Vec d => ∑ i : Fin d,
          (matFieldDivergence K x i * u.grad x i) * φ x from
      funext fun x => Finset.sum_mul _ _ _]
    exact MeasureTheory.integral_finsetSum _
      (fun i _ => (hgrad i).integrable_mul hφL2)
  have hcorrPt : ∀ x : Vec d, ∑ i : Fin d, (u.toFun x *
      euclideanCoordDeriv i (fun y : Vec d => matFieldDivergence K y i) x) *
      φ x = 0 := by
    intro x
    have hfac : ∀ i : Fin d, (u.toFun x *
        euclideanCoordDeriv i (fun y : Vec d => matFieldDivergence K y i) x) * φ x =
      (u.toFun x * φ x) *
        euclideanCoordDeriv i (fun y : Vec d => matFieldDivergence K y i) x :=
      fun i => by ring
    rw [Finset.sum_congr rfl fun i _ => hfac i, ← Finset.mul_sum,
      sumCoordDerivDivergenceEqZero hK hskew x, mul_zero]
  have hcorrSum := MeasureTheory.integral_finsetSum
    (μ := volume.restrict (openCubeSet Q)) (Finset.univ : Finset (Fin d))
    (f := fun (i : Fin d) (x : Vec d) => (u.toFun x *
      euclideanCoordDeriv i (fun y : Vec d => matFieldDivergence K y i) x) * φ x)
    (fun i _ => (hcorr i).integrable_mul hφL2)
  have hcorrIntZero : ∫ x in openCubeSet Q, (∑ i : Fin d, (u.toFun x *
      euclideanCoordDeriv i (fun y : Vec d => matFieldDivergence K y i) x) *
      φ x) ∂volume = 0 := by
    simp only [hcorrPt]
    exact MeasureTheory.integral_zero _ _
  have hcorrZero : ∑ i : Fin d, ∫ x in openCubeSet Q, (u.toFun x *
        euclideanCoordDeriv i (fun y : Vec d => matFieldDivergence K y i) x) *
        φ x ∂volume = 0 := hcorrSum.symm.trans hcorrIntZero
  have hsum : ∑ i : Fin d, (∫ x in openCubeSet Q,
        (matFieldDivergence K x i * u.toFun x) * euclideanCoordDeriv i φ x ∂volume) =
      ∑ i : Fin d, -((∫ x in openCubeSet Q,
          (matFieldDivergence K x i * u.grad x i) * φ x ∂volume) +
        ∫ x in openCubeSet Q, (u.toFun x *
          euclideanCoordDeriv i (fun y : Vec d => matFieldDivergence K y i) x) *
          φ x ∂volume) := Finset.sum_congr rfl fun i _ => hpair i
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib] at hsum
  rw [hleft, hright, hsum, hcorrZero, add_zero]

/-! ## The skew cancellation -/

/-- **The skew flux `K ∇u` has a weak divergence for `u` merely in `H¹`.**  For
an antisymmetric `C²` matrix field `K` on a cube and `u ∈ H¹`,

`∇·(K ∇u) = (∇·K)·∇u`

in the weak sense of `HasWeakDivergenceOn`.  This is the assertion of the paper
for the skew flux, and it needs no weak Hessian of `u`: the second-order terms cancel against
the antisymmetry of `K` before any second derivative of `u` is required. -/
theorem hasWeakDivergenceOn_matVecMul_of_skew (Q : TriadicCube d)
    {K : Vec d → Mat d}
    (hK : ∀ i j : Fin d, ContDiff ℝ 2 (fun x : Vec d => K x i j))
    (hskew : ∀ (x : Vec d) (i j : Fin d), K x i j = -K x j i)
    (u : H1Function (openCubeSet Q)) :
    HasWeakDivergenceOn (openCubeSet Q) (fun x => matVecMul (K x) (u.grad x))
      (fun x => vecDot (matFieldDivergence K x) (u.grad x)) := by
  intro φ hφ hcs hsub
  show (∫ x in openCubeSet Q,
      vecDot (matVecMul (K x) (u.grad x)) (euclideanGradient φ x) ∂volume) =
    -∫ x in openCubeSet Q,
      vecDot (matFieldDivergence K x) (u.grad x) * φ x ∂volume
  have hsumpair : ∑ i : Fin d, ∑ j : Fin d,
      ((∫ x in openCubeSet Q,
          (K x i j * u.grad x j) * euclideanCoordDeriv i φ x ∂volume) +
        ∫ x in openCubeSet Q,
          (u.toFun x * euclideanCoordDeriv j (fun y : Vec d => K y i j) x) *
            euclideanCoordDeriv i φ x ∂volume) =
      ∑ i : Fin d, ∑ j : Fin d,
        -∫ x in openCubeSet Q, (K x i j * u.toFun x) *
          euclideanCoordDeriv j (euclideanCoordDeriv i φ) x ∂volume :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      skewPairIdentity Q hK u hφ hcs hsub i j
  have hleftSplit : ∑ i : Fin d, ∑ j : Fin d,
      ((∫ x in openCubeSet Q,
          (K x i j * u.grad x j) * euclideanCoordDeriv i φ x ∂volume) +
        ∫ x in openCubeSet Q,
          (u.toFun x * euclideanCoordDeriv j (fun y : Vec d => K y i j) x) *
            euclideanCoordDeriv i φ x ∂volume) =
      (∑ i : Fin d, ∑ j : Fin d, ∫ x in openCubeSet Q,
          (K x i j * u.grad x j) * euclideanCoordDeriv i φ x ∂volume) +
        ∑ i : Fin d, ∑ j : Fin d, ∫ x in openCubeSet Q,
          (u.toFun x * euclideanCoordDeriv j (fun y : Vec d => K y i j) x) *
            euclideanCoordDeriv i φ x ∂volume := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
  have hrightSplit : ∑ i : Fin d, ∑ j : Fin d,
      (-∫ x in openCubeSet Q, (K x i j * u.toFun x) *
        euclideanCoordDeriv j (euclideanCoordDeriv i φ) x ∂volume) =
      -∑ i : Fin d, ∑ j : Fin d, ∫ x in openCubeSet Q, (K x i j * u.toFun x) *
        euclideanCoordDeriv j (euclideanCoordDeriv i φ) x ∂volume := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_neg_distrib _
  rw [hleftSplit, hrightSplit, fluxPairingSum Q hK u hφ hcs |>.symm,
    valueDivergencePairingSum Q hK hskew u hφ hcs,
    hessianPairingSum Q hK hskew u hφ hcs, neg_zero] at hsumpair
  rw [divergencePartsIdentity Q hK hskew u hφ hcs hsub] at hsumpair
  linarith only [hsumpair]

end

end SuperdiffusionCLT.Section3.Terms
