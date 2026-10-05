/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Frozen.Section2.CoefficientCutoff
public import SuperdiffusionCLT.Section2.Cutoff.Drift
public import SuperdiffusionCLT.Section3.Setup.Scales
public import SuperdiffusionCLT.Section3.Setup.Parameters
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementCubeMomentLocality
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinftyLargeCube

/-!
# The master identity `e.ellsep.testing`

The identity on which the whole of Section 3 rests.  Testing the equation `e.ellsep`
(`-∇·a_ℓ∇u_m = (f_{L'} − f_ℓ)·∇u_m` in `cu_m`) and the Dirichlet problem
`e.def.w` against `w`, the paper obtains the two displays

* `⨍_{cu_m} ∇w·a_ℓ∇u_m = ⨍_{cu_m} w (f_{L'} − f_ℓ)·∇u_m
   = p·⨍_{cu_m} w (f_{L'} − f_ℓ) + ⨍_{cu_m} w (f_{L'} − f_ℓ)·(∇u_m − p)`, and
* `e.w.testing.formula`:
  `⨍_{cu_m} |∇w|² = p·⨍_{cu_m} w (f_{L'} − f_{ℓ'})
   = p·⨍_{cu_m} w (f_{L'} − f_ℓ) + p·⨍_{cu_m} w (f_ℓ − f_{ℓ'})`,

combines them with the vector `q` of `e.Sec3.p.q.def` into the
combined testing display (`ellsep_testing` below), and then splits the terms
involving `∇u_m` into the smaller-scale maximizers and the additivity defect,
using `a_{L'} = a_ℓ + k_{L'} − k_ℓ`, to reach `e.ellsep.testing`
(`ellsep_testing_decomposition` below).

## What is proved and what is carried

The four printed testing displays are carried as explicit hypotheses in the
exact shapes of the paper; they are the steps whose inputs — the equation satisfied
by the maximizer `u_m` on `cu_m`, and the integration by parts in the paper,
which uses the antisymmetry of `k_{L'}` and `k_ℓ` and the vanishing of the
contraction of an antisymmetric matrix with the Hessian of `u_m` — have no
carrier at this surface (`e.ellsep` itself is not available here; the paper
writes it for the maximizer `u_m = u_{m,0}`, whose gradient is the
free binder `uMgrad` here).

Everything else is proved:

* the insertion of `q`, which is the silent use of
  `(∇w)_{cu_m} = 0` for the zero-trace response `w` (`H10Function`), available in
  `CoarseGraining` as `H10Function.averageGradient_eq_zero`;
* the passage from the combined testing display to `e.ellsep.testing`, i.e.
  the splitting sentence of the paper: it is the pointwise vector identity
  `a_ℓ v + (k_{L'} − k_ℓ) v = a_{L'} v` together with the splitting
  `∇u_m = ∇u_n + (∇u_m − ∇u_n)`, and holds under the linearity of the
  normalized cube average alone;
* the expectation form `ellsep_testing_annealed`, the display as the four term
  lemmas of Section 3 consume it.

A *carrier bridge* used downstream is also proved here:
`volumeAverage_originCube_eq_subcube_avsum` (the printed `⨍_{cu_m}` of
`e.ellsep.testing` equals the lattice average `avsum_{z ∈ 3^nℤ^d ∩ cu_m}
⨍_{z+cu_n}` in which `l.RHS.term2` is stated, a rewriting the paper does not
remark on).
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream

noncomputable section

variable {d : ℕ}

/-! ## Elementary algebra of the normalized cube average -/

private theorem volumeAverageAdd {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : IntegrableOn f U volume) (hg : IntegrableOn g U volume) :
    volumeAverage U (fun x => f x + g x) = volumeAverage U f + volumeAverage U g := by
  simp only [volumeAverage]
  rw [MeasureTheory.integral_add hf hg]
  ring

private theorem volumeAverageNeg {U : Set (Vec d)} (f : Vec d → ℝ) :
    volumeAverage U (fun x => -f x) = -volumeAverage U f := by
  simp only [volumeAverage]
  rw [MeasureTheory.integral_neg]
  ring

private theorem integrableOnVecDotConstRight {U : Set (Vec d)} {F : Vec d → Vec d}
    (c : Vec d) (hF : ∀ i : Fin d, IntegrableOn (fun x => F x i) U volume) :
    IntegrableOn (fun x => vecDot (F x) c) U volume := by
  have hrw : (fun x => vecDot (F x) c) = fun x => ∑ i : Fin d, F x i * c i := rfl
  rw [hrw]
  exact MeasureTheory.integrable_finsetSum _ fun i _ => (hF i).mul_const (c i)

private theorem volumeAverageVecDotConstRight {U : Set (Vec d)} (c : Vec d)
    {F : Vec d → Vec d} (hF : ∀ i : Fin d, IntegrableOn (fun x => F x i) U volume) :
    volumeAverage U (fun x => vecDot (F x) c) = vecDot (volumeAverageVec U F) c := by
  have hrw : (fun x => vecDot (F x) c)
      = fun x => ∑ i : Fin d, (fun (a : Fin d) (y : Vec d) => F y a * c a) i x := rfl
  have htarget : vecDot (volumeAverageVec U F) c
      = ∑ i : Fin d, volumeAverage U (fun y => F y i) * c i := rfl
  rw [hrw, Homogenization.volumeAverage_sum Finset.univ
      (fun (a : Fin d) (y : Vec d) => F y a * c a)
      (fun a _ => (hF a).mul_const (c a)), htarget]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsm : (fun y : Vec d => F y i * c i) = (c i) • fun y : Vec d => F y i := by
    funext y
    show F y i * c i = c i * F y i
    ring
  show volumeAverage U (fun y : Vec d => F y i * c i)
      = volumeAverage U (fun y => F y i) * c i
  rw [hsm, Homogenization.volumeAverage_smul]
  ring

/-- Integrability of the coordinates of the weak gradient of an `H¹` function on
a finite-measure domain. -/
private theorem integrableOnGradCoord {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (u : H1Function U) (i : Fin d) :
    IntegrableOn (fun x => u.grad x i) U volume := by
  simpa only [MeasureTheory.IntegrableOn, volumeMeasureOn] using
    (u.gradMemL2 i).integrable (by norm_num : (1 : ENNReal) ≤ 2)

/-! ## `(∇w)_{cu_m} = 0` and the insertion of `q` -/

/-- **The zero-trace response has vanishing mean gradient on the cube.**  This
is the fact the paper uses silently to insert the vector `q` of
`e.Sec3.p.q.def` into the first term. -/
theorem volumeAverageVec_grad_eq_zero (m : ℤ)
    (w : H10Function (openCubeSet (originCube d m))) :
    volumeAverageVec (openCubeSet (originCube d m)) w.toH1Function.grad = 0 :=
  w.averageGradient_eq_zero

/-- **The insertion of `q`**: subtracting a constant vector from the
second factor does not change the normalized average of its pairing with
`∇w`, because `(∇w)_{cu_m} = 0`. -/
theorem volumeAverage_vecDot_grad_sub_const (m : ℤ)
    (w : H10Function (openCubeSet (originCube d m))) (F : Vec d → Vec d) (q : Vec d)
    (hF : IntegrableOn (fun x => vecDot (w.toH1Function.grad x) (F x))
      (openCubeSet (originCube d m)) volume) :
    volumeAverage (openCubeSet (originCube d m))
        (fun x => vecDot (w.toH1Function.grad x) (F x - q)) =
      volumeAverage (openCubeSet (originCube d m))
        (fun x => vecDot (w.toH1Function.grad x) (F x)) := by
  have hgrad : ∀ i : Fin d, IntegrableOn (fun x => w.toH1Function.grad x i)
      (openCubeSet (originCube d m)) volume :=
    fun i => integrableOnGradCoord w.toH1Function i
  have hconst : IntegrableOn
      (fun x => -vecDot (w.toH1Function.grad x) q)
      (openCubeSet (originCube d m)) volume :=
    (integrableOnVecDotConstRight (F := w.toH1Function.grad) q hgrad).neg
  have hpt : (fun x => vecDot (w.toH1Function.grad x) (F x - q))
      = fun x => vecDot (w.toH1Function.grad x) (F x) +
          -vecDot (w.toH1Function.grad x) q := by
    funext x
    rw [show F x - q = F x + -q from (sub_eq_add_neg _ _),
      vecDot_add_right, vecDot_neg_right]
  rw [hpt, volumeAverageAdd hF hconst, volumeAverageNeg,
    volumeAverageVecDotConstRight (F := w.toH1Function.grad) q hgrad,
    volumeAverageVec_grad_eq_zero m w]
  have hzero : vecDot (0 : Vec d) q = 0 := by
    show ∑ i : Fin d, (0 : Vec d) i * q i = 0
    exact Finset.sum_eq_zero fun i _ => by simp
  rw [hzero]
  ring

/-! ## The two carrier bridges -/

/-- The two realizations of a triadic cube give the same normalized average:
they differ by a Lebesgue-null set. -/
private theorem volumeAverageOpenEqClosed (Q : TriadicCube d) (f : Vec d → ℝ) :
    volumeAverage (openCubeSet Q) f = volumeAverage (cubeSet Q) f := by
  simp only [volumeAverage, volume_openCubeSet_eq_volume_cubeSet]
  rw [MeasureTheory.setIntegral_congr_set (cubeSet_ae_eq_openCubeSet Q)]

/-- **The cube-partition bridge.**  The normalized average over `cu_l` of the
print's `e.ellsep.testing` is the plain average of the normalized averages over
the scale-`n` sub-cubes `z + cu_n`, `z ∈ 3^nℤ^d ∩ cu_l`, which is the form in
which `l.RHS.term2` states its term.  The paper does not remark on
this rewriting. -/
theorem volumeAverage_originCube_eq_subcube_avsum {n l : ℕ} {f : Vec d → ℝ}
    (hf : ∀ R ∈ largeCubeSubcubes d n l, IntegrableOn f (cubeSet R) volume) :
    volumeAverage (openCubeSet (originCube d (l : ℤ))) f =
      ((largeCubeSubcubes d n l).card : ℝ)⁻¹ *
        ∑ R ∈ largeCubeSubcubes d n l, volumeAverage (openCubeSet R) f := by
  rw [volumeAverageOpenEqClosed,
    volumeAverage_cubeSet_eq_inv_card_mul_sum_descendants (originCube d (l : ℤ)) (l - n) hf]
  refine congrArg (fun t => ((largeCubeSubcubes d n l).card : ℝ)⁻¹ * t) ?_
  exact Finset.sum_congr rfl fun R _ => (volumeAverageOpenEqClosed R f).symm

/-- **The coefficient bridge**, the identity `a_{L'} − a_ℓ = k_{L'} − k_ℓ` at a
point: the second term of `e.ellsep.testing` is written by the print with the
stream increment and by `l.RHS.term2` with the coefficient increment. -/
theorem coefficientCutoff_toCoeffField_sub_eq_streamCutoff_sub (nu : ℝ)
    (omega : ShellSeq d) (j k : ℕ) (x : Vec d) :
    (coefficientCutoff nu omega j).toCoeffField x -
        (coefficientCutoff nu omega k).toCoeffField x =
      streamCutoff omega j x - streamCutoff omega k x := by
  rw [coefficientCutoff_toCoeffField_apply, coefficientCutoff_toCoeffField_apply]
  abel

/-- **`a_{L'} = a_ℓ + (k_{L'} − k_ℓ)`** at a point, the identity the paper
records before the splitting. -/
theorem coefficientCutoff_toCoeffField_add_streamCutoff_sub (nu : ℝ)
    (omega : ShellSeq d) (j k : ℕ) (x : Vec d) :
    (coefficientCutoff nu omega k).toCoeffField x +
        (streamCutoff omega j x - streamCutoff omega k x) =
      (coefficientCutoff nu omega j).toCoeffField x := by
  rw [coefficientCutoff_toCoeffField_apply, coefficientCutoff_toCoeffField_apply]
  abel

/-! ## Matrix-vector algebra -/

private theorem matVecMulSub (A : Mat d) (x y : Vec d) :
    matVecMul A (x - y) = matVecMul A x - matVecMul A y := by
  rw [sub_eq_add_neg, matVecMul_add, matVecMul_neg, ← sub_eq_add_neg]

private theorem matVecMulAddMat (A B : Mat d) (x : Vec d) :
    matVecMul (A + B) x = matVecMul A x + matVecMul B x := by
  funext i
  show ∑ j, (A i j + B i j) * x j = (∑ j, A i j * x j) + ∑ j, B i j * x j
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem matVecMulNegMat (A : Mat d) (x : Vec d) :
    matVecMul (-A) x = -matVecMul A x := by
  funext i
  show ∑ j, (-A i j) * x j = -∑ j, A i j * x j
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem integrableOnVecDotGradSubConst {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (u : H1Function U)
    (F : Vec d → Vec d) (q : Vec d)
    (hF : IntegrableOn (fun x => vecDot (u.grad x) (F x)) U volume) :
    IntegrableOn (fun x => vecDot (u.grad x) (F x - q)) U volume := by
  have hgrad : ∀ i : Fin d, IntegrableOn (fun x => u.grad x i) U volume :=
    fun i => integrableOnGradCoord u i
  have hconst : IntegrableOn (fun x => -vecDot (u.grad x) q) U volume :=
    (integrableOnVecDotConstRight (F := u.grad) q hgrad).neg
  have hpt : (fun x => vecDot (u.grad x) (F x - q))
      = fun x => vecDot (u.grad x) (F x) + -vecDot (u.grad x) q := by
    funext x
    rw [show F x - q = F x + -q from (sub_eq_add_neg _ _), vecDot_add_right,
      vecDot_neg_right]
  rw [hpt]
  exact hF.add hconst

/-! ## The combined testing display -/

/-- **The combined testing identity**, the combination of the two printed testing displays
with the vector `q` of `e.Sec3.p.q.def`:

`⨍_{cu_m}|∇w|² = ⨍_{cu_m} ∇w·(a_ℓ∇u_m − q) − ⨍_{cu_m} ∇w·(k_ℓ − k_{L'})(∇u_m − p)
                 − p·⨍_{cu_m}(k_{ℓ'} − k_ℓ)∇w`.

`uMgrad` is `∇u_m = ∇u_{m,0}`, a free binder: the maximizer of `e.u.k.y.def` at
`(k, y) = (m, 0)` has a carrier (`Section3/Setup/Scales.setupMaximizer`),
but the equation `e.ellsep` it satisfies does not, and it is that
equation which enters here, through `hTestEllsep`.

The four hypotheses are the printed displays, verbatim:

* `hTestEllsep` — `e.ellsep` tested against `w` and split at
  the constant `p`;
* `hTestW` — `e.w.testing.formula`, `e.def.w` tested against
  `w` and split at the shell `ℓ`;
* `hParts` — the integration by parts of the paper applied to the term carrying
  `∇u_m − p`, which uses the antisymmetry of `k_{L'}` and `k_ℓ`;
* `hPartsP` — the same integration by parts applied to the constant `p`.

The remaining hypothesis `hIntFlux` is the integrability of the flux pairing on
the cube, the side condition of the one step this theorem proves: the insertion
of `q`, which is `volumeAverage_vecDot_grad_sub_const`, i.e.
`(∇w)_{cu_m} = 0`. -/
theorem ellsep_testing (nu : ℝ) (omega : ShellSeq d) (S : ScaleSelection) (p q : Vec d)
    (w : H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (uMgrad : Vec d → Vec d)
    (hIntFlux : IntegrableOn (fun x => vecDot (w.toH1Function.grad x)
        (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (uMgrad x)))
      (openCubeSet (originCube d (S.m : ℤ))) volume)
    (hTestEllsep :
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot (w.toH1Function.grad x)
            (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (uMgrad x))) =
        vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => w.toH1Function.toFun x •
              (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x))) +
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => w.toH1Function.toFun x *
              vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x)
                (uMgrad x - p)))
    (hTestW :
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecNormSq (w.toH1Function.grad x)) =
        vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => w.toH1Function.toFun x •
              (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x))) +
          vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => w.toH1Function.toFun x •
              (driftCutoff omega S.ell x - driftCutoff omega S.ellPrime x))))
    (hParts :
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => w.toH1Function.toFun x *
            vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x)
              (uMgrad x - p)) =
        volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot (w.toH1Function.grad x)
            (matVecMul (streamCutoff omega S.ell x - streamCutoff omega S.LPrime x)
              (uMgrad x - p))))
    (hPartsP :
      vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => w.toH1Function.toFun x •
            (driftCutoff omega S.ell x - driftCutoff omega S.ellPrime x))) =
        -vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
            (w.toH1Function.grad x)))) :
    volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecNormSq (w.toH1Function.grad x)) =
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot (w.toH1Function.grad x)
            (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (uMgrad x) - q)) -
        volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot (w.toH1Function.grad x)
            (matVecMul (streamCutoff omega S.ell x - streamCutoff omega S.LPrime x)
              (uMgrad x - p))) -
        vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
            (w.toH1Function.grad x))) := by
  have hq : volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot (w.toH1Function.grad x)
          (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (uMgrad x) - q)) =
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot (w.toH1Function.grad x)
          (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (uMgrad x))) :=
    volumeAverage_vecDot_grad_sub_const (S.m : ℤ) w
      (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (uMgrad x)) q
      hIntFlux
  rw [hq]
  linarith only [hTestW, hTestEllsep, hParts, hPartsP]

/-! ## `e.ellsep.testing` -/

/-- **`e.ellsep.testing`**:

`⨍_{cu_m}|∇w|² = ⨍_{cu_m} ∇w·(a_ℓ∇u_n − q) + ⨍_{cu_m} ∇w·(k_{L'} − k_ℓ)(∇u_n − p)
                 + ⨍_{cu_m} ∇w·a_{L'}(∇u_m − ∇u_n) − p·⨍_{cu_m}(k_{ℓ'} − k_ℓ)∇w`.

The four hypotheses `hTestEllsep`, `hTestW`, `hParts`, `hPartsP` are those of
`ellsep_testing`.  The passage from that display to this one — the sentence of
the paper, "we next split the terms on the right side of the previous display
involving `∇u_m` into smaller scale maximizers and additivity defect terms,
noting also that `a_{L'} = a_ℓ + k_{L'} − k_ℓ`" — is *proved* here: it is the
pointwise vector identity

`(a_ℓ ∇u_m − q) + (k_{L'} − k_ℓ)(∇u_m − p)
   = (a_ℓ ∇u_n − q) + (k_{L'} − k_ℓ)(∇u_n − p) + a_{L'}(∇u_m − ∇u_n)`

together with the linearity of the normalized cube average, whose side
conditions are the four integrability hypotheses `hIntK`, `hInt1`, `hInt2`,
`hInt3`.  The glued field `∇u_n` of `e.u.k.def` is the free binder `uNGlued`;
on the sub-cube `z + cu_n` it is `∇u_{n,z}`, which is what makes the printed
rewriting of the second term as a lattice average of small-cube averages an
identity (`volumeAverage_originCube_eq_subcube_avsum`). -/
theorem ellsep_testing_decomposition (nu : ℝ) (omega : ShellSeq d) (S : ScaleSelection)
    (p q : Vec d)
    (w : H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (uMgrad uNGlued : Vec d → Vec d)
    (hIntFlux : IntegrableOn (fun x => vecDot (w.toH1Function.grad x)
        (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (uMgrad x)))
      (openCubeSet (originCube d (S.m : ℤ))) volume)
    (hIntK : IntegrableOn (fun x => vecDot (w.toH1Function.grad x)
        (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
          (uMgrad x - p))) (openCubeSet (originCube d (S.m : ℤ))) volume)
    (hInt1 : IntegrableOn (fun x => vecDot (w.toH1Function.grad x)
        (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (uNGlued x) - q))
      (openCubeSet (originCube d (S.m : ℤ))) volume)
    (hInt2 : IntegrableOn (fun x => vecDot (w.toH1Function.grad x)
        (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
          (uNGlued x - p))) (openCubeSet (originCube d (S.m : ℤ))) volume)
    (hInt3 : IntegrableOn (fun x => vecDot (w.toH1Function.grad x)
        (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
          (uMgrad x - uNGlued x))) (openCubeSet (originCube d (S.m : ℤ))) volume)
    (hTestEllsep :
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot (w.toH1Function.grad x)
            (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (uMgrad x))) =
        vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => w.toH1Function.toFun x •
              (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x))) +
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => w.toH1Function.toFun x *
              vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x)
                (uMgrad x - p)))
    (hTestW :
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecNormSq (w.toH1Function.grad x)) =
        vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => w.toH1Function.toFun x •
              (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x))) +
          vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => w.toH1Function.toFun x •
              (driftCutoff omega S.ell x - driftCutoff omega S.ellPrime x))))
    (hParts :
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => w.toH1Function.toFun x *
            vecDot (driftCutoff omega S.LPrime x - driftCutoff omega S.ell x)
              (uMgrad x - p)) =
        volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot (w.toH1Function.grad x)
            (matVecMul (streamCutoff omega S.ell x - streamCutoff omega S.LPrime x)
              (uMgrad x - p))))
    (hPartsP :
      vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => w.toH1Function.toFun x •
            (driftCutoff omega S.ell x - driftCutoff omega S.ellPrime x))) =
        -vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
            (w.toH1Function.grad x)))) :
    volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecNormSq (w.toH1Function.grad x)) =
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot (w.toH1Function.grad x)
            (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (uNGlued x) - q)) +
        volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot (w.toH1Function.grad x)
            (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
              (uNGlued x - p))) +
        volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot (w.toH1Function.grad x)
            (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
              (uMgrad x - uNGlued x))) -
        vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
            (w.toH1Function.grad x))) := by
  have hbase := ellsep_testing nu omega S p q w uMgrad hIntFlux hTestEllsep hTestW hParts
    hPartsP
  -- the term with `k_ℓ − k_{L'}` is the negative of the term with `k_{L'} − k_ℓ`
  have hneg : volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot (w.toH1Function.grad x)
          (matVecMul (streamCutoff omega S.ell x - streamCutoff omega S.LPrime x)
            (uMgrad x - p))) =
      -volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot (w.toH1Function.grad x)
          (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
            (uMgrad x - p))) := by
    have hpt : (fun x => vecDot (w.toH1Function.grad x)
          (matVecMul (streamCutoff omega S.ell x - streamCutoff omega S.LPrime x)
            (uMgrad x - p)))
        = fun x => -vecDot (w.toH1Function.grad x)
          (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
            (uMgrad x - p)) := by
      funext x
      rw [show streamCutoff omega S.ell x - streamCutoff omega S.LPrime x =
          -(streamCutoff omega S.LPrime x - streamCutoff omega S.ell x) from (neg_sub _ _).symm,
        matVecMulNegMat, vecDot_neg_right]
    rw [hpt, volumeAverageNeg]
  -- the splitting of the paper, as a pointwise vector identity
  have hIntM1 : IntegrableOn (fun x => vecDot (w.toH1Function.grad x)
      (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (uMgrad x) - q))
      (openCubeSet (originCube d (S.m : ℤ))) volume :=
    integrableOnVecDotGradSubConst w.toH1Function
      (fun x => matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (uMgrad x))
      q hIntFlux
  have hptv : ∀ x : Vec d,
      vecDot (w.toH1Function.grad x)
          (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (uMgrad x) - q) +
        vecDot (w.toH1Function.grad x)
          (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
            (uMgrad x - p)) =
      vecDot (w.toH1Function.grad x)
          (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (uNGlued x) - q) +
        vecDot (w.toH1Function.grad x)
          (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
            (uNGlued x - p)) +
        vecDot (w.toH1Function.grad x)
          (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
            (uMgrad x - uNGlued x)) := by
    intro x
    have hvec :
        (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (uMgrad x) - q) +
            matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
              (uMgrad x - p) =
          ((matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (uNGlued x) - q) +
              matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
                (uNGlued x - p)) +
            matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
              (uMgrad x - uNGlued x) := by
      have hA : (coefficientCutoff nu omega S.LPrime).toCoeffField x =
          (coefficientCutoff nu omega S.ell).toCoeffField x +
            (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x) :=
        (coefficientCutoff_toCoeffField_add_streamCutoff_sub nu omega S.LPrime S.ell x).symm
      rw [hA, matVecMulAddMat, matVecMulSub, matVecMulSub, matVecMulSub, matVecMulSub]
      abel
    rw [← vecDot_add_right, ← vecDot_add_right, ← vecDot_add_right, hvec]
  have hL : volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot (w.toH1Function.grad x)
            (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (uMgrad x) - q) +
          vecDot (w.toH1Function.grad x)
            (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
              (uMgrad x - p))) =
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot (w.toH1Function.grad x)
            (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (uMgrad x) - q)) +
        volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot (w.toH1Function.grad x)
            (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
              (uMgrad x - p))) := volumeAverageAdd hIntM1 hIntK
  have hR : volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => (vecDot (w.toH1Function.grad x)
              (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (uNGlued x) - q) +
            vecDot (w.toH1Function.grad x)
              (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
                (uNGlued x - p))) +
          vecDot (w.toH1Function.grad x)
            (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
              (uMgrad x - uNGlued x))) =
      (volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot (w.toH1Function.grad x)
            (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (uNGlued x) - q)) +
        volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot (w.toH1Function.grad x)
            (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
              (uNGlued x - p)))) +
        volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot (w.toH1Function.grad x)
            (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
              (uMgrad x - uNGlued x))) := by
    have hAdd12 : IntegrableOn (fun x => vecDot (w.toH1Function.grad x)
          (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x) (uNGlued x) - q) +
        vecDot (w.toH1Function.grad x)
          (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
            (uNGlued x - p))) (openCubeSet (originCube d (S.m : ℤ))) volume :=
      hInt1.add hInt2
    rw [volumeAverageAdd hAdd12 hInt3, volumeAverageAdd hInt1 hInt2]
  have hcongr := congrArg (volumeAverage (openCubeSet (originCube d (S.m : ℤ))))
    (funext hptv)
  rw [hL, hR] at hcongr
  linarith only [hbase, hneg, hcongr]

/-! ## The expectation form of `e.ellsep.testing` -/

/-- **`e.ellsep.testing` under the expectation**, the form in which the four
term lemmas of Section 3 consume it ("the strategy is to estimate the
expectation of the left side ... and then to upper bound the expectation of the
right side").

`hPt` is the conclusion of `ellsep_testing_decomposition` at every shell
sequence; the four remaining hypotheses are the `P`-integrability of the four
terms, without which the expectation does not split.  Nothing else is used. -/
theorem ellsep_testing_annealed (nu : ℝ) (P : MeasureTheory.ProbabilityMeasure (ShellSeq d))
    (S : ScaleSelection) (p q : Vec d)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (uMgrad uNGlued : ShellSeq d → Vec d → Vec d)
    (hPt : ∀ omega : ShellSeq d,
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecNormSq ((w omega).toH1Function.grad x)) =
        volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => vecDot ((w omega).toH1Function.grad x)
              (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                (uNGlued omega x) - q)) +
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => vecDot ((w omega).toH1Function.grad x)
              (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
                (uNGlued omega x - p))) +
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => vecDot ((w omega).toH1Function.grad x)
              (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
                (uMgrad omega x - uNGlued omega x))) -
          vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
              ((w omega).toH1Function.grad x))))
    (hI1 : Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x)
          (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
            (uNGlued omega x) - q))) P.toMeasure)
    (hI2 : Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x)
          (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
            (uNGlued omega x - p)))) P.toMeasure)
    (hI3 : Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecDot ((w omega).toH1Function.grad x)
          (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
            (uMgrad omega x - uNGlued omega x)))) P.toMeasure)
    (hI4 : Integrable (fun omega : ShellSeq d =>
      vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
          ((w omega).toH1Function.grad x)))) P.toMeasure) :
    ∫ omega : ShellSeq d, volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
        (fun x => vecNormSq ((w omega).toH1Function.grad x)) ∂P.toMeasure =
      (∫ omega : ShellSeq d, volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot ((w omega).toH1Function.grad x)
            (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (uNGlued omega x) - q)) ∂P.toMeasure +
        ∫ omega : ShellSeq d, volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot ((w omega).toH1Function.grad x)
            (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
              (uNGlued omega x - p))) ∂P.toMeasure +
        ∫ omega : ShellSeq d, volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot ((w omega).toH1Function.grad x)
            (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
              (uMgrad omega x - uNGlued omega x))) ∂P.toMeasure) -
        ∫ omega : ShellSeq d, vecDot p (volumeAverageVec (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => matVecMul (streamCutoff omega S.ellPrime x - streamCutoff omega S.ell x)
            ((w omega).toH1Function.grad x))) ∂P.toMeasure := by
  have hI12 : Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot ((w omega).toH1Function.grad x)
            (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
              (uNGlued omega x) - q)) +
        volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot ((w omega).toH1Function.grad x)
            (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
              (uNGlued omega x - p)))) P.toMeasure := hI1.add hI2
  have hI123 : Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => vecDot ((w omega).toH1Function.grad x)
              (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                (uNGlued omega x) - q)) +
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => vecDot ((w omega).toH1Function.grad x)
              (matVecMul (streamCutoff omega S.LPrime x - streamCutoff omega S.ell x)
                (uNGlued omega x - p))) +
        volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => vecDot ((w omega).toH1Function.grad x)
            (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x)
              (uMgrad omega x - uNGlued omega x)))) P.toMeasure := hI12.add hI3
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hPt),
    MeasureTheory.integral_sub hI123 hI4, MeasureTheory.integral_add hI12 hI3,
    MeasureTheory.integral_add hI1 hI2]

end

end SuperdiffusionCLT.Section3.Terms
