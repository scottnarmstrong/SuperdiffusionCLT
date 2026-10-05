/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.StationaryRealizationConcrete
public import SuperdiffusionCLT.Probability.RealizationFirstConjunct
public import SuperdiffusionCLT.Probability.StationaryProjectionConditional

/-!
# The second conjunct of the stationary potential realization at `ShellSeq d`

The main statement `SuperdiffusionCLT.Frozen.Section3.stationaryPotentialRealization`
has two conjuncts.  The first, the existence at a.e. sample of an `H¹` function on the cube
whose weak gradient is the realized field `x ↦ gradHatW (x +ᵥ ω)`, is proved in
`SuperdiffusionCLT.Probability.RealizationFirstConjunct`.  This module treats the
second, the per-sample weak equation

`∫ x in U, vecDot ((uReal ω).grad x) (φ.grad x) = -∫ x in U, vecDot (F ω x) (φ.grad x)`

for every `φ : H10Function U`, at the concrete carrier `Ω := ShellSeq d`, `μ := P.toMeasure`.

## What the second conjunct asks

At `U = openCubeSet (originCube d (M : ℤ))`, the stationarity cocycle
`F ω x = F (x +ᵥ ω) 0` and the first
conjunct turn the weak equation into the single statement

`∫ x in U, vecDot (anchorStationaryField (x +ᵥ ω)) (φ.grad x) = 0`,

where `anchorStationaryField ω = gradHatW ω + F ω 0` is the printed stationary potential
field of the response-field construction.  The hypothesis `hproj` says exactly that
this field is *solenoidal*: its `L²(Ω)` class lies in `stationarySolenoidalSubspace`, the
orthogonal complement of the closed stationary potential subspace
(`anchorStationaryField_toLp_mem_stationarySolenoidalSubspace`), hence it pairs to zero
against every stationary horizontal gradient.  The second conjunct is therefore the transfer of
that `L²(Ω)`-orthogonality to a single spatial sample, i.e. the statement that the sample
field `x ↦ anchorStationaryField (x + ᵥ ω)` is weakly divergence free on the cube.

## The transfer, and the countable family of test functions

The transfer is an orbit smearing.  The module proves its first formal step (`smearScalar`,
`smearGrad`, `smearScalar_vadd_basisVec`); for a test function `θ` on `Vec d` and a scalar field
`f` on `Ω`,

* `smearScalar θ f ω = ∫ y, θ y * f ((-y) +ᵥ ω)` is the smeared potential, and
* `smearGrad θ f ω = fun i => ∫ y, (fderiv ℝ θ y) (basisVec i) * f ((-y) +ᵥ ω)` is its
  candidate spatial gradient.

With `Ψ_θ(ω) := ∫ x, vecDot (anchorStationaryField gradHatW F (x +ᵥ ω)) (∇θ x)`, the smearing
argument is: `Ψ_θ` is the field whose smear against a square-integrable `f` is the pairing of
the anchor field with `smearGrad θ f`; the pair `(smearScalar θ f, smearGrad θ f)` is a
stationary horizontal gradient; so `hproj` makes that pairing zero; so `∫ f · Ψ_θ = 0` for
every `f`, and taking `f := Ψ_θ` gives `Ψ_θ = 0` almost everywhere.

A countable family of test functions is needed to pass from "for each `φ`, almost every `ω`" to
"for almost every `ω`, every `φ`".  The `approx` sequence of a fixed `φ : H10Function U` is
countable, but its null set depends on `φ`, and `H10Function U` is uncountable.  What is needed
is a countable set `T` of test functions, fixed before `φ` is named, whose gradients are dense in
`{∇φ : φ ∈ H¹₀(U)} ⊆ L²(U; Vec d)`.  Only then does `H10Function.approx` carry the conclusion
from the smooth tests to a single `φ`.

## Scope

* the solenoidal membership of the anchor field
  (`anchorStationaryField_toLp_mem_stationarySolenoidalSubspace`);
* the exact per-sample form into which the second conjunct reduces
  (`weakEquation_of_anchorPairing_eq_zero`): at a sample, the weak equation follows
  from the vanishing of the anchor-slice divergence pairing, through the `L²(U)`
  inner-product form of the two sides;
* the conclusion at the concrete carrier (`exists_realization_of_anchorPairing`): the first
  conjunct supplies `uReal`, and the single per-sample statement `hpair` supplies the second,

where `hpair` reads `∀ᵐ ω, ∀ φ : H10Function (openCubeSet (originCube d (M : ℤ))),
∫ x, vecDot (anchorStationaryField gradHatW F (x +ᵥ ω)) (φ.toH1Function.grad x) = 0`.
It is a consequence of the hypotheses of the main statement by the smearing argument above.
Two ingredients enter: the horizontal-gradient property of the smear, that the smeared pair
is a strong horizontal gradient for every `ContDiff ℝ 1` compactly supported `θ` and every
`f ∈ L²(Ω)`, which is the group-mollifier
differentiation estimate (at the carrier `ShellSeq d` it is built from
`MeasurableVAdd₂ (Vec d) (ShellSeq d)` by Tonelli and dominated convergence); and
the pairing transfer, the Fubini identity
`∫ ω, f ω * Ψ_θ(ω) = ∫ ω, vecDot (anchor field ω) (smearGrad θ f ω)`, which converts the
`L²(Ω)`-orthogonality against the smeared gradient into the vanishing of the per-sample
divergence pairing.  Orthogonality of the anchor field against all stationary horizontal
gradients (which is what `hproj` gives) is strictly stronger than the single averaged identity,
and it is this that makes the per-sample statement true.  The smearing of the test potential is
used because its gradient is a vector field and hence carries the orthogonality directly.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open scoped ENNReal Topology

noncomputable section

namespace SuperdiffusionCLT.Probability.Stationary

variable {d : ℕ}

/-! ## The stationary potential field of the anchor -/

/-- The printed stationary potential field `∇ŵ + F (·) 0` of the response-field
construction: the sum of the potential field and the flux sampled at the origin. -/
def anchorStationaryField (gradHatW : ShellSeq d → Vec d) (F : ShellSeq d → Vec d → Vec d)
    (ω : ShellSeq d) : Vec d :=
  gradHatW ω + F ω 0

/-- The Hilbert realization of the anchor field is the sum of the two realizations. -/
theorem ofVec_anchorStationaryField (gradHatW : ShellSeq d → Vec d)
    (F : ShellSeq d → Vec d → Vec d) (ω : ShellSeq d) :
    HilbertVec.ofVec (anchorStationaryField gradHatW F ω) =
      HilbertVec.ofVec (gradHatW ω) + HilbertVec.ofVec (F ω 0) := by
  ext i
  simp [anchorStationaryField]

/-- The anchor field is square integrable whenever its two summands are. -/
theorem anchorStationaryField_memLp {P : ProbabilityMeasure (ShellSeq d)}
    [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
    {gradHatW : ShellSeq d → Vec d} {F : ShellSeq d → Vec d → Vec d}
    (hF : MemLp (fun ω : ShellSeq d => HilbertVec.ofVec (F ω 0)) 2 P.toMeasure)
    (hG : MemLp (fun ω : ShellSeq d => HilbertVec.ofVec (gradHatW ω)) 2 P.toMeasure) :
    MemLp (fun ω : ShellSeq d => HilbertVec.ofVec (anchorStationaryField gradHatW F ω))
      2 P.toMeasure := by
  have h : (fun ω : ShellSeq d => HilbertVec.ofVec (anchorStationaryField gradHatW F ω)) =
      fun ω : ShellSeq d => HilbertVec.ofVec (gradHatW ω) + HilbertVec.ofVec (F ω 0) :=
    funext fun ω => ofVec_anchorStationaryField gradHatW F ω
  rw [h]
  exact hG.add hF

/-- **The anchor field is solenoidal.**  This is the projection hypothesis `hproj` read
as membership of the `L²(Ω)` class of the printed stationary potential field in
`stationarySolenoidalSubspace`, the orthogonal complement of the closed stationary potential
subspace.  It is `add_field_toLp_mem_stationarySolenoidalSubspace` transported along the
pointwise identification `ofVec (a + b) = ofVec a + ofVec b`. -/
theorem anchorStationaryField_toLp_mem_stationarySolenoidalSubspace
    {P : ProbabilityMeasure (ShellSeq d)}
    [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
    {gradHatW : ShellSeq d → Vec d} {F : ShellSeq d → Vec d → Vec d}
    {hF : MemLp (fun ω : ShellSeq d => HilbertVec.ofVec (F ω 0)) 2 P.toMeasure}
    {hG : MemLp (fun ω : ShellSeq d => HilbertVec.ofVec (gradHatW ω)) 2 P.toMeasure}
    (hproj : hG.toLp (fun ω : ShellSeq d => HilbertVec.ofVec (gradHatW ω)) =
      -stationaryPotentialProjection (μ := P.toMeasure) (d := d)
        (hF.toLp (fun ω : ShellSeq d => HilbertVec.ofVec (F ω 0)))) :
    (anchorStationaryField_memLp (P := P) hF hG).toLp
        (fun ω : ShellSeq d => HilbertVec.ofVec (anchorStationaryField gradHatW F ω)) ∈
      stationarySolenoidalSubspace (μ := P.toMeasure) (d := d) := by
  have h := SuperdiffusionCLT.Section3.Terms.add_field_toLp_mem_stationarySolenoidalSubspace
    (μ := P.toMeasure) hproj
  have hkey : (anchorStationaryField_memLp (P := P) hF hG).toLp
      (fun ω : ShellSeq d => HilbertVec.ofVec (anchorStationaryField gradHatW F ω)) =
      (hG.add hF).toLp (fun ω : ShellSeq d =>
        HilbertVec.ofVec (gradHatW ω) + HilbertVec.ofVec (F ω 0)) :=
    MemLp.toLp_congr (anchorStationaryField_memLp (P := P) hF hG) (hG.add hF)
      (Filter.Eventually.of_forall fun ω => ofVec_anchorStationaryField gradHatW F ω)
  rwa [hkey]

/-! ## The smearing construction

The transfer from the `L²(Ω)`-orthogonality to a single spatial sample is the orbit
smearing: for a test function `θ` on `Vec d` and a scalar field `f` on `Ω`, the smeared
potential and its candidate gradient are

* `smearScalar θ f ω = ∫ y, θ y * f ((-y) +ᵥ ω)`,
* `smearGrad θ f ω = fun i => ∫ y, (fderiv ℝ θ y) (basisVec i) * f ((-y) +ᵥ ω)`.

The point of this section is the *shift identity* `smearScalar_vadd_basisVec`: shifting the
sample by `t • eᵢ` moves the shift from the field to the test function, so that the whole
`t`-dependence sits in the smooth factor `θ (· + t • eᵢ)`.  That is what makes the orbit
derivative of the smeared potential computable without any regularity of `f`: the difference
quotient of the smear is the smeared difference quotient of `θ`, and it converges to
`smearGrad` by dominated convergence with the pointwise bound
`‖(θ (y + t eᵢ) - θ y)/t‖ ≤ sup ‖∇θ‖`. -/

/-- The smeared scalar potential of a scalar field along the orbit. -/
def smearScalar (θ : Vec d → ℝ) (f : ShellSeq d → ℝ) (ω : ShellSeq d) : ℝ :=
  ∫ y, θ y * f ((-y) +ᵥ ω)

/-- The candidate spatial gradient of the smeared potential: the smear of the field against
the partial derivative of the test function. -/
def smearGrad (θ : Vec d → ℝ) (f : ShellSeq d → ℝ) (ω : ShellSeq d) : Vec d :=
  fun i => ∫ y, fderiv ℝ θ y (Homogenization.basisVec i) * f ((-y) +ᵥ ω)

/-- **Orbit shift of the smear.**  Shifting the sample by `t • eᵢ` moves the shift from the
field to the test function. -/
theorem smearScalar_vadd_basisVec (θ : Vec d → ℝ) (f : ShellSeq d → ℝ) (ω : ShellSeq d)
    (t : ℝ) (i : Fin d) :
    smearScalar θ f (t • Homogenization.basisVec i +ᵥ ω) =
      ∫ y, θ (y + t • Homogenization.basisVec i) * f ((-y) +ᵥ ω) := by
  have hshift : ∀ y : Vec d, (-y) +ᵥ (t • Homogenization.basisVec i +ᵥ ω) =
      (t • Homogenization.basisVec i - y) +ᵥ ω := by
    intro y
    rw [vadd_vadd, sub_eq_neg_add, add_comm]
  have hpt : (∫ y, θ y * f ((-y) +ᵥ (t • Homogenization.basisVec i +ᵥ ω))) =
      ∫ y, θ y * f ((t • Homogenization.basisVec i - y) +ᵥ ω) := by
    refine integral_congr_ae ?_
    filter_upwards with y
    rw [hshift y]
  rw [smearScalar, hpt]
  have htrans := MeasureTheory.integral_add_right_eq_self (μ := (volume : Measure (Vec d)))
    (f := fun y : Vec d => θ y * f ((t • Homogenization.basisVec i - y) +ᵥ ω))
    (t • Homogenization.basisVec i)
  rw [← htrans]
  refine integral_congr_ae ?_
  filter_upwards with y
  have harg : t • Homogenization.basisVec i - (y + t • Homogenization.basisVec i) = -y := by
    abel
  rw [harg]

/-! ## The per-sample reduction

The hypotheses give the `L²(Ω)`-orthogonality of the anchor field against stationary
horizontal gradients.  The second conjunct is the
statement that, at almost every sample, the *slice* `x ↦ anchorStationaryField (x +ᵥ ω)` is
weakly divergence free on the cube.  This section proves that reduction: the weak
equation at a sample follows from the vanishing, at that same sample, of the divergence
pairing of the anchor slice against every `H¹₀(U)` test function, by reading both pairings
as `L²(U)` inner products. -/

/-- **The gradient class of an `H¹` function read on an a.e. equal field.**  This is
`gradToHilbertVectorL2_eq_toLp` with the exact equality
of the gradient weakened to an almost everywhere equality, which is the only form in which the
hypotheses supply the translated gradient. -/
theorem gradToHilbertVectorL2_eq_toLp_of_ae_eq {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {v : H1Function U} {G : Vec d → Vec d}
    (hgrad : v.grad =ᵐ[volumeMeasureOn U] G)
    (hG : MemLp (fun x => HilbertVec.ofVec (G x)) 2 (volumeMeasureOn U)) :
    v.gradToHilbertVectorL2 = hG.toLp (fun x => HilbertVec.ofVec (G x)) := by
  rw [H1Function.gradToHilbertVectorL2, Homogenization.toHilbertVectorL2OfVecField,
    Homogenization.toHilbertVectorL2]
  refine MemLp.toLp_congr _ hG ?_
  filter_upwards [hgrad] with x hx
  simp only [Homogenization.hilbertifyVecField, hx]

/-- **The integral pairing against an `H¹` test function, as an `L²(U)` inner product.**
For an `L²(U)` class `f` carried by the field `G`, the divergence pairing of `G` against the
gradient of a test function is the inner product of the class of `f` with the gradient class of
the test function.  The test function is an arbitrary `H¹(U)` function: the `H¹₀` case is the
instance `v := φ.toH1Function`, and the general form is what lets the smeared, smooth tests be
compared with an `H¹₀` test. -/
theorem integral_vecDot_eq_inner_of_ae_eq {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {f : VectorL2 d (volumeMeasureOn U)} {G : Vec d → Vec d}
    (hf : f =ᵐ[volumeMeasureOn U] fun x => HilbertVec.ofVec (G x)) (v : H1Function U) :
    ∫ x in U, vecDot (G x) (v.grad x) =
      inner ℝ f v.gradToHilbertVectorL2 := by
  have hinner : inner ℝ f v.gradToHilbertVectorL2 =
      ∫ x in U, vecDot (f x).toVec (v.grad x) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [H1Function.coeFn_gradToHilbertVectorL2 v] with x hx
    rw [hx, Homogenization.hilbertifyVecField, HilbertVec.inner_def, HilbertVec.toVec_ofVec]
  rw [hinner]
  refine integral_congr_ae ?_
  filter_upwards [hf] with x hx
  rw [hx, HilbertVec.toVec_ofVec]

/-- **The weak equation at one sample, reduced to the anchor divergence pairing.**
Suppose that at the sample `ω` the `H¹` function `u` realizes the translated potential
field, that the flux is a cocycle, and that the slice of the anchor field is square integrable
and pairs to zero against every `H¹₀(U)` test function.  Then the weak equation holds
at `ω` for every `H¹₀(U)` test function.  The proof is the `L²(U)` inner-product form of the
pairing together with the additivity of the inner product: the anchor pairing is the sum of the
pairings of its two summands, so the vanishing of the sum forces the weak equation. -/
theorem weakEquation_of_anchorPairing_eq_zero (M : ℕ) {F : ShellSeq d → Vec d → Vec d}
    {gradHatW : ShellSeq d → Vec d} {ω : ShellSeq d}
    {u : H1Function (openCubeSet (originCube d (M : ℤ)))}
    (hgrad : u.grad =ᵐ[volumeMeasureOn (openCubeSet (originCube d (M : ℤ)))]
      fun x => gradHatW (x +ᵥ ω))
    (hcocycle : ∀ x y : Vec d, F (x +ᵥ ω) y = F ω (y + x))
    (hGslice : MemLp (fun x => HilbertVec.ofVec (gradHatW (x +ᵥ ω))) 2
      (volumeMeasureOn (openCubeSet (originCube d (M : ℤ)))))
    (hFslice : MemLp (fun x => HilbertVec.ofVec (F (x +ᵥ ω) 0)) 2
      (volumeMeasureOn (openCubeSet (originCube d (M : ℤ)))))
    (hanchor : ∀ φ : H10Function (openCubeSet (originCube d (M : ℤ))),
      ∫ x in openCubeSet (originCube d (M : ℤ)),
        vecDot (anchorStationaryField gradHatW F (x +ᵥ ω)) (φ.toH1Function.grad x) = 0) :
    ∀ φ : H10Function (openCubeSet (originCube d (M : ℤ))),
      ∫ x in openCubeSet (originCube d (M : ℤ)),
          vecDot (u.grad x) (φ.toH1Function.grad x) =
        -∫ x in openCubeSet (originCube d (M : ℤ)),
          vecDot (F ω x) (φ.toH1Function.grad x) := by
  intro φ
  have hGc : u.gradToHilbertVectorL2 = hGslice.toLp
      (fun x => HilbertVec.ofVec (gradHatW (x +ᵥ ω))) :=
    gradToHilbertVectorL2_eq_toLp_of_ae_eq hgrad hGslice
  have hFU : u.gradToHilbertVectorL2 =ᵐ[volumeMeasureOn (openCubeSet (originCube d (M : ℤ)))]
      fun x => HilbertVec.ofVec (u.grad x) := by
    filter_upwards [H1Function.coeFn_gradToHilbertVectorL2 u] with x hx
    simpa only [Homogenization.hilbertifyVecField] using hx
  have hpairG : ∫ x in openCubeSet (originCube d (M : ℤ)),
      vecDot (gradHatW (x +ᵥ ω)) (φ.toH1Function.grad x) =
      inner ℝ (hGslice.toLp (fun x => HilbertVec.ofVec (gradHatW (x +ᵥ ω))))
        φ.toH1Function.gradToHilbertVectorL2 :=
    integral_vecDot_eq_inner_of_ae_eq (MemLp.coeFn_toLp hGslice) φ.toH1Function
  have hpairF : ∫ x in openCubeSet (originCube d (M : ℤ)),
      vecDot (F (x +ᵥ ω) 0) (φ.toH1Function.grad x) =
      inner ℝ (hFslice.toLp (fun x => HilbertVec.ofVec (F (x +ᵥ ω) 0)))
        φ.toH1Function.gradToHilbertVectorL2 :=
    integral_vecDot_eq_inner_of_ae_eq (MemLp.coeFn_toLp hFslice) φ.toH1Function
  have hanchorClass : inner ℝ (hGslice.toLp (fun x => HilbertVec.ofVec (gradHatW (x +ᵥ ω))) +
      hFslice.toLp (fun x => HilbertVec.ofVec (F (x +ᵥ ω) 0)))
      φ.toH1Function.gradToHilbertVectorL2 = 0 := by
    rw [← integral_vecDot_eq_inner_of_ae_eq
      (f := hGslice.toLp (fun x => HilbertVec.ofVec (gradHatW (x +ᵥ ω))) +
        hFslice.toLp (fun x => HilbertVec.ofVec (F (x +ᵥ ω) 0)))
      (G := fun x => anchorStationaryField gradHatW F (x +ᵥ ω))
      (by
        filter_upwards [Lp.coeFn_add
            (hGslice.toLp (fun x => HilbertVec.ofVec (gradHatW (x +ᵥ ω))))
            (hFslice.toLp (fun x => HilbertVec.ofVec (F (x +ᵥ ω) 0))),
          MemLp.coeFn_toLp hGslice, MemLp.coeFn_toLp hFslice] with x h0 h1 h2
        rw [h0, Pi.add_apply, h1, h2]
        exact (ofVec_anchorStationaryField gradHatW F (x +ᵥ ω)).symm)
      φ.toH1Function]
    exact hanchor φ
  have hsum : inner ℝ (hGslice.toLp (fun x => HilbertVec.ofVec (gradHatW (x +ᵥ ω))))
        φ.toH1Function.gradToHilbertVectorL2 +
      inner ℝ (hFslice.toLp (fun x => HilbertVec.ofVec (F (x +ᵥ ω) 0)))
        φ.toH1Function.gradToHilbertVectorL2 = 0 := by
    rw [← inner_add_left]
    exact hanchorClass
  have hu : ∫ x in openCubeSet (originCube d (M : ℤ)),
      vecDot (u.grad x) (φ.toH1Function.grad x) =
      inner ℝ (hGslice.toLp (fun x => HilbertVec.ofVec (gradHatW (x +ᵥ ω))))
        φ.toH1Function.gradToHilbertVectorL2 := by
    rw [integral_vecDot_eq_inner_of_ae_eq hFU φ.toH1Function, hGc]
  have hFω : ∫ x in openCubeSet (originCube d (M : ℤ)),
      vecDot (F ω x) (φ.toH1Function.grad x) =
      inner ℝ (hFslice.toLp (fun x => HilbertVec.ofVec (F (x +ᵥ ω) 0)))
        φ.toH1Function.gradToHilbertVectorL2 := by
    rw [← hpairF]
    refine integral_congr_ae ?_
    filter_upwards with x
    have hx := hcocycle x 0
    rw [zero_add] at hx
    rw [hx]
  rw [hu, hFω]
  exact eq_neg_of_add_eq_zero_left hsum

/-! ## The second conjunct at the concrete carrier -/

/-- **The conclusion at `ShellSeq d`, reduced to the per-sample anchor pairing.**
This is the whole conclusion of `stationaryPotentialRealization` at `Ω = ShellSeq d`,
`μ = P.toMeasure`, `M = M`, with the cocycle hypothesis explicit, proved from two inputs: the
first conjunct (`exists_h1_realization_of_eq_neg_stationaryPotentialProjection`, which supplies
`uReal` and its translated gradient) and the single per-sample statement `hpair` that the slice
of the anchor field pairs to zero against every `H¹₀` test function at almost every sample.  The
slice integrabilities of `hpair`'s two summands are supplied here from the `L²(Ω)`
hypotheses through a measurable representative and `ae_memLp_slice_openCube_vec`, so `hpair` is
the only hypothesis beyond those of the main statement. -/
theorem exists_realization_of_anchorPairing {P : ProbabilityMeasure (ShellSeq d)}
    [VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
    (M : ℕ) {F : ShellSeq d → Vec d → Vec d} {gradHatW : ShellSeq d → Vec d}
    (hcocycle : ∀ (ω : ShellSeq d) (x y : Vec d), F (x +ᵥ ω) y = F ω (y + x))
    (hFmemLp : MemLp (fun ω : ShellSeq d => HilbertVec.ofVec (F ω 0)) 2 P.toMeasure)
    (hG : MemLp (fun ω : ShellSeq d => HilbertVec.ofVec (gradHatW ω)) 2 P.toMeasure)
    (hproj : hG.toLp (fun ω : ShellSeq d => HilbertVec.ofVec (gradHatW ω)) =
      -stationaryPotentialProjection (μ := P.toMeasure) (d := d)
        (hFmemLp.toLp (fun ω : ShellSeq d => HilbertVec.ofVec (F ω 0))))
    (hpair : ∀ᵐ ω ∂P.toMeasure, ∀ φ : H10Function (openCubeSet (originCube d (M : ℤ))),
      ∫ x in openCubeSet (originCube d (M : ℤ)),
        vecDot (anchorStationaryField gradHatW F (x +ᵥ ω)) (φ.toH1Function.grad x) = 0) :
    ∃ uReal : ShellSeq d → H1Function (openCubeSet (originCube d (M : ℤ))),
      (∀ᵐ ω ∂P.toMeasure,
        (uReal ω).grad =ᵐ[volumeMeasureOn (openCubeSet (originCube d (M : ℤ)))]
          fun x => gradHatW (x +ᵥ ω)) ∧
      (∀ᵐ ω ∂P.toMeasure, ∀ φ : H10Function (openCubeSet (originCube d (M : ℤ))),
        ∫ x in openCubeSet (originCube d (M : ℤ)),
            vecDot ((uReal ω).grad x) (φ.toH1Function.grad x) =
          -∫ x in openCubeSet (originCube d (M : ℤ)),
            vecDot (F ω x) (φ.toH1Function.grad x)) := by
  classical
  obtain ⟨W, hWm, hWmem, hWtoLp⟩ := exists_measurable_representative_of_vectorL2 (P := P)
    (hG.toLp (fun ω : ShellSeq d => HilbertVec.ofVec (gradHatW ω)))
  have hW1 : (hWmem.toLp (fun ω => HilbertVec.ofVec (W ω)) : ShellSeq d → HilbertVec d)
      =ᵐ[P.toMeasure] fun ω => HilbertVec.ofVec (W ω) := MemLp.coeFn_toLp hWmem
  have hW2 : (hWmem.toLp (fun ω => HilbertVec.ofVec (W ω)) : ShellSeq d → HilbertVec d)
      =ᵐ[P.toMeasure] fun ω => HilbertVec.ofVec (gradHatW ω) := by
    rw [hWtoLp]
    exact MemLp.coeFn_toLp hG
  have hWae : W =ᵐ[P.toMeasure] gradHatW :=
    (hW1.symm.trans hW2).mono fun ω hω => by
      have h := congrArg HilbertVec.toVec hω
      simpa only [HilbertVec.toVec_ofVec] using h
  obtain ⟨G₀, hG₀m, hG₀mem, hG₀toLp⟩ := exists_measurable_representative_of_vectorL2 (P := P)
    (hFmemLp.toLp (fun ω : ShellSeq d => HilbertVec.ofVec (F ω 0)))
  have hG₀1 : (hG₀mem.toLp (fun ω => HilbertVec.ofVec (G₀ ω)) : ShellSeq d → HilbertVec d)
      =ᵐ[P.toMeasure] fun ω => HilbertVec.ofVec (G₀ ω) := MemLp.coeFn_toLp hG₀mem
  have hG₀2 : (hG₀mem.toLp (fun ω => HilbertVec.ofVec (G₀ ω)) : ShellSeq d → HilbertVec d)
      =ᵐ[P.toMeasure] fun ω => HilbertVec.ofVec (F ω 0) := by
    rw [hG₀toLp]
    exact MemLp.coeFn_toLp hFmemLp
  have hG₀ae : G₀ =ᵐ[P.toMeasure] (fun ω : ShellSeq d => F ω 0) :=
    (hG₀1.symm.trans hG₀2).mono fun ω hω => by
      have h := congrArg HilbertVec.toVec hω
      simpa only [HilbertVec.toVec_ofVec] using h
  have hWslice := ae_memLp_slice_openCube_vec (P := P) (originCube d (M : ℤ)) hWm hWmem
  have hG₀slice := ae_memLp_slice_openCube_vec (P := P) (originCube d (M : ℤ)) hG₀m hG₀mem
  have hWsliceEq := ae_slice_eq_of_ae_eq (P := P) hWae (originCube d (M : ℤ))
  have hG₀sliceEq := ae_slice_eq_of_ae_eq (P := P) hG₀ae (originCube d (M : ℤ))
  have hGslice : ∀ᵐ ω ∂P.toMeasure, MemLp
      (fun x => HilbertVec.ofVec (gradHatW (x +ᵥ ω))) 2
      (volumeMeasureOn (openCubeSet (originCube d (M : ℤ)))) := by
    filter_upwards [hWslice, hWsliceEq] with ω h1 h2
    exact h1.ae_eq (h2.mono fun x hx => congrArg HilbertVec.ofVec hx)
  have hFslice : ∀ᵐ ω ∂P.toMeasure, MemLp
      (fun x => HilbertVec.ofVec (F (x +ᵥ ω) 0)) 2
      (volumeMeasureOn (openCubeSet (originCube d (M : ℤ)))) := by
    filter_upwards [hG₀slice, hG₀sliceEq] with ω h1 h2
    exact h1.ae_eq (h2.mono fun x hx => congrArg HilbertVec.ofVec hx)
  obtain ⟨uReal, huReal⟩ :
      ∃ uReal : ShellSeq d → H1Function (openCubeSet (originCube d (M : ℤ))),
        ∀ᵐ ω ∂P.toMeasure,
          (uReal ω).grad =ᵐ[volumeMeasureOn (openCubeSet (originCube d (M : ℤ)))]
            fun x => gradHatW (x +ᵥ ω) := by
    have hex := exists_h1_realization_of_eq_neg_stationaryPotentialProjection (P := P) M
      hFmemLp hG hproj
    let v : ShellSeq d → H1Function (openCubeSet (originCube d (M : ℤ))) := fun ω =>
      if h : ∃ u : H1Function (openCubeSet (originCube d (M : ℤ))),
          u.grad =ᵐ[volumeMeasureOn (openCubeSet (originCube d (M : ℤ)))]
            fun x => gradHatW (x +ᵥ ω)
        then h.choose else 0
    refine ⟨v, ?_⟩
    filter_upwards [hex] with ω hω
    rw [show v ω = hω.choose from dite_eq_left hω]
    exact hω.choose_spec
  refine ⟨uReal, huReal, ?_⟩
  filter_upwards [huReal, hpair, hGslice, hFslice] with ω hωu hωpair hωG hωF
  exact weakEquation_of_anchorPairing_eq_zero M hωu (hcocycle ω) hωG hωF hωpair

/-! ## Binder-for-binder match with the binder of the main statement

The binder `hStationaryAnchor` of `lhs_term1_of_stationaryAnchor`
takes `gradHatW`, the two `MemLp` hypotheses, and the
projection equation *with the instance `ShellField.vaddInvariantMeasure hPrefix hJ2` written
explicitly*, and returns the conclusion at cube side `S.m`.  The theorem below has
exactly that conclusion and exactly those hypotheses, with the instance supplied from
the prefix and `J2` as the binder does, and with the only further inputs being the cocycle of
`F` and the per-sample pairing `hpair`.  It is the alignment test: the projection binder of the
`hproj` and the implicit instance of `exists_realization_of_anchorPairing` unify, so no
restatement of the projection is needed when the binder is discharged. -/

end SuperdiffusionCLT.Probability.Stationary

end
