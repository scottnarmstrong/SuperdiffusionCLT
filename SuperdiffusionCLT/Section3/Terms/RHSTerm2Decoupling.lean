/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.RHSTerm2Glued

/-!
# The input `hDecouple` of `l.RHS.term2`

The assembly of `l.RHS.term2` in `RHSTerm2Main` and its constant-first
restatement `l_RHS_term2_constFirst` of `RHSTerm2Glued` carry the step
`l.RHS.term2#independence-decoupling` as the hypothesis `hDecouple`:

`E[⨍_{cu_m} R·(∇ũ_n − p̃)] = E[avsum_{z} ⨍_{z+cu_n} (R − (R)_z)·(∇ũ_n − (∇ũ_n)_z)]`.

The paper reaches that identity in one sentence: "Subtracting `(R)_{z+cu_n}` on
each cube", after the vanishing

`E[(R)_{z+cu_n}·((∇ũ_{n,z})_{z+cu_n} − p̃)] = 0`

The vanishing itself is `independence_decoupling` of `RHSTerm2Displays`; what
is needed is the bridge from it to the shape `hDecouple` has, namely the
deterministic cube algebra that turns the large-cube
average into the lattice average of the *doubly centred* sub-cube pairings, plus
the integrability needed to split the expectation.  `decoupling_bridge` below is
that bridge.

## The one input that is not a consequence of J2

The paper's justification of the vanishing is

> The field `R` is `F_>`-measurable, while `∇ũ_n` is measurable with respect to
> `σ(j_r : r ≤ ℓ)`.

and the independence of those two sigma-fields is `ShellLawJ2`.  The
*measurability* half is not available, in either slot:

* `R = (k_{L'} − k_ℓ)^t ∇w` involves the Dirichlet response `w`, which the
  rendered statement of `l.RHS.term2` carries as a free binder given only by
  `IsDirichletResponse`; nothing records how `w` depends on the shells, and no
  theorem gives joint measurability of `omega ↦ w omega` at all;
* `∇ũ_n` at the carriers used here is `gluedGradientField` at cutoff `ℓ`, whose
  cube-by-cube pieces come from `Book.Ch02.responseExistenceTheory` through a
  choice (see `qVector_apply` of `GluedField`), so not even joint
  measurability in `omega` is available for it, let alone measurability for the
  low shells.

`decoupling_bridge` therefore carries exactly one hypothesis that J2 does not
supply, `hindep`: on each sub-cube of the family, the two *cube mean vectors*
are independent.  That is the shape `independence_decoupling` already
uses, and the shape the paper asserts through the range of dependence alone.
`RHSTerm2DecouplingB` derives `hindep` from `ShellLawJ2` together with the
printed measurability sentence, so that J2 is genuinely consumed and the
remaining input is literally the measurability sentence of the paper.

Everything else in `hDecouple` is proved here: the sub-cube splitting of the
large-cube average (`volumeAverage_avsum_openCubeSet`), the double centring on
one cube (`volumeAverage_vecDot_sub_const_eq`), the vanishing of the cross term
in the sample (`independence_decoupling`), and the splitting of the expectation.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section2.Estimates.Stream
open Homogenization
open Homogenization.Book.Ch02

noncomputable section

variable {d : ℕ}

/-! ## Cube algebra: the double centring on one cube -/

/-- Each coordinate of an `L²` vector field is integrable on an open triadic
cube: the cube has finite volume, so `L²` sits inside `L¹`. -/
theorem integrableOn_component_of_memVectorL2 {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) (i : Fin d) :
    IntegrableOn (fun y => F y i) (openCubeSet Q) volume := by
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    SuperdiffusionCLT.Section3.ResponseFields.instIsFiniteMeasureVolumeMeasureOnOpenCubeSet Q
  exact MemLp.integrable (by norm_num) (memL2On_component_of_memVectorL2 hF i)

/-- Pulling a constant vector out of the **right** slot of a normalized
average, the mirror of `volumeAverage_vecDot_const_left`. -/
theorem volumeAverage_vecDot_const_right {U : Set (Vec d)} (c : Vec d)
    {F : Vec d → Vec d} (hF : ∀ i, IntegrableOn (fun y => F y i) U volume) :
    volumeAverage U (fun y => vecDot (F y) c) = vecDot (volumeAverageVec U F) c := by
  have h : (fun y => vecDot (F y) c) = fun y => vecDot c (F y) :=
    funext fun y => vecDot_comm (F y) c
  rw [h, volumeAverage_vecDot_const_left c hF, vecDot_comm]

/-- **The double centring on one cube** ("Subtracting `(R)_{z+cu_n}` on each cube"
in the proof of `l.RHS.term2`): on a cube `Q`, the
normalized average of the pairing of `G` against `F − c` is the average of the
pairing of the two fields centred at their own cube means, plus the pairing of
the two cube means with `c` subtracted.

Both centrings are free: the average of `G − (G)_Q` vanishes, so replacing
`F − c` by `F − (F)_Q` in the centred term costs nothing. -/
theorem volumeAverage_vecDot_sub_const_eq {Q : TriadicCube d}
    {G F : Vec d → Vec d} (c : Vec d)
    (hG : MemVectorL2 (openCubeSet Q) G) (hF : MemVectorL2 (openCubeSet Q) F) :
    volumeAverage (openCubeSet Q) (fun y => vecDot (G y) (F y - c)) =
      volumeAverage (openCubeSet Q)
          (fun y => vecDot (G y - volumeAverageVec (openCubeSet Q) G)
            (F y - volumeAverageVec (openCubeSet Q) F)) +
        vecDot (volumeAverageVec (openCubeSet Q) G)
          (volumeAverageVec (openCubeSet Q) F - c) := by
  have hGc : ∀ i, IntegrableOn (fun y => G y i) (openCubeSet Q) volume :=
    integrableOn_component_of_memVectorL2 hG
  have hFc : ∀ i, IntegrableOn (fun y => F y i) (openCubeSet Q) volume :=
    integrableOn_component_of_memVectorL2 hF
  have hFsub : MemVectorL2 (openCubeSet Q) (fun y => F y - c) := memVectorL2_sub_const c hF
  have hFsubc : ∀ i, IntegrableOn (fun y => (F y - c) i) (openCubeSet Q) volume :=
    integrableOn_component_of_memVectorL2 hFsub
  have hGsub : MemVectorL2 (openCubeSet Q)
      (fun y => G y - volumeAverageVec (openCubeSet Q) G) :=
    memVectorL2_sub_const (volumeAverageVec (openCubeSet Q) G) hG
  have hGsubAvg : volumeAverageVec (openCubeSet Q)
      (fun y => G y - volumeAverageVec (openCubeSet Q) G) = 0 := by
    rw [volumeAverageVec_sub_const hGc (volumeAverageVec (openCubeSet Q) G), sub_self]
  have hsplit := volumeAverage_vecDot_split G (fun y => F y - c)
    (integrableOn_vecDot hG hFsub) hFsubc
  rw [hsplit, volumeAverageVec_sub_const hFc c]
  refine congrArg (fun t : ℝ => t + vecDot (volumeAverageVec (openCubeSet Q) G)
    (volumeAverageVec (openCubeSet Q) F - c)) ?_
  have hFsub2 : MemVectorL2 (openCubeSet Q)
      (fun y => F y - volumeAverageVec (openCubeSet Q) F) :=
    memVectorL2_sub_const (volumeAverageVec (openCubeSet Q) F) hF
  have hconst : MemVectorL2 (openCubeSet Q)
      (fun _ : Vec d => volumeAverageVec (openCubeSet Q) F - c) :=
    memVectorL2_const (volumeAverageVec (openCubeSet Q) F - c)
  have hpt : (fun y => vecDot (G y - volumeAverageVec (openCubeSet Q) G) (F y - c)) =
      fun y => vecDot (G y - volumeAverageVec (openCubeSet Q) G)
            (F y - volumeAverageVec (openCubeSet Q) F) +
          vecDot (G y - volumeAverageVec (openCubeSet Q) G)
            (volumeAverageVec (openCubeSet Q) F - c) := by
    funext y
    have hy : F y - c = (F y - volumeAverageVec (openCubeSet Q) F) +
        (volumeAverageVec (openCubeSet Q) F - c) := by abel
    rw [hy, vecDot_add_right]
  rw [hpt, volumeAverage_add' (integrableOn_vecDot hGsub hFsub2)
      (integrableOn_vecDot hGsub hconst),
    volumeAverage_vecDot_const_right (volumeAverageVec (openCubeSet Q) F - c)
      (integrableOn_component_of_memVectorL2 hGsub),
    hGsubAvg]
  have hzero : vecDot (0 : Vec d) (volumeAverageVec (openCubeSet Q) F - c) = 0 := by
    show ∑ i : Fin d, (0 : ℝ) * (volumeAverageVec (openCubeSet Q) F - c) i = 0
    exact Finset.sum_eq_zero fun i _ => zero_mul _
  rw [hzero, add_zero]

/-! ## The lattice average of the doubly centred sub-cube pairings -/

/-- **The cube-by-cube decomposition of the proxy pairing** in the proof of
`l.RHS.term2`: the large-cube average of the pairing of `G` against `F − c` is
the lattice average of the doubly centred sub-cube pairings plus the lattice average of the
pairings of the sub-cube means. -/
theorem avsum_proxy_split {n m : ℕ} {G F : Vec d → Vec d} (c : Vec d)
    (hG : MemVectorL2 (openCubeSet (originCube d (m : ℤ))) G)
    (hF : MemVectorL2 (openCubeSet (originCube d (m : ℤ))) F) :
    volumeAverage (openCubeSet (originCube d (m : ℤ)))
        (fun y => vecDot (G y) (F y - c)) =
      ((largeCubeSubcubes d n m).card : ℝ)⁻¹ *
          ∑ z ∈ largeCubeSubcubes d n m,
            volumeAverage (openCubeSet z)
              (fun y => vecDot (G y - volumeAverageVec (openCubeSet z) G)
                (F y - volumeAverageVec (openCubeSet z) F)) +
        ((largeCubeSubcubes d n m).card : ℝ)⁻¹ *
          ∑ z ∈ largeCubeSubcubes d n m,
            vecDot (volumeAverageVec (openCubeSet z) G)
              (volumeAverageVec (openCubeSet z) F - c) := by
  have hFsub : MemVectorL2 (openCubeSet (originCube d (m : ℤ))) (fun y => F y - c) :=
    memVectorL2_sub_const c hF
  have hsum : ∀ z ∈ largeCubeSubcubes d n m,
      IntegrableOn (fun y => vecDot (G y) (F y - c)) (openCubeSet z) volume :=
    fun z hz => integrableOn_vecDot (memVectorL2_subcube hz hG) (memVectorL2_subcube hz hFsub)
  rw [volumeAverage_avsum_openCubeSet hsum]
  have hz : ∀ z ∈ largeCubeSubcubes d n m,
      volumeAverage (openCubeSet z) (fun y => vecDot (G y) (F y - c)) =
        volumeAverage (openCubeSet z)
            (fun y => vecDot (G y - volumeAverageVec (openCubeSet z) G)
              (F y - volumeAverageVec (openCubeSet z) F)) +
          vecDot (volumeAverageVec (openCubeSet z) G)
            (volumeAverageVec (openCubeSet z) F - c) :=
    fun z hz => volumeAverage_vecDot_sub_const_eq c (memVectorL2_subcube hz hG)
      (memVectorL2_subcube hz hF)
  rw [Finset.sum_congr rfl hz, Finset.sum_add_distrib, mul_add]

/-! ## The cross term in the sample -/

/-- The pairing of the two cube means against the shifted mean is an integrable
observable: componentwise it is a product of two independent integrable
variables minus a constant multiple of the first. -/
theorem integrable_vecDot_volumeAverageVec {P : ProbabilityMeasure (ShellSeq d)}
    {Q : TriadicCube d} {Rf UT : ShellSeq d → Vec d → Vec d} {pT : Vec d}
    (hindep : ProbabilityTheory.IndepFun
      (fun omega : ShellSeq d => volumeAverageVec (openCubeSet Q) (Rf omega))
      (fun omega : ShellSeq d => volumeAverageVec (openCubeSet Q) (UT omega)) P.toMeasure)
    (hRint : ∀ i : Fin d, Integrable
      (fun omega : ShellSeq d => volumeAverageVec (openCubeSet Q) (Rf omega) i) P.toMeasure)
    (hTint : ∀ i : Fin d, Integrable
      (fun omega : ShellSeq d => volumeAverageVec (openCubeSet Q) (UT omega) i) P.toMeasure) :
    Integrable (fun omega : ShellSeq d =>
      vecDot (volumeAverageVec (openCubeSet Q) (Rf omega))
        (volumeAverageVec (openCubeSet Q) (UT omega) - pT)) P.toMeasure := by
  classical
  have hcomp : ∀ i : Fin d, ProbabilityTheory.IndepFun
      (fun omega : ShellSeq d => volumeAverageVec (openCubeSet Q) (Rf omega) i)
      (fun omega : ShellSeq d => volumeAverageVec (openCubeSet Q) (UT omega) i)
      P.toMeasure := fun i =>
    hindep.comp (measurable_pi_apply i) (measurable_pi_apply i)
  have hmul : ∀ i : Fin d, Integrable
      (fun omega : ShellSeq d => volumeAverageVec (openCubeSet Q) (Rf omega) i *
        volumeAverageVec (openCubeSet Q) (UT omega) i) P.toMeasure := fun i =>
    (hcomp i).integrable_mul (hRint i) (hTint i)
  have hterm : ∀ i : Fin d, Integrable
      (fun omega : ShellSeq d => volumeAverageVec (openCubeSet Q) (Rf omega) i *
        (volumeAverageVec (openCubeSet Q) (UT omega) i - pT i)) P.toMeasure := by
    intro i
    have heq : (fun omega : ShellSeq d =>
        volumeAverageVec (openCubeSet Q) (Rf omega) i *
          (volumeAverageVec (openCubeSet Q) (UT omega) i - pT i)) =
        fun omega : ShellSeq d => volumeAverageVec (openCubeSet Q) (Rf omega) i *
            volumeAverageVec (openCubeSet Q) (UT omega) i -
          volumeAverageVec (openCubeSet Q) (Rf omega) i * pT i := by
      funext omega
      ring
    rw [heq]
    exact (hmul i).sub ((hRint i).mul_const (pT i))
  have hshow : (fun omega : ShellSeq d =>
      vecDot (volumeAverageVec (openCubeSet Q) (Rf omega))
        (volumeAverageVec (openCubeSet Q) (UT omega) - pT)) =
      fun omega : ShellSeq d => ∑ i : Fin d,
        volumeAverageVec (openCubeSet Q) (Rf omega) i *
          (volumeAverageVec (openCubeSet Q) (UT omega) i - pT i) := rfl
  rw [hshow]
  exact integrable_finsetSum _ fun i _ => hterm i

/-- Splitting an expectation along a pointwise decomposition whose second piece
is integrable with vanishing integral. -/
private theorem integral_eq_of_add_eq {alpha : Type*} [MeasurableSpace alpha]
    {mu : Measure alpha} {f g h : alpha → ℝ} (hfg : ∀ x, f x = g x + h x)
    (hf : Integrable f mu) (hh : Integrable h mu) (hzero : ∫ x, h x ∂mu = 0) :
    ∫ x, f x ∂mu = ∫ x, g x ∂mu := by
  have hg : Integrable g mu := by
    have heq : g = fun x => f x - h x := by
      funext x
      rw [hfg x]
      ring
    rw [heq]
    exact hf.sub hh
  calc ∫ x, f x ∂mu = ∫ x, (g x + h x) ∂mu :=
        integral_congr_ae (Filter.Eventually.of_forall hfg)
    _ = ∫ x, g x ∂mu + ∫ x, h x ∂mu := integral_add hg hh
    _ = ∫ x, g x ∂mu := by rw [hzero, add_zero]

/-! ## `hDecouple` -/

/-- **The decoupling identity `hDecouple`** of `l.RHS.term2`, in the exact shape the
assembly of `RHSTerm2Main.lean` and the constant-first restatement
`l_RHS_term2_constFirst` of `RHSTerm2Glued` consume:

`E[⨍_{cu_m} R·(∇ũ_n − p̃)] = E[avsum_z ⨍_{z+cu_n} (R − (R)_z)·(∇ũ_n − (∇ũ_n)_z)]`.

The proof is the paper's own: split the large-cube average into the lattice
average over the sub-cubes `z`, subtract `(R)_z` and `(∇ũ_n)_z` on each cube
(`avsum_proxy_split`), and observe that the cross term
`E[(R)_z·((∇ũ_n)_z − p̃)]` vanishes on every sub-cube by
`independence_decoupling`.

Hypotheses.  `hR`, `hT` and `hIntProxy` are already carried by the term-2 chain
(`hRL2`, `hUtL2`, `hIntProxy` of that chain).  `hRint`, `hTint` and `hmean`
are the inputs of `independence_decoupling` on each sub-cube of the family:
Bochner integrability in the sample of the two cube-mean vectors, and the
identification `E[(∇ũ_{n,z})_{z+cu_n}] = p̃`, which for the
glued proxy is the stationarity statement
`integral_volumeAverageVec_gluedGradientField_eq_testVector` read at the cutoff
level `ℓ`.  `hindep` is the single input that `ShellLawJ2` does not supply on
its own; see the module docstring, and `RHSTerm2DecouplingB` for its
derivation from J2 and the printed measurability sentence. -/
theorem decoupling_bridge {n m : ℕ} {P : ProbabilityMeasure (ShellSeq d)}
    {Rf UT : ShellSeq d → Vec d → Vec d} {pT : Vec d}
    (hR : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet (originCube d (m : ℤ))) (Rf omega))
    (hT : ∀ omega : ShellSeq d,
      MemVectorL2 (openCubeSet (originCube d (m : ℤ))) (UT omega))
    (hindep : ∀ z ∈ largeCubeSubcubes d n m, ProbabilityTheory.IndepFun
      (fun omega : ShellSeq d => volumeAverageVec (openCubeSet z) (Rf omega))
      (fun omega : ShellSeq d => volumeAverageVec (openCubeSet z) (UT omega)) P.toMeasure)
    (hRint : ∀ z ∈ largeCubeSubcubes d n m, ∀ i : Fin d, Integrable
      (fun omega : ShellSeq d => volumeAverageVec (openCubeSet z) (Rf omega) i) P.toMeasure)
    (hTint : ∀ z ∈ largeCubeSubcubes d n m, ∀ i : Fin d, Integrable
      (fun omega : ShellSeq d => volumeAverageVec (openCubeSet z) (UT omega) i) P.toMeasure)
    (hmean : ∀ z ∈ largeCubeSubcubes d n m, ∀ i : Fin d,
      ∫ omega : ShellSeq d,
        volumeAverageVec (openCubeSet z) (UT omega) i ∂P.toMeasure = pT i)
    (hIntProxy : Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet (originCube d (m : ℤ)))
        (fun y => vecDot (Rf omega y) (UT omega y - pT))) P.toMeasure) :
    ∫ omega : ShellSeq d,
        volumeAverage (openCubeSet (originCube d (m : ℤ)))
          (fun y => vecDot (Rf omega y) (UT omega y - pT)) ∂P.toMeasure =
      ∫ omega : ShellSeq d,
        (((largeCubeSubcubes d n m).card : ℝ)⁻¹ *
          ∑ z ∈ largeCubeSubcubes d n m,
            volumeAverage (openCubeSet z)
              (fun y => vecDot
                (Rf omega y - volumeAverageVec (openCubeSet z) (Rf omega))
                (UT omega y -
                  volumeAverageVec (openCubeSet z) (UT omega)))) ∂P.toMeasure := by
  classical
  have hcross : ∀ z ∈ largeCubeSubcubes d n m, Integrable
      (fun omega : ShellSeq d =>
        vecDot (volumeAverageVec (openCubeSet z) (Rf omega))
          (volumeAverageVec (openCubeSet z) (UT omega) - pT)) P.toMeasure :=
    fun z hz => integrable_vecDot_volumeAverageVec (hindep z hz) (hRint z hz) (hTint z hz)
  have hBint : Integrable (fun omega : ShellSeq d =>
      ((largeCubeSubcubes d n m).card : ℝ)⁻¹ *
        ∑ z ∈ largeCubeSubcubes d n m,
          vecDot (volumeAverageVec (openCubeSet z) (Rf omega))
            (volumeAverageVec (openCubeSet z) (UT omega) - pT)) P.toMeasure :=
    (integrable_finsetSum _ fun z hz => hcross z hz).const_mul _
  have hBzero : ∫ omega : ShellSeq d,
      ((largeCubeSubcubes d n m).card : ℝ)⁻¹ *
        ∑ z ∈ largeCubeSubcubes d n m,
          vecDot (volumeAverageVec (openCubeSet z) (Rf omega))
            (volumeAverageVec (openCubeSet z) (UT omega) - pT) ∂P.toMeasure = 0 := by
    have hz : ∀ z ∈ largeCubeSubcubes d n m,
        ∫ omega : ShellSeq d,
          vecDot (volumeAverageVec (openCubeSet z) (Rf omega))
            (volumeAverageVec (openCubeSet z) (UT omega) - pT) ∂P.toMeasure = 0 :=
      fun z hz => independence_decoupling (hindep z hz) (hRint z hz) (hTint z hz)
        (hmean z hz)
    rw [integral_const_mul,
      integral_finsetSum _ (fun z hz => hcross z hz),
      Finset.sum_congr rfl hz, Finset.sum_const_zero, mul_zero]
  exact integral_eq_of_add_eq
    (fun omega => avsum_proxy_split pT (hR omega) (hT omega)) hIntProxy hBint hBzero

end

end SuperdiffusionCLT.Section3.Terms
