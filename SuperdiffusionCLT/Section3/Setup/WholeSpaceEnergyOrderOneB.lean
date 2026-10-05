/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Estimates.Stream.ShellHminusEndpointOrderOneB
public import SuperdiffusionCLT.Section3.Setup.WholeSpaceEnergyOrderOne

/-!
# `l.LHS.term1` in the order-one hatted carrier, with its Section 2 inputs

The statement and proof of `l.LHS.term1`, restated with the vector-field hatted negative norm
read at order one, and then with its two Section 2 inputs discharged.

The first half of the module follows the printed chain: the two per-shell branches of
`WholeSpaceEnergyOrderOne.lean` are packaged as one family, summed, and fed to the
scale-free part of the chain, which never mentions the carrier and is
therefore reused verbatim.  The result is
`l_LHS_term1_constFirst_of_shellData`, at the order-one carrier and at the
order-one endpoint prefactor `1 + (m−r)`.

The second half discharges what is now available:

* `e.abstract.response.ND.weak` (`hNDweak`) from
  `Section3.ResponseFields.responseFields_apriori_orderOne_of_clauses`, the
  version-3 a priori statement whose fourth clause is stated in the order-one
  carrier;
* `e.jk.Hminus.endpoint` (`hZhmBound`, `hZhmBigO`) on the shells `r ≤ m` from
  `vecHatNegENormOrderOne_centeredShellFlux_le` and
  `isBigO_gammaSigma_shellHminusBound`;
* `e.jk.spatialavg` (`Z`, `Zav`) from `exists_shellFluxAverage_bound`.

`l_LHS_term1_of_anchors` is the result.  What it still takes as hypotheses is
listed in its docstring: the shell-law binders, the response fields of the
scale selection, the `r > m` form of the endpoint (Poincaré and `a.j.reg`;
it is not proved here) and the `L̲⁴` bound of the paper.

## Main results

* `shellResponseGap_branch`, `exists_gammaSigma_sum_of_shellGapBranch`:
  the two branches as one family and the single dominating observable.
* `lhsTerm1ShellConst`, `l_LHS_term1_constFirst_of_shellData`:
  `l.LHS.term1` with its constant written out, at the order-one carrier.
* `l_LHS_term1_of_anchors`: the same, with the a priori statement, the `r ≤ m`
  endpoint and the spatial-average display discharged.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open MeasureTheory
open ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Probability.Stationary
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section3.ResponseFields
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The two branches as one family -/

/-- **The scale-by-scale estimate of the proof of `l.LHS.term1` as one family,
at order one.**  The
carrier of `hNDweak` and `hZhmBound` is read at order one and the `r < M` branch
of `hZhmBigO` carries `1 + (M−r)` in place of the printed `(M−r)^{1/2}`. -/
theorem shellResponseGap_branch (hd : 2 ≤ d)
    (P : ProbabilityMeasure (ShellSeq d)) (M : ℕ) (t : Finset ℕ)
    (p : Vec d) (hpnorm : 0 < vecNorm p)
    (wDr : ℕ → ShellSeq d → H10Function (openCubeSet (originCube d (M : ℤ))))
    (wNr : ℕ → ShellSeq d →
      H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ))))
    (hwDr : ∀ r ∈ t, ∀ omega : ShellSeq d,
      IsCubeDirichletResponse (originCube d (M : ℤ)) (shellFlux omega r p)
        (wDr r omega))
    (hwNr : ∀ r ∈ t, ∀ omega : ShellSeq d,
      IsCubeNeumannResponse (originCube d (M : ℤ)) (shellFlux omega r p)
        (wNr r omega))
    (Cnd : ℝ) (hCnd : 0 < Cnd)
    (hNDweak : ∀ (G : Vec d → Vec d)
      (v : H10Function (openCubeSet (originCube d (M : ℤ))))
      (vN : H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ)))),
      IsCubeDirichletResponse (originCube d (M : ℤ)) G v →
      IsCubeNeumannResponse (originCube d (M : ℤ)) G vN →
      vecCubeLpENorm (originCube d (M : ℤ)) 2
          (fun x => vN.toH1Function.grad x - v.toH1Function.grad x) ≤
        ENNReal.ofReal Cnd *
            (vecHatNegENormOrderOne (originCube d (M : ℤ))
              (fun x => G x -
                volumeAverageVec (cubeSet (originCube d (M : ℤ))) G))
              ^ ((1 : ℝ) / 5) *
            (vecCubeLpENorm (originCube d (M : ℤ)) 4
              (fun x => G x -
                volumeAverageVec (cubeSet (originCube d (M : ℤ))) G))
              ^ ((4 : ℝ) / 5) +
          ENNReal.ofReal Cnd * ‖HilbertVec.ofVec
            (volumeAverageVec (cubeSet (originCube d (M : ℤ))) G)‖ₑ)
    (Chm : ℝ) (hChm : 0 < Chm) (Zhm : ℕ → ShellSeq d → ℝ)
    (hZhm0 : ∀ r omega, 0 ≤ Zhm r omega)
    (hZhmMeas : ∀ r, Measurable (Zhm r))
    (hZhmBigO : ∀ r ∈ t, IsBigO P.toMeasure (gammaSigma 2) (Zhm r)
      (if M ≤ r then Chm * vecNorm p * (3 : ℝ) ^ (-((r - M : ℕ) : ℝ))
        else Chm * vecNorm p *
          ((1 + ((M - r : ℕ) : ℝ)) * (3 : ℝ) ^ (-((M - r : ℕ) : ℝ)))))
    (hZhmBound : ∀ r ∈ t, ∀ omega, vecHatNegENormOrderOne (originCube d (M : ℤ))
        (fun x => shellFlux omega r p x -
          volumeAverageVec (cubeSet (originCube d (M : ℤ)))
            (shellFlux omega r p)) ≤ ENNReal.ofReal (Zhm r omega))
    (Cl4 : ℝ) (hCl4 : 0 < Cl4) (Zl4 : ℕ → ShellSeq d → ℝ)
    (hZl40 : ∀ r omega, 0 ≤ Zl4 r omega)
    (hZl4Meas : ∀ r, Measurable (Zl4 r))
    (hZl4BigO : ∀ r ∈ t,
      IsBigO P.toMeasure (gammaSigma 2) (Zl4 r) (Cl4 * vecNorm p))
    (hZl4Bound : ∀ r ∈ t, ∀ omega, vecCubeLpENorm (originCube d (M : ℤ)) 4
        (fun x => shellFlux omega r p x -
          volumeAverageVec (cubeSet (originCube d (M : ℤ)))
            (shellFlux omega r p)) ≤ ENNReal.ofReal (Zl4 r omega))
    (CavLt : ℝ) (hCavLt : 0 < CavLt) (Zav : ℕ → ShellSeq d → ℝ)
    (hZav0 : ∀ r omega, 0 ≤ Zav r omega)
    (hZavMeas : ∀ r, Measurable (Zav r))
    (hZavBigO : ∀ r ∈ t, IsBigO P.toMeasure (gammaSigma 2) (Zav r)
      (CavLt * vecNorm p * (3 : ℝ) ^ (-((d : ℝ) / 2) * ((M - r : ℕ) : ℝ))))
    (hZavBound : ∀ r ∈ t, ∀ omega,
      vecNorm (shellFluxAverage (M : ℤ) omega r p) ≤ Zav r omega) :
    ∀ r ∈ t, ∃ Zg : ShellSeq d → ℝ, (∀ omega, 0 ≤ Zg omega) ∧ Measurable Zg ∧
      IsBigO P.toMeasure (gammaSigma 2) Zg
        (shellGapAmplitude (shellResponseGapConst Cnd Chm Cl4 CavLt)
          (shellResponseGapGeConst Cnd Chm Cl4) (vecNorm p) M r) ∧
      ∀ omega, vecCubeLpENorm (originCube d (M : ℤ)) 2
          (fun x => (wNr r omega).toH1Function.grad x +
              (if M ≤ r then shellFluxAverage (M : ℤ) omega r p else 0) -
            (wDr r omega).toH1Function.grad x) ≤ ENNReal.ofReal (Zg omega) := by
  intro r hr
  by_cases hcase : M ≤ r
  · obtain ⟨Zg, hZg0, hZgMeas, hZgBig, hZgBound⟩ :=
      shellResponseGap_ge P p hpnorm (wDr r) (wNr r) (hwDr r hr) (hwNr r hr)
        Cnd hCnd hNDweak Chm hChm (Zhm r) (hZhm0 r) (hZhmMeas r)
        (by simpa only [ite_eq_left hcase] using hZhmBigO r hr)
        (hZhmBound r hr) Cl4 hCl4 (Zl4 r) (hZl40 r) (hZl4Meas r)
        (hZl4BigO r hr) (hZl4Bound r hr)
    refine ⟨Zg, hZg0, hZgMeas, ?_, ?_⟩
    · rw [shellGapAmplitude, ite_eq_left hcase]
      exact hZgBig
    · intro omega
      simpa only [ite_eq_left hcase] using hZgBound omega
  · obtain ⟨Zg, hZg0, hZgMeas, hZgBig, hZgBound⟩ :=
      shellResponseGap_lt hd P p hpnorm (wDr r) (wNr r) (hwDr r hr)
        (hwNr r hr) Cnd hCnd hNDweak Chm hChm (Zhm r) (hZhm0 r) (hZhmMeas r)
        (by simpa only [ite_eq_right hcase] using hZhmBigO r hr)
        (hZhmBound r hr) Cl4 hCl4 (Zl4 r) (hZl40 r) (hZl4Meas r)
        (hZl4BigO r hr) (hZl4Bound r hr) CavLt hCavLt (Zav r) (hZav0 r)
        (hZavMeas r) (hZavBigO r hr) (hZavBound r hr)
    refine ⟨Zg, hZg0, hZgMeas, ?_, ?_⟩
    · rw [shellGapAmplitude, ite_eq_right hcase]
      exact hZgBig
    · intro omega
      simpa only [ite_eq_right hcase, add_zero] using hZgBound omega

/-! ## The single dominating observable -/

/-- **The summed display `e.wN.wD.with.average.error`, packaged, at order
one.**  The amplitude is the order-one amplitude `shellGapAmplitude`. -/
theorem exists_gammaSigma_sum_of_shellGapBranch
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsFiniteMeasure mu] (m : ℕ) (t : Finset ℕ) (ht : t.Nonempty)
    {Clt Cge B : ℝ} (hClt : 0 < Clt) (hCge : 0 < Cge) (hB : 0 < B)
    (N : ℕ → Omega → ℝ≥0∞)
    (h : ∀ r ∈ t, ∃ Zg : Omega → ℝ, (∀ omega, 0 ≤ Zg omega) ∧ Measurable Zg ∧
      IsBigO mu (gammaSigma 2) Zg (shellGapAmplitude Clt Cge B m r) ∧
      ∀ omega, N r omega ≤ ENNReal.ofReal (Zg omega)) :
    ∃ (Zgap : ℕ → Omega → ℝ) (Y : Omega → ℝ),
      (∀ r ∈ t, ∀ omega, 0 ≤ Zgap r omega) ∧
      (∀ r ∈ t, ∀ omega, N r omega ≤ ENNReal.ofReal (Zgap r omega)) ∧
      (∀ omega, 0 ≤ Y omega) ∧ Measurable Y ∧
      IsBigO mu (gammaSigma 2) Y (shellGapSumConst Clt Cge * B) ∧
      ∀ omega, ∑ r ∈ t, Zgap r omega ≤ Y omega := by
  classical
  set Zgap : ℕ → Omega → ℝ :=
    fun r => if hr : r ∈ t then Classical.choose (h r hr) else 0 with hZdef
  have h0 : ∀ r ∈ t, ∀ omega, 0 ≤ Zgap r omega := by
    intro r hr omega
    rw [hZdef]
    simp only [dite_eq_left hr]
    exact (Classical.choose_spec (h r hr)).1 omega
  have hmeas : ∀ r ∈ t, Measurable (Zgap r) := by
    intro r hr
    rw [hZdef]
    simp only [dite_eq_left hr]
    exact (Classical.choose_spec (h r hr)).2.1
  have hbig : ∀ r ∈ t, IsBigO mu (gammaSigma 2) (Zgap r)
      (shellGapAmplitude Clt Cge B m r) := by
    intro r hr
    rw [hZdef]
    simp only [dite_eq_left hr]
    exact (Classical.choose_spec (h r hr)).2.2.1
  have hbound : ∀ r ∈ t, ∀ omega,
      N r omega ≤ ENNReal.ofReal (Zgap r omega) := by
    intro r hr omega
    rw [hZdef]
    simp only [dite_eq_left hr]
    exact (Classical.choose_spec (h r hr)).2.2.2 omega
  refine ⟨Zgap, fun omega => ∑ r ∈ t, Zgap r omega, h0, hbound, ?_, ?_, ?_,
    fun _ => le_rfl⟩
  · intro omega
    exact Finset.sum_nonneg fun r hr => h0 r hr omega
  · exact Finset.measurable_sum t hmeas
  · exact isBigO_gammaSigma_sum_of_shellGapAmplitude m t ht hClt hCge hB Zgap
      hmeas hbig


/-! ## The constant written out -/

/-- **The constant `C(d)` of `e.nabla.w.lower.bound` at order one**:
`lhsTerm1Const` at the summed amplitude constant `shellGapSumConst`, i.e. at
the finite-family `Γ₂` triangle constant times the two geometric series,
evaluated at the two per-shell constants of `shellResponseGap_lt` and
`shellResponseGap_ge`.

It depends only on the a priori response constant `Cnd`, the two centered
weak-norm constants `Chm` and `Cl4`, and the two applied constants `Cav`,
`CavLt` of `e.jk.spatialavg` — never on the scale selection, the shell law or
the direction.  Replacing the printed `(m−r)^{1/2}` of the endpoint by
`1 + (m−r)` changes only the value of the summed series constant
(`shellPolyTailSeriesConstScaled` in place of `shellPolyTailSeriesConst`); it stays
a pure number, so `C(d)` is still a constant in `d` alone. -/
def lhsTerm1ShellConst (Cnd Chm Cl4 Cav CavLt : ℝ) : ℝ :=
  lhsTerm1Const
    (shellGapSumConst (shellResponseGapConst Cnd Chm Cl4 CavLt)
      (shellResponseGapGeConst Cnd Chm Cl4)) Cav

theorem one_le_lhsTerm1ShellConst (Cnd Chm Cl4 Cav CavLt : ℝ) :
    1 ≤ lhsTerm1ShellConst Cnd Chm Cl4 Cav CavLt :=
  one_le_lhsTerm1Const _ _

/-- **Lemma `l.LHS.term1` in the manuscript's quantifier order, from the
per-shell data, at the order-one carrier**.

There are two changes to the printed statement: the hatted negative norm of `hNDweak` and
`hZhmBound` is `Section2.Norms.vecHatNegENormOrderOne`, and the `r < m` amplitude of `hZhmBigO` is
`Chm |p| (1+(m−r)) 3^{−(m−r)}` in place of the printed
`Chm |p| (m−r)^{1/2} 3^{−(m−r)}`.  The conclusion's constant is
`lhsTerm1ShellConst`, a function of the input constants alone. -/
theorem l_LHS_term1_constFirst_of_shellData
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (Cnd Chm Cl4 Cav CavLt : ℝ) (hCnd : 0 < Cnd) (hChm : 0 < Chm)
    (hCl4 : 0 < Cl4) (hCav : 0 < Cav) (hCavLt : 0 < CavLt)
    (nu : ℝ) (hnu : 0 < nu)
    (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)
    [hInv : VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
    (cStar K : ℝ)
    (S : ScaleSelection) (hSorder : ScalesOrdering S)
    (e : Vec d) (he : vecNormSq e = 1) (hunit : Book.Ch02.vecNorm e = 1)
    (p : Vec d) (hp : p = testVector nu S.LPrime P S.n e)
    (F : ShellSeq d → Vec d → Vec d)
    (hF : ∀ omega : ShellSeq d, F omega = fun x =>
      matVecMul (streamCutoff omega S.LPrime x -
        streamCutoff omega S.ellPrime x) p)
    (gradHatW : ShellSeq d → Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (wN : ShellSeq d →
      H1MeanZeroFunction (openCubeSet (originCube d (S.m : ℤ))))
    (hwD : ∀ omega : ShellSeq d,
      IsCubeDirichletResponse (originCube d (S.m : ℤ)) (F omega) (wD omega))
    (hwN : ∀ omega : ShellSeq d,
      IsCubeNeumannResponse (originCube d (S.m : ℤ)) (F omega) (wN omega))
    (hwDmeas : AEStronglyMeasurable
      (fun omega : ShellSeq d => vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (wD omega).toH1Function.grad) P.toMeasure)
    (hFmemLp : MemLp (fun omega : ShellSeq d =>
        HilbertVec.ofVec (F omega 0)) 2 P.toMeasure)
    (hGmemLp : MemLp (fun omega : ShellSeq d =>
        HilbertVec.ofVec (gradHatW omega)) 2 P.toMeasure)
    (hproj : (hGmemLp.toLp fun omega : ShellSeq d =>
          HilbertVec.ofVec (gradHatW omega)) =
        -stationaryPotentialProjection (μ := P.toMeasure)
          (hFmemLp.toLp fun omega : ShellSeq d =>
            HilbertVec.ofVec (F omega 0)))
    (hlow : ∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (wD omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure ≤
        ∫⁻ omega : ShellSeq d,
          ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure)
    (hup : ∫⁻ omega : ShellSeq d,
          ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure ≤
        ∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (wN omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure)
    (Z : ℕ → ShellSeq d → ℝ) (hZm : ∀ r, Measurable (Z r))
    (hZbig : ∀ r ∈ Finset.Icc S.m S.LPrime,
      IsBigO P.toMeasure (gammaSigma 2) (Z r)
        (Cav * Book.Ch02.vecNorm p))
    (hZbound : ∀ (r : ℕ) (omega : ShellSeq d),
      Book.Ch02.vecNorm (shellFluxAverage (S.m : ℤ) omega r p) ≤ Z r omega)
    (hJ5app : |‖blockPotentialResponse P S.ellPrime S.LPrime
            (blockRegLaw_stationary hPrefix hJ2 S.ellPrime S.LPrime) e
            (memLp_originForcing_blockRegLaw hJ3 S.ellPrime S.LPrime e
              hunit)‖ ^ 2 -
          cStar * Real.log 3 * ((S.LPrime - S.ellPrime : ℕ) : ℝ)| ≤ K)
    (wDr : ℕ → ShellSeq d →
      H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (wNr : ℕ → ShellSeq d →
      H1MeanZeroFunction (openCubeSet (originCube d (S.m : ℤ))))
    (hwDr : ∀ r ∈ Finset.Ioc S.ellPrime S.LPrime, ∀ omega : ShellSeq d,
      IsCubeDirichletResponse (originCube d (S.m : ℤ)) (shellFlux omega r p)
        (wDr r omega))
    (hwNr : ∀ r ∈ Finset.Ioc S.ellPrime S.LPrime, ∀ omega : ShellSeq d,
      IsCubeNeumannResponse (originCube d (S.m : ℤ)) (shellFlux omega r p)
        (wNr r omega))
    (hNDweak : ∀ (G : Vec d → Vec d)
      (v : H10Function (openCubeSet (originCube d (S.m : ℤ))))
      (vN : H1MeanZeroFunction (openCubeSet (originCube d (S.m : ℤ)))),
      IsCubeDirichletResponse (originCube d (S.m : ℤ)) G v →
      IsCubeNeumannResponse (originCube d (S.m : ℤ)) G vN →
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => vN.toH1Function.grad x - v.toH1Function.grad x) ≤
        ENNReal.ofReal Cnd *
            (vecHatNegENormOrderOne (originCube d (S.m : ℤ))
              (fun x => G x -
                volumeAverageVec (cubeSet (originCube d (S.m : ℤ))) G))
              ^ ((1 : ℝ) / 5) *
            (vecCubeLpENorm (originCube d (S.m : ℤ)) 4
              (fun x => G x -
                volumeAverageVec (cubeSet (originCube d (S.m : ℤ))) G))
              ^ ((4 : ℝ) / 5) +
          ENNReal.ofReal Cnd * ‖HilbertVec.ofVec
            (volumeAverageVec (cubeSet (originCube d (S.m : ℤ))) G)‖ₑ)
    (Zhm : ℕ → ShellSeq d → ℝ)
    (hZhm0 : ∀ r omega, 0 ≤ Zhm r omega)
    (hZhmMeas : ∀ r, Measurable (Zhm r))
    (hZhmBigO : ∀ r ∈ Finset.Ioc S.ellPrime S.LPrime,
      IsBigO P.toMeasure (gammaSigma 2) (Zhm r)
        (if S.m ≤ r then
            Chm * Book.Ch02.vecNorm p * (3 : ℝ) ^ (-((r - S.m : ℕ) : ℝ))
          else Chm * Book.Ch02.vecNorm p *
            ((1 + ((S.m - r : ℕ) : ℝ)) * (3 : ℝ) ^ (-((S.m - r : ℕ) : ℝ)))))
    (hZhmBound : ∀ r ∈ Finset.Ioc S.ellPrime S.LPrime, ∀ omega : ShellSeq d,
      vecHatNegENormOrderOne (originCube d (S.m : ℤ))
        (fun x => shellFlux omega r p x -
          volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
            (shellFlux omega r p)) ≤ ENNReal.ofReal (Zhm r omega))
    (Zl4 : ℕ → ShellSeq d → ℝ)
    (hZl40 : ∀ r omega, 0 ≤ Zl4 r omega)
    (hZl4Meas : ∀ r, Measurable (Zl4 r))
    (hZl4BigO : ∀ r ∈ Finset.Ioc S.ellPrime S.LPrime,
      IsBigO P.toMeasure (gammaSigma 2) (Zl4 r) (Cl4 * Book.Ch02.vecNorm p))
    (hZl4Bound : ∀ r ∈ Finset.Ioc S.ellPrime S.LPrime, ∀ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 4
        (fun x => shellFlux omega r p x -
          volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
            (shellFlux omega r p)) ≤ ENNReal.ofReal (Zl4 r omega))
    (Zav : ℕ → ShellSeq d → ℝ)
    (hZav0 : ∀ r omega, 0 ≤ Zav r omega)
    (hZavMeas : ∀ r, Measurable (Zav r))
    (hZavBigO : ∀ r ∈ Finset.Ioc S.ellPrime S.LPrime,
      IsBigO P.toMeasure (gammaSigma 2) (Zav r)
        (CavLt * Book.Ch02.vecNorm p *
          (3 : ℝ) ^ (-((d : ℝ) / 2) * ((S.m - r : ℕ) : ℝ))))
    (hZavBound : ∀ r ∈ Finset.Ioc S.ellPrime S.LPrime, ∀ omega : ShellSeq d,
      Book.Ch02.vecNorm (shellFluxAverage (S.m : ℤ) omega r p) ≤ Zav r omega) :
    |(∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (wD omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure :
            ℝ≥0∞).toReal -
        cStar * Real.log 3 * ((S.m - S.n : ℕ) : ℝ) * vecNormSq p| ≤
      (lhsTerm1ShellConst Cnd Chm Cl4 Cav CavLt *
          (1 + ((S.LPrime - S.m : ℕ) : ℝ)) + K) * vecNormSq p := by
  classical
  have hlm : S.ellPrime < S.m := hSorder.ellPrime_lt_m
  have hmL : S.m < S.LPrime := hSorder.m_lt_LPrime
  have ht : (Finset.Ioc S.ellPrime S.LPrime).Nonempty :=
    ⟨S.m, Finset.mem_Ioc.2 ⟨hlm, le_of_lt hmL⟩⟩
  have hlam := sigmaBarStarInvSqrt_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
  have hp' : p = sigmaBarStarInvSqrt nu S.LPrime P S.n • e := by
    rw [hp, testVector]
  have hpt : 0 < Book.Ch02.vecNorm p := by
    have hnorm : Book.Ch02.vecNorm p =
        |sigmaBarStarInvSqrt nu S.LPrime P S.n| * Book.Ch02.vecNorm e := by
      rw [hp']
      show ‖HilbertVec.ofVec (sigmaBarStarInvSqrt nu S.LPrime P S.n • e)‖ = _
      rw [ofVec_smul, norm_smul, Real.norm_eq_abs]
      rfl
    rw [hnorm, hunit, mul_one, abs_of_pos hlam]
    exact hlam
  have hbranch := shellResponseGap_branch hd P S.m
    (Finset.Ioc S.ellPrime S.LPrime) p hpt wDr wNr hwDr hwNr Cnd hCnd hNDweak
    Chm hChm Zhm hZhm0 hZhmMeas hZhmBigO hZhmBound Cl4 hCl4 Zl4 hZl40 hZl4Meas
    hZl4BigO hZl4Bound CavLt hCavLt Zav hZav0 hZavMeas hZavBigO hZavBound
  obtain ⟨Zgap, Y, hZgap0, hZgapBound, hY0, hYm, hYbig, hYsum⟩ :=
    exists_gammaSigma_sum_of_shellGapBranch (mu := P.toMeasure) S.m
      (Finset.Ioc S.ellPrime S.LPrime) ht
      (shellResponseGapConst_pos hCnd hChm hCl4 hCavLt)
      (shellResponseGapGeConst_pos hCnd hChm hCl4) hpt
      (fun r omega => vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (fun x => (wNr r omega).toH1Function.grad x +
            (if S.m ≤ r then shellFluxAverage (S.m : ℤ) omega r p else 0) -
          (wDr r omega).toH1Function.grad x)) hbranch
  have hbridge := vecCubeLpENorm_grad_sub_le_of_shellGapSum d S hlm
    (le_of_lt hmL) p F hF wD wN hwD hwN wDr wNr hwDr hwNr Zgap hZgap0
    hZgapBound Y hYsum
  rw [lhsTerm1ShellConst]
  exact abs_toReal_sub_cStar_mul_le_lhsTerm1Const d
    (shellGapSumConst (shellResponseGapConst Cnd Chm Cl4 CavLt)
      (shellResponseGapGeConst Cnd Chm Cl4)) Cav
    (shellGapSumConst_pos (shellResponseGapConst_pos hCnd hChm hCl4 hCavLt)
      (shellResponseGapGeConst_pos hCnd hChm hCl4)) hCav nu hnu P hPrefix hJ2
    hJ3 hJ4 cStar K S hSorder e he hunit p hp F hF gradHatW wD wN hwD hwN
    hwDmeas hFmemLp hGmemLp hproj hlow hup Y hY0 hYm hYbig Z hZm hZbig hZbound
    hbridge hJ5app

/-! ## The LHS term from the Section 2 inputs -/

/-- **Lemma `l.LHS.term1` with its Section 2 inputs discharged.**

The constant is produced first, from `d`, from the a priori statement and from the
two remaining input constants alone, and the whole statement of `l.LHS.term1`
follows for every shell law, scale selection and direction.

Discharged here, with no residue:

* `e.abstract.response.ND.weak`: `hApriori` is the conclusion of the version-3
  a priori statement `l.abstract.response.fields.apriori` verbatim, so
  `Section3.ResponseFields.responseFields_apriori_orderOne_of_clauses d hd` supplies
  it; only its finiteness is used, through `Cnd = C.toReal + 1`;
* `e.jk.Hminus.endpoint` on the shells `r ≤ m`, from
  `vecHatNegENormOrderOne_centeredShellFlux_le` and
  `isBigO_gammaSigma_shellHminusBound`, at the amplitude
  `shellHminusConst d |p| (1+(m−r)) 3^{−(m−r)}`;
* `e.jk.spatialavg`, both applied shapes, from
  `exists_shellFluxAverage_bound` and
  `exists_shellFluxAverage_bound_ge`, at `Cav = CavLt =
  spatialAverageTailConst d`.

What remains, and why:

* the shell-law binders `hPrefix`, `hJ1`, `hJ2`, `hJ3`, `hJ4` and the
  translation invariance of `P`, which are the standing assumptions themselves;
* the response fields of the scale selection (`wD`, `wN`, `wDr`, `wNr` and
  their defining relations, `hproj`, `hlow`, `hup`, `hJ5app`), which are the
  data `l.abstract.response.fields` and `e.ellsep.testing` provide, not
  estimates;
* `ZhmGe`: `e.jk.Hminus.endpoint` in its `r > m` form,
  `‖j_r p − (j_r p)_{cu_m}‖_{Ĥ̲^{-1}(cu_m)} ≤ O_{Γ₂}(C|p|3^{−(r−m)})`, which
  the paper gets from Poincaré's inequality and `a.j.reg`; it is not proved
  here, and `ShellHminusEndpointOrderOneB.lean` covers only `r ≤ m`;
* `Zl4`: the `L̲⁴` bound of the paper, likewise taken as a hypothesis. -/
theorem l_LHS_term1_of_anchors
    (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (hApriori : ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ (M : ℕ) (F : Vec d → Vec d)
        (wD : H10Function (openCubeSet (originCube d (M : ℤ))))
        (wN : H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ)))),
        IsCubeDirichletResponse (originCube d (M : ℤ)) F wD →
        IsCubeNeumannResponse (originCube d (M : ℤ)) F wN →
        (vecCubeLpENorm (originCube d (M : ℤ)) 8 wD.toH1Function.grad +
              vecCubeLpENorm (originCube d (M : ℤ)) 8 wN.toH1Function.grad ≤
            C * vecCubeLpENorm (originCube d (M : ℤ)) 8 F) ∧
        (∀ (DF : Fin d → Vec d → Vec d)
            (HD : HasWeakHessianOn (openCubeSet (originCube d (M : ℤ)))
              wD.toH1Function),
            (∀ i, HasWeakGradientOn (openCubeSet (originCube d (M : ℤ)))
              (fun x => F x i) (DF i)) →
            cubeLpENorm (originCube d (M : ℤ)) 8
                (fun x => HilbertMat.ofMat (fun i j => HD.hess i j x)) ≤
            C * cubeLpENorm (originCube d (M : ℤ)) 8
                (fun x => HilbertMat.ofMat (fun i j => DF i x j))) ∧
        (cubeHsENorm (originCube d (M : ℤ)) (1 / 2)
                (hilbertifyVecField wD.toH1Function.grad) ≤
            C * cubeHsENorm (originCube d (M : ℤ)) (1 / 2)
                (hilbertifyVecField F)) ∧
        (vecCubeLpENorm (originCube d (M : ℤ)) 2
              (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) ≤
            C * (vecHatNegENormOrderOne (originCube d (M : ℤ))
                  (fun x => F x - volumeAverageVec
                    (cubeSet (originCube d (M : ℤ))) F)) ^ ((1 : ℝ) / 5) *
                (vecCubeLpENorm (originCube d (M : ℤ)) 4
                  (fun x => F x - volumeAverageVec
                    (cubeSet (originCube d (M : ℤ))) F)) ^ ((4 : ℝ) / 5) +
              C * ‖HilbertVec.ofVec (volumeAverageVec
                  (cubeSet (originCube d (M : ℤ))) F)‖ₑ))
    (Cl4 ChmGe : ℝ) (hCl4 : 0 < Cl4) (hChmGe : 0 < ChmGe) :
    ∃ Clhs : ℝ, 1 ≤ Clhs ∧
      ∀ (nu : ℝ), 0 < nu →
      ∀ (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P)
        (_hJ1 : ShellLawJ1 d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
        (_hJ4 : ShellLawJ4 d P)
        (_hInv : VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure)
        (cStar K : ℝ) (S : ScaleSelection), ScalesOrdering S →
      ∀ (e : Vec d) (_he : vecNormSq e = 1) (hunit : Book.Ch02.vecNorm e = 1)
        (p : Vec d), p = testVector nu S.LPrime P S.n e →
      ∀ F : ShellSeq d → Vec d → Vec d,
        (∀ omega : ShellSeq d, F omega = fun x =>
          matVecMul (streamCutoff omega S.LPrime x -
            streamCutoff omega S.ellPrime x) p) →
      ∀ (gradHatW : ShellSeq d → Vec d)
        (wD : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (wN : ShellSeq d →
          H1MeanZeroFunction (openCubeSet (originCube d (S.m : ℤ)))),
        (∀ omega : ShellSeq d, IsCubeDirichletResponse (originCube d (S.m : ℤ))
          (F omega) (wD omega)) →
        (∀ omega : ShellSeq d, IsCubeNeumannResponse (originCube d (S.m : ℤ))
          (F omega) (wN omega)) →
        AEStronglyMeasurable (fun omega : ShellSeq d =>
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (wD omega).toH1Function.grad) P.toMeasure →
      ∀ (hFmemLp : MemLp (fun omega : ShellSeq d =>
            HilbertVec.ofVec (F omega 0)) 2 P.toMeasure)
        (hGmemLp : MemLp (fun omega : ShellSeq d =>
            HilbertVec.ofVec (gradHatW omega)) 2 P.toMeasure),
        (hGmemLp.toLp fun omega : ShellSeq d =>
              HilbertVec.ofVec (gradHatW omega)) =
            -stationaryPotentialProjection (μ := P.toMeasure)
              (hFmemLp.toLp fun omega : ShellSeq d =>
                HilbertVec.ofVec (F omega 0)) →
        (∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (wD omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure ≤
            ∫⁻ omega : ShellSeq d,
              ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure) →
        (∫⁻ omega : ShellSeq d,
              ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure ≤
            ∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (wN omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure) →
        |‖blockPotentialResponse P S.ellPrime S.LPrime
              (blockRegLaw_stationary hPrefix hJ2 S.ellPrime S.LPrime) e
              (memLp_originForcing_blockRegLaw hJ3 S.ellPrime S.LPrime e
                hunit)‖ ^ 2 -
            cStar * Real.log 3 * ((S.LPrime - S.ellPrime : ℕ) : ℝ)| ≤ K →
      ∀ (wDr : ℕ → ShellSeq d →
            H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (wNr : ℕ → ShellSeq d →
            H1MeanZeroFunction (openCubeSet (originCube d (S.m : ℤ)))),
        (∀ r ∈ Finset.Ioc S.ellPrime S.LPrime, ∀ omega : ShellSeq d,
          IsCubeDirichletResponse (originCube d (S.m : ℤ))
            (shellFlux omega r p) (wDr r omega)) →
        (∀ r ∈ Finset.Ioc S.ellPrime S.LPrime, ∀ omega : ShellSeq d,
          IsCubeNeumannResponse (originCube d (S.m : ℤ))
            (shellFlux omega r p) (wNr r omega)) →
      ∀ Zl4 : ℕ → ShellSeq d → ℝ, (∀ r omega, 0 ≤ Zl4 r omega) →
        (∀ r, Measurable (Zl4 r)) →
        (∀ r ∈ Finset.Ioc S.ellPrime S.LPrime,
          IsBigO P.toMeasure (gammaSigma 2) (Zl4 r)
            (Cl4 * Book.Ch02.vecNorm p)) →
        (∀ r ∈ Finset.Ioc S.ellPrime S.LPrime, ∀ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 4
            (fun x => shellFlux omega r p x -
              volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
                (shellFlux omega r p)) ≤ ENNReal.ofReal (Zl4 r omega)) →
      ∀ ZhmGe : ℕ → ShellSeq d → ℝ, (∀ r omega, 0 ≤ ZhmGe r omega) →
        (∀ r, Measurable (ZhmGe r)) →
        (∀ r ∈ Finset.Ioc S.m S.LPrime,
          IsBigO P.toMeasure (gammaSigma 2) (ZhmGe r)
            (ChmGe * Book.Ch02.vecNorm p *
              (3 : ℝ) ^ (-((r - S.m : ℕ) : ℝ)))) →
        (∀ r ∈ Finset.Ioc S.m S.LPrime, ∀ omega : ShellSeq d,
          vecHatNegENormOrderOne (originCube d (S.m : ℤ))
            (fun x => shellFlux omega r p x -
              volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
                (shellFlux omega r p)) ≤ ENNReal.ofReal (ZhmGe r omega)) →
        |(∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (wD omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure :
                ℝ≥0∞).toReal -
            cStar * Real.log 3 * ((S.m - S.n : ℕ) : ℝ) * vecNormSq p| ≤
          (Clhs * (1 + ((S.LPrime - S.m : ℕ) : ℝ)) + K) * vecNormSq p := by
  classical
  obtain ⟨C, hCtop, hC⟩ := hApriori
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  set Cnd : ℝ := C.toReal + 1 with hCnddef
  have hCnd : 0 < Cnd := by
    have h := ENNReal.toReal_nonneg (a := C)
    rw [hCnddef]
    linarith only [h]
  have hCav : 0 < Section2.Estimates.Stream.spatialAverageTailConst d :=
    Section2.Norms.spatialAverageTailConst_pos hd0
  have hChmV2 : 0 < Section2.Estimates.Stream.shellHminusConst d := by
    have htri : (0 : ℝ) < gammaTriangleConst 2 := gammaTriangleConst_pos
    have hCdm : 0 < Section2.Norms.cubeDepthMomentTailConst d 2 :=
      Section2.Norms.cubeDepthMomentTailConst_pos hd0 2
    have hCsv : 0 < Section2.Estimates.Stream.shellValueLargeCubeConst d :=
      Section2.Estimates.Stream.shellValueLargeCubeConst_pos_of_pos hd0
    have hCms : 0 < Section2.Estimates.Stream.multiscaleOrderOneConst d :=
      lt_of_lt_of_le zero_lt_one
        (Section2.Estimates.Stream.one_le_multiscaleOrderOneConst d)
    rw [Section2.Estimates.Stream.shellHminusConst]
    positivity
  set Chm : ℝ := Section2.Estimates.Stream.shellHminusConst d + ChmGe
    with hChmdef
  have hChm : 0 < Chm := by rw [hChmdef]; linarith only [hChmV2, hChmGe]
  have hChmGeLe : ChmGe ≤ Chm := by rw [hChmdef]; linarith only [hChmV2]
  have hChmV2Le : Section2.Estimates.Stream.shellHminusConst d ≤ Chm := by
    rw [hChmdef]; linarith only [hChmGe]
  refine ⟨lhsTerm1ShellConst Cnd Chm Cl4
      (Section2.Estimates.Stream.spatialAverageTailConst d)
      (Section2.Estimates.Stream.spatialAverageTailConst d),
    one_le_lhsTerm1ShellConst _ _ _ _ _, ?_⟩
  intro nu hnu P hPrefix hJ1 hJ2 hJ3 hJ4 hInv cStar K S hSorder e he hunit p hp
    F hF gradHatW wD wN hwD hwN hwDmeas hFmemLp hGmemLp hproj hlow hup hJ5app
    wDr wNr hwDr hwNr Zl4 hZl40 hZl4Meas hZl4BigO hZl4Bound ZhmGe hZhmGe0
    hZhmGeMeas hZhmGeBigO hZhmGeBound
  have : VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure := hInv
  have hlam := sigmaBarStarInvSqrt_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
  have hpt : 0 < Book.Ch02.vecNorm p := by
    have hp' : p = sigmaBarStarInvSqrt nu S.LPrime P S.n • e := by
      rw [hp, testVector]
    have hnorm : Book.Ch02.vecNorm p =
        |sigmaBarStarInvSqrt nu S.LPrime P S.n| * Book.Ch02.vecNorm e := by
      rw [hp']
      show ‖HilbertVec.ofVec (sigmaBarStarInvSqrt nu S.LPrime P S.n • e)‖ = _
      rw [ofVec_smul, norm_smul, Real.norm_eq_abs]
      rfl
    rw [hnorm, hunit, mul_one, abs_of_pos hlam]
    exact hlam
  have hCle : C ≤ ENNReal.ofReal Cnd := by
    calc C = ENNReal.ofReal C.toReal := (ENNReal.ofReal_toReal hCtop.ne).symm
      _ ≤ ENNReal.ofReal Cnd :=
        ENNReal.ofReal_le_ofReal (by rw [hCnddef]; exact (lt_add_one _).le)
  have hNDweak : ∀ (G : Vec d → Vec d)
      (v : H10Function (openCubeSet (originCube d (S.m : ℤ))))
      (vN : H1MeanZeroFunction (openCubeSet (originCube d (S.m : ℤ)))),
      IsCubeDirichletResponse (originCube d (S.m : ℤ)) G v →
      IsCubeNeumannResponse (originCube d (S.m : ℤ)) G vN →
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (fun x => vN.toH1Function.grad x - v.toH1Function.grad x) ≤
        ENNReal.ofReal Cnd *
            (vecHatNegENormOrderOne (originCube d (S.m : ℤ))
              (fun x => G x -
                volumeAverageVec (cubeSet (originCube d (S.m : ℤ))) G))
              ^ ((1 : ℝ) / 5) *
            (vecCubeLpENorm (originCube d (S.m : ℤ)) 4
              (fun x => G x -
                volumeAverageVec (cubeSet (originCube d (S.m : ℤ))) G))
              ^ ((4 : ℝ) / 5) +
          ENNReal.ofReal Cnd * ‖HilbertVec.ofVec
            (volumeAverageVec (cubeSet (originCube d (S.m : ℤ))) G)‖ₑ := by
    intro G v vN hDv hNv
    refine le_trans ((hC S.m G v vN hDv hNv).2.2.2) ?_
    exact add_le_add (mul_le_mul' (mul_le_mul' hCle le_rfl) le_rfl)
      (mul_le_mul' hCle le_rfl)
  obtain ⟨Zav, hZav0, hZavMeas, hZavBigO, hZavBound⟩ :=
    Section2.Estimates.Stream.exists_shellFluxAverage_bound hPrefix hJ1 hJ3 hJ4
      S.m p
  obtain ⟨Z, hZ0, hZm, hZbigAll, hZbound⟩ :=
    Section2.Estimates.Stream.exists_shellFluxAverage_bound_ge hPrefix hJ1 hJ3
      hJ4 S.m p
  set Zhm : ℕ → ShellSeq d → ℝ := fun r =>
    if S.m < r then ZhmGe r
    else Section2.Estimates.Stream.shellHminusBound r S.m p with hZhmdef
  have hZhm0 : ∀ r omega, 0 ≤ Zhm r omega := by
    intro r omega
    by_cases hgt : S.m < r
    · simp only [hZhmdef, ite_eq_left hgt]
      exact hZhmGe0 r omega
    · simp only [hZhmdef, ite_eq_right hgt]
      exact Section2.Estimates.Stream.shellHminusBound_nonneg r S.m p omega
  have hZhmMeas : ∀ r, Measurable (Zhm r) := by
    intro r
    by_cases hgt : S.m < r
    · simp only [hZhmdef, ite_eq_left hgt]
      exact hZhmGeMeas r
    · simp only [hZhmdef, ite_eq_right hgt]
      exact Section2.Estimates.Stream.measurable_shellHminusBound r S.m p
  have hZhmBound : ∀ r ∈ Finset.Ioc S.ellPrime S.LPrime, ∀ omega : ShellSeq d,
      vecHatNegENormOrderOne (originCube d (S.m : ℤ))
        (fun x => shellFlux omega r p x -
          volumeAverageVec (cubeSet (originCube d (S.m : ℤ)))
            (shellFlux omega r p)) ≤ ENNReal.ofReal (Zhm r omega) := by
    intro r hr omega
    by_cases hgt : S.m < r
    · simp only [hZhmdef, ite_eq_left hgt]
      exact hZhmGeBound r (Finset.mem_Ioc.2 ⟨hgt, (Finset.mem_Ioc.1 hr).2⟩) omega
    · simp only [hZhmdef, ite_eq_right hgt]
      exact Section2.Estimates.Stream.vecHatNegENormOrderOne_centeredShellFlux_le hd0
        omega (not_lt.1 hgt) p
  have hZhmBigO : ∀ r ∈ Finset.Ioc S.ellPrime S.LPrime,
      IsBigO P.toMeasure (gammaSigma 2) (Zhm r)
        (if S.m ≤ r then
            Chm * Book.Ch02.vecNorm p * (3 : ℝ) ^ (-((r - S.m : ℕ) : ℝ))
          else Chm * Book.Ch02.vecNorm p *
            ((1 + ((S.m - r : ℕ) : ℝ)) *
              (3 : ℝ) ^ (-((S.m - r : ℕ) : ℝ)))) := by
    intro r hr
    by_cases hgt : S.m < r
    · have hbig := hZhmGeBigO r
        (Finset.mem_Ioc.2 ⟨hgt, (Finset.mem_Ioc.1 hr).2⟩)
      simp only [hZhmdef, ite_eq_left hgt, ite_eq_left (le_of_lt hgt)]
      refine hbig.mono_scale ?_
      have h3 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((r - S.m : ℕ) : ℝ)) :=
        Real.rpow_nonneg (by norm_num) _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hChmGeLe (Book.Ch02.vecNorm_nonneg p)) h3
    · have hle : r ≤ S.m := not_lt.1 hgt
      have hbase := Section2.Estimates.Stream.isBigO_gammaSigma_shellHminusBound
        hPrefix hJ1 hJ3 hJ4 hd hle hpt
      simp only [hZhmdef, ite_eq_right hgt]
      by_cases hge : S.m ≤ r
      · have h1 : (S.m - r : ℕ) = 0 := by omega
        have h2 : (r - S.m : ℕ) = 0 := by omega
        rw [h1] at hbase
        rw [ite_eq_left hge, h2]
        refine hbase.mono_scale ?_
        simp only [Nat.cast_zero, neg_zero, Real.rpow_zero, add_zero, mul_one]
        have hB : (0 : ℝ) ≤ ChmGe * Book.Ch02.vecNorm p :=
          mul_nonneg hChmGe.le (Book.Ch02.vecNorm_nonneg p)
        rw [hChmdef]
        linarith only [hB]
      · rw [ite_eq_right hge]
        refine hbase.mono_scale ?_
        have hw : (0 : ℝ) ≤ (1 + ((S.m - r : ℕ) : ℝ)) *
            (3 : ℝ) ^ (-((S.m - r : ℕ) : ℝ)) := by positivity
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hChmV2Le (Book.Ch02.vecNorm_nonneg p)) hw
  exact l_LHS_term1_constFirst_of_shellData d hd Cnd Chm Cl4
    (Section2.Estimates.Stream.spatialAverageTailConst d)
    (Section2.Estimates.Stream.spatialAverageTailConst d) hCnd hChm hCl4 hCav
    hCav nu hnu P hPrefix hJ2 hJ3 hJ4 cStar K S hSorder e he hunit p hp F hF
    gradHatW wD wN hwD hwN hwDmeas hFmemLp hGmemLp hproj hlow hup Z hZm
    (fun r hr => hZbigAll r (Finset.mem_Icc.1 hr).1) hZbound hJ5app wDr wNr
    hwDr hwNr hNDweak Zhm hZhm0 hZhmMeas hZhmBigO hZhmBound Zl4 hZl40 hZl4Meas
    hZl4BigO hZl4Bound Zav (fun r omega => hZav0 r omega) hZavMeas
    (fun r _ => hZavBigO r) (fun r _ omega => hZavBound r omega)
end

end SuperdiffusionCLT.Section3.Setup
