/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.MasterAssembly
public import SuperdiffusionCLT.Section3.Terms.MasterIdentity

/-!
# The master identity inside the final assembly of Section 3

The assembly of the master inequality carries `e.ellsep.testing` as the
last conjunct of its term-level residue, in the carrier
`master_inequality_of_selection` reads it in.
`Terms.ellsep_testing_decomposition` and `Terms.ellsep_testing_annealed` prove
that identity from the four testing displays of the paper, but in the
carrier of the paper.  Three rewritings, all unstated in the paper, separate
the two: the left side, read by the term lemmas as the real part of
`∫⁻ ‖∇w‖²_{L̲²(cu_m)} dP`; the second term, read by `l.RHS.term2` as the lattice
average of the scale-`n` sub-cube averages, with `a_{L'} − a_ℓ` in place of the
stream increment; and the fourth term, whose constant vector `p` the print keeps
outside the cube average and `l.RHS.term4` keeps inside it.  This module supplies the
cube-average identities by which these rewritings are carried out.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open MeasureTheory ProbabilityTheory
open Homogenization
open Homogenization.Book.Ch02
open Homogenization.IndependentSums
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Probability
open SuperdiffusionCLT.Probability.Stationary
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Norms
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Terms
open scoped BigOperators ENNReal

noncomputable section

/-- **A constant vector moves through the normalized cube average**, the
rewriting the print performs on the fourth term of `e.ellsep.testing`.  It is
the public counterpart, in the orientation the master identity uses, of the
private `Terms.volumeAverageVecDotConstRight`. -/
theorem volumeAverage_vecDot_const_left {d : ℕ} {U : Set (Vec d)} (c : Vec d)
    {F : Vec d → Vec d}
    (hF : ∀ i : Fin d, IntegrableOn (fun x => F x i) U volume) :
    volumeAverage U (fun x => vecDot c (F x)) = vecDot c (volumeAverageVec U F) := by
  have hrw : (fun x => vecDot c (F x))
      = fun x => ∑ i : Fin d, (fun (a : Fin d) (y : Vec d) => c a * F y a) i x := rfl
  have htarget : vecDot c (volumeAverageVec U F)
      = ∑ i : Fin d, c i * volumeAverage U (fun y => F y i) := rfl
  rw [hrw, Homogenization.volumeAverage_sum Finset.univ
      (fun (a : Fin d) (y : Vec d) => c a * F y a)
      (fun a _ => (hF a).const_mul (c a)), htarget]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsm : (fun y : Vec d => c i * F y i) = (c i) • fun y : Vec d => F y i := rfl
  show volumeAverage U (fun y : Vec d => c i * F y i)
      = c i * volumeAverage U (fun y => F y i)
  rw [hsm, Homogenization.volumeAverage_smul]

/-- **The energy rewriting**: the expectation of the print's `⨍_{cu_m}|∇w|²`
is the real part of the lower integral of `‖∇w‖²_{L̲²(cu_m)}` in which the five
term lemmas of Section 3 read the left side of `e.ellsep.testing`. -/
theorem toReal_lintegral_vecCubeLpENorm_two_sq_eq_integral_volumeAverage {d : ℕ}
    {P : ProbabilityMeasure (ShellSeq d)} (Q : TriadicCube d)
    (G : ShellSeq d → Vec d → Vec d)
    (hL2 : ∀ omega : ShellSeq d, MemVectorL2 (openCubeSet Q) (G omega))
    (hInt : Integrable (fun omega : ShellSeq d =>
      volumeAverage (openCubeSet Q) (fun x => vecNormSq (G omega x))) P.toMeasure) :
    (∫⁻ omega : ShellSeq d,
        vecCubeLpENorm Q 2 (G omega) ^ (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal =
      ∫ omega : ShellSeq d,
        volumeAverage (openCubeSet Q) (fun x => vecNormSq (G omega x)) ∂P.toMeasure := by
  have hnn : ∀ omega : ShellSeq d,
      0 ≤ volumeAverage (openCubeSet Q) (fun x => vecNormSq (G omega x)) := fun omega =>
    mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
      (integral_nonneg fun x => vecNormSq_nonneg (G omega x))
  have hpt : ∀ omega : ShellSeq d, vecCubeLpENorm Q 2 (G omega) ^ (2 : ℕ) =
      ENNReal.ofReal (volumeAverage (openCubeSet Q) (fun x => vecNormSq (G omega x))) := by
    intro omega
    rw [vecCubeLpENorm_two_sq_eq_ofReal (hL2 omega),
      integral_normalizedCubeMeasure_eq_volumeAverage]
  rw [lintegral_congr hpt, ← ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall hnn),
    ENNReal.toReal_ofReal (integral_nonneg hnn)]

/-- **The lattice rewriting**: the print's `⨍_{cu_m} ∇w·(k_j−k_k)(∇u_n−p)` is
the plain average of the normalized averages over the scale-`n` sub-cubes of
`cu_m`, with the stream increment `k_j − k_k` written as the coefficient
increment `a_j − a_k`; both steps are silent in the source. -/
theorem volumeAverage_vecDot_streamCutoff_sub_eq_subcube_avsum {d : ℕ} (nu : ℝ)
    (omega : ShellSeq d) (n m j k : ℕ) (p : Vec d) (V G : Vec d → Vec d)
    (hInt : ∀ R ∈ largeCubeSubcubes d n m,
      IntegrableOn (fun y => vecDot (G y)
        (matVecMul ((coefficientCutoff nu omega j).toCoeffField y -
          (coefficientCutoff nu omega k).toCoeffField y) (V y - p))) (cubeSet R) volume) :
    volumeAverage (openCubeSet (originCube d (m : ℤ)))
        (fun y => vecDot (G y)
          (matVecMul (streamCutoff omega j y - streamCutoff omega k y) (V y - p))) =
      ((largeCubeSubcubes d n m).card : ℝ)⁻¹ *
        ∑ z ∈ largeCubeSubcubes d n m,
          volumeAverage (openCubeSet z)
            (fun y => vecDot (G y)
              (matVecMul ((coefficientCutoff nu omega j).toCoeffField y -
                (coefficientCutoff nu omega k).toCoeffField y) (V y - p))) := by
  have hpt : (fun y => vecDot (G y)
        (matVecMul (streamCutoff omega j y - streamCutoff omega k y) (V y - p)))
      = fun y => vecDot (G y)
        (matVecMul ((coefficientCutoff nu omega j).toCoeffField y -
          (coefficientCutoff nu omega k).toCoeffField y) (V y - p)) := by
    funext y
    rw [coefficientCutoff_toCoeffField_sub_eq_streamCutoff_sub]
  rw [hpt]
  exact volumeAverage_originCube_eq_subcube_avsum hInt

end

end SuperdiffusionCLT.Section3.Setup
