/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.MasterIdentity
public import SuperdiffusionCLT.Section3.ResponseFields.Norms
public import SuperdiffusionCLT.Frozen.Section3.BEllHomogenization
public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolume

/-!
# The master inequality of the root, and the passage to `e.sstar.lower.bound`

The proof of Proposition `p.sstar.lower.bound` combines Lemma `l.LHS.term1` with the master
identity `e.ellsep.testing` and the four upper bounds `e.RHS.term1`-`e.RHS.term4`, and
reaches the display

`c⋆ h σ̄_{L',*}^{-1}(cu_n) ≤ C(δ + L^{-1000})^{1/2}(σ̄_ℓ(cu_n) + h σ̄_{L',*}^{-1}(cu_n))
                             + C(1 + K_nd + K log(ν⁻¹L)) σ̄_{L',*}^{-1}(cu_n)`,

which is `master_inequality` below.  The subsequent absorptions, the
homogenization comparison `e.bell.vs.starell` and the localization comparisons
then give `e.crude.enhance.h.bnd` and, after the choice of
`h`, the conclusion `e.sstar.lower.bound` at the pigeonhole scale, which is
`sstar_lower_bound_of_terms` below.

## The order of the quantifiers

The constants of the paper are `C(d)`: they are fixed **before** the scales, the
law and the direction, and the threshold in `e.L.vs.nu` is increased afterwards.
The Section 3 term lemmas as proved put their constant *inside* every binder
(`∃ C : ℝ, 1 ≤ C ∧ …`), which is a strictly weaker statement — with a finite
left side and a positive right coefficient such an existential is provable for
trivial reasons — so composing them in that shape would not reproduce the
printed argument.  The two theorems below are therefore stated in the
**constant-first** form: the five term constants `CL, C1, C2, C3, C4` (and the
constant `c₀` of the crude lower bound `e.CG.bounds.1`) are binders that precede
the molecular diffusivity, the law, the scale selection and the direction, each
term bound is a hypothesis at its own constant, and the constant of the
conclusion is the explicit `masterConst`/`sstarLowerBoundConst` below.  A caller
holding the `∃ C` conclusions instantiates these theorems at the five
witnesses.

## The carrier bridges folded into `hIdentity`

`hIdentity` is the conclusion of `ellsep_testing_annealed`
(`Section3/Terms/MasterIdentity.lean`) after three rewritings, each of which the
paper performs silently:

* the left side, `E[⨍_{cu_m}|∇w|²]`, is written as
  `(∫⁻ ω ‖∇w(ω)‖²_{L̲²(cu_m)})^{}.toReal`, the carrier of `l.LHS.term1`;
* the second term's `⨍_{cu_m}` is written as the lattice average
  `avsum_{z ∈ 3^nℤ^d ∩ cu_m} ⨍_{z+cu_n}` of `l.RHS.term2` — this is
  `volumeAverage_originCube_eq_subcube_avsum` — and its matrix `k_{L'} − k_ℓ`
  as `a_{L'} − a_ℓ` — this is
  `coefficientCutoff_toCoeffField_sub_eq_streamCutoff_sub`;
* the fourth term's constant `p` is moved inside the cube average, the carrier
  of `l.RHS.term4`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open Homogenization
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Arithmetic preliminaries -/

/-- `1 ≤ log 3`, the factor `log 3` of `l.LHS.term1` which the paper drops when
it writes the left side of the master inequality as `c⋆ h σ̄_{L',*}^{-1}`. -/
theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  have hexp : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hlt : Real.log (Real.exp 1) < Real.log 3 :=
    Real.log_lt_log (Real.exp_pos 1) hexp
  rw [Real.log_exp] at hlt
  exact hlt.le

/-- `√(a²b² + c²) ≤ ab + c` for nonnegative `a, b, c`: the elementary step by
which the paper turns the square root of `e.RHS.term3` into the sum
`(L' − ℓ)σ̄_{L',*}^{-1}(cu_n) + σ̄_ℓ(cu_n)`. -/
theorem sqrt_sq_mul_sq_add_sq_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (a ^ (2 : ℕ) * b ^ (2 : ℕ) + c ^ (2 : ℕ)) ≤ a * b + c := by
  have habc : (0 : ℝ) ≤ a * b + c := add_nonneg (mul_nonneg ha hb) hc
  have hsq : a ^ (2 : ℕ) * b ^ (2 : ℕ) + c ^ (2 : ℕ) ≤ (a * b + c) ^ (2 : ℕ) := by
    have h2 : (0 : ℝ) ≤ 2 * (a * b) * c :=
      mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg ha hb)) hc
    have hexp : (a * b + c) ^ (2 : ℕ) = a ^ (2 : ℕ) * b ^ (2 : ℕ) + 2 * (a * b) * c +
        c ^ (2 : ℕ) := by ring
    rw [hexp]
    linarith only [h2]
  calc Real.sqrt (a ^ (2 : ℕ) * b ^ (2 : ℕ) + c ^ (2 : ℕ))
      ≤ Real.sqrt ((a * b + c) ^ (2 : ℕ)) := Real.sqrt_le_sqrt hsq
    _ = a * b + c := Real.sqrt_sq habc

/-- The constant of the master inequality, explicit in the constant `CL` of
`l.LHS.term1`, the constant `C3` of `l.RHS.term3`, the constant `C4` of
`l.RHS.term4` and the constant `c₀` of the crude lower bound
`σ̄_{L',*}^{-1}(cu_n) ≥ c₀ν²L⁻¹`.  The constants `C1` of
`l.RHS.term1` and `C2` of `l.RHS.term2` do not appear: their contributions enter
only through the scale condition `hScaleCond` of `master_inequality`, where the paper
absorbs them into the threshold of `e.L.vs.nu`. -/
def masterConst (CL C3 C4 c0 : ℝ) : ℝ := 4 * CL + 2 * C3 + C4 + c0⁻¹ + 1

theorem one_le_masterConst {CL C3 C4 c0 : ℝ} (hCL : 1 ≤ CL) (hC3 : 0 ≤ C3)
    (hC4 : 0 ≤ C4) (hc0 : 0 < c0) : 1 ≤ masterConst CL C3 C4 c0 := by
  have hinv : (0 : ℝ) < c0⁻¹ := inv_pos.2 hc0
  rw [masterConst]
  linarith only [hCL, hC3, hC4, hinv]

/-! ## The master inequality -/

/-- **The master inequality**: "Combining Lemma `l.LHS.term1` and `e.ellsep.testing` with
`e.RHS.term1`, `e.RHS.term2`, `e.RHS.term3` and `e.RHS.term4`, taking note of
`e.Sec3.p.q.def` and `e.homs.defs.U`, we see that

`c⋆ h σ̄_{L',*}^{-1}(cu_n) ≤ C(δ + L^{-1000})^{1/2}(σ̄_ℓ(cu_n) + h σ̄_{L',*}^{-1}(cu_n))
                             + C(1 + K_nd + K log(ν⁻¹L)) σ̄_{L',*}^{-1}(cu_n)`."

Constant-first: the five term constants precede the scale selection, the law and
the direction, and the constant of the conclusion is `masterConst CL C3 C4 c₀`.

* `hLHS` is `l.LHS.term1` (`e.nabla.w.lower.bound`) at the
  constant `CL`, in the carrier of the whole-space energy identity
  (`Section3/Setup/WholeSpaceEnergyOrderOne.lean`), with
  the additive term the J5 constant `Knd` (the paper's `\nondegconst`);
* `hT1` is `e.RHS.term1` at `C1`;
* `hT2` is `e.RHS.term2` at `C2`, in its printed lattice-average
  carrier;
* `hT3` is `e.RHS.term3` at `C3`;
* `hT4` is `e.RHS.term4` at `C4`;
* `hIdentity` is `e.ellsep.testing` under the expectation, in the four carriers
  of those lemmas (see the module docstring).

The remaining hypotheses are the scale conditions of the paper:

* `hScaleCond` is the scale condition of the proof.  The paper states it with the
  common envelope `C(ν⁻¹L)^9`, which dominates each of the three polynomial
  error groups that occur; carrying the three groups themselves is weaker, and
  avoids the envelope comparison.
* `hEta` is `η_L ≤ L^{-1000}`;
* `hCrude` is the crude lower bound `σ̄_{L',*}^{-1}(cu_n) ≥ c₀ν²L^{-1}`;
* `hha` is `h ≥ 100(ℓ − n) = 100a`, which is
  `Setup.hundred_mul_scaleOffset_le`, and is what absorbs `(L' − ℓ)σ̄^{-1}` into
  `hσ̄^{-1}`;
* `haK` is `a = ⌈K log(ν⁻¹L)⌉` read as `a ≤ K log(ν⁻¹L) + 1`, which is
  `Setup.scaleOffset_lt_add_one`;
* `hL1`, `hKlog`, `hKnd`, `hcStar`, `hdelta`, `hetaL` are the standing
  positivity data. -/
theorem master_inequality [NeZero d]
    (CL C1 C2 C3 C4 c0 : ℝ) (hCL : 1 ≤ CL) (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    (hc0 : 0 < c0)
    (nu : ℝ) (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P)
    (cStar Knd K delta etaL : ℝ) (hcStar : 0 ≤ cStar) (hKnd : 0 ≤ Knd)
    (hdelta : 0 ≤ delta) (hetaL : 0 ≤ etaL)
    (S : ScaleSelection) (hL1 : (1 : ℝ) ≤ (S.L : ℝ))
    (hKlog : 0 ≤ K * Real.log (nu⁻¹ * (S.L : ℝ)))
    (e : Vec d) (he : vecNormSq e = 1)
    (p : Vec d) (hp : p = testVector nu S.LPrime P S.n e) (q : Vec d)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (uMgrad uNGlued : ShellSeq d → Vec d → Vec d)
    (hha : 100 * S.a ≤ S.h)
    (haK : ((S.a : ℕ) : ℝ) ≤ K * Real.log (nu⁻¹ * (S.L : ℝ)) + 1)
    (hEta : etaL ≤ (S.L : ℝ) ^ (-(1000 : ℝ)))
    (hCrude : c0 * nu ^ (2 : ℕ) * (S.L : ℝ)⁻¹ ≤ sigmaBarStarInvSeq nu S.LPrime P S.n)
    (hScaleCond :
      C1 * nu ^ (-(3 : ℝ)) * ((S.ell : ℝ) ^ (2 : ℕ) * (S.h : ℝ)) *
            ((3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) +
              (3 : ℝ) ^ (-((S.ellPrime - S.ell : ℕ) : ℝ))) +
          C2 * nu ^ (-(3 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) *
            (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) +
          C3 * nu ^ (-(4 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) *
            ((3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) +
              (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 8)) +
              (3 : ℝ) ^ (-((((S.ellPrime - S.ell : ℕ) : ℝ)) / 4)) +
              (3 : ℝ) ^ (-((((S.h : ℕ) : ℝ)) / 8))) ≤
        nu ^ (2 : ℕ) * (S.L : ℝ) ^ (-(1000 : ℝ)))
    (hLHS :
      |(∫⁻ omega : ShellSeq d,
            vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (w omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal -
          cStar * Real.log 3 * ((S.m - S.n : ℕ) : ℝ) * vecNormSq p| ≤
        (CL * (1 + ((S.LPrime - S.m : ℕ) : ℝ)) + Knd) * vecNormSq p)
    (hT1 :
      |∫ omega : ShellSeq d,
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun x => vecDot ((w omega).toH1Function.grad x)
              (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                  (uNGlued omega x) - q)) ∂P.toMeasure| ≤
        C1 * nu ^ (-(3 : ℝ)) * ((S.ell : ℝ) ^ (2 : ℕ) * (S.h : ℝ)) *
          ((3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)) +
            (3 : ℝ) ^ (-((S.ellPrime - S.ell : ℕ) : ℝ))))
    (hT2 :
      |∫ omega : ShellSeq d,
          ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
            ∑ z ∈ largeCubeSubcubes d S.n S.m,
              volumeAverage (openCubeSet z)
                (fun y => vecDot ((w omega).toH1Function.grad y)
                  (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                    (coefficientCutoff nu omega S.ell).toCoeffField y)
                    (uNGlued omega y - p))) ∂P.toMeasure| ≤
        C2 * nu ^ (-(3 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (2 : ℕ)) *
          (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 2)))
    (hT3 :
      ∫ omega : ShellSeq d,
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot ((w omega).toH1Function.grad y)
              (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                (uMgrad omega y - uNGlued omega y))) ∂P.toMeasure ≤
        C3 * (delta + etaL) ^ ((1 : ℝ) / 2) *
            Real.sqrt (((S.LPrime - S.ell : ℕ) : ℝ) ^ (2 : ℕ) *
                (sigmaBarStarInvSeq nu S.LPrime P S.n) ^ (2 : ℕ) +
              (sigmaBarSeq nu S.ell P S.n) ^ (2 : ℕ)) +
          C3 * nu ^ (-(4 : ℝ)) * (((S.LPrime : ℕ) : ℝ) ^ (4 : ℕ)) *
            ((3 : ℝ) ^ (-((((S.ellPrime - S.n : ℕ) : ℝ)) / 2)) +
              (3 : ℝ) ^ (-((((S.ell - S.n : ℕ) : ℝ)) / 8)) +
              (3 : ℝ) ^ (-((((S.ellPrime - S.ell : ℕ) : ℝ)) / 4)) +
              (3 : ℝ) ^ (-((((S.h : ℕ) : ℝ)) / 8))))
    (hT4 :
      |∫ omega : ShellSeq d,
          volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
            (fun y => vecDot p (matVecMul (streamCutoff omega S.ellPrime y -
                streamCutoff omega S.ell y) ((w omega).toH1Function.grad y)))
        ∂P.toMeasure| ≤ C4 * (sigmaBarStarInvSqrt nu S.LPrime P S.n) ^ (2 : ℕ))
    (hIdentity :
      (∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (w omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal =
        ((∫ omega : ShellSeq d,
              volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
                (fun x => vecDot ((w omega).toH1Function.grad x)
                  (matVecMul ((coefficientCutoff nu omega S.ell).toCoeffField x)
                      (uNGlued omega x) - q)) ∂P.toMeasure +
            ∫ omega : ShellSeq d,
              ((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹ *
                ∑ z ∈ largeCubeSubcubes d S.n S.m,
                  volumeAverage (openCubeSet z)
                    (fun y => vecDot ((w omega).toH1Function.grad y)
                      (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y -
                        (coefficientCutoff nu omega S.ell).toCoeffField y)
                        (uNGlued omega y - p))) ∂P.toMeasure) +
            ∫ omega : ShellSeq d,
              volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
                (fun y => vecDot ((w omega).toH1Function.grad y)
                  (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField y)
                    (uMgrad omega y - uNGlued omega y))) ∂P.toMeasure) -
          ∫ omega : ShellSeq d,
            volumeAverage (openCubeSet (originCube d (S.m : ℤ)))
              (fun y => vecDot p (matVecMul (streamCutoff omega S.ellPrime y -
                  streamCutoff omega S.ell y) ((w omega).toH1Function.grad y)))
            ∂P.toMeasure) :
    cStar * (S.h : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n ≤
      masterConst CL C3 C4 c0 * (delta + (S.L : ℝ) ^ (-(1000 : ℝ))) ^ ((1 : ℝ) / 2) *
          (sigmaBarSeq nu S.ell P S.n +
            (S.h : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n) +
        masterConst CL C3 C4 c0 * (1 + Knd + K * Real.log (nu⁻¹ * (S.L : ℝ))) *
          sigmaBarStarInvSeq nu S.LPrime P S.n := by
  classical
  -- `|p|² = σ̄_{L',*}^{-1}(cu_n)` and `(σ̄_{L',*}^{-1/2})² = σ̄_{L',*}^{-1}`, both
  -- proved earlier (`e.Sec3.p.q.def`)
  have hpsq : vecNormSq p = sigmaBarStarInvSeq nu S.LPrime P S.n := by
    rw [hp]
    exact vecNormSq_testVector hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n he
  have hsqrtsq : (sigmaBarStarInvSqrt nu S.LPrime P S.n) ^ (2 : ℕ) =
      sigmaBarStarInvSeq nu S.LPrime P S.n :=
    sq_sigmaBarStarInvSqrt hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
  rw [hpsq] at hLHS
  rw [hsqrtsq] at hT4
  obtain ⟨hLHSl, -⟩ := abs_le.1 hLHS
  obtain ⟨-, hT1r⟩ := abs_le.1 hT1
  obtain ⟨-, hT2r⟩ := abs_le.1 hT2
  obtain ⟨hT4l, -⟩ := abs_le.1 hT4
  -- the two annealed scalars and the four abbreviations of the display
  set sg : ℝ := sigmaBarStarInvSeq nu S.LPrime P S.n with hsgdef
  set bt : ℝ := sigmaBarSeq nu S.ell P S.n with hbtdef
  set KLv : ℝ := 1 + Knd + K * Real.log (nu⁻¹ * (S.L : ℝ)) with hKLdef
  set DE : ℝ := (delta + (S.L : ℝ) ^ (-(1000 : ℝ))) ^ ((1 : ℝ) / 2) with hDEdef
  set MC : ℝ := masterConst CL C3 C4 c0 with hMCdef
  have hsgpos : 0 < sg := sigmaBarStarInvSeq_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
  have hbtpos : 0 < bt := sigmaBarSeq_pos hnu S.ell hPrefix hJ2 hJ3 hJ4 S.n
  have hCLnn : (0 : ℝ) ≤ CL := le_trans zero_le_one hCL
  have hc0inv : (0 : ℝ) < c0⁻¹ := inv_pos.2 hc0
  have hLnn : (0 : ℝ) ≤ (S.L : ℝ) := le_trans zero_le_one hL1
  -- the printed scale identities
  have haR : (0 : ℝ) ≤ (S.a : ℝ) := Nat.cast_nonneg _
  have hhR : (0 : ℝ) ≤ (S.h : ℝ) := Nat.cast_nonneg _
  have hmn : ((S.m - S.n : ℕ) : ℝ) = (S.h : ℝ) + 2 * (S.a : ℝ) := by
    rw [S.m_sub_n]; push_cast; ring
  have hLm : ((S.LPrime - S.m : ℕ) : ℝ) = 2 * (S.a : ℝ) := by
    rw [S.LPrime_sub_m]; push_cast; ring
  have hLl : ((S.LPrime - S.ell : ℕ) : ℝ) = (S.h : ℝ) + 3 * (S.a : ℝ) := by
    rw [S.LPrime_sub_ell]; push_cast; ring
  have hhaR : 100 * (S.a : ℝ) ≤ (S.h : ℝ) := by
    have h : ((100 * S.a : ℕ) : ℝ) ≤ ((S.h : ℕ) : ℝ) := Nat.cast_le.2 hha
    push_cast at h
    linarith only [h]
  have hLl2 : ((S.LPrime - S.ell : ℕ) : ℝ) ≤ 2 * (S.h : ℝ) := by
    rw [hLl]; linarith only [hhaR, haR]
  -- the crude lower bound absorbs the polynomial errors
  have hLpow : (S.L : ℝ) ^ (-(1000 : ℝ)) ≤ (S.L : ℝ)⁻¹ := by
    have h := Real.rpow_le_rpow_of_exponent_le hL1
      (by norm_num : (-(1000 : ℝ)) ≤ (-1 : ℝ))
    rwa [Real.rpow_neg_one] at h
  have hLpownn : (0 : ℝ) ≤ (S.L : ℝ) ^ (-(1000 : ℝ)) := Real.rpow_nonneg hLnn _
  have hnu2 : (0 : ℝ) ≤ nu ^ (2 : ℕ) := by positivity
  have hdiv : nu ^ (2 : ℕ) * (S.L : ℝ)⁻¹ ≤ c0⁻¹ * sg := by
    have h := mul_le_mul_of_nonneg_left hCrude hc0inv.le
    have hrw : c0⁻¹ * (c0 * nu ^ (2 : ℕ) * (S.L : ℝ)⁻¹) = nu ^ (2 : ℕ) * (S.L : ℝ)⁻¹ := by
      field_simp
    rwa [hrw] at h
  have herr : nu ^ (2 : ℕ) * (S.L : ℝ) ^ (-(1000 : ℝ)) ≤ c0⁻¹ * sg := by
    have h := mul_le_mul_of_nonneg_left hLpow hnu2
    linarith only [h, hdiv]
  -- the left side of the master inequality: `log 3 ≥ 1`, `m − n ≥ h`
  have hmnge : (S.h : ℝ) ≤ Real.log 3 * ((S.m - S.n : ℕ) : ℝ) := by
    rw [hmn]
    have hnn : (0 : ℝ) ≤ (S.h : ℝ) + 2 * (S.a : ℝ) := by linarith only [hhR, haR]
    have h := mul_le_mul_of_nonneg_right one_le_log_three hnn
    rw [one_mul] at h
    linarith only [h, haR]
  have hlow : cStar * (S.h : ℝ) * sg ≤ cStar * Real.log 3 * ((S.m - S.n : ℕ) : ℝ) * sg := by
    have hcs : (0 : ℝ) ≤ cStar * sg := mul_nonneg hcStar hsgpos.le
    have h := mul_le_mul_of_nonneg_left hmnge hcs
    linarith only [h]
  -- the square root of `e.RHS.term3`, with `L' − ℓ = h + 3a ≤ 2h`
  have hsqrtle : Real.sqrt (((S.LPrime - S.ell : ℕ) : ℝ) ^ (2 : ℕ) * sg ^ (2 : ℕ) +
      bt ^ (2 : ℕ)) ≤ 2 * ((S.h : ℝ) * sg + bt) := by
    have h1 := sqrt_sq_mul_sq_add_sq_le (a := ((S.LPrime - S.ell : ℕ) : ℝ)) (b := sg)
      (c := bt) (Nat.cast_nonneg _) hsgpos.le hbtpos.le
    have h2 : ((S.LPrime - S.ell : ℕ) : ℝ) * sg ≤ 2 * (S.h : ℝ) * sg :=
      mul_le_mul_of_nonneg_right hLl2 hsgpos.le
    linarith only [h1, h2, hbtpos.le]
  -- the amplitude `(δ + η_L)^{1/2} ≤ (δ + L^{-1000})^{1/2}`
  have hdenn : (0 : ℝ) ≤ delta + etaL := by linarith only [hdelta, hetaL]
  have hDEetann : (0 : ℝ) ≤ (delta + etaL) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hdenn _
  have hDEnn : (0 : ℝ) ≤ DE := by
    rw [hDEdef]
    exact Real.rpow_nonneg (by linarith only [hdelta, hLpownn]) _
  have hDEmono : (delta + etaL) ^ ((1 : ℝ) / 2) ≤ DE := by
    rw [hDEdef]
    exact Real.rpow_le_rpow hdenn (by linarith only [hEta]) (by norm_num)
  have hM3 : C3 * (delta + etaL) ^ ((1 : ℝ) / 2) *
      Real.sqrt (((S.LPrime - S.ell : ℕ) : ℝ) ^ (2 : ℕ) * sg ^ (2 : ℕ) + bt ^ (2 : ℕ)) ≤
      2 * C3 * DE * ((S.h : ℝ) * sg + bt) := by
    have hc3e : (0 : ℝ) ≤ C3 * (delta + etaL) ^ ((1 : ℝ) / 2) := mul_nonneg hC3 hDEetann
    have hA := mul_le_mul_of_nonneg_left hsqrtle hc3e
    have hnnr : (0 : ℝ) ≤ 2 * ((S.h : ℝ) * sg + bt) := by
      have : (0 : ℝ) ≤ (S.h : ℝ) * sg := mul_nonneg hhR hsgpos.le
      linarith only [this, hbtpos.le]
    have hB : C3 * (delta + etaL) ^ ((1 : ℝ) / 2) ≤ C3 * DE :=
      mul_le_mul_of_nonneg_left hDEmono hC3
    have hC := mul_le_mul_of_nonneg_right hB hnnr
    linarith only [hA, hC]
  -- the lower-order constants, with `L' − m = 2a` and `a ≤ K log(ν⁻¹L) + 1`
  have hKLge1 : (1 : ℝ) ≤ KLv := by rw [hKLdef]; linarith only [hKnd, hKlog]
  have hscalar : CL * (1 + ((S.LPrime - S.m : ℕ) : ℝ)) + Knd + C4 + c0⁻¹ ≤
      (4 * CL + C4 + c0⁻¹ + 1) * KLv := by
    have h1 : 1 + ((S.LPrime - S.m : ℕ) : ℝ) ≤ 4 * KLv := by
      rw [hLm, hKLdef]
      linarith only [haK, hKnd, hKlog]
    have hA := mul_le_mul_of_nonneg_left h1 hCLnn
    have h2 : Knd ≤ KLv := by rw [hKLdef]; linarith only [hKlog]
    have h3 : C4 ≤ C4 * KLv := by
      have := mul_le_mul_of_nonneg_left hKLge1 hC4
      linarith only [this]
    have h4 : c0⁻¹ ≤ c0⁻¹ * KLv := by
      have := mul_le_mul_of_nonneg_left hKLge1 hc0inv.le
      linarith only [this]
    linarith only [hA, h2, h3, h4]
  have hconst : (CL * (1 + ((S.LPrime - S.m : ℕ) : ℝ)) + Knd) * sg + C4 * sg + c0⁻¹ * sg ≤
      (4 * CL + C4 + c0⁻¹ + 1) * KLv * sg :=
    by linarith only [mul_le_mul_of_nonneg_right hscalar hsgpos.le]
  -- the two comparisons with the constant of the conclusion
  have h2C3 : 2 * C3 ≤ MC := by
    rw [hMCdef, masterConst]
    linarith only [hCL, hC4, hc0inv]
  have hsum4 : 4 * CL + C4 + c0⁻¹ + 1 ≤ MC := by
    rw [hMCdef, masterConst]
    linarith only [hC3]
  have hfront : (0 : ℝ) ≤ DE * (bt + (S.h : ℝ) * sg) := by
    have : (0 : ℝ) ≤ (S.h : ℝ) * sg := mul_nonneg hhR hsgpos.le
    exact mul_nonneg hDEnn (by linarith only [this, hbtpos.le])
  have h7a : 2 * C3 * DE * ((S.h : ℝ) * sg + bt) ≤ MC * DE * (bt + (S.h : ℝ) * sg) := by
    have := mul_le_mul_of_nonneg_right h2C3 hfront
    linarith only [this]
  have h7b : (4 * CL + C4 + c0⁻¹ + 1) * KLv * sg ≤ MC * KLv * sg := by
    have hkn : (0 : ℝ) ≤ KLv * sg := mul_nonneg (by linarith only [hKLge1]) hsgpos.le
    have := mul_le_mul_of_nonneg_right hsum4 hkn
    linarith only [this]
  linarith only [hlow, hLHSl, hIdentity, hT1r, hT2r, hT3, hT4l, hScaleCond, herr,
    hM3, hconst, h7a, h7b]

/-! ## From the master inequality to `e.sstar.lower.bound` -/

private theorem rpowPowTwo (x a : ℝ) (hx : 0 < x) : (x ^ a) ^ (2 : ℕ) = x ^ (a + a) := by
  rw [Real.rpow_add hx, pow_two]

/-- The constant of the lower bound `e.sstar.lower.bound` at the pigeonhole
scale, explicit in the constant `CB` of `e.bell.vs.starell`, the constant `Cq`
of the logarithmic envelope, the constant `Clog` comparing
`log(ν⁻¹L)` with `log(ν⁻¹m)` on the pigeonhole range, the constant `c₁` of the
optimized window size `e.h.optimized.size`, and the constant `CDE` bounding the
factor `C(δ + L^{-1000})^{1/2}`, which the paper keeps on `σ̄_ℓ(cu_n)` in the
display after the absorptions and absorbs into its unspecified constant `c(d)`. -/
def sstarLowerBoundConst (CB Cq Clog c1 CDE : ℝ) : ℝ :=
  Real.sqrt (c1 / (64 * CB * Cq * Clog ^ (9 : ℕ) * CDE))

theorem sstarLowerBoundConst_pos {CB Cq Clog c1 CDE : ℝ} (hCB : 0 < CB)
    (hCq : 0 < Cq) (hClog : 0 < Clog) (hc1 : 0 < c1) (hCDE : 0 < CDE) :
    0 < sstarLowerBoundConst CB Cq Clog c1 CDE := by
  rw [sstarLowerBoundConst]
  refine Real.sqrt_pos.2 ?_
  have h : (0 : ℝ) < 64 * CB * Cq * Clog ^ (9 : ℕ) * CDE := by positivity
  exact div_pos hc1 h

/-- The real-arithmetic core of the passage to `e.sstar.lower.bound`: every carrier of
Section 3 has been abstracted to a real number, so that the chain of
absorptions, the homogenization comparison, the two localization comparisons,
the optimized window size and the final square root are one bounded
computation. -/
private theorem sstarArith
    (CM CB Cq Clog c1 CDE cStar hh LL mm sg bt se Y LamL lam Q4 DE KL
      nuInv4 nu4 nuTwo : ℝ)
    (hCB : 0 < CB) (hCq : 0 < Cq) (hClog : 0 < Clog) (hc1 : 0 < c1)
    (hCDE : 0 < CDE)
    (hcStar : 0 < cStar) (hsgpos : 0 < sg) (hbtpos : 0 < bt)
    (hhR : 0 ≤ hh) (hm1 : 1 ≤ mm) (hQ4nn : 0 ≤ Q4)
    (hnuInv4 : 0 < nuInv4) (hnu4pos : 0 < nu4) (hnuprod : nuInv4 * nu4 = 1)
    (hnuTwo : nuTwo ^ (2 : ℕ) = nu4) (hnuTwonn : 0 ≤ nuTwo)
    (hMaster : cStar * hh * sg ≤ CM * DE * (bt + hh * sg) + CM * KL * sg)
    (hFactor : CM * DE ≤ CDE) (hSmallC : CM * DE ≤ cStar / 4)
    (hLowerAbs : CM * KL ≤ cStar * hh / 4)
    (hbell : bt ≤ CB * nuInv4 * Q4 * se⁻¹)
    (hQ : Q4 ≤ Cq * LamL ^ (8 : ℕ))
    (hLocal1 : se⁻¹ ≤ 2 * sg⁻¹)
    (hLocal2 : (1 / 4 : ℝ) * sg⁻¹ ≤ Y)
    (hHsize : c1 * cStar ^ (2 : ℕ) * LL ≤ hh * LamL)
    (hLogL : (1 : ℝ) ≤ LamL) (hLogm : (1 : ℝ) ≤ lam)
    (hlogcomp : LamL ≤ Clog * lam) (hmL : mm ≤ LL) :
    sstarLowerBoundConst CB Cq Clog c1 CDE * cStar ^ ((3 : ℝ) / 2) * nuTwo *
        mm ^ ((1 : ℝ) / 2) * lam ^ (-((9 : ℝ) / 2)) ≤ Y := by
  have hsgne : sg ≠ 0 := ne_of_gt hsgpos
  have hmpos : (0 : ℝ) < mm := lt_of_lt_of_le zero_lt_one hm1
  have hlampos : (0 : ℝ) < lam := lt_of_lt_of_le zero_lt_one hLogm
  have hLamLpos : (0 : ℝ) < LamL := lt_of_lt_of_le zero_lt_one hLogL
  have hLR : (0 : ℝ) ≤ LL := le_trans (le_trans zero_le_one hm1) hmL
  -- Step 1: the two absorptions, the factor
  -- `C(δ + L^{-1000})^{1/2}` being kept on `σ̄_ℓ(cu_n)` as in the paper
  have habs : cStar / 2 * hh * sg ≤ CDE * bt := by
    have t1 := mul_le_mul_of_nonneg_right hFactor hbtpos.le
    have t2 := mul_le_mul_of_nonneg_right hSmallC (mul_nonneg hhR hsgpos.le)
    have t3 := mul_le_mul_of_nonneg_right hLowerAbs hsgpos.le
    linarith only [hMaster, t1, t2, t3]
  -- Step 2: `e.bell.vs.starell` and the first localization comparison
  have hcoefnn : (0 : ℝ) ≤ CB * nuInv4 * Q4 :=
    mul_nonneg (mul_nonneg hCB.le hnuInv4.le) hQ4nn
  have hbt2 : bt ≤ CB * nuInv4 * Q4 * (2 * sg⁻¹) := by
    have := mul_le_mul_of_nonneg_left hLocal1 hcoefnn
    linarith only [hbell, this]
  -- Step 3: multiply through by `σ̄_{L',*}^{-1}(cu_n)`
  have hinvmul : sg⁻¹ * sg = 1 := inv_mul_cancel₀ hsgne
  have s1 := mul_le_mul_of_nonneg_right habs hsgpos.le
  have s2 := mul_le_mul_of_nonneg_right hbt2 hsgpos.le
  have hrw1 : CB * nuInv4 * Q4 * (2 * sg⁻¹) * sg = 2 * (CB * nuInv4 * Q4) := by
    calc CB * nuInv4 * Q4 * (2 * sg⁻¹) * sg
        = 2 * (CB * nuInv4 * Q4) * (sg⁻¹ * sg) := by ring
      _ = 2 * (CB * nuInv4 * Q4) := by rw [hinvmul, mul_one]
  rw [hrw1] at s2
  have s2' := mul_le_mul_of_nonneg_left s2 hCDE.le
  have hA : cStar / 2 * hh * sg ^ (2 : ℕ) ≤ 2 * (CB * nuInv4 * Q4) * CDE := by
    linarith only [s1, s2']
  -- Step 4: clear the negative power of `nu`
  have s3 := mul_le_mul_of_nonneg_right hA hnu4pos.le
  have hrw2 : 2 * (CB * nuInv4 * Q4) * CDE * nu4 = 2 * CB * Q4 * CDE := by
    calc 2 * (CB * nuInv4 * Q4) * CDE * nu4
        = 2 * CB * Q4 * CDE * (nuInv4 * nu4) := by ring
      _ = 2 * CB * Q4 * CDE := by rw [hnuprod, mul_one]
  rw [hrw2] at s3
  -- Step 5: the logarithmic envelope
  have s4 : cStar / 2 * hh * sg ^ (2 : ℕ) * nu4 ≤
      2 * CB * (Cq * LamL ^ (8 : ℕ)) * CDE := by
    have := mul_le_mul_of_nonneg_left hQ (mul_nonneg (mul_nonneg zero_le_two hCB.le) hCDE.le)
    linarith only [s3, this]
  -- Step 6: the optimized window size `e.h.optimized.size`
  have s5 := mul_le_mul_of_nonneg_right s4 hLamLpos.le
  have hrw3 : 2 * CB * (Cq * LamL ^ (8 : ℕ)) * CDE * LamL =
      2 * CB * Cq * LamL ^ (9 : ℕ) * CDE := by ring
  rw [hrw3] at s5
  have hsize := mul_le_mul_of_nonneg_left hHsize
    (mul_nonneg (mul_nonneg (half_pos hcStar).le (sq_nonneg sg)) hnu4pos.le)
  have hE : c1 / 2 * cStar ^ (3 : ℕ) * LL * sg ^ (2 : ℕ) * nu4 ≤
      2 * CB * Cq * LamL ^ (9 : ℕ) * CDE := by linarith only [s5, hsize]
  -- Step 7: the second localization comparison
  have hYsg : (1 : ℝ) / 4 ≤ Y * sg := by
    have h := mul_le_mul_of_nonneg_right hLocal2 hsgpos.le
    rw [mul_assoc, hinvmul, mul_one] at h
    linarith only [h]
  have hsq : (1 : ℝ) / 16 ≤ Y ^ (2 : ℕ) * sg ^ (2 : ℕ) := by
    have h := mul_le_mul hYsg hYsg (by norm_num) (le_trans (by norm_num) hYsg)
    have hrw : Y * sg * (Y * sg) = Y ^ (2 : ℕ) * sg ^ (2 : ℕ) := by ring
    rw [hrw] at h
    linarith only [h]
  have hF : c1 / 32 * cStar ^ (3 : ℕ) * LL * nu4 ≤
      2 * CB * Cq * LamL ^ (9 : ℕ) * CDE * Y ^ (2 : ℕ) := by
    have t1 := mul_le_mul_of_nonneg_right hE (sq_nonneg Y)
    have t2 := mul_le_mul_of_nonneg_left hsq
      (mul_nonneg (mul_nonneg (mul_nonneg (half_pos hc1).le (pow_nonneg hcStar.le 3)) hLR) hnu4pos.le)
    linarith only [t1, t2]
  -- Step 8: the comparability of the scales and logarithms over `[L/4, L/2]`
  have hLam9 : LamL ^ (9 : ℕ) ≤ Clog ^ (9 : ℕ) * lam ^ (9 : ℕ) := by
    calc LamL ^ (9 : ℕ) ≤ (Clog * lam) ^ (9 : ℕ) := pow_le_pow_left₀ hLamLpos.le hlogcomp 9
      _ = Clog ^ (9 : ℕ) * lam ^ (9 : ℕ) := by rw [mul_pow]
  have hG : c1 / 32 * cStar ^ (3 : ℕ) * mm * nu4 ≤
      2 * CB * Cq * Clog ^ (9 : ℕ) * lam ^ (9 : ℕ) * CDE * Y ^ (2 : ℕ) := by
    have t1 := mul_le_mul_of_nonneg_left hmL
      (mul_nonneg (mul_nonneg (div_nonneg hc1.le (by norm_num : (0 : ℝ) ≤ 32)) (pow_nonneg hcStar.le 3)) hnu4pos.le)
    have t2 := mul_le_mul_of_nonneg_left hLam9
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hCB.le) hCq.le) (sq_nonneg Y)) hCDE.le)
    linarith only [hF, t1, t2]
  -- Step 9: the constant of the conclusion
  have hD2 : (0 : ℝ) < 64 * CB * Cq * Clog ^ (9 : ℕ) * CDE :=
    mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) hCB) hCq) (pow_pos hClog 9)) hCDE
  have hcfin2 : sstarLowerBoundConst CB Cq Clog c1 CDE ^ (2 : ℕ) =
      c1 / (64 * CB * Cq * Clog ^ (9 : ℕ) * CDE) := by
    rw [sstarLowerBoundConst, Real.sq_sqrt (div_nonneg hc1.le hD2.le)]
  have hkey : sstarLowerBoundConst CB Cq Clog c1 CDE ^ (2 : ℕ) * cStar ^ (3 : ℕ) * nu4 * mm ≤
      Y ^ (2 : ℕ) * lam ^ (9 : ℕ) := by
    rw [hcfin2, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_le_iff₀ hD2]
    linarith only [hG]
  -- Step 10: the square root
  have hcfinnn : (0 : ℝ) ≤ sstarLowerBoundConst CB Cq Clog c1 CDE := by
    rw [sstarLowerBoundConst]; exact Real.sqrt_nonneg _
  have hcs : (0 : ℝ) ≤ cStar ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hcStar.le _
  have hms : (0 : ℝ) ≤ mm ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hmpos.le _
  have hls : (0 : ℝ) ≤ lam ^ (-((9 : ℝ) / 2)) := Real.rpow_nonneg hlampos.le _
  have hZnn : (0 : ℝ) ≤ sstarLowerBoundConst CB Cq Clog c1 CDE * cStar ^ ((3 : ℝ) / 2) *
      nuTwo * mm ^ ((1 : ℝ) / 2) * lam ^ (-((9 : ℝ) / 2)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hcfinnn hcs) hnuTwonn) hms) hls
  have hYnn : (0 : ℝ) ≤ Y := by
    have : (0 : ℝ) < (1 / 4 : ℝ) * sg⁻¹ := mul_pos (by norm_num) (inv_pos.2 hsgpos)
    linarith only [hLocal2, this]
  have e1 : (cStar ^ ((3 : ℝ) / 2)) ^ (2 : ℕ) = cStar ^ (3 : ℕ) := by
    rw [rpowPowTwo _ _ hcStar,
      show (3 : ℝ) / 2 + (3 : ℝ) / 2 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e3 : (mm ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = mm := by
    rw [rpowPowTwo _ _ hmpos,
      show (1 : ℝ) / 2 + (1 : ℝ) / 2 = (1 : ℝ) by norm_num, Real.rpow_one]
  have e4 : (lam ^ (-((9 : ℝ) / 2))) ^ (2 : ℕ) = lam ^ (-(9 : ℝ)) := by
    rw [rpowPowTwo _ _ hlampos,
      show -((9 : ℝ) / 2) + -((9 : ℝ) / 2) = -(9 : ℝ) by norm_num]
  have hlam9 : lam ^ (-(9 : ℝ)) * lam ^ (9 : ℕ) = 1 := by
    rw [← Real.rpow_natCast lam 9, ← Real.rpow_add hlampos]
    norm_num
  have hZ2 : (sstarLowerBoundConst CB Cq Clog c1 CDE * cStar ^ ((3 : ℝ) / 2) * nuTwo *
        mm ^ ((1 : ℝ) / 2) * lam ^ (-((9 : ℝ) / 2))) ^ (2 : ℕ) =
      sstarLowerBoundConst CB Cq Clog c1 CDE ^ (2 : ℕ) * cStar ^ (3 : ℕ) * nu4 * mm *
        lam ^ (-(9 : ℝ)) := by
    calc (sstarLowerBoundConst CB Cq Clog c1 CDE * cStar ^ ((3 : ℝ) / 2) * nuTwo *
          mm ^ ((1 : ℝ) / 2) * lam ^ (-((9 : ℝ) / 2))) ^ (2 : ℕ)
        = sstarLowerBoundConst CB Cq Clog c1 CDE ^ (2 : ℕ) * (cStar ^ ((3 : ℝ) / 2)) ^ (2 : ℕ) *
            nuTwo ^ (2 : ℕ) * (mm ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) *
            (lam ^ (-((9 : ℝ) / 2))) ^ (2 : ℕ) := by ring
      _ = sstarLowerBoundConst CB Cq Clog c1 CDE ^ (2 : ℕ) * cStar ^ (3 : ℕ) * nu4 * mm *
            lam ^ (-(9 : ℝ)) := by rw [e1, hnuTwo, e3, e4]
  have hlam9pos : (0 : ℝ) < lam ^ (9 : ℕ) := pow_pos hlampos 9
  have hZY : (sstarLowerBoundConst CB Cq Clog c1 CDE * cStar ^ ((3 : ℝ) / 2) * nuTwo *
        mm ^ ((1 : ℝ) / 2) * lam ^ (-((9 : ℝ) / 2))) ^ (2 : ℕ) ≤ Y ^ (2 : ℕ) := by
    have h : (sstarLowerBoundConst CB Cq Clog c1 CDE * cStar ^ ((3 : ℝ) / 2) * nuTwo *
          mm ^ ((1 : ℝ) / 2) * lam ^ (-((9 : ℝ) / 2))) ^ (2 : ℕ) * lam ^ (9 : ℕ) ≤
        Y ^ (2 : ℕ) * lam ^ (9 : ℕ) := by
      rw [hZ2]
      calc sstarLowerBoundConst CB Cq Clog c1 CDE ^ (2 : ℕ) * cStar ^ (3 : ℕ) * nu4 * mm *
            lam ^ (-(9 : ℝ)) * lam ^ (9 : ℕ)
          = sstarLowerBoundConst CB Cq Clog c1 CDE ^ (2 : ℕ) * cStar ^ (3 : ℕ) * nu4 * mm *
              (lam ^ (-(9 : ℝ)) * lam ^ (9 : ℕ)) := by ring
        _ = sstarLowerBoundConst CB Cq Clog c1 CDE ^ (2 : ℕ) * cStar ^ (3 : ℕ) * nu4 * mm := by
            rw [hlam9, mul_one]
        _ ≤ Y ^ (2 : ℕ) * lam ^ (9 : ℕ) := hkey
    exact le_of_mul_le_mul_right (by linarith only [h]) hlam9pos
  have hfin := Real.sqrt_le_sqrt hZY
  rwa [Real.sqrt_sq hZnn, Real.sqrt_sq hYnn] at hfin

/-- **The passage from the master inequality to `e.sstar.lower.bound` at the
pigeonhole scale**.

From the master inequality (`hMaster`, the conclusion of `master_inequality` at
the constant `CM`), the two absorptions, the homogenization
comparison `e.bell.vs.starell` (`hbell`, the statement
`Frozen.Section3.sigmaBar_le_sigmaBarStar_homogenization`
in the Section 3 carriers, at its constant `CB`), the two localization
comparisons, and the optimized window size
`e.h.optimized.size`, one obtains

`σ̄_{L,*}(cu_m) ≥ c c⋆^{3/2} ν² m^{1/2} log^{-9/2}(ν⁻¹ m)`,

which is the second conjunct of
`Frozen.Section3.sigmaBarStar_lower_bound` at the
pigeonhole scale `m`.

Constant-first: `CM, CB, Cq, Clog, c₁, CDE` precede the molecular diffusivity,
the law, the scale selection and the direction, and the conclusion's constant is
`sstarLowerBoundConst CB Cq Clog c₁ CDE`.

The following hypotheses are explicit here:

* `hSmallC` — the relative smallness `C(δ + L^{-1000})^{1/2} ≤ ¼c⋆`, i.e.
  `δ = c₀c⋆²` with `c₀(d)` small;
* `hFactor` — the bound `CDE` on the factor `C(δ + L^{-1000})^{1/2}` which the
  paper keeps on `σ̄_ℓ(cu_n)` after the absorptions and absorbs into its
  unspecified constant `c(d)`; no absolute smallness of `δ` independent of `c⋆`
  is used, and no upper bound on `c⋆` is assumed;
* `hLowerAbs` — `c⋆h > C(1 + K_nd + K log(ν⁻¹L))`;
* `hbell` — `e.bell.vs.starell` at `(n, ℓ)`, with `σ̄_{ℓ,*}(cu_n)` written as the
  inverse of `sigmaBarStarInvSeq`;
* `hQ` — the logarithmic envelope `(ℓ − n + log²(ν⁻¹ℓ))⁴ ≤ Cq log⁸(ν⁻¹L)`
  (the paper writes the conclusion with `log⁸(ν⁻¹L)`);
* `hLocal1`, `hLocal2` — the two balanced localization comparisons,
  `σ̄_{ℓ,*}(cu_n) ≤ 2σ̄_{L',*}(cu_n)` and
  `σ̄_{L,*}(cu_m) ≥ ¼σ̄_{L',*}(cu_n)`;
* `hHsize` — `h ≥ c₁c⋆²L/log(ν⁻¹L)`, cleared of its division;
* `hLogL`, `hLogm`, `hlogcomp`, `hmL`, `hm1` — the comparability of the scales
  and logarithms over the pigeonhole range `m ∈ [L/4, L/2]`. -/
theorem sstar_lower_bound_of_terms [NeZero d]
    (CM CB Cq Clog c1 CDE : ℝ) (hCB : 0 < CB) (hCq : 0 < Cq) (hClog : 0 < Clog)
    (hc1 : 0 < c1) (hCDE : 0 < CDE)
    (nu : ℝ) (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d))
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P)
    (cStar Knd K delta : ℝ) (hcStar : 0 < cStar)
    (S : ScaleSelection)
    (hMaster : cStar * (S.h : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n ≤
      CM * (delta + (S.L : ℝ) ^ (-(1000 : ℝ))) ^ ((1 : ℝ) / 2) *
          (sigmaBarSeq nu S.ell P S.n +
            (S.h : ℝ) * sigmaBarStarInvSeq nu S.LPrime P S.n) +
        CM * (1 + Knd + K * Real.log (nu⁻¹ * (S.L : ℝ))) *
          sigmaBarStarInvSeq nu S.LPrime P S.n)
    (hFactor : CM * (delta + (S.L : ℝ) ^ (-(1000 : ℝ))) ^ ((1 : ℝ) / 2) ≤ CDE)
    (hSmallC : CM * (delta + (S.L : ℝ) ^ (-(1000 : ℝ))) ^ ((1 : ℝ) / 2) ≤ cStar / 4)
    (hLowerAbs : CM * (1 + Knd + K * Real.log (nu⁻¹ * (S.L : ℝ))) ≤
      cStar * (S.h : ℝ) / 4)
    (hbell : sigmaBarSeq nu S.ell P S.n ≤
      CB * nu ^ (-(4 : ℝ)) *
          (((S.ell - S.n : ℕ) : ℝ) + Real.log (nu⁻¹ * (S.ell : ℝ)) ^ (2 : ℕ)) ^ (4 : ℕ) *
        (sigmaBarStarInvSeq nu S.ell P S.n)⁻¹)
    (hQ : (((S.ell - S.n : ℕ) : ℝ) + Real.log (nu⁻¹ * (S.ell : ℝ)) ^ (2 : ℕ)) ^ (4 : ℕ) ≤
      Cq * Real.log (nu⁻¹ * (S.L : ℝ)) ^ (8 : ℕ))
    (hLocal1 : (sigmaBarStarInvSeq nu S.ell P S.n)⁻¹ ≤
      2 * (sigmaBarStarInvSeq nu S.LPrime P S.n)⁻¹)
    (hLocal2 : (1 / 4 : ℝ) * (sigmaBarStarInvSeq nu S.LPrime P S.n)⁻¹ ≤
      sigmaBarStarScalar nu S.L P (cubeSet (originCube d (S.m : ℤ))))
    (hHsize : c1 * cStar ^ (2 : ℕ) * (S.L : ℝ) ≤
      (S.h : ℝ) * Real.log (nu⁻¹ * (S.L : ℝ)))
    (hLogL : (1 : ℝ) ≤ Real.log (nu⁻¹ * (S.L : ℝ)))
    (hLogm : (1 : ℝ) ≤ Real.log (nu⁻¹ * (S.m : ℝ)))
    (hlogcomp : Real.log (nu⁻¹ * (S.L : ℝ)) ≤ Clog * Real.log (nu⁻¹ * (S.m : ℝ)))
    (hmL : (S.m : ℝ) ≤ (S.L : ℝ)) (hm1 : (1 : ℝ) ≤ (S.m : ℝ)) :
    sstarLowerBoundConst CB Cq Clog c1 CDE * cStar ^ ((3 : ℝ) / 2) * nu ^ (2 : ℝ) *
        (S.m : ℝ) ^ ((1 : ℝ) / 2) *
        Real.log (nu⁻¹ * (S.m : ℝ)) ^ (-((9 : ℝ) / 2)) ≤
      sigmaBarStarScalar nu S.L P (cubeSet (originCube d (S.m : ℤ))) := by
  have hsgpos : 0 < sigmaBarStarInvSeq nu S.LPrime P S.n :=
    sigmaBarStarInvSeq_pos hnu S.LPrime hPrefix hJ2 hJ3 hJ4 S.n
  have hbtpos : 0 < sigmaBarSeq nu S.ell P S.n :=
    sigmaBarSeq_pos hnu S.ell hPrefix hJ2 hJ3 hJ4 S.n
  have hQ4nn : (0 : ℝ) ≤
      (((S.ell - S.n : ℕ) : ℝ) + Real.log (nu⁻¹ * (S.ell : ℝ)) ^ (2 : ℕ)) ^ (4 : ℕ) := by
    have hbase : (0 : ℝ) ≤ ((S.ell - S.n : ℕ) : ℝ) +
        Real.log (nu⁻¹ * (S.ell : ℝ)) ^ (2 : ℕ) := by positivity
    positivity
  have hnuprod : nu ^ (-(4 : ℝ)) * nu ^ (4 : ℕ) = 1 := by
    rw [← Real.rpow_natCast nu 4, ← Real.rpow_add hnu]
    norm_num
  have hnuTwo : (nu ^ (2 : ℝ)) ^ (2 : ℕ) = nu ^ (4 : ℕ) := by
    rw [rpowPowTwo _ _ hnu,
      show (2 : ℝ) + (2 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact sstarArith CM CB Cq Clog c1 CDE cStar (S.h : ℝ) (S.L : ℝ) (S.m : ℝ)
    (sigmaBarStarInvSeq nu S.LPrime P S.n) (sigmaBarSeq nu S.ell P S.n)
    (sigmaBarStarInvSeq nu S.ell P S.n)
    (sigmaBarStarScalar nu S.L P (cubeSet (originCube d (S.m : ℤ))))
    (Real.log (nu⁻¹ * (S.L : ℝ))) (Real.log (nu⁻¹ * (S.m : ℝ)))
    ((((S.ell - S.n : ℕ) : ℝ) + Real.log (nu⁻¹ * (S.ell : ℝ)) ^ (2 : ℕ)) ^ (4 : ℕ))
    ((delta + (S.L : ℝ) ^ (-(1000 : ℝ))) ^ ((1 : ℝ) / 2))
    (1 + Knd + K * Real.log (nu⁻¹ * (S.L : ℝ))) (nu ^ (-(4 : ℝ))) (nu ^ (4 : ℕ))
    (nu ^ (2 : ℝ)) hCB hCq hClog hc1 hCDE hcStar hsgpos hbtpos (Nat.cast_nonneg _)
    hm1 hQ4nn (Real.rpow_pos_of_pos hnu _) (by positivity) hnuprod hnuTwo
    (Real.rpow_nonneg hnu.le _) hMaster hFactor hSmallC hLowerAbs hbell hQ hLocal1
    hLocal2 hHsize hLogL hLogm hlogcomp hmL

end

end SuperdiffusionCLT.Section3.Terms
