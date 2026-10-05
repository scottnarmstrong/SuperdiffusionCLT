/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Probability.OrliczMoments
public import SuperdiffusionCLT.Section3.ResponseFields.StationaryComparison
public import SuperdiffusionCLT.Section3.Setup.WholeSpaceEnergyC

/-!
# The closing coarsening of `l.LHS.term1`, and the lemma itself

The last two steps of the proof of `e.nabla.w.lower.bound`, and the assembly.

* the closing coarsening.  The sandwich
  `E‖∇w‖² ≤ E|∇ŵ(0)|² ≤ E‖∇w̃‖²` and the exact gap identity
  `e.energy.quadratic.N.D` (`volumeAverage_energy_gap`) turn the
  summed display `e.wN.wD.with.average.error` into
  `|E‖∇w‖² − E|∇ŵ(0)|²| ≤ C(1 + L' − m)|p|²`;
* the assembly with `e.use.nondeg.ass`, which is
  `abs_wholeSpaceEnergy_sub_cStar_mul_le`.

The one step of the printed proof that is not proved here is the summed display
`e.wN.wD.with.average.error` itself: it needs the linearity
`w = Σ_r w_r`, `w̃ = Σ_r w̃_r` of the two response problems in the flux.
It enters the theorems below as an explicit hypothesis
in the exact shape of the print — a `Γ₂` observable plus the norm
of the vector sum of the cube averages — and never as a proposition-valued
definition.

The shell-level inputs — the second moment of a `Γ₂` observable, the zero-mean
consequence of `ShellLawJ4`, and `e.average.error.energy` itself
— are in the companion module
`Section3/Setup/WholeSpaceEnergyC.lean`.

## Main results

* `lintegral_vecCubeLpENorm_sq_response_gap_le`: the second moment of the
  summed display `e.wN.wD.with.average.error`.
* `vecCubeLpENorm_two_sq_energy_gap`: `e.energy.quadratic.N.D` for the squared
  normalized norms.
* `abs_toReal_sub_wholeSpaceEnergy_le`: the energy gap display of the
  closing coarsening.
* `l_LHS_term1_constFirst`: `e.nabla.w.lower.bound`, the paper's own quantifier order, with the
  constant `lhsTerm1Const` produced before the scales, the shell law and the
  direction.
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
open SuperdiffusionCLT.Section3.ResponseFields
open scoped BigOperators ENNReal

noncomputable section

variable {d : ℕ}

/-! ## `e.energy.quadratic.N.D` and the closing coarsening -/

section Closing

variable {P : ProbabilityMeasure (ShellSeq d)}

/-- The normalized cube integral of a scalar field is its volume average over
the open cube. -/
theorem integral_normalizedCubeMeasure_eq_volumeAverage (Q : TriadicCube d)
    (f : Vec d → ℝ) :
    ∫ x, f x ∂normalizedCubeMeasure Q = volumeAverage (openCubeSet Q) f := by
  rw [integral_normalizedCubeMeasure_eq, volumeAverage, volume_openCubeSet_toReal]

private theorem volumeAverage_vecNormSq_nonneg (Q : TriadicCube d)
    (G : Vec d → Vec d) :
    0 ≤ volumeAverage (openCubeSet Q) (fun x => vecNormSq (G x)) :=
  mul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg)
    (integral_nonneg fun x => vecNormSq_nonneg (G x))

/-- **`e.energy.quadratic.N.D`** for the squared normalized
cube norms, which is the shape in which the sandwich of
`responseFields_stationary` presents the two response energies:

`‖∇w_N‖²_{L̲²(cu_M)} = ‖∇w_D‖²_{L̲²(cu_M)} + ‖∇w_N − ∇w_D‖²_{L̲²(cu_M)}`. -/
theorem vecCubeLpENorm_two_sq_energy_gap {Q : TriadicCube d} {F : Vec d → Vec d}
    {wN : H1MeanZeroFunction (openCubeSet Q)} {wD : H10Function (openCubeSet Q)}
    (hN : IsCubeNeumannResponse Q F wN) (hD : IsCubeDirichletResponse Q F wD) :
    vecCubeLpENorm Q 2 wN.toH1Function.grad ^ (2 : ℕ) =
      vecCubeLpENorm Q 2 wD.toH1Function.grad ^ (2 : ℕ) +
        vecCubeLpENorm Q 2
          (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x)
            ^ (2 : ℕ) := by
  have hsub : MemVectorL2 (openCubeSet Q)
      (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x) :=
    wN.toH1Function.grad_memVectorL2.sub wD.toH1Function.grad_memVectorL2
  have hgap := volumeAverage_energy_gap hN hD
  rw [vecCubeLpENorm_two_sq_eq_ofReal wN.toH1Function.grad_memVectorL2,
    vecCubeLpENorm_two_sq_eq_ofReal wD.toH1Function.grad_memVectorL2,
    vecCubeLpENorm_two_sq_eq_ofReal hsub,
    integral_normalizedCubeMeasure_eq_volumeAverage,
    integral_normalizedCubeMeasure_eq_volumeAverage,
    integral_normalizedCubeMeasure_eq_volumeAverage,
    ← ENNReal.ofReal_add (volumeAverage_vecNormSq_nonneg Q wD.toH1Function.grad)
      (volumeAverage_vecNormSq_nonneg Q
        (fun x => wN.toH1Function.grad x - wD.toH1Function.grad x))]
  congr 1
  linarith only [hgap]

/-- **The second moment of the summed display `e.wN.wD.with.average.error`**.
The print's bound
`‖∇w̃ − ∇w‖_{L̲²(cu_M)} ≤ O_{Γ₂}(C|p|) + |Σ_{r ∈ s} (j_r p)_{cu_M}|`
is squared through `(a + b)² ≤ 2a² + 2b²`, the first term by the second-moment
bound for a `Γ₂` observable and the second by `e.average.error.energy`. -/
theorem lintegral_vecCubeLpENorm_sq_response_gap_le (hJ2 : ShellLawJ2 d P)
    (hJ4 : ShellLawJ4 d P) (M : ℕ) (s : Finset ℕ) (p : Vec d)
    (wD : ShellSeq d → H10Function (openCubeSet (originCube d (M : ℤ))))
    (wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ))))
    (Cy : ℝ) (hCy : 0 < Cy) (Y : ShellSeq d → ℝ) (hY0 : ∀ omega, 0 ≤ Y omega)
    (hYm : Measurable Y) (hYbig : IsBigO P.toMeasure (gammaSigma 2) Y Cy)
    (A : ℕ → ℝ) (hApos : ∀ r ∈ s, 0 < A r) (Z : ℕ → ShellSeq d → ℝ)
    (hZm : ∀ r, Measurable (Z r))
    (hZbig : ∀ r ∈ s, IsBigO P.toMeasure (gammaSigma 2) (Z r) (A r))
    (hZbound : ∀ (r : ℕ) (omega : ShellSeq d),
      vecNorm (shellFluxAverage (M : ℤ) omega r p) ≤ Z r omega)
    (hbridge : ∀ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (M : ℤ)) 2
          (fun x => (wN omega).toH1Function.grad x -
            (wD omega).toH1Function.grad x) ≤
        ENNReal.ofReal (Y omega +
          vecNorm (∑ r ∈ s, shellFluxAverage (M : ℤ) omega r p))) :
    ∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (M : ℤ)) 2
        (fun x => (wN omega).toH1Function.grad x -
          (wD omega).toH1Function.grad x) ^ (2 : ℕ) ∂P.toMeasure ≤
      ENNReal.ofReal (2 * (Cy ^ 2 * (1 + Real.Gamma 2)) +
        2 * ((1 + Real.Gamma 2) * ∑ r ∈ s, A r ^ 2)) := by
  classical
  set n : ShellSeq d → ℝ :=
    fun omega => vecNorm (∑ r ∈ s, shellFluxAverage (M : ℤ) omega r p) with hndef
  have hn0 : ∀ omega, 0 ≤ n omega := fun omega =>
    norm_nonneg (HilbertVec.ofVec (∑ r ∈ s, shellFluxAverage (M : ℤ) omega r p))
  have hnsq : ∀ omega, n omega ^ 2 =
      vecNormSq (∑ r ∈ s, shellFluxAverage (M : ℤ) omega r p) :=
    fun omega => vecNorm_sq_eq_vecNormSq _
  set g : ShellSeq d → ℝ := fun omega => 2 * Y omega ^ 2 + 2 * n omega ^ 2
    with hgdef
  have hYsq : Integrable (fun omega => Y omega ^ 2) P.toMeasure :=
    integrable_sq_of_isBigO_gammaSigma_two hCy hYm.aemeasurable hYbig
  have hnsqInt : Integrable (fun omega => n omega ^ 2) P.toMeasure := by
    refine (integrable_vecNormSq_sum_shellFluxAverage (M : ℤ) s p A hApos Z hZm
      hZbig hZbound).congr (Filter.Eventually.of_forall fun omega => ?_)
    exact (hnsq omega).symm
  have hgint : Integrable g P.toMeasure :=
    (hYsq.const_mul 2).add (hnsqInt.const_mul 2)
  have hg0 : ∀ omega, 0 ≤ g omega := fun omega => by
    have h1 : (0 : ℝ) ≤ Y omega ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) ≤ n omega ^ 2 := sq_nonneg _
    rw [hgdef]
    positivity
  have hpoint : ∀ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (M : ℤ)) 2
          (fun x => (wN omega).toH1Function.grad x -
            (wD omega).toH1Function.grad x) ^ (2 : ℕ) ≤
        ENNReal.ofReal (g omega) := by
    intro omega
    have hsum0 : (0 : ℝ) ≤ Y omega + n omega :=
      add_nonneg (hY0 omega) (hn0 omega)
    have h1 : vecCubeLpENorm (originCube d (M : ℤ)) 2
        (fun x => (wN omega).toH1Function.grad x -
          (wD omega).toH1Function.grad x) ^ (2 : ℕ) ≤
        ENNReal.ofReal (Y omega + n omega) ^ (2 : ℕ) :=
      pow_le_pow_left' (hbridge omega) 2
    refine h1.trans ?_
    rw [← ENNReal.ofReal_pow hsum0]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsq : (0 : ℝ) ≤ (Y omega - n omega) ^ 2 := sq_nonneg _
    have hexp : 2 * Y omega ^ 2 + 2 * n omega ^ 2 -
        (Y omega + n omega) ^ 2 = (Y omega - n omega) ^ 2 := by ring
    rw [hgdef]
    linarith only [hsq, hexp]
  calc ∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (M : ℤ)) 2
        (fun x => (wN omega).toH1Function.grad x -
          (wD omega).toH1Function.grad x) ^ (2 : ℕ) ∂P.toMeasure ≤
      ∫⁻ omega : ShellSeq d, ENNReal.ofReal (g omega) ∂P.toMeasure :=
        lintegral_mono hpoint
    _ = ENNReal.ofReal (∫ omega, g omega ∂P.toMeasure) :=
        (ofReal_integral_eq_lintegral_ofReal hgint
          (Filter.Eventually.of_forall hg0)).symm
    _ ≤ ENNReal.ofReal (2 * (Cy ^ 2 * (1 + Real.Gamma 2)) +
          2 * ((1 + Real.Gamma 2) * ∑ r ∈ s, A r ^ 2)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hY := integral_sq_le_of_isBigO_gammaSigma_two hCy hYm.aemeasurable
          hYbig
        have hN := integral_vecNormSq_sum_shellFluxAverage_le hJ2 hJ4 (M : ℤ) s p
          A hApos Z hZm hZbig hZbound
        have hNn : ∫ omega, n omega ^ 2 ∂P.toMeasure ≤
            (1 + Real.Gamma 2) * ∑ r ∈ s, A r ^ 2 := by
          refine le_trans (le_of_eq ?_) hN
          exact integral_congr_ae (Filter.Eventually.of_forall hnsq)
        rw [hgdef, integral_add (hYsq.const_mul 2) (hnsqInt.const_mul 2),
          integral_const_mul, integral_const_mul]
        have h2 : (0 : ℝ) ≤ 2 := by norm_num
        exact add_le_add (mul_le_mul_of_nonneg_left hY h2)
          (mul_le_mul_of_nonneg_left hNn h2)

/-- **The energy gap display of the closing coarsening**:
`|E‖∇w‖²_{L̲²(cu_M)} − E|∇ŵ(0)|²| ≤ B`, from the two halves of the sandwich
`e.energy.comparison.N.D`, the exact gap identity `e.energy.quadratic.N.D` and
any bound `B` on the second moment of the Neumann-minus-Dirichlet gap.

Finiteness of the Dirichlet energy — the junk-value escape of `ENNReal.toReal`
— is not assumed: it follows from the lower half of the sandwich together with
the square integrability `hGmemLp` of the stationary gradient. -/
theorem abs_toReal_sub_wholeSpaceEnergy_le {M : ℕ}
    {F : ShellSeq d → Vec d → Vec d} {gradHatW : ShellSeq d → Vec d}
    {wD : ShellSeq d → H10Function (openCubeSet (originCube d (M : ℤ)))}
    {wN : ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d (M : ℤ)))}
    (hwD : ∀ omega : ShellSeq d,
      IsCubeDirichletResponse (originCube d (M : ℤ)) (F omega) (wD omega))
    (hwN : ∀ omega : ShellSeq d,
      IsCubeNeumannResponse (originCube d (M : ℤ)) (F omega) (wN omega))
    (hwDmeas : AEStronglyMeasurable
      (fun omega : ShellSeq d => vecCubeLpENorm
        (originCube d (M : ℤ)) 2 (wD omega).toH1Function.grad) P.toMeasure)
    (hGmemLp : MemLp (fun omega : ShellSeq d =>
      HilbertVec.ofVec (gradHatW omega)) 2 P.toMeasure)
    (hlow : ∫⁻ omega : ShellSeq d, vecCubeLpENorm
        (originCube d (M : ℤ)) 2 (wD omega).toH1Function.grad ^ (2 : ℕ)
        ∂P.toMeasure ≤
      ∫⁻ omega : ShellSeq d,
        ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure)
    (hup : ∫⁻ omega : ShellSeq d,
        ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure ≤
      ∫⁻ omega : ShellSeq d, vecCubeLpENorm
        (originCube d (M : ℤ)) 2 (wN omega).toH1Function.grad ^ (2 : ℕ)
        ∂P.toMeasure)
    {B : ℝ} (hB : 0 ≤ B)
    (hgapB : ∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (M : ℤ)) 2
        (fun x => (wN omega).toH1Function.grad x -
          (wD omega).toH1Function.grad x) ^ (2 : ℕ) ∂P.toMeasure ≤
      ENNReal.ofReal B) :
    |(∫⁻ omega : ShellSeq d, vecCubeLpENorm
          (originCube d (M : ℤ)) 2 (wD omega).toH1Function.grad ^ (2 : ℕ)
          ∂P.toMeasure : ℝ≥0∞).toReal -
        wholeSpaceEnergy P.toMeasure gradHatW| ≤ B := by
  have hEtop : (∫⁻ omega : ShellSeq d,
      ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure) ≠ ⊤ :=
    lintegral_enorm_sq_ofVec_ne_top hGmemLp
  have hAtop : (∫⁻ omega : ShellSeq d, vecCubeLpENorm
      (originCube d (M : ℤ)) 2 (wD omega).toH1Function.grad ^ (2 : ℕ)
      ∂P.toMeasure) ≠ ⊤ := ne_top_of_le_ne_top hEtop hlow
  have hmeasA : AEMeasurable (fun omega : ShellSeq d => vecCubeLpENorm
      (originCube d (M : ℤ)) 2 (wD omega).toH1Function.grad ^ (2 : ℕ))
      P.toMeasure := hwDmeas.aemeasurable.pow_const 2
  have hsum : (∫⁻ omega : ShellSeq d, vecCubeLpENorm
        (originCube d (M : ℤ)) 2 (wN omega).toH1Function.grad ^ (2 : ℕ)
        ∂P.toMeasure) =
      (∫⁻ omega : ShellSeq d, vecCubeLpENorm
          (originCube d (M : ℤ)) 2 (wD omega).toH1Function.grad ^ (2 : ℕ)
          ∂P.toMeasure) +
        ∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (M : ℤ)) 2
          (fun x => (wN omega).toH1Function.grad x -
            (wD omega).toH1Function.grad x) ^ (2 : ℕ) ∂P.toMeasure := by
    rw [← lintegral_add_left' hmeasA]
    exact lintegral_congr fun omega =>
      vecCubeLpENorm_two_sq_energy_gap (hwN omega) (hwD omega)
  have hEle : (∫⁻ omega : ShellSeq d,
      ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure) ≤
      (∫⁻ omega : ShellSeq d, vecCubeLpENorm
          (originCube d (M : ℤ)) 2 (wD omega).toH1Function.grad ^ (2 : ℕ)
          ∂P.toMeasure) + ENNReal.ofReal B := by
    refine hup.trans ?_
    rw [hsum]
    exact add_le_add le_rfl hgapB
  have hfin : (∫⁻ omega : ShellSeq d, vecCubeLpENorm
        (originCube d (M : ℤ)) 2 (wD omega).toH1Function.grad ^ (2 : ℕ)
        ∂P.toMeasure) + ENNReal.ofReal B ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hAtop, ENNReal.ofReal_ne_top⟩
  have hEtoReal := ENNReal.toReal_mono hfin hEle
  rw [ENNReal.toReal_add hAtop ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hB] at hEtoReal
  have hAle := ENNReal.toReal_mono hEtop hlow
  rw [wholeSpaceEnergy, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hAle)]
  linarith only [hEtoReal]

end Closing

/-! ## `l.LHS.term1` -/

section Assembly

/-- **The constant `C(d)` of `e.nabla.w.lower.bound`** produced by the chain of
this file: the multiplicative constant of the energy gap display of the closing
coarsening, assembled from the two `Γ₂` amplitude constants that the printed
proof feeds into it — `Cgap`, the constant of the summed display
`e.wN.wD.with.average.error`, and `Cav`, the constant of
`e.jk.spatialavg` at the shells `r ≥ m`.

It is quantified before the scales, the shell law and the direction, exactly as
the manuscript quantifies `C(d)`; the dimension enters only through `Cgap` and
`Cav`, which are themselves the `C(d)` of the two printed displays. -/
def lhsTerm1Const (Cgap Cav : ℝ) : ℝ :=
  max 1 (2 * (1 + Real.Gamma 2) * (Cgap ^ 2 + Cav ^ 2))

theorem one_le_lhsTerm1Const (Cgap Cav : ℝ) : 1 ≤ lhsTerm1Const Cgap Cav :=
  le_max_left _ _

/-- **Lemma `l.LHS.term1`** (`e.nabla.w.lower.bound`) in the paper's own
quantifier order: the constant is produced **before** the scales, the shell
law, the probability measure and the direction, from the two amplitude
constants of the printed displays alone.

The proof is the printed one:

* the summed display `e.wN.wD.with.average.error` is the
  hypothesis `hbridge`, the one step not proved here — it needs the
  linearity `w = Σ_r w_r`, `w̃ = Σ_r w̃_r` of the two response problems in the
  flux — and it is stated in exactly the printed shape;
* `e.jk.spatialavg` at the shells `m ≤ r ≤ L'` is `hZbig`/`hZbound`, again in
  its exact applied shape (there the printed decay factor `3^{-(d/2)((m−r)∨0)}`
  is `1`, so the amplitude is `Cav|p|`);
* `e.average.error.energy` is
  `integral_vecNormSq_sum_shellFluxAverage_le`, from `ShellLawJ2`
  and the negation clause of `ShellLawJ4`;
* the energy gap display is `abs_toReal_sub_wholeSpaceEnergy_le`, from the two
  halves `hlow`, `hup` of `e.energy.comparison.N.D` and the exact gap identity
  `e.energy.quadratic.N.D`;
* `e.use.nondeg.ass` is
  `abs_wholeSpaceEnergy_sub_cStar_mul_le` together with the scale identity
  `L' − ℓ' = m − n`.

No degeneracy is used: the test vector `p` is nonzero because
`shom_{L',*}^{-1/2}(cu_n) > 0`, and the finiteness of the Dirichlet energy
comes from the lower half of the sandwich together with `hGmemLp`. -/
theorem l_LHS_term1_constFirst [NeZero d] (Cgap Cav : ℝ) (hCgap : 0 < Cgap)
    (hCav : 0 < Cav) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (nu : ℝ) (_hnu : 0 < nu)
        (P : ProbabilityMeasure (ShellSeq d)) (hPrefix : ShellLawPrefix d P)
        (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (_hJ4 : ShellLawJ4 d P)
        [_hInv : VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure]
        (cStar K : ℝ) (_hK : 0 ≤ K)
        (S : ScaleSelection) (_hSorder : ScalesOrdering S)
        (e : Vec d) (_he : vecNormSq e = 1) (hunit : Book.Ch02.vecNorm e = 1)
        (p : Vec d) (_hp : p = testVector nu S.LPrime P S.n e)
        (F : ShellSeq d → Vec d → Vec d)
        (_hF : ∀ omega : ShellSeq d, F omega = fun x =>
          matVecMul (streamCutoff omega S.LPrime x -
            streamCutoff omega S.ellPrime x) p)
        (gradHatW : ShellSeq d → Vec d)
        (wD : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
        (wN : ShellSeq d →
          H1MeanZeroFunction (openCubeSet (originCube d (S.m : ℤ))))
        (_hwD : ∀ omega : ShellSeq d,
          IsCubeDirichletResponse (originCube d (S.m : ℤ)) (F omega) (wD omega))
        (_hwN : ∀ omega : ShellSeq d,
          IsCubeNeumannResponse (originCube d (S.m : ℤ)) (F omega) (wN omega))
        (_hwDmeas : AEStronglyMeasurable
          (fun omega : ShellSeq d => vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (wD omega).toH1Function.grad) P.toMeasure)
        (hFmemLp : MemLp (fun omega : ShellSeq d =>
            HilbertVec.ofVec (F omega 0)) 2 P.toMeasure)
        (hGmemLp : MemLp (fun omega : ShellSeq d =>
            HilbertVec.ofVec (gradHatW omega)) 2 P.toMeasure)
        (_hproj : (hGmemLp.toLp fun omega : ShellSeq d =>
              HilbertVec.ofVec (gradHatW omega)) =
            -stationaryPotentialProjection (μ := P.toMeasure)
              (hFmemLp.toLp fun omega : ShellSeq d =>
                HilbertVec.ofVec (F omega 0)))
        (_hlow : ∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (wD omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure ≤
            ∫⁻ omega : ShellSeq d,
              ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure)
        (_hup : ∫⁻ omega : ShellSeq d,
              ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure ≤
            ∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (wN omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure)
        (E0 : ℝ) (_hE0 : E0 = (∫⁻ omega : ShellSeq d,
            ‖HilbertVec.ofVec (gradHatW omega)‖ₑ ^ (2 : ℕ) ∂P.toMeasure :
              ℝ≥0∞).toReal)
        (Y : ShellSeq d → ℝ) (_hY0 : ∀ omega, 0 ≤ Y omega)
        (_hYm : Measurable Y)
        (_hYbig : IsBigO P.toMeasure (gammaSigma 2) Y
          (Cgap * Book.Ch02.vecNorm p))
        (Z : ℕ → ShellSeq d → ℝ) (_hZm : ∀ r, Measurable (Z r))
        (_hZbig : ∀ r ∈ Finset.Icc S.m S.LPrime,
          IsBigO P.toMeasure (gammaSigma 2) (Z r)
            (Cav * Book.Ch02.vecNorm p))
        (_hZbound : ∀ (r : ℕ) (omega : ShellSeq d),
          Book.Ch02.vecNorm (shellFluxAverage (S.m : ℤ) omega r p) ≤ Z r omega)
        (_hbridge : ∀ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (fun x => (wN omega).toH1Function.grad x -
                (wD omega).toH1Function.grad x) ≤
            ENNReal.ofReal (Y omega + Book.Ch02.vecNorm
              (∑ r ∈ Finset.Icc S.m S.LPrime,
                shellFluxAverage (S.m : ℤ) omega r p)))
        (_hJ5app : |‖blockPotentialResponse P S.ellPrime S.LPrime
                (blockRegLaw_stationary hPrefix hJ2 S.ellPrime S.LPrime) e
                (memLp_originForcing_blockRegLaw hJ3 S.ellPrime S.LPrime e
                  hunit)‖ ^ 2 -
              cStar * Real.log 3 * ((S.LPrime - S.ellPrime : ℕ) : ℝ)| ≤ K),
        |(∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
              (wD omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure :
                ℝ≥0∞).toReal -
            cStar * Real.log 3 * ((S.m - S.n : ℕ) : ℝ) * vecNormSq p| ≤
          (C * (1 + ((S.LPrime - S.m : ℕ) : ℝ)) + K) * vecNormSq p := by
  refine ⟨lhsTerm1Const Cgap Cav, one_le_lhsTerm1Const Cgap Cav, ?_⟩
  intro nu hnu P hPrefix hJ2 hJ3 hJ4 hInv cStar K hK S hSorder e he hunit p hp F
    hF gradHatW wD wN hwD hwN hwDmeas hFmemLp hGmemLp hproj hlow hup E0 hE0 Y hY0
    hYm hYbig Z hZm hZbig hZbound hbridge hJ5app
  have : VAddInvariantMeasure (Vec d) (ShellSeq d) P.toMeasure := hInv
  -- the test vector `p = shom_{L',*}^{-1/2}(cu_n) e` is nonzero
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
  set t : ℝ := Book.Ch02.vecNorm p with htdef
  have hpsq : vecNormSq p = t ^ 2 := (vecNorm_sq_eq_vecNormSq p).symm
  have ht2 : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  set Q : ℝ := 1 + ((S.LPrime - S.m : ℕ) : ℝ) with hQdef
  have hQ1 : (1 : ℝ) ≤ Q := by
    have h0 : (0 : ℝ) ≤ ((S.LPrime - S.m : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [hQdef]
    linarith only [h0]
  have hQ0 : (0 : ℝ) ≤ Q := le_trans zero_le_one hQ1
  set G2 : ℝ := 1 + Real.Gamma 2 with hG2def
  have hG20 : (0 : ℝ) ≤ G2 := by
    have hg := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 2)
    rw [hG2def]
    linarith only [hg]
  -- `e.average.error.energy` and the summed display, squared
  have hApos : ∀ r ∈ Finset.Icc S.m S.LPrime, 0 < Cav * t :=
    fun _ _ => mul_pos hCav hpt
  have hgapB := lintegral_vecCubeLpENorm_sq_response_gap_le hJ2 hJ4 S.m
    (Finset.Icc S.m S.LPrime) p wD wN (Cgap * t) (mul_pos hCgap hpt) Y hY0 hYm
    hYbig (fun _ => Cav * t) hApos Z hZm hZbig hZbound hbridge
  -- the amplitude comparison
  have hcard : (Finset.Icc S.m S.LPrime).card = S.LPrime - S.m + 1 := by
    rw [Nat.card_Icc]
    have := hSorder.m_lt_LPrime
    omega
  have hsumconst : ∑ _r ∈ Finset.Icc S.m S.LPrime, (Cav * t) ^ 2 =
      Q * (Cav * t) ^ 2 := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul, hQdef]
    push_cast
    ring
  have hBle : 2 * ((Cgap * t) ^ 2 * G2) +
      2 * (G2 * ∑ _r ∈ Finset.Icc S.m S.LPrime, (Cav * t) ^ 2) ≤
      lhsTerm1Const Cgap Cav * Q * vecNormSq p := by
    have ha0 : (0 : ℝ) ≤ 2 * G2 * Cgap ^ 2 := by positivity
    have hb0 : (0 : ℝ) ≤ 2 * G2 * Cav ^ 2 := by positivity
    have hQt : t ^ 2 ≤ Q * t ^ 2 := le_mul_of_one_le_left ht2 hQ1
    have hQt0 : (0 : ℝ) ≤ Q * t ^ 2 := mul_nonneg hQ0 ht2
    have hmax : 2 * G2 * Cgap ^ 2 + 2 * G2 * Cav ^ 2 ≤ lhsTerm1Const Cgap Cav := by
      have h := le_max_right (1 : ℝ) (2 * (1 + Real.Gamma 2) * (Cgap ^ 2 + Cav ^ 2))
      rw [lhsTerm1Const, hG2def]
      have hring : 2 * (1 + Real.Gamma 2) * Cgap ^ 2 +
          2 * (1 + Real.Gamma 2) * Cav ^ 2 =
          2 * (1 + Real.Gamma 2) * (Cgap ^ 2 + Cav ^ 2) := by ring
      rw [hring]
      exact h
    calc 2 * ((Cgap * t) ^ 2 * G2) +
        2 * (G2 * ∑ _r ∈ Finset.Icc S.m S.LPrime, (Cav * t) ^ 2)
        = 2 * G2 * Cgap ^ 2 * t ^ 2 + 2 * G2 * Cav ^ 2 * (Q * t ^ 2) := by
          rw [hsumconst]; ring
      _ ≤ 2 * G2 * Cgap ^ 2 * (Q * t ^ 2) + 2 * G2 * Cav ^ 2 * (Q * t ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left hQt ha0) le_rfl
      _ = (2 * G2 * Cgap ^ 2 + 2 * G2 * Cav ^ 2) * (Q * t ^ 2) := by ring
      _ ≤ lhsTerm1Const Cgap Cav * (Q * t ^ 2) :=
          mul_le_mul_of_nonneg_right hmax hQt0
      _ = lhsTerm1Const Cgap Cav * Q * vecNormSq p := by rw [hpsq]; ring
  have hBnn : (0 : ℝ) ≤ lhsTerm1Const Cgap Cav * Q * vecNormSq p := by
    have h1 : (0 : ℝ) ≤ lhsTerm1Const Cgap Cav :=
      le_trans zero_le_one (one_le_lhsTerm1Const Cgap Cav)
    have h2 : (0 : ℝ) ≤ vecNormSq p := vecNormSq_nonneg p
    positivity
  have hgapB' : ∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
      (fun x => (wN omega).toH1Function.grad x -
        (wD omega).toH1Function.grad x) ^ (2 : ℕ) ∂P.toMeasure ≤
      ENNReal.ofReal (lhsTerm1Const Cgap Cav * Q * vecNormSq p) :=
    hgapB.trans (ENNReal.ofReal_le_ofReal hBle)
  -- the energy gap display, written through `E0`
  have hEnergyGap := abs_toReal_sub_wholeSpaceEnergy_le hwD hwN hwDmeas hGmemLp
    hlow hup hBnn hgapB'
  have hE0eq : wholeSpaceEnergy P.toMeasure gradHatW = E0 := by
    rw [wholeSpaceEnergy]
    exact hE0.symm
  rw [hE0eq] at hEnergyGap
  -- `e.use.nondeg.ass`
  have hnm : S.ellPrime ≤ S.LPrime :=
    le_of_lt (lt_trans hSorder.ellPrime_lt_m hSorder.m_lt_LPrime)
  have hscale : ((S.LPrime - S.ellPrime : ℕ) : ℝ) = ((S.m - S.n : ℕ) : ℝ) := by
    rw [S.LPrime_sub_ellPrime_eq_m_sub_n]
  have hnondeg := abs_wholeSpaceEnergy_sub_cStar_mul_le hPrefix hJ2 hJ3 hnm e
    hunit he (sigmaBarStarInvSqrt nu S.LPrime P S.n) p hp' F hF gradHatW hFmemLp
    hGmemLp hproj hJ5app
  rw [hscale, hE0eq] at hnondeg
  have htri := abs_sub_le
    ((∫⁻ omega : ShellSeq d, vecCubeLpENorm (originCube d (S.m : ℤ)) 2
        (wD omega).toH1Function.grad ^ (2 : ℕ) ∂P.toMeasure : ℝ≥0∞).toReal)
    E0 (cStar * Real.log 3 * ((S.m - S.n : ℕ) : ℝ) * vecNormSq p)
  have hsplit : lhsTerm1Const Cgap Cav * Q * vecNormSq p + K * vecNormSq p =
      (lhsTerm1Const Cgap Cav * Q + K) * vecNormSq p := by ring
  rw [← hsplit]
  exact htri.trans (add_le_add hEnergyGap hnondeg)

end Assembly

end

end SuperdiffusionCLT.Section3.Setup
