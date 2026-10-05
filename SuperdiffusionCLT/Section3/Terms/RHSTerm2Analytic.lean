/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Terms.GluedFieldEnergyObservable
public import SuperdiffusionCLT.Section3.Terms.TranslatedBlocks
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2RField
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2LocDisplays
public import SuperdiffusionCLT.Frozen.Section3.WBasicRegbounds
public import SuperdiffusionCLT.Section3.Terms.RHSTerm2KmnBounds

/-!
# The non-localization residues of `l.RHS.term2`

The reduction of the conclusion
`SuperdiffusionCLT.Frozen.Section3.rhs_term2` to the localization clause
`hLocMin` plus three analytic hypotheses on the residual field

`R = (k_{L'} − k_ℓ)ᵗ ∇w`,

namely `hfinR`, `hRcanon` (the bounds on `R` and its weak gradient, at one fixed weak
gradient of `R`) and `hcube` (the comparison of the two annealed energies at the
nested cubes `cu_n ⊆ cu_m`).  This module attacks those three.

## The cube comparison `hcube`

The comparison is not an extra assumption: it is the stationarity step of the
paper ("stationarity gives the same bounds on `z + cu_n`").  The
squared normalized norm on `cu_m` is the plain average of the squared norms on
the `N = 3^{(m−n)d}` scale-`n` sub-cubes of `cu_m`
(`cubeLpENorm_two_sq_eq_inv_card_mul_sum`), and on each sub-cube `R` the glued
field is the *transported* glued field of the centred cube
(`vecCubeLpENorm_gluedGradientField_translate`), which the lattice translation
`ShellField.translateSequence (triadicCubeShift R)` carries back to the centred
cube `cu_n` (`vecCubeLpENorm_gluedGradientField_eq_cubeMaximizer`).  That
translation preserves the shell law (`ShellLawPrefix` + `ShellLawJ2`,
`measurePreserving_translateSequence`), so every one of the `N` sub-cube
expectations equals the same number `∫⁻ ‖∇u_k‖²_{L̲²(cu_n)}`, and the average of
`N` copies of it is itself.  So

`∫⁻ ‖∇u_k‖²_{L̲²(cu_n)} = ∫⁻ ‖∇u_k‖²_{L̲²(cu_m)}`

holds with **equality**, and `hcube` follows.  No hypothesis beyond the
binders (`d`, `[NeZero d]`, `hnu`, `hPrefix`, `hJ2`, `S`, `hSorder`) enters.

## The canonical weak gradient `hRcanon`

`hRcanon` asks for a single weak gradient `DR₀` of `i ↦ (M ∇w)_i` on `cu_m`
with three further clauses.  The lemma `exists_rfieldWeakJacobian` produces
exactly such a witness, `rfieldWeakJacobian S w H`, from a *named* weak Hessian
witness `H`; the two data clauses (weak gradient, `MemLp`) are discharged by
`rfieldWeakJacobian_hasWeakGradientOn` and `memLp_rfieldWeakJacobian`, and the
remaining three clauses are carried at the named witness.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open MeasureTheory
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.CoarseGraining
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section3.ResponseFields
open SuperdiffusionCLT.Section3.Setup
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section2.Norms
open Homogenization
open Homogenization.Book.Ch02
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## Scale bookkeeping -/

/-- The three strict inequalities of `e.scales.ordering` give `n ≤ m`. -/
theorem nm_of_scalesOrdering {S : ScaleSelection} (hSorder : ScalesOrdering S) :
    S.n ≤ S.m := by
  have h1 := hSorder.n_lt_ell
  have h2 := hSorder.ell_lt_ellPrime
  have h3 := hSorder.ellPrime_lt_m
  omega

/-! ## The cube comparison `hcube` -/

/-- **The transported cube norm on a sub-cube of the family.**  On a scale-`n`
sub-cube `R` of `cu_m` the squared normalized norm of the glued field is the
squared norm on the centred cube `cu_n` of the glued field read at the
translated shell sequence: the single maximizer on `R` is transported to the
maximizer of the centred cube, and the glued field agrees with the maximizer on
the half-open realization. -/
theorem vecCubeLpENorm_gluedGradientField_subcube_sq {nu : ℝ} (hnu : 0 < nu)
    {S : ScaleSelection} (hSorder : ScalesOrdering S) (F : Vec d)
    {R : TriadicCube d} (hR : R ∈ largeCubeSubcubes d S.n S.m) (omega : ShellSeq d) :
    vecCubeLpENorm R 2 (gluedGradientField hnu S.ell S.n S.m F omega) ^ (2 : ℕ) =
      vecCubeLpENorm (originCube d (S.n : ℤ)) 2
        (gluedGradientField hnu S.ell S.n S.m F
          (ShellField.translateSequence (triadicCubeShift R) omega)) ^ (2 : ℕ) := by
  have hnm : S.n ≤ S.m := nm_of_scalesOrdering hSorder
  rw [vecCubeLpENorm_gluedGradientField_translate hnu omega S.ell hnm F hR,
    vecCubeLpENorm_gluedGradientField_eq_cubeMaximizer hnu _ S.ell S.n S.m F
      (originCube_mem_largeCubeSubcubes hnm)]

variable [NeZero d]

/-- **The observables of the two nested cubes have the same annealed mean.**
The squared `cu_m` norm decomposes into the average of the squared norms on the
scale-`n` sub-cubes; each of those, by the transported-norm identity, is the
centred observable read at a lattice translate of the shell sequence; the
translate preserves the law, so all `N` summands integrate to the same number,
and the average of `N` copies of it is itself. -/
theorem lintegral_vecCubeLpENorm_gluedGradientField_cuM_eq_cuN {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    {S : ScaleSelection} (hSorder : ScalesOrdering S) (F : Vec d) :
    (∫⁻ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (gluedGradientField hnu S.ell S.n S.m F omega) ^ (2 : ℕ)
      ∂P.toMeasure) =
      ∫⁻ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.n : ℤ)) 2
          (gluedGradientField hnu S.ell S.n S.m F omega) ^ (2 : ℕ)
      ∂P.toMeasure := by
  set X : ShellSeq d → ℝ≥0∞ := fun omega : ShellSeq d =>
    vecCubeLpENorm (originCube d (S.n : ℤ)) 2
      (gluedGradientField hnu S.ell S.n S.m F omega) ^ (2 : ℕ) with hXdef
  have hnm : S.n ≤ S.m := nm_of_scalesOrdering hSorder
  have hXmeas : Measurable X := by
    rw [hXdef]
    exact measurable_vecCubeLpENorm_two_sq_gluedGradientField hnu le_rfl hnm S.ell F
  have hcardpos : (0 : ℝ) < ((largeCubeSubcubes d S.n S.m).card : ℝ) :=
    Nat.cast_pos.2 (Finset.card_pos.2 (largeCubeSubcubes_nonempty d S.n S.m))
  have hcancel : ENNReal.ofReal (((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹) *
      (((largeCubeSubcubes d S.n S.m).card : ℕ) : ℝ≥0∞) = 1 := by
    rw [← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (le_of_lt (inv_pos.2 hcardpos)),
      inv_mul_cancel₀ (ne_of_gt hcardpos), ENNReal.ofReal_one]
  have hsplit : ∀ omega : ShellSeq d,
      vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (gluedGradientField hnu S.ell S.n S.m F omega) ^ (2 : ℕ) =
        ENNReal.ofReal (((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹) *
          ∑ R ∈ largeCubeSubcubes d S.n S.m,
            vecCubeLpENorm R 2 (gluedGradientField hnu S.ell S.n S.m F omega) ^ (2 : ℕ) := by
    intro omega
    have h := cubeLpENorm_two_sq_eq_inv_card_mul_sum (Q := originCube d (S.m : ℤ))
      (S.m - S.n) (hilbertifyVecField (gluedGradientField hnu S.ell S.n S.m F omega))
    rw [show descendantsAtDepth (originCube d (S.m : ℤ)) (S.m - S.n) =
      largeCubeSubcubes d S.n S.m from rfl] at h
    exact h
  have hRmeas : ∀ R ∈ largeCubeSubcubes d S.n S.m, Measurable (fun omega : ShellSeq d =>
      vecCubeLpENorm R 2 (gluedGradientField hnu S.ell S.n S.m F omega) ^ (2 : ℕ)) := by
    intro R hR
    have heq : (fun omega : ShellSeq d =>
        vecCubeLpENorm R 2 (gluedGradientField hnu S.ell S.n S.m F omega) ^ (2 : ℕ)) =
        fun omega : ShellSeq d =>
          X (ShellField.translateSequence (triadicCubeShift R) omega) := by
      funext omega
      rw [hXdef]
      exact vecCubeLpENorm_gluedGradientField_subcube_sq hnu hSorder F hR omega
    rw [heq]
    exact hXmeas.comp (ShellField.measurable_translateSequence (triadicCubeShift R))
  have hInt : ∀ R ∈ largeCubeSubcubes d S.n S.m,
      (∫⁻ omega : ShellSeq d,
          vecCubeLpENorm R 2 (gluedGradientField hnu S.ell S.n S.m F omega) ^ (2 : ℕ)
        ∂P.toMeasure) = ∫⁻ omega : ShellSeq d, X omega ∂P.toMeasure := by
    intro R hR
    calc ∫⁻ omega : ShellSeq d,
          vecCubeLpENorm R 2 (gluedGradientField hnu S.ell S.n S.m F omega) ^ (2 : ℕ)
          ∂P.toMeasure
        = ∫⁻ omega : ShellSeq d,
            X (ShellField.translateSequence (triadicCubeShift R) omega) ∂P.toMeasure := by
          refine lintegral_congr fun omega => ?_
          rw [hXdef]
          exact vecCubeLpENorm_gluedGradientField_subcube_sq hnu hSorder F hR omega
      _ = ∫⁻ omega : ShellSeq d, X omega ∂P.toMeasure :=
          (measurePreserving_translateSequence hPrefix hJ2
            (triadicCubeShift R)).lintegral_comp hXmeas
  calc (∫⁻ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.m : ℤ)) 2
          (gluedGradientField hnu S.ell S.n S.m F omega) ^ (2 : ℕ)
      ∂P.toMeasure)
      = ∫⁻ omega : ShellSeq d,
          ENNReal.ofReal (((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹) *
            ∑ R ∈ largeCubeSubcubes d S.n S.m,
              vecCubeLpENorm R 2 (gluedGradientField hnu S.ell S.n S.m F omega) ^ (2 : ℕ)
          ∂P.toMeasure := lintegral_congr hsplit
    _ = ENNReal.ofReal (((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹) *
          ∫⁻ omega : ShellSeq d,
            ∑ R ∈ largeCubeSubcubes d S.n S.m,
              vecCubeLpENorm R 2 (gluedGradientField hnu S.ell S.n S.m F omega) ^ (2 : ℕ)
          ∂P.toMeasure := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹) *
          ∑ R ∈ largeCubeSubcubes d S.n S.m,
            ∫⁻ omega : ShellSeq d,
              vecCubeLpENorm R 2 (gluedGradientField hnu S.ell S.n S.m F omega) ^ (2 : ℕ)
            ∂P.toMeasure := by
          refine congrArg (fun s => ENNReal.ofReal
            (((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹) * s) ?_
          exact lintegral_finsetSum _ (fun R hR => hRmeas R hR)
    _ = ENNReal.ofReal (((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹) *
          ∑ _R ∈ largeCubeSubcubes d S.n S.m,
            ∫⁻ omega : ShellSeq d, X omega ∂P.toMeasure := by
          refine congrArg (fun s => ENNReal.ofReal
            (((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹) * s) ?_
          exact Finset.sum_congr rfl (fun R hR => hInt R hR)
    _ = ENNReal.ofReal (((largeCubeSubcubes d S.n S.m).card : ℝ)⁻¹) *
          ((((largeCubeSubcubes d S.n S.m).card : ℕ) : ℝ≥0∞) *
            ∫⁻ omega : ShellSeq d, X omega ∂P.toMeasure) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∫⁻ omega : ShellSeq d, X omega ∂P.toMeasure := by
          rw [← mul_assoc, hcancel, one_mul]
    _ = ∫⁻ omega : ShellSeq d,
        vecCubeLpENorm (originCube d (S.n : ℤ)) 2
          (gluedGradientField hnu S.ell S.n S.m F omega) ^ (2 : ℕ)
      ∂P.toMeasure := by rw [hXdef]

/-- **`hcube` of the term-2 reduction holds with equality.**  The annealed squared
`L̲²(cu_n)` energy of the cutoff-`ℓ` glued field is at most the annealed squared
`L̲²(cu_m)` energy — indeed equal to it — with no hypothesis beyond the
standing data and the two shell laws `ShellLawPrefix` and `ShellLawJ2` that
carry the lattice stationarity of the shell sequence. -/
theorem hcube_of_stationarity {nu : ℝ} (hnu : 0 < nu)
    {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P)
    {S : ScaleSelection} (hSorder : ScalesOrdering S) (F : Vec d) :
    (∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.n : ℤ)) 2
            (fun x => gluedGradientField hnu S.ell S.n S.m F omega x) ^ (2 : ℕ)
        ∂P.toMeasure : ℝ≥0∞).toReal ≤
      (∫⁻ omega : ShellSeq d,
          vecCubeLpENorm (originCube d (S.m : ℤ)) 2
            (fun x => gluedGradientField hnu S.ell S.n S.m F omega x) ^ (2 : ℕ)
        ∂P.toMeasure : ℝ≥0∞).toReal :=
  le_of_eq (congrArg ENNReal.toReal
    (lintegral_vecCubeLpENorm_gluedGradientField_cuM_eq_cuN hnu hPrefix hJ2 hSorder F).symm)

/-! ## The canonical weak gradient `hRcanon` -/

/-- **The canonical weak-Hessian witness of the Dirichlet response.**  Chosen
sample by sample from the divergence-form endpoint
`exists_hasWeakHessianOn_of_isDirichletResponse`, so that the weak Jacobian of
`R` below is a *nameable* function: the three clauses of `hRcanon` are carried at
this witness, which the fixed-constant chain can consume by unfolding. -/
noncomputable def rfieldHessianWitness (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (S : ScaleSelection) (hSorder : ScalesOrdering S) (p : Vec d)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega)) :
    ∀ omega : ShellSeq d,
      HasWeakHessianOn (openCubeSet (originCube d (S.m : ℤ))) (w omega).toH1Function :=
  fun omega => Classical.choice (exists_hasWeakHessianOn_of_isDirichletResponse hd omega
    (ellPrime_le_LPrime_of_scalesOrdering hSorder) p (w omega) (hw omega))

/-- **The canonical weak Jacobian of `R = (k_{L'} − k_ℓ) ∇w`.**  The
`rfieldWeakJacobian` at the named weak-Hessian witness: weak gradient and `L²`
membership of this field are *theorems*, not residues. -/
noncomputable def canonicalRJacobian (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (S : ScaleSelection) (hSorder : ScalesOrdering S) (p : Vec d)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega)) :
    ShellSeq d → Fin d → Vec d → Vec d :=
  rfieldWeakJacobian S w (rfieldHessianWitness d hd S hSorder p w hw)

/-- **The weak-gradient conjunct and the `L²` conjunct of `hRcanon`, discharged.**
At the named witness `canonicalRJacobian`, both are instances of
`rfieldWeakJacobian_hasWeakGradientOn` and `memLp_rfieldWeakJacobian`. -/
theorem canonicalRJacobian_hasWeakGradientOn (d : ℕ) [NeZero d] (hd : 2 ≤ d) (nu : ℝ)
    (S : ScaleSelection) (hSorder : ScalesOrdering S) (p : Vec d)
    (w : ShellSeq d → H10Function (openCubeSet (originCube d (S.m : ℤ))))
    (hw : ∀ omega : ShellSeq d,
      IsDirichletResponse omega S.LPrime S.ellPrime S.m p (w omega)) :
    (∀ (omega : ShellSeq d) (i : Fin d),
        HasWeakGradientOn (openCubeSet (originCube d (S.m : ℤ)))
          (fun x => (matVecMul ((coefficientCutoff nu omega S.LPrime).toCoeffField x -
                (coefficientCutoff nu omega S.ell).toCoeffField x)
              ((w omega).toH1Function.grad x)) i)
          (canonicalRJacobian d hd S hSorder p w hw omega i)) ∧
      (∀ omega : ShellSeq d,
        MemLp (fun x => HilbertMat.ofMat
            (fun i j => canonicalRJacobian d hd S hSorder p w hw omega i x j)) 2
          (volume.restrict (openCubeSet (originCube d (S.m : ℤ))))) :=
  ⟨rfieldWeakJacobian_hasWeakGradientOn nu S hSorder w
      (rfieldHessianWitness d hd S hSorder p w hw),
    fun omega => memLp_rfieldWeakJacobian S hSorder w
      (rfieldHessianWitness d hd S hSorder p w hw) omega⟩

/-! ## The finiteness `hfinR` -/

end

end SuperdiffusionCLT.Section3.Terms
