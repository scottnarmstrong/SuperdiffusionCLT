/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section6.Root.CenteredRecenteredBridge
public import SuperdiffusionCLT.Section6.Prereq.FullFieldGrad
public import SuperdiffusionCLT.Section6.Prereq.HarmonicApproxB

/-!
# Ellipticity of the full centered field on cubes

Almost surely the translated centered field `x ↦ ν Id + centeredStreamField ω cu_m (z + x)` is
elliptic on every cube `cu_n`: it is continuous (the recentered stream is, and the two differ by a
constant skew matrix), hence entrywise bounded on the bounded cube, and its symmetric part is
`ν Id`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section6

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Carriers

noncomputable section

variable {d : ℕ}

/-- A continuous matrix-valued map has entrywise bounded values on a bounded set. -/
theorem l9_entry_bound {F : Vec d → Mat d} (hF : Continuous F) {S : Set (Vec d)}
    (hS : Bornology.IsBounded S) : ∃ C : ℝ, ∀ x ∈ S, ∀ i j : Fin d, |F x i j| ≤ C := by
  set g : Vec d → ℝ := fun x => ∑ i : Fin d, ∑ j : Fin d, |F x i j| with hg
  have hcont : Continuous g := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact continuous_abs.comp ((continuous_apply j).comp ((continuous_apply i).comp hF))
  obtain ⟨C, hC⟩ := hS.isCompact_closure.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨C, fun x hx i j => ?_⟩
  have hle : ‖g x‖ ≤ C := hC x (subset_closure hx)
  rw [Real.norm_eq_abs] at hle
  have hsingle : |F x i j| ≤ g x := by
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun i' : Fin d => ∑ j' : Fin d, |F x i' j'|)
      (fun i' _ => Finset.sum_nonneg fun j' _ => abs_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j' : Fin d => |F x i j'|)
      (fun j' _ => abs_nonneg _) (Finset.mem_univ j)
  exact hsingle.trans ((le_abs_self (g x)).trans hle)

/-- The translated full centered field is elliptic on the cube, on the almost-sure event of
continuity of the recentered stream and summability of the derivative series. -/
theorem l9_exists_ell_centered [NeZero d] {omega : ShellSeq d}
    (hguard : ∀ i : ℕ, Summable fun k : ℕ =>
      shellDerivLinftyNorm (openCubeSet (originCube d (i : ℤ))) (omega k))
    (hcont : Continuous (fullStreamRecentered omega)) {nu : ℝ} (hnu : 0 < nu) (m n : ℕ)
    (z : Vec d) :
    ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (cubeSet (originCube d (n : ℤ)))
      (fun x => nu • (1 : Mat d) +
        centeredStreamField omega (cubeSet (originCube d (m : ℤ))) (z + x)) := by
  classical
  obtain ⟨K, -, hK⟩ := centered_eq_recentered_add_skew omega hguard nu m
  have hfield : (fun x => nu • (1 : Mat d) +
      centeredStreamField omega (cubeSet (originCube d (m : ℤ))) (z + x)) =
      fun x => fullCoefficientRecentered nu omega (z + x) + K := funext fun x => hK (z + x)
  have hc : Continuous fun x : Vec d => nu • (1 : Mat d) +
      centeredStreamField omega (cubeSet (originCube d (m : ℤ))) (z + x) := by
    rw [hfield]
    exact ((continuous_fullCoefficientRecentered hcont).comp (continuous_const_add z)).add
      continuous_const
  obtain ⟨C, hC⟩ := l9_entry_bound hc (isBounded_cubeSet (originCube d (n : ℤ)))
  refine ⟨nu, ((d : ℝ) * (d : ℝ) * C ^ 2 + nu ^ 2) / nu, ?_, fun x hx => ?_⟩
  · refine measurable_matrix_of_entries fun i j => Measurable.ite (measurableSet_cubeSet _) ?_
      measurable_const
    exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hc.measurable)
  · exact SuperdiffusionCLT.Section2.CoarseGraining.isEllipticMatrix_of_symmPart_eq_smul_one
      hnu (HarmonicApprox.symmPart_centeredStreamField_add nu omega _ _) (fun i j => hC x hx i j)

/-- Almost sure form: for every `m`, `n` and translation `z`. -/
theorem l9_ae_exists_ell_centered [NeZero d] {P : ProbabilityMeasure (ShellSeq d)}
    (hJ3 : ShellLawJ3 d P) {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂P.toMeasure, ∀ (m n : ℕ) (z : Vec d),
      ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (cubeSet (originCube d (n : ℤ)))
        (fun x => nu • (1 : Mat d) +
          centeredStreamField omega (cubeSet (originCube d (m : ℤ))) (z + x)) := by
  filter_upwards [ae_forall_summable_shellDerivLinftyNorm_originCube hJ3,
    ae_continuous_fullStreamRecentered hJ3] with omega hg hc m n z
  exact l9_exists_ell_centered hg hc hnu m n z

/-- Witness: the Dirac zero law meets `J3`, so the almost-sure ellipticity is non-vacuous. -/
example [NeZero d] {nu : ℝ} (hnu : 0 < nu) :
    ∀ᵐ omega : ShellSeq d ∂(SuperdiffusionCLT.Assumptions.ShellLaw.diracZeroLaw d).toMeasure,
      ∀ (m n : ℕ) (z : Vec d),
      ∃ lam Lam : ℝ, IsEllipticFieldOn lam Lam (cubeSet (originCube d (n : ℤ)))
        (fun x => nu • (1 : Mat d) +
          centeredStreamField omega (cubeSet (originCube d (m : ℤ))) (z + x)) :=
  l9_ae_exists_ell_centered
    SuperdiffusionCLT.Assumptions.ShellLaw.shellLawJ3_diracZeroLaw hnu

/-- Positivity of the ellipticity constants on a nonempty cube. -/
theorem l9_ell_pos [NeZero d] {lam Lam : ℝ} {a : CoeffField d} (n : ℤ)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet (originCube d n)) a) : 0 < lam ∧ lam ≤ Lam := by
  obtain ⟨x0, hx0⟩ := Book.Ch02.openCubeSet_nonempty (originCube d n)
  have h := hEll.2 x0 (openCubeSet_subset_cubeSet _ hx0)
  exact ⟨h.1, h.2.1⟩

end

end SuperdiffusionCLT.Section6
