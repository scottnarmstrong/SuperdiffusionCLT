/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.BoundaryC

/-!
# De Giorgi `L^∞–L²` bound up to the boundary of an arbitrary bounded open set

For `w ∈ H¹₀(U)` solving `-∇·(a∇w) = f - ∇·g` in `U`, with no regularity of `∂U`, the zero
extension of `w` to a cube `Q` satisfies the level identity of `boundary_level_identity` for the
coefficient extended by `λ Id` and the data extended by zero, so the iteration
`deGiorgi_eLpNorm_bound` applies to the zero extension.
-/

@[expose] public section

open Homogenization MeasureTheory
open scoped ENNReal

namespace SuperdiffusionCLT.Section7

variable {d : ℕ}

theorem eLpNorm_indicator_restrict_inter {U Q : Set (Vec d)} (hU : MeasurableSet U)
    {F : Vec d → ℝ} (p : ℝ≥0∞) :
    eLpNorm (U.indicator F) p (volume.restrict Q) = eLpNorm F p (volume.restrict (U ∩ Q)) := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hU, Measure.restrict_restrict hU]

theorem isEllipticFieldOn_boundaryCoeff {lam Lam : ℝ} {U Q : Set (Vec d)} {a : CoeffField d}
    (hU : MeasurableSet U) (hQ : MeasurableSet Q) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (h : IsEllipticFieldOn lam Lam U a) :
    IsEllipticFieldOn lam Lam Q (boundaryCoeff U (scalarMatrix lam) a) := by
  classical
  refine ⟨?_, fun x _ => ?_⟩
  · have h1 := h.1
    have hc : Measurable (fun (x : Vec d) (i j : Fin d) =>
        if x ∈ U then (0 : ℝ) else (scalarMatrix (d := d) lam) i j) :=
      measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
        Measurable.ite hU measurable_const measurable_const
    have heq : (fun (x : Vec d) (i j : Fin d) =>
        if x ∈ Q then boundaryCoeff U (scalarMatrix lam) a x i j else 0) =
        fun x => if x ∈ Q then (fun i j =>
          (if x ∈ U then a x i j else 0) + (if x ∈ U then (0 : ℝ) else
            (scalarMatrix (d := d) lam) i j)) else 0 := by
      funext x i j
      by_cases hxQ : x ∈ Q <;> by_cases hxU : x ∈ U <;> simp [boundaryCoeff, hxQ, hxU]
    rw [heq]
    exact Measurable.ite hQ (h1.add hc) measurable_const
  · by_cases hx : x ∈ U
    · simpa [boundaryCoeff, hx] using h.2 x hx
    · simpa [boundaryCoeff, hx] using
        (isEllipticMatrix_scalarMatrix (d := d) hlam).mono hlam le_rfl hlamLam

/-- **De Giorgi `L^∞–L²` bound up to the boundary of a bounded open set**, with no boundary
regularity: for `w ∈ H¹₀(U)` solving `-∇·(a∇w) = f - ∇·g` in `U`,
`sup_{U ∩ Q/2} w₊ ≤ C (Λ/λ)^N (L^{-d/2} ‖w₊‖_{L²(U ∩ Q)} + L²/λ ‖f‖_∞ + L/λ ‖g‖_∞)`,
with `N = deGiorgiPower d` and all norms over `U ∩ Q`. -/
theorem deGiorgi_boundary_bound (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {lam Lam : ℝ} {a : CoeffField d} {U : Set (Vec d)}, IsOpen U → IsBoundedDomain U →
      IsEllipticFieldOn lam Lam U a →
      ∀ (z : Vec d) {L : ℝ}, 0 < L → ∀ (f : Vec d → ℝ) (g : Vec d → Vec d),
        AEStronglyMeasurable g (volume.restrict (U ∩ axisCube z L)) →
        ∀ (w : H10Function U),
          IsWeakSolutionOn a U w.toH1Function f g →
          eLpNorm (fun x => max (w.toH1Function.toFun x) 0) ⊤
              (volume.restrict (U ∩ halfCube z L)) ≤
            ENNReal.ofReal (C * (Lam / lam) ^ deGiorgiPower d) *
              (ENNReal.ofReal (L ^ (-(d : ℝ) / 2)) *
                  eLpNorm (fun x => max (w.toH1Function.toFun x) 0) 2
                    (volume.restrict (U ∩ axisCube z L)) +
                ENNReal.ofReal (L ^ 2 / lam) * eLpNorm f ⊤ (volume.restrict (U ∩ axisCube z L)) +
                ENNReal.ofReal (L / lam) *
                  eLpNorm (fun x => eucNorm (g x)) ⊤ (volume.restrict (U ∩ axisCube z L))) := by
  classical
  obtain ⟨C, hC, hmain⟩ := deGiorgi_eLpNorm_bound hd
  refine ⟨C, hC, ?_⟩
  intro lam Lam a U hUo hUb hEll z L hL f g hgm w hw
  rcases U.eq_empty_or_nonempty with hU0 | ⟨x0, hx0⟩
  · subst hU0
    simp
  have hUm := hUo.measurableSet
  have hQo : IsOpen (axisCube z L) := isOpen_axisCube z L
  have hfin : volume U ≠ ⊤ := by simpa using hUb.isFiniteMeasure_restrict_volume.measure_univ_lt_top.ne
  obtain ⟨hlam, hlamLam, -, -⟩ := hEll.2 x0 hx0
  have hEll' := isEllipticFieldOn_boundaryCoeff hUm hQo.measurableSet hlam hlamLam hEll
  set W := zeroExtCube hUo hQo w with hW
  have hgm' : AEStronglyMeasurable (U.indicator g) (volume.restrict (axisCube z L)) := by
    rw [aestronglyMeasurable_indicator_iff hUm, Measure.restrict_restrict hUm]
    exact hgm
  have key := hmain z hL hEll' W (U.indicator f) (U.indicator g) hgm'
    (fun k hk _ hη hηc hηs => boundary_level_identity hUo hfin hQo w _ (scalarMatrix lam) f g hw
      hk hη hηc hηs)
  have hmaxW : (fun x => max (W.toFun x) 0) = U.indicator (fun x => max (w.toH1Function.toFun x) 0) := by
    funext x
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx, hW, zeroExtCube_toFun, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hW, zeroExtCube_toFun, Set.indicator_of_notMem hx]
      simp
  have hnormg : (fun x => eucNorm (U.indicator g x)) = U.indicator (fun x => eucNorm (g x)) := by
    funext x
    by_cases hx : x ∈ U
    · simp only [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx, eucNorm, vecNormSq, vecDot]
  rw [hmaxW, hnormg] at key
  simp only [eLpNorm_indicator_restrict_inter hUm] at key
  exact key

/-! ### Satisfiability witness

The zero solution in `H¹₀` of the unit square, with identity coefficients and zero data, meets
every non-law hypothesis of `deGiorgi_boundary_bound`. -/

/-- The zero function as an `H¹₀` function on the unit square. -/
noncomputable def witnessZeroH10 : H10Function (axisCube (0 : Vec 2) 1) :=
  H10Function.ofContDiff (U := axisCube (0 : Vec 2) 1) (isOpen_axisCube _ _)
    (f := fun _ => (0 : ℝ)) contDiff_const HasCompactSupport.zero (by simp)

theorem witnessZeroH10_weak :
    IsWeakSolutionOn (fun _ => (1 : Mat 2)) (axisCube (0 : Vec 2) 1)
      witnessZeroH10.toH1Function (fun _ => 0) (fun _ => 0) := by
  intro φ
  have : witnessZeroH10.toH1Function.grad = fun _ => 0 := by
    funext x i
    simp [witnessZeroH10, H10Function.ofContDiff, H1Function.ofContDiff]
  simp [this, vecDot, matVecMul]

example : True := by
  obtain ⟨C, -, hmain⟩ := deGiorgi_boundary_bound (d := 2) le_rfl
  have := hmain (lam := 1) (Lam := 1) (a := fun _ => (1 : Mat 2))
    (isOpen_axisCube (0 : Vec 2) 1)
    (isOpenBoundedConvexDomain_axisCube (0 : Vec 2) 1).isBoundedDomain
    witness_ellipticField (0 : Vec 2) one_pos (fun _ => 0) (fun _ => 0) aestronglyMeasurable_const
    witnessZeroH10 witnessZeroH10_weak
  trivial

end SuperdiffusionCLT.Section7
