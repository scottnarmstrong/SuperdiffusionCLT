/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageT1Inputs
public import SuperdiffusionCLT.Section2.Localization.LocalizationAverageAssembly
public import SuperdiffusionCLT.Section2.Annealed.Integrability
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinftyLargeCube
public import SuperdiffusionCLT.Assumptions.ShellField.J3Observable

/-!
# The last printed per-cube display of `T_2`, and the mechanical side conditions

The localization-average assembly carries, besides the printed per-cube inequality, a handful
of side conditions on the carriers.  This module proves the mechanical ones
and isolates the one printed display that is not obtained directly from the
existing results.

## The printed weight bound (`W_z`)

The printed proof bounds the
weight

```
W_z = |bfE_ℓ^{1/2} G_{-h_z} P|^2
```

by combining the deterministic envelope bound of `e.Enaught.mixing`,
`|bfE_ℓ| ≤ Cν⁻¹(1∨ℓ)`, with the gauge-vector bound
`|G_{-h_z}P|^2 ≤ C(1 + |h_z|^2)|P|^2` obtained from `e.jk.spatialavg` and
Proposition `p.concentration` (`|h_z|^2 ≤ O_{Γ_1}(C(L-ℓ))`).
The envelope half is proved
(`envelopeBlockMat` and `blockMatrixOperatorNorm_envelopeBlockMat_le`) but
the gauge-vector half is **not**, so `W_z = O_{Γ_1}(C ν⁻¹(1∨ℓ)(1∨L)|P|²)` is
reduced here to that one printed input.

## The four mechanical side conditions, all proved

* `localizationB_nonneg`, `localizationB_nonneg_on_grid` (the `hBdnn` input) —
  the positive semidefiniteness of the cutoff-`ℓ` coarse block matrix,
  `zero_le_blockVecDot_coarseBlockMatrix_coefficientCutoff`.
* `localizationB_measurable`, `localizationB_measurable_on_grid` (the `hBdmeas`
  input) — entrywise measurability of `bfA_ℓ(z+cu_n)` composed into the
  quadratic form against the gauge vector.
* `localizationPerturbSize_measurable`, `localizationDz_measurable`,
  `localizationDz_measurable_on_grid` (the `hDdmeas` input) — measurability of
  the `sSup`-based `L∞` carrier `D_z`.
* `localizationT1Carrier_measurable` (the `hT1m` input) — measurability of the
  averaged product `T₁`.

## The mechanics: `sSup`-measurability of the `L∞` carrier `D_z`

`D_z` carries the sup over the half-open cube `R = z + cu_n`.  The increment is
continuous in the space variable and the half-open cube sits in the closure of
its open realization, so the sup is unchanged when the index set is cut to the
intersection of the cube with a countable dense set; the countable sup is a
`⨆` over a countable index type, hence measurable.  This is the technique of
`SuperdiffusionCLT.Section3.HighContrast.measurable_finiteShellIncrementLinftyNormLargeCube_of_coords`,
adapted to the half-open cube.

`cd`, `KY`, `CR`, `Cw`, `K` enter only as named positive constants.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section2.Localization

open MeasureTheory Homogenization Homogenization.Book.Ch02
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Carriers
open SuperdiffusionCLT.Section2.Cutoff
open Set

variable {d : ℕ}

/-! ## `hBdnn`: the coarse block matrix is positive semidefinite -/

/-- **The `hBdnn` input at the carrier `localizationB`**: `B_z = |bfA_ℓ^{1/2}(z+cu_n)
G_{-h_z}P|² ≥ 0`.  The quadratic form of the cutoff-`ℓ` coarse block matrix is
nonnegative because that matrix is positive semidefinite
(`zero_le_blockVecDot_coarseBlockMatrix_coefficientCutoff`, itself the
form of `e.CG.bounds.2`).  The printed carrier `B_z` is the quadratic form of
the coarse matrix against the gauge vector, and the gauge acts by a linear map,
so positivity transfers with no hypothesis beyond `0 < ν`. -/
theorem localizationB_nonneg [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (l L : ℕ) (R : TriadicCube d) (Pvec : BlockVec d) (omega : ShellSeq d) :
    0 ≤ localizationB nu l L R Pvec omega := by
  unfold localizationB localizationCoarseAt
  exact zero_le_blockVecDot_coarseBlockMatrix_coefficientCutoff (hnu := hnu) (omega := omega)
    (m := l) (Q := R) (localizationGaugeVector l L R Pvec omega)

/-- **The `hBdnn` input on the descendant grid**, in the form the `T₁`
estimate consumes. -/
theorem localizationB_nonneg_on_grid [NeZero d] {nu : ℝ} (hnu : 0 < nu)
    (l L m n : ℕ) (Pvec : BlockVec d) :
    ∀ R ∈ localizationAverageGrid d m n, ∀ omega : ShellSeq d,
      0 ≤ localizationB nu l L R Pvec omega :=
  fun R _ omega => localizationB_nonneg hnu l L R Pvec omega

/-! ## `hBdmeas`: measurability of `B_z` -/

/-- Entrywise measurability of the coarse block matrix at the cutoff, in the
translated form this file needs. -/
theorem measurable_blockMatEntry_localizationCoarseAt {nu : ℝ} (hnu : 0 < nu)
    (l : ℕ) (R : TriadicCube d) :
    ∀ α β : BlockCoord d,
      Measurable (fun omega : ShellSeq d =>
        blockMatEntry (localizationCoarseAt nu l R omega) α β) := by
  intro α β
  have hul := measurable_coarseBlockMatrix_upperLeft_apply
    (A := fun omega : ShellSeq d => coefficientCutoff nu omega l)
    (measurable_coefficientCutoff nu l)
    (fun omega => aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega l) R
  have hur := measurable_coarseBlockMatrix_upperRight_apply
    (A := fun omega : ShellSeq d => coefficientCutoff nu omega l)
    (measurable_coefficientCutoff nu l)
    (fun omega => aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega l) R
  have hll := measurable_coarseBlockMatrix_lowerLeft_apply
    (A := fun omega : ShellSeq d => coefficientCutoff nu omega l)
    (measurable_coefficientCutoff nu l)
    (fun omega => aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega l) R
  have hlr := measurable_coarseBlockMatrix_lowerRight_apply
    (A := fun omega : ShellSeq d => coefficientCutoff nu omega l)
    (measurable_coefficientCutoff nu l)
    (fun omega => aeLocallyUniformlyEllipticField_coefficientCutoff hnu omega l) R
  unfold localizationCoarseAt
  cases α with
  | inl i =>
      cases β with
      | inl j => exact hul i j
      | inr j => exact hur i j
  | inr i =>
      cases β with
      | inl j => exact hll i j
      | inr j => exact hlr i j

/-- Measurability of a quadratic form `X · M X` with both `M` and `X`
`omega`-dependent and entrywise measurable. -/
theorem measurable_blockVecDot_blockMatVecMul_of_entries {M : ShellSeq d → BlockMat d}
    (hM : ∀ α β : BlockCoord d, Measurable (fun omega => blockMatEntry (M omega) α β))
    {X : ShellSeq d → BlockVec d}
    (hX1 : ∀ i, Measurable (fun omega => (X omega).1 i))
    (hX2 : ∀ i, Measurable (fun omega => (X omega).2 i)) :
    Measurable (fun omega => blockVecDot (X omega) (blockMatVecMul (M omega) (X omega))) := by
  have hul : ∀ i j, Measurable (fun omega => (M omega).upperLeft i j) :=
    fun i j => by simpa only [blockMatEntry] using hM (Sum.inl i) (Sum.inl j)
  have hur : ∀ i j, Measurable (fun omega => (M omega).upperRight i j) :=
    fun i j => by simpa only [blockMatEntry] using hM (Sum.inl i) (Sum.inr j)
  have hll : ∀ i j, Measurable (fun omega => (M omega).lowerLeft i j) :=
    fun i j => by simpa only [blockMatEntry] using hM (Sum.inr i) (Sum.inl j)
  have hlr : ∀ i j, Measurable (fun omega => (M omega).lowerRight i j) :=
    fun i j => by simpa only [blockMatEntry] using hM (Sum.inr i) (Sum.inr j)
  simp only [blockVecDot, blockMatVecMul, vecDot]
  refine Measurable.add ?_ ?_
  · refine Finset.measurable_sum _ fun i _ => ?_
    refine hX1 i |>.mul ?_
    exact (Finset.measurable_sum _ fun j _ => (hul i j).mul (hX1 j)).add
      (Finset.measurable_sum _ fun j _ => (hur i j).mul (hX2 j))
  · refine Finset.measurable_sum _ fun i _ => ?_
    refine hX2 i |>.mul ?_
    exact (Finset.measurable_sum _ fun j _ => (hll i j).mul (hX1 j)).add
      (Finset.measurable_sum _ fun j _ => (hlr i j).mul (hX2 j))

/-- **The `hBdmeas` input at the carrier `localizationB`**: `B_z` is measurable in the
shell sequence.  This is the entrywise measurability of `bfA_ℓ(z+cu_n)`
(`measurable_coarseBlockMatrix_..._apply`, the same source as
the measurability of `localizationY`) composed with the measurability of the gauge vector
`measurable_localizationGaugeVector_entry`. -/
theorem localizationB_measurable {nu : ℝ} (hnu : 0 < nu)
    (l L : ℕ) (R : TriadicCube d) (Pvec : BlockVec d) :
    Measurable (fun omega : ShellSeq d => localizationB nu l L R Pvec omega) := by
  have hX := measurable_localizationGaugeVector_entry l L R Pvec
  unfold localizationB
  exact measurable_blockVecDot_blockMatVecMul_of_entries
    (measurable_blockMatEntry_localizationCoarseAt hnu l R) hX.1 hX.2

/-- **The `hBdmeas` input on the descendant grid.** -/
theorem localizationB_measurable_on_grid {nu : ℝ} (hnu : 0 < nu)
    (l L m n : ℕ) (Pvec : BlockVec d) :
    ∀ R ∈ localizationAverageGrid d m n,
      Measurable (fun omega : ShellSeq d => localizationB nu l L R Pvec omega) :=
  fun R _ => localizationB_measurable hnu l L R Pvec

/-! ## `hDdmeas`: measurability of the `L∞` carrier `D_z`

`D_z = ν⁻¹‖k_L − k_ℓ − h_z‖ + ν⁻²‖·‖²` is carried by `localizationPerturbSize`,
the uncountable supremum over `Option {x // x ∈ cubeSet R}` of the perturbation
size at `x`.  The increment is continuous in the space variable, so the
supremum is unchanged when the index set is cut down to the intersection of the
cube with a countable dense set, and the resulting countable supremum is a `⨆`
over a countable index type.

The half-open `cubeSet` is not open, so the countable subset is taken inside the
*open* realization and the half-open cube is reached through
`cubeSet_subset_closure_openCubeSet`: a far-face point is a limit of interior
points, and continuity of the increment carries its value along. -/

/-- The perturbation size at a fixed space point,
`‖k_L − k_ℓ − h_z‖` evaluated at `x`.  This is the function whose supremum over
the cube is `localizationPerturbSize`. -/
private noncomputable def pertLinfty (l L : ℕ) (R : TriadicCube d)
    (omega : ShellSeq d) (x : Vec d) : ℝ :=
  matrixOperatorNorm (finiteShellIncrement omega l L x - localizationGaugeAverage l L R omega)

/-- Pointwise measurability of the perturbation size in the shell sequence. -/
private theorem measurable_pertLinfty_apply (l L : ℕ) (R : TriadicCube d) (x : Vec d) :
    Measurable (fun omega : ShellSeq d => pertLinfty l L R omega x) := by
  have hAvg : Measurable (fun omega : ShellSeq d => localizationGaugeAverage l L R omega) :=
    measurable_volumeAverageMat_of_isBounded (isBounded_cubeSet R) (measurableSet_cubeSet R)
      (measurable_finiteShellIncrement l L)
  have hEvEnt : ∀ i k : Fin d,
      Measurable (fun omega : ShellSeq d => finiteShellIncrement omega l L x i k) := by
    intro i k
    have hrw : (fun omega : ShellSeq d => finiteShellIncrement omega l L x i k) =
        fun omega : ShellSeq d => ∑ r ∈ Finset.Ioc l L, omega r x i k := by
      funext omega
      exact finiteShellIncrement_apply_entry omega l L x i k
    rw [hrw]
    exact Finset.measurable_sum _ fun r _ =>
      (ShellField.measurable_eval_entry x i k).comp (measurable_pi_apply r)
  have hAvgEnt : ∀ i k : Fin d,
      Measurable (fun omega : ShellSeq d => localizationGaugeAverage l L R omega i k) := by
    intro i k
    exact (measurable_pi_apply k).comp ((measurable_pi_apply i).comp hAvg)
  unfold pertLinfty
  refine ShellField.continuous_matrixOperatorNorm.measurable.comp ?_
  refine measurable_matrix_of_entries fun i k => ?_
  simp only [Matrix.sub_apply]
  exact (hEvEnt i k).sub (hAvgEnt i k)

/-- Continuity of the perturbation size in the space variable: the finite shell
increment is a finite sum of continuous functions and the gauge average is a
constant matrix, so only the continuity of the Euclidean operator norm is
used. -/
private theorem continuous_pertLinfty (l L : ℕ) (R : TriadicCube d) (omega : ShellSeq d) :
    Continuous (pertLinfty l L R omega) := by
  have hsum : Continuous fun x : Vec d => ∑ k ∈ Finset.Ioc l L, (omega k) x :=
    continuous_finsetSum _ fun k _ => (omega k).1.1.continuous
  have hinc : Continuous fun x : Vec d => finiteShellIncrement omega l L x :=
    hsum.congr (by intro x; rw [finiteShellIncrement_apply]; rfl)
  unfold pertLinfty
  exact ShellField.continuous_matrixOperatorNorm.comp (hinc.sub continuous_const)

/-- **The `hDdmeas` input at the carrier `localizationDz`**: the printed `L∞` perturbation
size `‖k_L − k_ℓ − h_z‖_{L∞(z+cu_n)}` is measurable in the shell sequence.

The supremum runs over the uncountable half-open cube.  A countable dense set
`D` of `ℝ^d` has `openCubeSet R ⊆ closure (D ∩ openCubeSet R)`, and
`cubeSet R ⊆ closure (openCubeSet R)`, so `D ∩ openCubeSet R` is dense in the
carrier set.  Continuity of the perturbation size then identifies the supremum
over the cube with the supremum over that countable set, which is a `⨆` over a
countable index type and hence measurable coordinatewise. -/
theorem localizationPerturbSize_measurable (l L : ℕ) (R : TriadicCube d) :
    Measurable (localizationPerturbSize (d := d) l L R) := by
  classical
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense (Vec d)
  have hUopen : IsOpen (openCubeSet R) := by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.isOpen_ball
  have : Countable (D ∩ openCubeSet R : Set (Vec d)) :=
    (hDcount.mono Set.inter_subset_left).to_subtype
  set F : Option (D ∩ openCubeSet R : Set (Vec d)) → ShellSeq d → ℝ := fun o =>
    match o with
    | none => fun _ => 0
    | some x => fun omega => pertLinfty l L R omega x.1
    with hFdef
  have hFnone : ∀ omega : ShellSeq d, F none omega = 0 := by
    intro omega
    rw [hFdef]
  have hFsome : ∀ (x : (D ∩ openCubeSet R : Set (Vec d))) (omega : ShellSeq d),
      F (some x) omega = pertLinfty l L R omega x.1 := by
    intro x omega
    rw [hFdef]
  have hFmeas : ∀ o, Measurable (F o) := by
    intro o
    cases o with
    | none => exact measurable_const
    | some x => exact measurable_pertLinfty_apply l L R x.1
  have hkey : localizationPerturbSize (d := d) l L R = fun omega => ⨆ o, F o omega := by
    funext omega
    have hgcont : Continuous (pertLinfty l L R omega) := continuous_pertLinfty l L R omega
    have hrange_at : Set.range (localizationPerturbSizeAtIndex (d := d) l L R omega) =
        insert 0 (pertLinfty l L R omega '' (cubeSet R)) := by
      ext r
      constructor
      · rintro ⟨o, rfl⟩
        cases o with
        | none => exact Set.mem_insert _ _
        | some x => exact Set.mem_insert_of_mem _ ⟨x.1, x.2, rfl⟩
      · intro hr
        rcases hr with hr | hr
        · subst hr
          exact ⟨none, rfl⟩
        · rcases hr with ⟨x, hx, rfl⟩
          exact ⟨some ⟨x, hx⟩, rfl⟩
    have hrange_F : Set.range (fun o => F o omega) =
        insert 0 (pertLinfty l L R omega '' (D ∩ openCubeSet R)) := by
      ext r
      constructor
      · rintro ⟨o, rfl⟩
        cases o with
        | none => exact Or.inl (hFnone omega)
        | some x => exact Or.inr ⟨x.1, x.2, (hFsome x omega).symm⟩
      · intro hr
        rcases hr with hr | hr
        · subst hr
          exact ⟨none, hFnone omega⟩
        · rcases hr with ⟨x, hx, rfl⟩
          exact ⟨some ⟨x, hx⟩, hFsome ⟨x, hx⟩ omega⟩
    have hbdd_g : BddAbove (pertLinfty l L R omega '' (cubeSet R)) := by
      have hK : IsCompact (closure (cubeSet R)) := (isBounded_cubeSet R).isCompact_closure
      exact (hK.bddAbove_image hgcont.continuousOn).mono (Set.image_mono subset_closure)
    have hsub : (D ∩ openCubeSet R : Set (Vec d)) ⊆ cubeSet R :=
      Set.inter_subset_right.trans (openCubeSet_subset_cubeSet R)
    have hbdd_F : BddAbove (Set.range fun o => F o omega) := by
      rw [hrange_F]
      exact (hbdd_g.insert 0).mono (Set.insert_subset_insert (Set.image_mono hsub))
    have hbdd_at : BddAbove
        (Set.range (localizationPerturbSizeAtIndex (d := d) l L R omega)) := by
      rw [hrange_at]
      exact hbdd_g.insert 0
    change sSup (Set.range (localizationPerturbSizeAtIndex (d := d) l L R omega)) =
      ⨆ o, F o omega
    refine le_antisymm ?_ ?_
    · have hS0 : (0 : ℝ) ≤ ⨆ o, F o omega := by
        have := le_ciSup hbdd_F none
        rwa [hFnone omega] at this
      refine csSup_le (Set.range_nonempty _) ?_
      rintro r ⟨o, rfl⟩
      cases o with
      | none => exact hS0
      | some x =>
          by_contra hcon
          have hlt : (⨆ o, F o omega) < pertLinfty l L R omega x.1 := lt_of_not_ge hcon
          have hVopen : IsOpen ((pertLinfty l L R omega) ⁻¹' Set.Ioi (⨆ o, F o omega)) :=
            isOpen_Ioi.preimage hgcont
          have hxcl : x.1 ∈ closure (openCubeSet R) :=
            SuperdiffusionCLT.Section2.Estimates.Stream.cubeSet_subset_closure_openCubeSet
              R x.2
          obtain ⟨y, hyV, hyU⟩ := mem_closure_iff.1 hxcl _ hVopen hlt
          obtain ⟨z, hzD, hzV, hzU⟩ :=
            hDdense.exists_mem_open (hVopen.inter hUopen) ⟨y, hyV, hyU⟩
          have hle := le_ciSup hbdd_F (some ⟨z, ⟨hzD, hzU⟩⟩)
          rw [hFsome ⟨z, ⟨hzD, hzU⟩⟩ omega] at hle
          exact absurd hzV (not_lt.mpr hle)
    · have h0mem : (0 : ℝ) ∈ Set.range (localizationPerturbSizeAtIndex (d := d) l L R omega) :=
        ⟨none, rfl⟩
      have hSsup0 : (0 : ℝ) ≤
          sSup (Set.range (localizationPerturbSizeAtIndex (d := d) l L R omega)) :=
        le_csSup hbdd_at h0mem
      refine ciSup_le fun o => ?_
      cases o with
      | none => rw [hFnone omega]; exact hSsup0
      | some x =>
          have hmem : pertLinfty l L R omega x.1 ∈
              Set.range (localizationPerturbSizeAtIndex (d := d) l L R omega) :=
            ⟨some ⟨x.1, openCubeSet_subset_cubeSet R x.2.2⟩, rfl⟩
          rw [hFsome x omega]
          exact le_csSup hbdd_at hmem
  rw [hkey]
  exact Measurable.iSup hFmeas

/-- **The `hDdmeas` input**: `D_z` is measurable in the shell sequence.  This is
immediate from the measurability of the `L∞` perturbation size, `D_z` being a
polynomial in it with constant coefficients. -/
theorem localizationDz_measurable {nu : ℝ} (l L : ℕ) (R : TriadicCube d) :
    Measurable (localizationDz nu l L R) := by
  have h := localizationPerturbSize_measurable (d := d) l L R
  have hsq : Measurable (fun omega : ShellSeq d =>
      localizationPerturbSize l L R omega ^ 2) := by
    exact h.pow_const 2
  unfold localizationDz
  exact ((measurable_const.mul h).add (measurable_const.mul hsq))

/-- **The `hDdmeas` input on the descendant grid.** -/
theorem localizationDz_measurable_on_grid {nu : ℝ} (l L m n : ℕ) :
    ∀ R ∈ localizationAverageGrid d m n, Measurable (localizationDz nu l L R) :=
  fun R _ => localizationDz_measurable l L R

/-- **The `hT1m` input**: the printed `T₁ = avsum_{z ∈ 3^nℤ^d ∩ cu_m} D_z B_z`
is measurable in the shell sequence.  It is a finite sum of
products of the measurable carriers `D_z` (`localizationDz_measurable`) and
`B_z` (`localizationB_measurable`). -/
theorem localizationT1Carrier_measurable {nu : ℝ} (hnu : 0 < nu)
    (l L m n : ℕ) (Pvec : BlockVec d) :
    Measurable (localizationT1Carrier nu l L m n Pvec) := by
  unfold localizationT1Carrier
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ fun R _ => ?_
  exact (localizationDz_measurable l L R).mul (localizationB_measurable hnu l L R Pvec)

/-! ## `hcube`: the printed weight bound

The printed proof bounds `W_z = |bfE_ℓ^{1/2}G_{-h_z}P|²` in two steps: the
deterministic envelope bound `|bfE_ℓ| ≤ ν + 2Cν⁻¹(1∨ℓ)`
and the gauge-vector bound `|G_{-h_z}P|² ≤ C(1+|h_z|²)|P|² ≤ O_{Γ_1}(C(1∨L)|P|²)`
(from `e.jk.spatialavg` and `p.concentration`).  Only the first is proved here.
The reduction below consumes the second as a named hypothesis and produces the
printed display at the per-cube amplitude. -/

/-- **The printed weight bound, reduced to the printed
gauge-vector input.**  If the squared gauge length is `O_{Γ_1}` at the printed
gauge amplitude `CG(1∨L)|P|²` and the enlarged amplitude `A` dominates the
envelope constant times that gauge amplitude, then the weight
`W_z = |bfE_ℓ^{1/2}G_{-h_z}P|²` is `O_{Γ_1}(A)`.

The printed envelope bound `|bfE_ℓ| ≤ ν + 2Cν⁻¹(1∨ℓ)`
(`blockMatrixOperatorNorm_envelopeBlockMat_le`) and the block Cauchy--Schwarz
are the only analytic inputs; the gauge-vector bound is the one printed display
that is taken as a hypothesis. -/
theorem localizationW_isBigO_of_gaugeVectorNormSq {nu : ℝ} (hnu : 0 < nu)
    (l L : ℕ) (Pvec : BlockVec d) (R : TriadicCube d)
    {P : ProbabilityMeasure (ShellSeq d)} {CG A : ℝ}
    (hG : IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1)
      (fun omega : ShellSeq d =>
        blockVecNorm (localizationGaugeVector l L R Pvec omega) ^ 2)
      (CG * max 1 (L : ℝ) * blockVecDot Pvec Pvec))
    (hAmp : envelopeUpperScalar d nu l * (CG * max 1 (L : ℝ) * blockVecDot Pvec Pvec) ≤ A) :
    IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1)
      (localizationW nu l L R Pvec) A := by
  have hup : 0 ≤ envelopeUpperScalar d nu l := (envelopeUpperScalar_pos hnu d l).le
  have hdom : ∀ omega : ShellSeq d, localizationW nu l L R Pvec omega ≤
      envelopeUpperScalar d nu l *
        blockVecNorm (localizationGaugeVector l L R Pvec omega) ^ 2 := by
    intro omega
    set G : BlockVec d := localizationGaugeVector l L R Pvec omega with hGdef
    have hGnn : 0 ≤ blockVecNorm G := blockVecNorm_nonneg G
    have h1 : localizationW nu l L R Pvec omega =
        blockVecDot G (blockMatVecMul (envelopeBlockMat d nu l) G) :=
      localizationW_eq_envelopeBlockMat hnu l L R Pvec omega
    rw [h1]
    calc blockVecDot G (blockMatVecMul (envelopeBlockMat d nu l) G)
        ≤ |blockVecDot G (blockMatVecMul (envelopeBlockMat d nu l) G)| := le_abs_self _
      _ ≤ blockVecNorm G * blockVecNorm (blockMatVecMul (envelopeBlockMat d nu l) G) :=
          abs_blockVecDot_le_blockVecNorm_mul _ _
      _ ≤ blockVecNorm G *
            (blockMatrixOperatorNorm (envelopeBlockMat d nu l) * blockVecNorm G) :=
          mul_le_mul_of_nonneg_left (blockVecNorm_blockMatVecMul_le _ _) hGnn
      _ ≤ blockVecNorm G * (envelopeUpperScalar d nu l * blockVecNorm G) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              (blockMatrixOperatorNorm_envelopeBlockMat_le hnu d l) hGnn) hGnn
      _ = envelopeUpperScalar d nu l * blockVecNorm G ^ 2 := by ring
  have hc := IndependentSums.IsBigO.const_mul (μ := P.toMeasure)
    (Ψ := IndependentSums.gammaSigma 1) (X := fun omega : ShellSeq d =>
      blockVecNorm (localizationGaugeVector l L R Pvec omega) ^ 2)
    (A := CG * max 1 (L : ℝ) * blockVecDot Pvec Pvec) hup hG
  refine (hc.of_abs_le (fun omega => ?_)).mono_scale hAmp
  rw [abs_of_nonneg (localizationW_nonneg nu l L R Pvec omega), abs_mul, abs_of_nonneg hup,
    abs_of_nonneg (sq_nonneg _)]
  exact hdom omega

/-- **The amplitude bookkeeping of the weight bound.**  For `ν ∈ (0,1]` the printed
envelope constant `ν + 2Cν⁻¹(1∨ℓ)` is dominated by the unified
`(1 + 2C)ν⁻¹(1∨ℓ)`, so the product of the envelope constant with the gauge
amplitude `CG(1∨L)|P|²` fits inside the per-cube amplitude
`localizationAverageWbarCubeAmplitude` at the enlarged constant
`(1 + 2C)CG`. -/
theorem envelopeUpperScalar_mul_gaugeAmplitude_le_wbarCubeAmplitude {nu CG : ℝ}
    (hnu : 0 < nu) (hnu1 : nu ≤ 1) (hCG : 0 ≤ CG)
    (l L : ℕ) (Pvec : BlockVec d) :
    envelopeUpperScalar d nu l * (CG * max 1 (L : ℝ) * blockVecDot Pvec Pvec) ≤
      localizationAverageWbarCubeAmplitude
        ((1 + 2 * cutoffEnvelopeConst d) * CG) nu l L Pvec := by
  have hC : 0 < cutoffEnvelopeConst d := cutoffEnvelopeConst_pos d
  have hmaxl : (1 : ℝ) ≤ max 1 (l : ℝ) := le_max_left _ _
  have hmaxl0 : (0 : ℝ) ≤ max 1 (l : ℝ) := le_trans zero_le_one hmaxl
  have hmaxL0 : (0 : ℝ) ≤ max 1 (L : ℝ) := le_trans zero_le_one (le_max_left _ _)
  have hdot : 0 ≤ blockVecDot Pvec Pvec := blockVecDot_self_nonneg Pvec
  have hnule1 : nu ≤ 1 := hnu1
  have hnuinv1 : (1 : ℝ) ≤ nu⁻¹ := (one_le_inv₀ hnu).2 hnule1
  have hnu_le_nuinv : nu ≤ nu⁻¹ := by
    calc nu ≤ 1 := hnule1
      _ ≤ nu⁻¹ := hnuinv1
  have hnu_le : nu ≤ nu⁻¹ * max 1 (l : ℝ) := by
    calc nu ≤ nu⁻¹ := hnu_le_nuinv
      _ = nu⁻¹ * 1 := (mul_one _).symm
      _ ≤ nu⁻¹ * max 1 (l : ℝ) := mul_le_mul_of_nonneg_left hmaxl (by positivity)
  have hsplit : envelopeUpperScalar d nu l ≤
      (1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * max 1 (l : ℝ) := by
    unfold envelopeUpperScalar
    have hrearr : 2 * cutoffEnvelopeConst d * nu⁻¹ * max 1 (l : ℝ) =
        (2 * cutoffEnvelopeConst d) * (nu⁻¹ * max 1 (l : ℝ)) := by ring
    rw [hrearr]
    nlinarith only [hnu_le, hnu]
  calc envelopeUpperScalar d nu l * (CG * max 1 (L : ℝ) * blockVecDot Pvec Pvec)
      ≤ ((1 + 2 * cutoffEnvelopeConst d) * nu⁻¹ * max 1 (l : ℝ)) *
          (CG * max 1 (L : ℝ) * blockVecDot Pvec Pvec) :=
        mul_le_mul_of_nonneg_right hsplit
          (mul_nonneg (mul_nonneg hCG hmaxL0) hdot)
    _ = localizationAverageWbarCubeAmplitude
          ((1 + 2 * cutoffEnvelopeConst d) * CG) nu l L Pvec := by
        unfold localizationAverageWbarCubeAmplitude
        rw [Real.rpow_neg_one]
        ring

/-- **The printed weight bound at the carrier `localizationW` and the per-cube amplitude.**  The
weight bound `W_z = O_{Γ_1}(Cν⁻¹(1∨ℓ)(1∨L)|P|²)` on the descendant grid, with
the printed `(1∨(m-n))` factor of the maximum *absent* — the
per-cube display carries no such factor; it is the finite-maximum step
`localizationAverage_wbar_bound_of_cube_bounds` that produces it.  The only
surviving hypothesis is the printed gauge-vector bound. -/
theorem localizationW_isBigO_on_grid_of_gaugeVectorNormSq {nu : ℝ} (hnu : 0 < nu)
    (hnu1 : nu ≤ 1) (l L m n : ℕ) (Pvec : BlockVec d)
    (P : ProbabilityMeasure (ShellSeq d)) {CG : ℝ} (hCG : 0 ≤ CG)
    (hG : ∀ R ∈ localizationAverageGrid d m n,
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1)
        (fun omega : ShellSeq d =>
          blockVecNorm (localizationGaugeVector l L R Pvec omega) ^ 2)
        (CG * max 1 (L : ℝ) * blockVecDot Pvec Pvec)) :
    ∀ R ∈ localizationAverageGrid d m n,
      IndependentSums.IsBigO P.toMeasure (IndependentSums.gammaSigma 1)
        (localizationW nu l L R Pvec)
        (localizationAverageWbarCubeAmplitude
          ((1 + 2 * cutoffEnvelopeConst d) * CG) nu l L Pvec) :=
  fun R hR => localizationW_isBigO_of_gaugeVectorNormSq hnu l L Pvec R (hG R hR)
    (envelopeUpperScalar_mul_gaugeAmplitude_le_wbarCubeAmplitude hnu hnu1 hCG l L Pvec)

end SuperdiffusionCLT.Section2.Localization
