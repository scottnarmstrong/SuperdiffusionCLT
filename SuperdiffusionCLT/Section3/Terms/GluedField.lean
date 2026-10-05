/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section3.Setup.Scales
public import SuperdiffusionCLT.Section2.Estimates.Stream.IncrementLinftyLargeCube
public import SuperdiffusionCLT.Section2.Annealed.EnvelopeDomain

/-!
# The glued gradient field `∇u_k`, the vector `q`, and the cutoff-`ℓ` proxy

The paper fixes a unit vector `e`,
sets `Q = shom_{L',*}^{1/2}(cu_n) e`, and for `y ∈ ℝ^d`, `k ∈ ℕ` lets
`u_{k,y} = v_{L'}(·, y + cu_k, 0, Q)` be the maximizer of the variational
problem on the translated cube `y + cu_k` formed with the cutoff coefficient
`a_{L'}` (`e.u.k.y.def`).  The **glued gradient field** of
`e.u.k.def` is

`∇u_k = ∑_{z ∈ 3^k ℤ^d} ∇u_{k,z} 1_{z+cu_k}`,

a genuinely piecewise object: the print notes that it is "not necessarily a
gradient field except on subdomains of a single cube of the form `z + cu_k`".

`e.Sec3.p.q.def` then sets `q = E[(a_ℓ ∇u_n)_{cu_ℓ}]`, and
`e.average.of.vn` records the annealed identity
`E[(∇u_n)_{z+cu_n}] = shom_{L',*}^{-1}(cu_n) shom_{L',*}^{1/2}(cu_n) e = p`
for every `z ∈ 3^n ℤ^d`.

## The carriers used here

The lattice `3^k ℤ^d ∩ cu_m` of centres is the triadic sub-cube family
`largeCubeSubcubes d k m`,
i.e. `descendantsAtDepth (originCube d m) (m - k)`.  Its half-open realizations
`cubeSet z` are pairwise disjoint and cover `cubeSet (originCube d m)` exactly,
so the printed sum of indicators is literally a definition by cases and needs
no choice: `gluedGradientField` below **is** the printed
`∑_z ∇u_{k,z} 1_{z+cu_k}`, restricted to the sub-cubes of `cu_m` and extended
by `0` outside `cu_m`.

On each sub-cube the maximizer is the canonical, choice-free
`setupMaximizer` of `Section3/Setup/Scales.lean` for the Chapter 2 domain
`Book.Ch02.cubeDomain z` and the Chapter 2 coefficient object
`cutoffDomainCoeffOn` of the cutoff field `a_L = nu Id + k_L`; its underlying
`H¹` gradient is a genuine function `Vec d → Vec d`, so no per-cube `∃!` and no
unique-choice step is needed.

## The three instances

With `S : ScaleSelection` and `F = fluxSlot nu S.LPrime P S.n e`:

* `∇u_n` (the field `uNGlued` of the consumers) is
  `gluedGradientField hnu S.LPrime S.n S.m F`;
* `∇u_m` at `y = 0` (the field `uMgrad`) is the one-cube instance
  `gluedGradientField hnu S.LPrime S.m S.m F`, whose family
  `largeCubeSubcubes d S.m S.m` is the singleton `{cu_m}`;
* `∇ũ_n` (the field `uTildeGlued` of the cutoff-`ℓ` proxy of the
  `l.RHS.term2` proof) is
  `gluedGradientField hnu S.ell S.n S.m F` — **the same flux slot**
  `F = shom_{L',*}^{1/2}(cu_n) e = (sigmaBarStarInvSqrt nu S.LPrime P S.n)⁻¹ • e`,
  only the coefficient cutoff level changes from `L'` to `ℓ`.

## Main definitions

* `cubeMaximizer`, `cubeMaximizerGradient`: `u_{k,z}` and `∇u_{k,z}`.
* `gluedGradientField`: `∇u_k` of `e.u.k.def`.
* `annealedCubeAverage`, `annealedGluedAverage`, `qVector`: `E[(·)_{cu_r}]`,
  the vector `p̃` of the `l.RHS.term2` proof, and the vector `q` of `e.Sec3.p.q.def`.

## Main results

* `gluedGradientField_apply_of_mem_cubeSet`, `..._of_mem_openCubeSet`: the
  cube-by-cube characterization, an exact pointwise identity.
* `memLp_two_gluedGradientField`: the glued field is square integrable.
* `volumeAverageVec_gluedGradientField`: the quenched precursor
  `(∇u_k)_{z+cu_k} = s_{L',*}^{-1}(z+cu_k) Q` of `e.v.spatial.averages`.
* `sigmaStarInvCoarse_openCubeSet_coefficientCutoff`,
  `integral_sigmaStarInvCoarse_openCubeSet_eq`: the source's "by stationarity"
  on a translated cube — the quenched coarse matrix of `z + cu_k` is the one of
  `cu_k` for the translated shell sequence, and the shell law is invariant under
  that translation by `ShellLawPrefix` and `ShellLawJ2`.
* `integral_volumeAverageVec_gluedGradientField_eq_testVector`:
  **`e.average.of.vn` on every sub-cube** `z` of the family, whose instance at `z = 0`
  identifies `annealedGluedAverage` with the test vector.  The only
  hypothesis beyond the shell laws is integrability of the quenched coarse
  matrix in the shell sequence, which is not supplied by an existing theorem because the
  Chapter 2 maximizer is produced by a choice.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Terms

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Frozen.Section2
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff
open SuperdiffusionCLT.Section2.Estimates.Stream
open SuperdiffusionCLT.Section3.Setup

noncomputable section

variable {d : ℕ}

/-! ## The cube-wise maximizers `u_{k,z}` -/

section CubeMaximizer

variable {nu : ℝ}

/-- The Chapter 2 coefficient object of the cutoff field `a_L = nu Id + k_L` on
the open triadic cube `z`, the coefficient of the variational problem
`J_L(z + cu_k, 0, Q)` of `e.u.k.y.def`. -/
def cubeCutoffCoeffOn (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ)
    (z : TriadicCube d) : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain z) :=
  cutoffDomainCoeffOn (Book.Ch02.cubeDomain z) hnu omega L

@[simp] theorem cubeCutoffCoeffOn_toCoeffField (hnu : 0 < nu) (omega : ShellSeq d)
    (L : ℕ) (z : TriadicCube d) :
    (cubeCutoffCoeffOn hnu omega L z).toCoeffField =
      (coefficientCutoff nu omega L).toCoeffField :=
  rfl

/-- **`e.u.k.y.def`** on the triadic cube `z`: the canonical
mean-zero maximizer `u_{k,z} = v_L(·, z + cu_k, 0, F)` of the pure-flux
variational problem formed with the cutoff coefficient `a_L`. -/
def cubeMaximizer (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ) (F : Vec d)
    (z : TriadicCube d) :
    Book.Ch02.CanonicalMaximizer (Book.Ch02.cubeDomain z)
      (cubeCutoffCoeffOn hnu omega L z) 0 F :=
  setupMaximizer (Book.Ch02.cubeDomain z) (cubeCutoffCoeffOn hnu omega L z) F

/-- `∇u_{k,z}`, the gradient of the cube-wise maximizer as an honest function
`Vec d → Vec d`. -/
def cubeMaximizerGradient (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ) (F : Vec d)
    (z : TriadicCube d) : Vec d → Vec d :=
  (cubeMaximizer hnu omega L F z).toSolution.toH1.grad

variable (hnu : 0 < nu) (omega : ShellSeq d) (L : ℕ) (F : Vec d) (z : TriadicCube d)

/-- `∇u_{k,z} ∈ L²(z + cu_k)`, componentwise. -/
theorem gradMemL2On_cubeMaximizerGradient :
    GradMemL2On (openCubeSet z) (cubeMaximizerGradient hnu omega L F z) :=
  (cubeMaximizer hnu omega L F z).toSolution.toH1.gradMemL2

/-- `∇u_{k,z} ∈ L²(z + cu_k)` as a vector field. -/
theorem memLp_two_cubeMaximizerGradient :
    MemLp (cubeMaximizerGradient hnu omega L F z) 2
      (MeasureTheory.volume.restrict (openCubeSet z)) :=
  MemLp.of_eval (gradMemL2On_cubeMaximizerGradient hnu omega L F z)

/-- **`e.v.spatial.averages` in the pure-flux slot**, the quenched precursor of
`e.average.of.vn`: `(∇u_{k,z})_{z+cu_k} = s_{L,*}^{-1}(z + cu_k) F`. -/
theorem volumeAverageVec_cubeMaximizerGradient :
    volumeAverageVec (openCubeSet z) (cubeMaximizerGradient hnu omega L F z) =
      matVecMul (sigmaStarInvCoarse (openCubeSet z)
        (coefficientCutoff nu omega L).toCoeffField) F :=
  averageGradient_setupMaximizer (Book.Ch02.cubeDomain z)
    (cubeCutoffCoeffOn hnu omega L z) F

end CubeMaximizer

/-! ## The sub-cube family of `cu_m` -/

section Subcubes

/-- `largeCubeSubcubes` unfolded: the scale-`k` sub-cubes of `cu_m` are the
descendants of `cu_m` at depth `m - k`. -/
theorem largeCubeSubcubes_eq_descendantsAtDepth (k m : ℕ) :
    largeCubeSubcubes d k m = descendantsAtDepth (originCube d (m : ℤ)) (m - k) :=
  rfl

/-- The half-open realizations of the sub-cube family are pairwise disjoint. -/
theorem pairwiseDisjoint_cubeSet_largeCubeSubcubes (k m : ℕ) :
    (largeCubeSubcubes d k m : Set (TriadicCube d)).PairwiseDisjoint cubeSet :=
  pairwiseDisjoint_descendantsAtDepth (originCube d (m : ℤ)) (m - k)

/-- Every sub-cube of the family sits inside the large cube. -/
theorem cubeSet_subset_of_mem_largeCubeSubcubes {k m : ℕ} {z : TriadicCube d}
    (hz : z ∈ largeCubeSubcubes d k m) :
    cubeSet z ⊆ cubeSet (originCube d (m : ℤ)) :=
  cubeSet_subset_of_mem_descendantsAtDepth hz

/-- The centred triadic cube at scale `s - j` is a depth-`j` descendant of the
centred cube at scale `s`: at each step it is the middle child. -/
private theorem originCubeMemDesc (s : ℤ) :
    ∀ j : ℕ, originCube d (s - (j : ℤ)) ∈ descendantsAtDepth (originCube d s) j
  | 0 => by simp
  | j + 1 => by
      rw [mem_descendantsAtDepth_succ_iff]
      refine ⟨originCube d (s - (j : ℤ)), originCubeMemDesc s j, ?_⟩
      rw [mem_childCubes_iff]
      refine ⟨fun _ => (1 : Fin 3), ?_⟩
      have hs : s - ((j + 1 : ℕ) : ℤ) = s - (j : ℤ) - 1 := by
        push_cast
        ring
      simp only [originCube, hs, TriadicCube.mk.injEq]
      refine ⟨trivial, ?_⟩
      funext i
      norm_num

/-- **`z = 0` is one of the sub-cube centres**: the centred cube `cu_k` belongs
to the scale-`k` sub-cube family of `cu_m` whenever `k ≤ m`. -/
theorem originCube_mem_largeCubeSubcubes {k m : ℕ} (hkm : k ≤ m) :
    originCube d (k : ℤ) ∈ largeCubeSubcubes d k m := by
  have hcast : (m : ℤ) - ((m - k : ℕ) : ℤ) = (k : ℤ) := by
    have : ((m - k : ℕ) : ℤ) = (m : ℤ) - (k : ℤ) := by omega
    omega
  have h := originCubeMemDesc (d := d) (m : ℤ) (m - k)
  rwa [hcast] at h

/-- The scale-`m` sub-cube family of `cu_m` is the single cube `cu_m`: this is
the instance of `e.u.k.def` that gives `∇u_m` of the source. -/
theorem largeCubeSubcubes_self (m : ℕ) :
    largeCubeSubcubes d m m = ({originCube d (m : ℤ)} : Finset (TriadicCube d)) := by
  rw [largeCubeSubcubes_eq_descendantsAtDepth, Nat.sub_self, descendantsAtDepth_zero]

end Subcubes

/-! ## The glued field `∇u_k` of `e.u.k.def` -/

section Glued

variable {nu : ℝ}

/-- **`e.u.k.def`**: the piecewise field
`∇u_k = ∑_{z} ∇u_{k,z} 1_{z+cu_k}`, summed over the scale-`k` triadic sub-cubes
`z` of the large cube `cu_m` (whose centres are the lattice points
`3^k ℤ^d ∩ cu_m`) and extended by `0` outside `cu_m`.

The half-open realizations `cubeSet z` of the family are pairwise disjoint and
cover `cubeSet (originCube d m)`, so at each point at most one summand is
nonzero: the gluing itself is a definition by cases, and the only choice in the
construction is the one already inside the canonical maximizer. -/
def gluedGradientField (hnu : 0 < nu) (L k m : ℕ) (F : Vec d)
    (omega : ShellSeq d) : Vec d → Vec d := fun x =>
  ∑ z ∈ largeCubeSubcubes d k m,
    Set.indicator (cubeSet z) (cubeMaximizerGradient hnu omega L F z) x

variable (hnu : 0 < nu) (L k m : ℕ) (F : Vec d) (omega : ShellSeq d)

/-- The defining sum of `e.u.k.def`, evaluated at a point. -/
theorem gluedGradientField_apply (x : Vec d) :
    gluedGradientField hnu L k m F omega x =
      ∑ z ∈ largeCubeSubcubes d k m,
        Set.indicator (cubeSet z) (cubeMaximizerGradient hnu omega L F z) x :=
  rfl

/-- **The cube-by-cube characterization of `e.u.k.def`**: on the half-open
sub-cube `z` the glued field is exactly `∇u_{k,z}`, pointwise. -/
theorem gluedGradientField_apply_of_mem_cubeSet {z : TriadicCube d}
    (hz : z ∈ largeCubeSubcubes d k m) {x : Vec d} (hx : x ∈ cubeSet z) :
    gluedGradientField hnu L k m F omega x =
      cubeMaximizerGradient hnu omega L F z x := by
  classical
  rw [gluedGradientField_apply, Finset.sum_eq_single z]
  · exact Set.indicator_of_mem hx _
  · intro y hy hyz
    refine Set.indicator_of_notMem ?_ _
    intro hxy
    exact Set.disjoint_left.1
      (pairwiseDisjoint_cubeSet_largeCubeSubcubes k m (Finset.mem_coe.2 hy)
        (Finset.mem_coe.2 hz) hyz) hxy hx
  · intro hznot
    exact absurd hz hznot

/-- The same characterization on the **open** sub-cube, the form the print's
"except on subdomains of a single cube of the form `z + cu_k`" uses. -/
theorem gluedGradientField_apply_of_mem_openCubeSet {z : TriadicCube d}
    (hz : z ∈ largeCubeSubcubes d k m) {x : Vec d} (hx : x ∈ openCubeSet z) :
    gluedGradientField hnu L k m F omega x =
      cubeMaximizerGradient hnu omega L F z x :=
  gluedGradientField_apply_of_mem_cubeSet hnu L k m F omega hz
    (openCubeSet_subset_cubeSet z hx)

/-- The glued field is square integrable on all of `ℝ^d`: it is a finite sum of
indicators of the sub-cubes of the `L²` gradients `∇u_{k,z}`. -/
theorem memLp_two_gluedGradientField :
    MemLp (gluedGradientField hnu L k m F omega) 2 MeasureTheory.volume := by
  classical
  have hrw : gluedGradientField hnu L k m F omega =
      ∑ z ∈ largeCubeSubcubes d k m,
        Set.indicator (cubeSet z) (cubeMaximizerGradient hnu omega L F z) := by
    funext x
    rw [gluedGradientField_apply, Finset.sum_apply]
  rw [hrw]
  refine memLp_finsetSum' _ fun z _ => ?_
  rw [memLp_indicator_iff_restrict (measurableSet_cubeSet z),
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet z]
  exact memLp_two_cubeMaximizerGradient hnu omega L F z

/-- **`e.v.spatial.averages` for the glued field**, the quenched precursor of
`e.average.of.vn`: on every sub-cube `z` of the family the cube average of
`∇u_k` is `s_{L,*}^{-1}(z + cu_k) F`. -/
theorem volumeAverageVec_gluedGradientField {z : TriadicCube d}
    (hz : z ∈ largeCubeSubcubes d k m) :
    volumeAverageVec (openCubeSet z) (gluedGradientField hnu L k m F omega) =
      matVecMul (sigmaStarInvCoarse (openCubeSet z)
        (coefficientCutoff nu omega L).toCoeffField) F := by
  rw [← volumeAverageVec_cubeMaximizerGradient hnu omega L F z]
  funext i
  refine congrArg (fun t : ℝ => (MeasureTheory.volume (openCubeSet z)).toReal⁻¹ * t) ?_
  refine MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet z) ?_
  intro x hx
  show gluedGradientField hnu L k m F omega x i =
    cubeMaximizerGradient hnu omega L F z x i
  rw [gluedGradientField_apply_of_mem_openCubeSet hnu L k m F omega hz hx]

end Glued

/-! ## The annealed cube averages, `p̃` and the vector `q` -/

section AnnealedAverages

variable {nu : ℝ}

/-- `E[(V)_{cu_r}]`, the expectation of the `cu_r`-average of a vector field of
the shell sequence: a Bochner integral in `Vec d`. -/
def annealedCubeAverage (P : ProbabilityMeasure (ShellSeq d)) (r : ℕ)
    (V : ShellSeq d → Vec d → Vec d) : Vec d :=
  ∫ omega : ShellSeq d,
    volumeAverageVec (openCubeSet (originCube d (r : ℤ))) (V omega) ∂P.toMeasure

/-- The coordinates of `E[(V)_{cu_r}]` are the scalar expectations of the
coordinate averages, provided those are integrable. -/
theorem annealedCubeAverage_apply (P : ProbabilityMeasure (ShellSeq d)) (r : ℕ)
    (V : ShellSeq d → Vec d → Vec d)
    (hV : ∀ i : Fin d, MeasureTheory.Integrable
      (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet (originCube d (r : ℤ))) (fun x => V omega x i))
      P.toMeasure) (i : Fin d) :
    annealedCubeAverage P r V i =
      ∫ omega : ShellSeq d,
        volumeAverage (openCubeSet (originCube d (r : ℤ)))
          (fun x => V omega x i) ∂P.toMeasure :=
  MeasureTheory.eval_integral (f := fun omega : ShellSeq d =>
    volumeAverageVec (openCubeSet (originCube d (r : ℤ))) (V omega)) hV i

/-- **`p̃ = E[(∇ũ_n)_{cu_n}]`** of the cutoff-`ℓ` proxy: the annealed
`cu_k`-average of the glued field at maximizer scale `k`.  At `L = S.LPrime`
this is the left side of `e.average.of.vn` at `z = 0`, which the theorem
`integral_volumeAverageVec_gluedGradientField_eq_testVector` below identifies with `p`;
at `L = S.ell` it is the `p̃` of the `l.RHS.term2` proof. -/
def annealedGluedAverage (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d))
    (L k m : ℕ) (F : Vec d) : Vec d :=
  annealedCubeAverage P k (gluedGradientField hnu L k m F)

/-- `p̃` written out as a Bochner integral. -/
theorem annealedGluedAverage_eq (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d))
    (L k m : ℕ) (F : Vec d) :
    annealedGluedAverage hnu P L k m F =
      ∫ omega : ShellSeq d,
        volumeAverageVec (openCubeSet (originCube d (k : ℤ)))
          (gluedGradientField hnu L k m F omega) ∂P.toMeasure :=
  rfl

/-- **`q = E[(a_ℓ ∇u_n)_{cu_ℓ}]`**, the second half of `e.Sec3.p.q.def`:
the annealed `cu_ℓ`-average of the flux `a_ℓ ∇u_k` of the glued field.

With `L = S.LPrime`, `ell = S.ell`, `k = S.n`, `m = S.m` and
`F = fluxSlot nu S.LPrime P S.n e` this is the printed `q`; with `L = S.ell`
and the same remaining data it is the `q̃` of the localized proxy in the proofs
of `l.RHS.term1` and `l.RHS.term2`. -/
def qVector (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d))
    (L ell k m : ℕ) (F : Vec d) : Vec d :=
  annealedCubeAverage P ell fun omega x =>
    matVecMul ((coefficientCutoff nu omega ell).toCoeffField x)
      (gluedGradientField hnu L k m F omega x)

/-- `q` written out as the Bochner integral of `e.Sec3.p.q.def`. -/
theorem qVector_eq (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d))
    (L ell k m : ℕ) (F : Vec d) :
    qVector hnu P L ell k m F =
      ∫ omega : ShellSeq d,
        volumeAverageVec (openCubeSet (originCube d (ell : ℤ)))
          (fun x => matVecMul ((coefficientCutoff nu omega ell).toCoeffField x)
            (gluedGradientField hnu L k m F omega x)) ∂P.toMeasure :=
  rfl

/-- The coordinates of `q`.

Integrability of the coordinate averages is an explicit hypothesis: the
canonical maximizer of one cube is produced by `Book.Ch02.responseExistenceTheory`
through a choice, so there is no joint measurability result for
`omega ↦ ∇u_{k,z}(omega)`, and none of the energy bounds of
`e.v.ky.energy` supplies it either. -/
theorem qVector_apply (hnu : 0 < nu) (P : ProbabilityMeasure (ShellSeq d))
    (L ell k m : ℕ) (F : Vec d)
    (hq : ∀ i : Fin d, MeasureTheory.Integrable
      (fun omega : ShellSeq d =>
        volumeAverage (openCubeSet (originCube d (ell : ℤ)))
          (fun x => matVecMul ((coefficientCutoff nu omega ell).toCoeffField x)
            (gluedGradientField hnu L k m F omega x) i)) P.toMeasure) (i : Fin d) :
    qVector hnu P L ell k m F i =
      ∫ omega : ShellSeq d,
        volumeAverage (openCubeSet (originCube d (ell : ℤ)))
          (fun x => matVecMul ((coefficientCutoff nu omega ell).toCoeffField x)
            (gluedGradientField hnu L k m F omega x) i) ∂P.toMeasure :=
  annealedCubeAverage_apply P ell _ hq i

end AnnealedAverages

/-! ## Stationarity of the coarse matrix on a translated cube -/

section Stationarity

open scoped Matrix.Norms.Elementwise

/-- **The quenched coarse matrix on a translated cube.** `s_{L,*}^{-1}(z + cu_k)`
of the shell sequence `omega` is `s_{L,*}^{-1}(cu_k)` of the shell sequence
translated by the centre of `z`.  This is the deterministic half of the source's
"by stationarity" in `e.average.of.vn`. -/
theorem sigmaStarInvCoarse_openCubeSet_coefficientCutoff (nu : ℝ) (L : ℕ)
    (omega : ShellSeq d) (Q : TriadicCube d) :
    sigmaStarInvCoarse (openCubeSet Q) (coefficientCutoff nu omega L).toCoeffField =
      sigmaStarInvCoarse (openCubeSet (originCube d Q.scale))
        (coefficientCutoff nu
          (ShellField.translateSequence (triadicCubeShift Q) omega) L).toCoeffField := by
  rw [openCubeSet_eq_translateSet_originCube_of_triadicCube Q,
    sigmaStarInvCoarse_translateSet_eq_translateCoeffField,
    ← translateReg_coefficientCutoff nu (triadicCubeShift Q) omega L]
  rfl

/-- **The annealed block on a translated cube.**  Stationarity of the shell law
under real translations — `ShellLawPrefix` and `ShellLawJ2` through
`ShellField.map_translateSequence_eq` — moves the expectation of
`s_{L,*}^{-1}(z + cu_k)` to the centred cube `cu_k`. -/
theorem integral_sigmaStarInvCoarse_openCubeSet_eq
    {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
    (hJ2 : ShellLawJ2 d P) (nu : ℝ) (L : ℕ) (Q : TriadicCube d)
    (hInt : MeasureTheory.Integrable (fun omega : ShellSeq d =>
      sigmaStarInvCoarse (openCubeSet (originCube d Q.scale))
        (coefficientCutoff nu omega L).toCoeffField) P.toMeasure) :
    ∫ omega : ShellSeq d, sigmaStarInvCoarse (openCubeSet Q)
        (coefficientCutoff nu omega L).toCoeffField ∂P.toMeasure =
      ∫ omega : ShellSeq d, sigmaStarInvCoarse (openCubeSet (originCube d Q.scale))
        (coefficientCutoff nu omega L).toCoeffField ∂P.toMeasure := by
  have hmap : MeasureTheory.Measure.map
      (ShellField.translateSequence (triadicCubeShift Q)) P.toMeasure = P.toMeasure :=
    ShellField.map_translateSequence_eq hPrefix hJ2 (triadicCubeShift Q)
  have hmeas : AEStronglyMeasurable (fun omega : ShellSeq d =>
      sigmaStarInvCoarse (openCubeSet (originCube d Q.scale))
        (coefficientCutoff nu omega L).toCoeffField)
      (MeasureTheory.Measure.map (ShellField.translateSequence (triadicCubeShift Q))
        P.toMeasure) := by
    rw [hmap]
    exact hInt.aestronglyMeasurable
  calc ∫ omega : ShellSeq d, sigmaStarInvCoarse (openCubeSet Q)
          (coefficientCutoff nu omega L).toCoeffField ∂P.toMeasure
      = ∫ omega : ShellSeq d, sigmaStarInvCoarse (openCubeSet (originCube d Q.scale))
          (coefficientCutoff nu
            (ShellField.translateSequence (triadicCubeShift Q) omega) L).toCoeffField
          ∂P.toMeasure :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun omega =>
          sigmaStarInvCoarse_openCubeSet_coefficientCutoff nu L omega Q)
    _ = ∫ omega : ShellSeq d, sigmaStarInvCoarse (openCubeSet (originCube d Q.scale))
          (coefficientCutoff nu omega L).toCoeffField
          ∂(MeasureTheory.Measure.map
            (ShellField.translateSequence (triadicCubeShift Q)) P.toMeasure) :=
        (MeasureTheory.integral_map
          (ShellField.measurable_translateSequence (triadicCubeShift Q)).aemeasurable
          hmeas).symm
    _ = ∫ omega : ShellSeq d, sigmaStarInvCoarse (openCubeSet (originCube d Q.scale))
          (coefficientCutoff nu omega L).toCoeffField ∂P.toMeasure := by rw [hmap]

end Stationarity

/-! ## `e.average.of.vn`, the annealed identity on a sub-cube -/

section AverageOfVn

open scoped Matrix.Norms.Elementwise

variable [NeZero d] {nu : ℝ}

omit [NeZero d] in
private theorem matVecMulSmulOne (c : ℝ) (x : Vec d) :
    matVecMul (c • (1 : Mat d)) x = c • x := by
  rw [smul_matVecMul]
  refine congrArg (fun v : Vec d => c • v) ?_
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq]

omit [NeZero d] in
private theorem integralMatVecMul {mu : MeasureTheory.Measure (ShellSeq d)}
    {M : ShellSeq d → Mat d} (hM : MeasureTheory.Integrable M mu) (F : Vec d) :
    ∫ omega : ShellSeq d, matVecMul (M omega) F ∂mu =
      matVecMul (∫ omega : ShellSeq d, M omega ∂mu) F := by
  have hrow : ∀ i j : Fin d,
      MeasureTheory.Integrable (fun omega : ShellSeq d => M omega i j) mu :=
    fun i j => (hM.eval i).eval j
  have hcomp : ∀ i : Fin d, MeasureTheory.Integrable
      (fun omega : ShellSeq d => matVecMul (M omega) F i) mu := fun i =>
    MeasureTheory.integrable_finsetSum _ fun j _ => (hrow i j).mul_const (F j)
  funext i
  rw [MeasureTheory.eval_integral
    (f := fun omega : ShellSeq d => matVecMul (M omega) F) hcomp i]
  show ∫ omega : ShellSeq d, (∑ j, M omega i j * F j) ∂mu =
    ∑ j, (∫ omega : ShellSeq d, M omega ∂mu) i j * F j
  rw [MeasureTheory.integral_finsetSum _ fun j _ => (hrow i j).mul_const (F j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.integral_mul_const, Homogenization.integral_matrix_apply hM i j]

/-- **`e.average.of.vn`**: for every sub-cube `z` of the
scale-`k` family of `cu_m`,

`E[(∇u_k)_{z+cu_k}] = shom_{L',*}^{-1}(cu_k) shom_{L',*}^{1/2}(cu_k) e = p`,

the vector `p` of `e.Sec3.p.q.def`.  The quenched precursor is
`volumeAverageVec_gluedGradientField`; the source's "by stationarity" on the
translated cube is `integral_sigmaStarInvCoarse_openCubeSet_eq`, which uses
`ShellLawPrefix` and `ShellLawJ2`, and the scalar reduction of the annealed
block on the centred cube uses `ShellLawJ4`.

The one hypothesis beyond the standing shell laws is `hInt`, integrability in
`omega` of the quenched coarse matrix `s_{L',*}^{-1}(cu_k)`.  The canonical
maximizer of a cube comes from `Book.Ch02.responseExistenceTheory` through a
choice, so no theorem gives joint measurability of the Chapter 2 coarse
matrices in the shell sequence; the annealed modules of Section 2 carry the
same integrability as an explicit hypothesis (`sigmaBarStarInvScalar_pos`). -/
theorem integral_volumeAverageVec_gluedGradientField_eq_testVector
    (hnu : 0 < nu) {P : ProbabilityMeasure (ShellSeq d)}
    (hPrefix : ShellLawPrefix d P) (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P)
    (hJ4 : ShellLawJ4 d P) (LPrime : ℕ) {k m : ℕ} (hkm : k ≤ m) (e : Vec d)
    {z : TriadicCube d} (hz : z ∈ largeCubeSubcubes d k m)
    (hInt : MeasureTheory.Integrable (fun omega : ShellSeq d =>
      sigmaStarInvCoarse (openCubeSet (originCube d (k : ℤ)))
        (coefficientCutoff nu omega LPrime).toCoeffField) P.toMeasure) :
    ∫ omega : ShellSeq d, volumeAverageVec (openCubeSet z)
        (gluedGradientField hnu LPrime k m (fluxSlot nu LPrime P k e) omega)
        ∂P.toMeasure = testVector nu LPrime P k e := by
  have hscale : z.scale = (k : ℤ) := scale_of_mem_largeCubeSubcubes hkm hz
  have hIntz : MeasureTheory.Integrable (fun omega : ShellSeq d =>
      sigmaStarInvCoarse (openCubeSet (originCube d z.scale))
        (coefficientCutoff nu omega LPrime).toCoeffField) P.toMeasure := by
    rw [hscale]
    exact hInt
  have hpos : 0 < sigmaBarStarInvSeq nu LPrime P k :=
    sigmaBarStarInvSeq_pos hnu LPrime hPrefix hJ2 hJ3 hJ4 k
  have hblock : ∫ omega : ShellSeq d, sigmaStarInvCoarse (openCubeSet z)
      (coefficientCutoff nu omega LPrime).toCoeffField ∂P.toMeasure =
      sigmaBarStarInv nu LPrime P (cubeSet (originCube d (k : ℤ))) := by
    rw [integral_sigmaStarInvCoarse_openCubeSet_eq hPrefix hJ2 nu LPrime z hIntz,
      hscale]
    ext i j
    rw [Homogenization.integral_matrix_apply hInt i j]
    exact (sigmaBarStarInv_eq_integral_sigmaStarInvCoarse hnu LPrime P
      (originCube d (k : ℤ)) i j).symm
  have hInt' : MeasureTheory.Integrable (fun omega : ShellSeq d =>
      sigmaStarInvCoarse (openCubeSet z)
        (coefficientCutoff nu omega LPrime).toCoeffField) P.toMeasure := by
    have hcongr : (fun omega : ShellSeq d => sigmaStarInvCoarse (openCubeSet z)
        (coefficientCutoff nu omega LPrime).toCoeffField) =
        fun omega : ShellSeq d =>
          sigmaStarInvCoarse (openCubeSet (originCube d z.scale))
            (coefficientCutoff nu
              (ShellField.translateSequence (triadicCubeShift z) omega)
              LPrime).toCoeffField := by
      funext omega
      exact sigmaStarInvCoarse_openCubeSet_coefficientCutoff nu LPrime omega z
    have hGmap : MeasureTheory.Integrable
        (fun omega : ShellSeq d =>
          sigmaStarInvCoarse (openCubeSet (originCube d z.scale))
            (coefficientCutoff nu omega LPrime).toCoeffField)
        (MeasureTheory.Measure.map
          (ShellField.translateSequence (triadicCubeShift z)) P.toMeasure) := by
      rw [ShellField.map_translateSequence_eq hPrefix hJ2 (triadicCubeShift z)]
      exact hIntz
    rw [hcongr]
    exact hGmap.comp_measurable
      (ShellField.measurable_translateSequence (triadicCubeShift z))
  have hstep : ∫ omega : ShellSeq d, volumeAverageVec (openCubeSet z)
        (gluedGradientField hnu LPrime k m (fluxSlot nu LPrime P k e) omega)
        ∂P.toMeasure =
      ∫ omega : ShellSeq d, matVecMul (sigmaStarInvCoarse (openCubeSet z)
        (coefficientCutoff nu omega LPrime).toCoeffField)
        (fluxSlot nu LPrime P k e) ∂P.toMeasure :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun omega =>
      volumeAverageVec_gluedGradientField hnu LPrime k m
        (fluxSlot nu LPrime P k e) omega hz)
  rw [hstep, integralMatVecMul hInt', hblock,
    sigmaBarStarInv_originCube_eq_smul_one hnu LPrime hJ4 (k : ℤ), matVecMulSmulOne,
    fluxSlot, testVector, smul_smul]
  refine congrArg (fun c : ℝ => c • e) ?_
  show sigmaBarStarInvSeq nu LPrime P k * (sigmaBarStarInvSqrt nu LPrime P k)⁻¹ =
    sigmaBarStarInvSqrt nu LPrime P k
  have hsq : Real.sqrt (sigmaBarStarInvSeq nu LPrime P k) *
      Real.sqrt (sigmaBarStarInvSeq nu LPrime P k) = sigmaBarStarInvSeq nu LPrime P k :=
    Real.mul_self_sqrt hpos.le
  have hne : sigmaBarStarInvSqrt nu LPrime P k ≠ 0 :=
    (Real.sqrt_pos.2 hpos).ne'
  rw [sigmaBarStarInvSqrt]
  field_simp
  linarith only [hsq]

end AverageOfVn

end

end SuperdiffusionCLT.Section3.Terms
