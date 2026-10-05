/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import SuperdiffusionCLT.Section2.Annealed.InfiniteVolumeBelow
public import SuperdiffusionCLT.Section3.Setup.Parameters

/-!
# The pigeonhole selection of the scale `m`

The paper selects the scale `m` at
which the proof of Proposition `p.sstar.lower.bound` is run. Setting
`A_k = bfAhom_L(cu_k)`, the print records

> By subadditivity, `k ↦ A_k` is nonincreasing in the Loewner order. Moreover,
> `e.Enaught.vs.A.and.Ahom` gives `bfAhom_L ≤ A_k ≤ bfE_L`, while
> `det bfAhom_L = 1` and `det bfE_L ≤ (Cν⁻¹L)^{2d}`. If the following
> conclusion failed for every `m` in the lattice `⌊L/4⌋ + 2hℕ`, with
> `m ∈ [⌊L/4⌋ + 2h, ⌊L/2⌋]`, then telescoping the determinant ratios would give
> `(1+δ)^{⌊L/(8h)⌋−2} ≤ det A_{⌊L/4⌋}/det bfAhom_L ≤ (Cν⁻¹L)^{2d}`,

contradicting the second condition of `e.h.restrictions`, and concluding with
the existence of `m ∈ ℕ ∩ [L/4, L/2]` satisfying `e.pigeon.matrix`.

## The scalar reduction

Under J4 the annealed block matrix on an origin cube is block diagonal with
scalar diagonal blocks (`e.homs.defs.U`, available as
`annealedBlockMatrix_originCube_upperLeft_eq_sigmaBar`,
`sigmaBarStarInv_originCube_eq_smul_one` and the vanishing of the two
off-diagonal blocks). Hence

`det A_k = (shom_L(cu_k) · shom_{L,*}^{-1}(cu_k))^d`,

and the whole subargument reduces to the two real sequences
`sigmaBarSeq nu L P` and `sigmaBarStarInvSeq nu L P`, which
`Section2/Annealed/InfiniteVolume.lean` proves nonincreasing and positive. The
telescoping is carried out on their product by `exists_step_of_antitone`.

## What replaces `det bfAhom_L = 1`

The printed normalization `det bfAhom_L = 1` reads the block-diagonal
infinite-volume matrix `diag(shom_L Id, shom_{L,*}^{-1} Id)` as having
reciprocal diagonal scalars, which is exactly the identification
`sigmaBarUpperLimit = sigmaBarInfinite`; that identification is the qualitative homogenization
input of `AK.HC` and is **not** available. Nothing below uses it. The
determinant ratio is instead bounded through the annealed contrast inequality
`1 ≤ shom_L(cu_k) · shom_{L,*}^{-1}(cu_k)`
(`one_le_sigmaBarScalar_mul_sigmaBarStarInvScalar`, proved unconditionally),
which says `det A_k ≥ 1` at every scale and is all the telescoping needs: the
ratio `det A_{k₀}/det A_{k₀+2hN}` is at most `det bfE_L`, and the envelope
bound `det bfE_L ≤ (Cν⁻¹L)^{2d}` enters through the two envelope scalars of
`Section2/Annealed/Envelope.lean`.

## The counting hypothesis

The theorems below carry the counting comparison
`envelopeScalarProduct d nu L < (1 + delta) ^ N` — with the number `N` of
lattice steps free, where the print fixes `N = ⌊L/(8h)⌋ − 2` — as an explicit
hypothesis `hlt`. The print derives it from the second
condition of `e.h.restrictions` (`C log(Cν⁻¹L) h/δ ≤ L`)
through the exponential estimate `log(1+δ) ≥ δ/2`, and that
derivation is carried out, in exactly that exponential form, in
`envelopeScalarProduct_lt_one_add_delta_pow_of_windowRestrictions`, not here.
A *linear* comparison of the shape `R < 1 + Nδ` cannot play this role: the
envelope scalars are polynomially large in `L`, while the lattice range keeps
`N ≤ L`, so no admissible `N` makes `1 + Nδ` beat `envelopeScalarProduct`; no
such linear step is used, or available, here.

## The form of the conclusion

`e.pigeon.matrix` prints the normalized comparison
`|bfAhom_L^{-1/2}(cu_m) bfAhom_L(cu_{m−2h}) bfAhom_L^{-1/2}(cu_m) − I_{2d}| ≤ δ`.
This is read here as the
square-root-free two-sided Loewner comparison
`(1 − δ) bfAhom_L(cu_m) ≤ bfAhom_L(cu_{m−2h}) ≤ (1 + δ) bfAhom_L(cu_m)`.
The scalar selection theorem of this module is `exists_pigeonhole_scale`.
-/

@[expose] public section

namespace SuperdiffusionCLT.Section3.Setup

open Homogenization MeasureTheory
open SuperdiffusionCLT.Frozen.Assumptions
open SuperdiffusionCLT.Section2.Annealed
open SuperdiffusionCLT.Section2.Cutoff

noncomputable section

variable {d : ℕ}

/-! ## The telescoping pigeonhole for two nonincreasing positive sequences -/

section Telescoping

/-- **The telescoping step of the pigeonhole argument.** If neither of two
nonincreasing positive sequences `u`, `v` has an index `j < N` at which both
`u j ≤ (1+δ) u (j+1)` and `v j ≤ (1+δ) v (j+1)`, then the product `u · v`
contracts by a factor `1 + δ` at every one of the `N` steps, so
`(1+δ)^N (u N · v N) ≤ u 0 · v 0`. Together with a ratio bound
`u 0 · v 0 ≤ R (u N · v N)` this forces `(1+δ)^N ≤ R`; the hypothesis
`R < (1+δ)^N` therefore produces the index. -/
theorem exists_step_of_antitone {u v : ℕ → ℝ} (hu : Antitone u) (hv : Antitone v)
    (hupos : ∀ j, 0 < u j) (hvpos : ∀ j, 0 < v j) {delta R : ℝ}
    (hdelta : 0 ≤ delta) {N : ℕ} (hR : u 0 * v 0 ≤ R * (u N * v N))
    (hlt : R < (1 + delta) ^ N) :
    ∃ j < N, u j ≤ (1 + delta) * u (j + 1) ∧ v j ≤ (1 + delta) * v (j + 1) := by
  by_contra hcon
  push Not at hcon
  have hbase : (0 : ℝ) ≤ 1 + delta := by linarith only [hdelta]
  have key : ∀ n, n ≤ N → (1 + delta) ^ n * (u n * v n) ≤ u 0 * v 0 := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ k ih =>
        intro hk
        have hkN : k < N := hk
        have hstep : (1 + delta) * (u (k + 1) * v (k + 1)) ≤ u k * v k := by
          by_cases hcase : u k ≤ (1 + delta) * u (k + 1)
          · have hv' : (1 + delta) * v (k + 1) < v k := hcon k hkN hcase
            have huk : u (k + 1) ≤ u k := hu (Nat.le_succ k)
            have h1 : u (k + 1) * ((1 + delta) * v (k + 1)) ≤ u (k + 1) * v k :=
              mul_le_mul_of_nonneg_left hv'.le (hupos (k + 1)).le
            have h2 : u (k + 1) * v k ≤ u k * v k :=
              mul_le_mul_of_nonneg_right huk (hvpos k).le
            calc (1 + delta) * (u (k + 1) * v (k + 1))
                = u (k + 1) * ((1 + delta) * v (k + 1)) := by ring
              _ ≤ u (k + 1) * v k := h1
              _ ≤ u k * v k := h2
          · push Not at hcase
            have hvk : v (k + 1) ≤ v k := hv (Nat.le_succ k)
            have h1 : (1 + delta) * u (k + 1) * v (k + 1) ≤ u k * v (k + 1) :=
              mul_le_mul_of_nonneg_right hcase.le (hvpos (k + 1)).le
            have h2 : u k * v (k + 1) ≤ u k * v k :=
              mul_le_mul_of_nonneg_left hvk (hupos k).le
            calc (1 + delta) * (u (k + 1) * v (k + 1))
                = (1 + delta) * u (k + 1) * v (k + 1) := by ring
              _ ≤ u k * v (k + 1) := h1
              _ ≤ u k * v k := h2
        calc (1 + delta) ^ (k + 1) * (u (k + 1) * v (k + 1))
            = (1 + delta) ^ k * ((1 + delta) * (u (k + 1) * v (k + 1))) := by ring
          _ ≤ (1 + delta) ^ k * (u k * v k) :=
              mul_le_mul_of_nonneg_left hstep (pow_nonneg hbase k)
          _ ≤ u 0 * v 0 := ih (Nat.le_of_succ_le hk)
  have hNN := key N le_rfl
  have hpos : 0 < u N * v N := mul_pos (hupos N) (hvpos N)
  have hfinal : (1 + delta) ^ N * (u N * v N) ≤ R * (u N * v N) := by
    linarith only [hNN, hR]
  exact absurd hlt (not_lt.2 (le_of_mul_le_mul_right hfinal hpos))

end Telescoping

/-! ## The scalar determinant envelope -/

/-- The scalar whose `d`-th power is `det bfE_L`: the product of the two
diagonal scalars of the envelope matrix `bfE_L` of `e.Enaught.mixing`. The
printed bound `det bfE_L ≤ (Cν⁻¹L)^{2d}` becomes, for
this scalar, the bound `≤ 6 (Cν⁻¹L)²` proved as `envelopeScalarProduct_le`;
the sharper bound `≤ (Cν⁻¹L)²` is not
proved there. -/
def envelopeScalarProduct (d : ℕ) (nu : ℝ) (L : ℕ) : ℝ :=
  envelopeUpperScalar d nu L * envelopeLowerScalar d nu

theorem envelopeScalarProduct_pos {nu : ℝ} (hnu : 0 < nu) (d L : ℕ) :
    0 < envelopeScalarProduct d nu L :=
  mul_pos (envelopeUpperScalar_pos hnu d L) (envelopeLowerScalar_pos hnu d)

/-! ## The scalar action on doubled block matrices -/

/-! ## The pigeonhole selection -/

section Selection

variable [NeZero d] {nu : ℝ} (hnu : 0 < nu) (L : ℕ)
  {P : ProbabilityMeasure (ShellSeq d)} (hPrefix : ShellLawPrefix d P)
  (hJ2 : ShellLawJ2 d P) (hJ3 : ShellLawJ3 d P) (hJ4 : ShellLawJ4 d P)

include hnu hPrefix hJ2 hJ3 hJ4

/-- **`det A_k ≥ 1` in scalar form**: the annealed contrast inequality of
`InfiniteVolume.lean` read along the sequences of `e.homs.defs`. -/
theorem one_le_sigmaBarSeq_mul_sigmaBarStarInvSeq (n : ℕ) :
    1 ≤ sigmaBarSeq nu L P n * sigmaBarStarInvSeq nu L P n :=
  one_le_sigmaBarScalar_mul_sigmaBarStarInvScalar hnu L hPrefix hJ2 hJ3 hJ4 (n : ℤ)

/-- **The determinant ratio bound** in scalar form: the product of
the two annealed scalars at any scale is at most the envelope scalar product,
and at every scale it is at least `1`, so the ratio between any two scales is
at most `envelopeScalarProduct`. -/
theorem sigmaBarSeq_mul_le_envelopeScalarProduct (n : ℕ) :
    sigmaBarSeq nu L P n * sigmaBarStarInvSeq nu L P n ≤
      envelopeScalarProduct d nu L := by
  have h1 := sigmaBarSeq_le_envelopeUpperScalar hnu L hPrefix hJ2 hJ3 hJ4 n
  have h2 := sigmaBarStarInvSeq_le_envelopeLowerScalar hnu L hPrefix hJ2 hJ3 hJ4 n
  have hpos := sigmaBarStarInvSeq_pos hnu L hPrefix hJ2 hJ3 hJ4 n
  have hU := envelopeUpperScalar_pos hnu d L
  have hstep1 : sigmaBarSeq nu L P n * sigmaBarStarInvSeq nu L P n ≤
      envelopeUpperScalar d nu L * sigmaBarStarInvSeq nu L P n :=
    mul_le_mul_of_nonneg_right h1 hpos.le
  have hstep2 : envelopeUpperScalar d nu L * sigmaBarStarInvSeq nu L P n ≤
      envelopeUpperScalar d nu L * envelopeLowerScalar d nu :=
    mul_le_mul_of_nonneg_left h2 hU.le
  exact le_trans hstep1 (le_trans hstep2 (le_of_eq rfl))

/-- **The pigeonhole step on the lattice `k₀ + 2hℕ`**, under
the explicit counting hypothesis `hlt` (the pigeonhole step proper; the print
derives the hypothesis, and
`envelopeScalarProduct_lt_one_add_delta_pow_of_windowRestrictions` discharges it
from the window restrictions). If the number `N` of available steps satisfies
`envelopeScalarProduct < (1+δ)^N`, then one of the `N` steps of length `2h`
starting at `k₀` satisfies the `δ` comparison in both diagonal blocks
simultaneously. -/
theorem exists_lattice_step (k0 h N : ℕ) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hlt : envelopeScalarProduct d nu L < (1 + delta) ^ N) :
    ∃ j < N,
      sigmaBarSeq nu L P (k0 + 2 * h * j) ≤
          (1 + delta) * sigmaBarSeq nu L P (k0 + 2 * h * (j + 1)) ∧
        sigmaBarStarInvSeq nu L P (k0 + 2 * h * j) ≤
          (1 + delta) * sigmaBarStarInvSeq nu L P (k0 + 2 * h * (j + 1)) := by
  have hmono : Monotone fun j : ℕ => k0 + 2 * h * j := by
    intro i j hij
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hij) _
  have hu : Antitone fun j : ℕ => sigmaBarSeq nu L P (k0 + 2 * h * j) :=
    (antitone_sigmaBarSeq hnu L hPrefix hJ2 hJ3 hJ4).comp_monotone hmono
  have hv : Antitone fun j : ℕ => sigmaBarStarInvSeq nu L P (k0 + 2 * h * j) :=
    (antitone_sigmaBarStarInvSeq hnu L hPrefix hJ2 hJ3 hJ4).comp_monotone hmono
  have hupos : ∀ j : ℕ, 0 < sigmaBarSeq nu L P (k0 + 2 * h * j) := fun j =>
    sigmaBarSeq_pos hnu L hPrefix hJ2 hJ3 hJ4 _
  have hvpos : ∀ j : ℕ, 0 < sigmaBarStarInvSeq nu L P (k0 + 2 * h * j) := fun j =>
    sigmaBarStarInvSeq_pos hnu L hPrefix hJ2 hJ3 hJ4 _
  have hEpos := envelopeScalarProduct_pos hnu d L
  have hend := one_le_sigmaBarSeq_mul_sigmaBarStarInvSeq hnu L hPrefix hJ2 hJ3 hJ4
    (k0 + 2 * h * N)
  have hstart := sigmaBarSeq_mul_le_envelopeScalarProduct hnu L hPrefix hJ2 hJ3 hJ4
    (k0 + 2 * h * 0)
  have hR : sigmaBarSeq nu L P (k0 + 2 * h * 0) *
        sigmaBarStarInvSeq nu L P (k0 + 2 * h * 0) ≤
      envelopeScalarProduct d nu L *
        (sigmaBarSeq nu L P (k0 + 2 * h * N) *
          sigmaBarStarInvSeq nu L P (k0 + 2 * h * N)) := by
    have := mul_le_mul_of_nonneg_left hend hEpos.le
    rw [mul_one] at this
    exact le_trans hstart this
  exact exists_step_of_antitone hu hv hupos hvpos hdelta hR hlt

/-- **`p.sstar.lower.bound#pigeonhole-scale`**, in scalar form,
under the explicit counting hypothesis `hlt` (the pigeonhole step proper; the
print derives the hypothesis, and
`envelopeScalarProduct_lt_one_add_delta_pow_of_windowRestrictions` discharges it
from the window restrictions). Taking the lattice base `k₀ = ⌊L/4⌋` and `N` steps of length
`2h` inside `[⌊L/4⌋, ⌊L/2⌋]`, there is a scale `m ∈ ℕ ∩ [L/4, L/2]` in the
lattice `⌊L/4⌋ + 2hℕ`, with `m ≥ ⌊L/4⌋ + 2h`, at which both annealed scalars
satisfy the `δ` comparison against the scale `m − 2h`. The conclusion
`L / 4 + 2 * h ≤ m` is the `ℕ`-division form of the printed `m ≥ ⌊L/4⌋ + 2h`;
the print states the range as `m ∈ ℕ ∩ [L/4, L/2]`
with the *real* `L/4`, and that lower endpoint is recovered from the `ℕ` one
for `h ≥ 1`, since then `m ≥ ⌊L/4⌋ + 2 > L/4`. -/
theorem exists_pigeonhole_scale (h N : ℕ) (hN : L / 4 + 2 * h * N ≤ L / 2)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hlt : envelopeScalarProduct d nu L < (1 + delta) ^ N) :
    ∃ m : ℕ, L / 4 + 2 * h ≤ m ∧ m ≤ L / 2 ∧ 2 * h ≤ m ∧
      (∃ j : ℕ, m = L / 4 + 2 * h * (j + 1)) ∧
      sigmaBarSeq nu L P (m - 2 * h) ≤ (1 + delta) * sigmaBarSeq nu L P m ∧
        sigmaBarStarInvSeq nu L P (m - 2 * h) ≤
          (1 + delta) * sigmaBarStarInvSeq nu L P m := by
  obtain ⟨j, hjN, hju, hjv⟩ :=
    exists_lattice_step hnu L hPrefix hJ2 hJ3 hJ4 (L / 4) h N hdelta hlt
  have hexp : 2 * h * (j + 1) = 2 * h * j + 2 * h := by ring
  have hstep : 2 * h * (j + 1) ≤ 2 * h * N := Nat.mul_le_mul_left _ hjN
  have hzero : 0 ≤ 2 * h * j := Nat.zero_le _
  refine ⟨L / 4 + 2 * h * (j + 1), by omega, by omega, by omega, ⟨j, rfl⟩, ?_, ?_⟩
  · have hrw : L / 4 + 2 * h * (j + 1) - 2 * h = L / 4 + 2 * h * j := by omega
    rw [hrw]; exact hju
  · have hrw : L / 4 + 2 * h * (j + 1) - 2 * h = L / 4 + 2 * h * j := by omega
    rw [hrw]; exact hjv

/-! ### The matrix form `e.pigeon.matrix` -/

end Selection

end

end SuperdiffusionCLT.Section3.Setup
