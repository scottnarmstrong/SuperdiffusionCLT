/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Homogenization.Book.Ch05.Theorems.Section54.Pigeonhole.RealAlgebra

/-!
# Corrected deterministic pigeonhole estimate

The matrix profile in this file is diagonal in one fixed basis.  Its entries
are arbitrary positive, nonincreasing sequences; no probability law or
ellipticity realization is used.  The potential is the determinant (the
`d`-th power of the determinant-root normalization `ΞDet`).
-/

@[expose] public section

noncomputable section

/-- The determinant potential of a diagonal block profile, equal to the
product of its diagonal entries. -/
def akhcPigeon_thetaPow {d : ℕ} (a : ℕ → Fin d → ℝ) (n : ℕ) : ℝ :=
  ∏ i : Fin d, a n i

private theorem akhcPigeon_antitone
    {d : ℕ} {a : ℕ → Fin d → ℝ}
    (hmono : ∀ n i, a (n + 1) i ≤ a n i) :
    ∀ {n m : ℕ}, n ≤ m → ∀ i, a m i ≤ a n i := by
  intro n m hnm
  induction hnm with
  | refl =>
      intro i
      rfl
  | @step m hnm ih =>
      intro i
      exact le_trans (hmono m i) (ih i)

private theorem akhcPigeon_product_step
    {d : ℕ} (a b : Fin d → ℝ) {c : ℝ}
    (hc : 0 < c) (hb_pos : ∀ i, 0 < b i)
    (hmono : ∀ i, b i ≤ a i)
    (hbad : ¬ ∀ i, a i ≤ c * b i) :
    (∏ i, b i) ≤ c⁻¹ * ∏ i, a i := by
  classical
  have hex : ∃ i, ¬ a i ≤ c * b i := by
    by_contra h
    apply hbad
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i₀, hi₀⟩ := hex
  have hcontract : b i₀ ≤ c⁻¹ * a i₀ :=
    (le_inv_mul_iff₀ hc).2 (not_le.mp hi₀).le
  have hpoint : ∀ i, b i ≤ (if i = i₀ then c⁻¹ else 1) * a i := by
    intro i
    by_cases hi : i = i₀
    · subst i
      simpa using hcontract
    · simpa [hi] using hmono i
  have hprod := Finset.prod_le_prod₀ (s := Finset.univ)
    (fun i hi => (hb_pos i).le)
    (fun i hi => hpoint i)
  calc
    (∏ i, b i) ≤ ∏ i, ((if i = i₀ then c⁻¹ else 1) * a i) := hprod
    _ = (∏ i, if i = i₀ then c⁻¹ else 1) * ∏ i, a i := by
      rw [Finset.prod_mul_distrib]
    _ = c⁻¹ * ∏ i, a i := by rw [Finset.prod_ite_eq']; simp

private theorem akhcPigeon_iterate
    {A : ℕ → ℝ} {r : ℝ} (hr : 0 ≤ r) :
    ∀ k : ℕ,
      (∀ j, 1 ≤ j → j ≤ k → A j ≤ r * A (j - 1)) →
        A k ≤ r ^ k * A 0
  | 0, _ => by simp
  | k + 1, hstep => by
      have hprev : A k ≤ r ^ k * A 0 :=
        akhcPigeon_iterate hr k (by
          intro j hj₁ hjk
          exact hstep j hj₁ (Nat.le_trans hjk (Nat.le_succ k)))
      have hlast : A (k + 1) ≤ r * A k := by
        simpa using hstep (k + 1) (Nat.succ_le_succ (Nat.zero_le k)) le_rfl
      calc
        A (k + 1) ≤ r * A k := hlast
        _ ≤ r * (r ^ k * A 0) := mul_le_mul_of_nonneg_left hprev hr
        _ = r ^ (k + 1) * A 0 := by ring

/-- Corrected deterministic pigeonhole estimate for a nonincreasing diagonal
block profile.  Either one block changes by at most `1 + delta` in every
coordinate, or the determinant potential contracts by `sigma ^ d`.  The
factor `d` in the horizon compensates for taking the `d`-th root to obtain
`ΞDet`.

The matrix sequence is `n ↦ akhcPigeon_block a n`; its Loewner comparison is
equivalent to the displayed coordinate inequalities because all blocks are
diagonal in the same basis. -/
theorem akhcPigeon_main
    {d : ℕ} [NeZero d] (a : ℕ → Fin d → ℝ)
    {delta sigma : ℝ} (hdelta_pos : 0 < delta)
    (hdelta_le : delta ≤ 1 / 2)
    (hsigma_pos : 0 < sigma) (hsigma_le : sigma ≤ 1 / 2)
    (hpos : ∀ n i, 0 < a n i)
    (hmono : ∀ n i, a (n + 1) i ≤ a n i)
    {m₁ h N : ℕ}
    (horizon :
      h * Nat.ceil (2 * (d : ℝ) * delta⁻¹ * |Real.log sigma|) ≤ N) :
    (∃ m : ℕ,
      m₁ + h ≤ m ∧ m ≤ m₁ + N ∧
        ∀ i, a (m - h) i ≤ (1 + delta) * a m i) ∨
      akhcPigeon_thetaPow a (m₁ + N) ≤
        sigma ^ d * akhcPigeon_thetaPow a m₁ := by
  classical
  let k : ℕ := Nat.ceil (2 * (d : ℝ) * delta⁻¹ * |Real.log sigma|)
  by_cases hgood : ∃ m : ℕ,
      m₁ + h ≤ m ∧ m ≤ m₁ + N ∧
        ∀ i, a (m - h) i ≤ (1 + delta) * a m i
  · exact Or.inl hgood
  · right
    let Q : ℕ → ℝ := fun j => akhcPigeon_thetaPow a (m₁ + j * h)
    let r : ℝ := (1 + delta)⁻¹
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hkN : k * h ≤ N := by simpa [k, Nat.mul_comm] using horizon
    have hstep :
        ∀ j : ℕ, 1 ≤ j → j ≤ k → Q j ≤ r * Q (j - 1) := by
      intro j hj₁ hjk
      have hindex : m₁ + j * h - h = m₁ + (j - 1) * h := by
        cases j with
        | zero => omega
        | succ t =>
            simp only [Nat.succ_mul, Nat.succ_sub_one]
            omega
      have hstep_bad :
          ¬ ∀ i, a (m₁ + (j - 1) * h) i ≤
            (1 + delta) * a (m₁ + j * h) i := by
        intro hstep_good
        apply hgood
        refine ⟨m₁ + j * h, ?_, ?_, ?_⟩
        · have hh_le : h ≤ j * h := by
            simpa using Nat.mul_le_mul_right h hj₁
          omega
        · have hjh_le : j * h ≤ k * h := Nat.mul_le_mul_right h hjk
          omega
        · simpa [hindex] using hstep_good
      have hprev_le : m₁ + (j - 1) * h ≤ m₁ + j * h := by
        have hmul : (j - 1) * h ≤ j * h := Nat.mul_le_mul_right h (Nat.sub_le j 1)
        omega
      have hcoordinate_mono :
          ∀ i, a (m₁ + j * h) i ≤ a (m₁ + (j - 1) * h) i :=
        fun i => akhcPigeon_antitone hmono hprev_le i
      have hcontract := akhcPigeon_product_step
        (fun i => a (m₁ + (j - 1) * h) i)
        (fun i => a (m₁ + j * h) i)
        (by positivity)
        (fun i => hpos _ i)
        hcoordinate_mono hstep_bad
      simpa [Q, r, akhcPigeon_thetaPow] using hcontract
    have hgeom : Q k ≤ r ^ k * Q 0 := akhcPigeon_iterate hr k hstep
    have hN_le : m₁ + k * h ≤ m₁ + N := Nat.add_le_add_left hkN _
    have htail :
        r ^ k ≤ sigma ^ d := by
      have hsigma_pow_pos : 0 < sigma ^ d := pow_pos hsigma_pos d
      have hsigma_pow_le_one : sigma ^ d ≤ 1 := by
        exact pow_le_one₀ (by positivity) (by linarith only [hsigma_le])
      have habs :
          |Real.log (sigma ^ d)| = (d : ℝ) * |Real.log sigma| := by
        rw [Real.log_pow sigma d, abs_mul, abs_of_nonneg (Nat.cast_nonneg d)]
      have hceilRaw :
          2 * delta⁻¹ * ((d : ℝ) * |Real.log sigma|) =
            2 * (d : ℝ) * delta⁻¹ * |Real.log sigma| := by
        ring
      have hceilPow :
          Nat.ceil (2 * delta⁻¹ * ((d : ℝ) * |Real.log sigma|)) = k := by
        simpa [k] using congrArg Nat.ceil hceilRaw
      have htail' :=
        Homogenization.Book.Ch05.Section54.Pigeonhole.inv_one_add_delta_pow_natCeil_two_delta_inv_abs_log_le
          hdelta_pos hdelta_le hsigma_pow_pos hsigma_pow_le_one
      rw [habs, hceilPow] at htail'
      simpa [r, inv_pow] using htail'
    have hQ0_nonneg : 0 ≤ Q 0 := by
      apply Finset.prod_nonneg
      intro i hi
      exact (hpos _ i).le
    have hcontract : Q k ≤ sigma ^ d * Q 0 := by
      calc
        Q k ≤ r ^ k * Q 0 := hgeom
        _ ≤ sigma ^ d * Q 0 := mul_le_mul_of_nonneg_right htail hQ0_nonneg
    have hNpotential :
        akhcPigeon_thetaPow a (m₁ + N) ≤ Q k := by
      apply Finset.prod_le_prod₀ (s := Finset.univ)
      · intro i hi
        exact (hpos _ i).le
      · intro i hi
        apply akhcPigeon_antitone hmono
        omega
    calc
      akhcPigeon_thetaPow a (m₁ + N) ≤ Q k := hNpotential
      _ ≤ sigma ^ d * Q 0 := hcontract
      _ = sigma ^ d * akhcPigeon_thetaPow a m₁ := by simp [Q]

end
