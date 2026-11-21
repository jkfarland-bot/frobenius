module

/-
Run r25, seat L1: shared foundation for the Frobenius level counts (ledger R-058, R-060, R-080).

Abstract setting: a commutative ring `A`, a prime `p`, a ring endomorphism `σ` of `A` with
`σ a ≡ a ^ p (mod p A)` (a Frobenius lift), `B = σ(A)`.
Concrete setting: `A = MvPowerSeries τ R` with `σ = frob p`, the substitution `x_i ↦ x_i ^ p`
(Mathlib's `MvPowerSeries.expand`), for every coefficient ring `R` with `a ^ p ≡ a (mod p R)`;
this covers `R = ℤ` and `R = ℤ_[p]`.

Lean v4.33.1 with Mathlib. No sorry, no axioms beyond propext, Classical.choice, Quot.sound.
See FOUNDATION.md for the list of definitions and how to import this file.
-/
public import Mathlib

@[expose] public section

-- Port (Mathlib v4.35.0-rc2): restore the v4.33 instance path for `AddCommGroup (ZMod p)`.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace FrobLevel

/-! ## 1. Abstract setting -/

section Abstract

open Polynomial

variable {A : Type*} [CommRing A]

/-- `σ` is a Frobenius lift for the prime `p`: `σ a ≡ a ^ p` modulo `p A`. -/
def IsFrobLift (p : ℕ) (σ : A →+* A) : Prop := ∀ a : A, (p : A) ∣ σ a - a ^ p

/-- `A` has no `p`-torsion. -/
def NoPTorsion (p : ℕ) (A : Type*) [CommRing A] : Prop := ∀ a : A, (p : A) * a = 0 → a = 0

/-- The Frobenius image `B = σ(A)`, a subring of `A`. -/
abbrev frobImage (σ : A →+* A) : Subring A := σ.range

/-- `B[X]` inside `A[X]`: the polynomials all of whose coefficients lie in `B = σ(A)`. -/
noncomputable abbrev BPoly (σ : A →+* A) : Subring A[X] := (Polynomial.mapRingHom σ).range

theorem mem_BPoly_iff {σ : A →+* A} {P : A[X]} : P ∈ BPoly σ ↔ ∀ i, P.coeff i ∈ frobImage σ :=
  Polynomial.mem_map_range σ

theorem C_mem_BPoly (σ : A →+* A) (a : A) : C (σ a) ∈ BPoly σ := ⟨C a, by simp⟩

theorem X_mem_BPoly (σ : A →+* A) : (X : A[X]) ∈ BPoly σ := ⟨X, by simp⟩

theorem natCast_mem_BPoly (σ : A →+* A) (n : ℕ) : ((n : A[X])) ∈ BPoly σ := natCast_mem _ n

/-- `δ(a) = (σ a - a ^ p) / p`: a choice of quotient; it is the quotient when `A` has no
`p`-torsion (`delta_unique`). -/
noncomputable def delta {p : ℕ} {σ : A →+* A} (h : IsFrobLift p σ) (a : A) : A :=
  Classical.choose (h a)

theorem p_mul_delta {p : ℕ} {σ : A →+* A} (h : IsFrobLift p σ) (a : A) :
    (p : A) * delta h a = σ a - a ^ p :=
  (Classical.choose_spec (h a)).symm

theorem delta_unique {p : ℕ} {σ : A →+* A} (ht : NoPTorsion p A) (h : IsFrobLift p σ) {a d : A}
    (hd : (p : A) * d = σ a - a ^ p) : d = delta h a := by
  have : (p : A) * (d - delta h a) = 0 := by rw [mul_sub, hd, p_mul_delta, sub_self]
  exact sub_eq_zero.1 (ht _ this)

/-- Level form (ledger R-058, note Definition 5.1): there are `g_0, ..., g_L` in `A` with
`1/f ≡ ∑_{z ≤ L} f ^ z σ(g_z) (mod p ^ k A)`, written without the inverse as
`f * ∑_{z ≤ L} f ^ z σ(g_z) ≡ 1`. (The statement forces `f` to be a unit modulo `p ^ k`.) -/
def HasLevel (p : ℕ) (σ : A →+* A) (f : A) (k L : ℕ) : Prop :=
  ∃ g : ℕ → A, (p : A) ^ k ∣ 1 - f * ∑ z ∈ Finset.range (L + 1), f ^ z * σ (g z)

/-- Monic form (ledger R-060, note Lemma 5.2): some monic `P ∈ B[X]` of degree `m` has
`P(u) ∈ p ^ k A`. -/
def MonicAnn (p : ℕ) (σ : A →+* A) (u : A) (k m : ℕ) : Prop :=
  ∃ P : A[X], P.Monic ∧ P.natDegree = m ∧ P ∈ BPoly σ ∧ (p : A) ^ k ∣ P.eval u

/-- The level count `L_f(p, k)`: the least `L` with a level `L` identity (`0` if there is none;
use it together with a `HasLevel` witness). -/
noncomputable def levelCount (p : ℕ) (σ : A →+* A) (f : A) (k : ℕ) : ℕ :=
  sInf {L | HasLevel p σ f k L}

/-- The least degree of a monic annihilator of `u` modulo `p ^ k` over `B`
(`0` if there is none). For `u = 1/f` this is `L_f(p, k) + 1` (`levelCount_add_one`). -/
noncomputable def annDegree (p : ℕ) (σ : A →+* A) (u : A) (k : ℕ) : ℕ :=
  sInf {m | MonicAnn p σ u k m}

theorem levelCount_le {p : ℕ} {σ : A →+* A} {f : A} {k L : ℕ} (h : HasLevel p σ f k L) :
    levelCount p σ f k ≤ L := Nat.sInf_le h

theorem annDegree_le {p : ℕ} {σ : A →+* A} {u : A} {k m : ℕ} (h : MonicAnn p σ u k m) :
    annDegree p σ u k ≤ m := Nat.sInf_le h

theorem hasLevel_levelCount {p : ℕ} {σ : A →+* A} {f : A} {k L : ℕ} (h : HasLevel p σ f k L) :
    HasLevel p σ f k (levelCount p σ f k) := Nat.sInf_mem (s := {L | HasLevel p σ f k L}) ⟨L, h⟩

theorem monicAnn_annDegree {p : ℕ} {σ : A →+* A} {u : A} {k m : ℕ} (h : MonicAnn p σ u k m) :
    MonicAnn p σ u k (annDegree p σ u k) := Nat.sInf_mem (s := {m | MonicAnn p σ u k m}) ⟨m, h⟩

/-- A monic annihilator of degree `m` gives one of every larger degree (multiply by `X`). -/
theorem MonicAnn.succ [Nontrivial A] {p : ℕ} {σ : A →+* A} {u : A} {k m : ℕ}
    (h : MonicAnn p σ u k m) : MonicAnn p σ u k (m + 1) := by
  obtain ⟨P, hmon, hdeg, hB, hP⟩ := h
  refine ⟨P * X, hmon.mul monic_X, ?_, mul_mem hB (X_mem_BPoly σ), ?_⟩
  · rw [hmon.natDegree_mul monic_X, hdeg, natDegree_X]
  · rw [eval_mul, eval_X]; exact Dvd.dvd.mul_right hP u

theorem MonicAnn.mono [Nontrivial A] {p : ℕ} {σ : A →+* A} {u : A} {k m m' : ℕ}
    (h : MonicAnn p σ u k m) (hm : m ≤ m') : MonicAnn p σ u k m' := by
  induction hm with
  | refl => exact h
  | step _ ih => exact ih.succ

/-- A level `L` identity gives one of every larger level (take the new `g_z` to be `0`). -/
theorem HasLevel.mono {p : ℕ} {σ : A →+* A} {f : A} {k L L' : ℕ}
    (h : HasLevel p σ f k L) (hL : L ≤ L') : HasLevel p σ f k L' := by
  obtain ⟨g, hg⟩ := h
  refine ⟨fun z => if z < L + 1 then g z else 0, ?_⟩
  have : ∑ z ∈ Finset.range (L' + 1), f ^ z * σ (if z < L + 1 then g z else 0)
      = ∑ z ∈ Finset.range (L + 1), f ^ z * σ (g z) := by
    have hsub : Finset.range (L + 1) ⊆ Finset.range (L' + 1) :=
      Finset.range_subset_range.2 (by omega)
    rw [← Finset.sum_subset hsub]
    · exact Finset.sum_congr rfl fun z hz => by rw [if_pos (Finset.mem_range.1 hz)]
    · intro z _ hz
      rw [if_neg (by simpa using hz), map_zero, mul_zero]
  rw [this]; exact hg

/-- Monic form, first half (note Lemma 5.2): a level `L` identity for `f` gives a monic
annihilator of degree `L + 1` of any inverse `u` of `f` modulo `p ^ k`. -/
theorem HasLevel.monicAnn [Nontrivial A] {p : ℕ} {σ : A →+* A} {f u : A} {k L : ℕ}
    (hfu : (p : A) ^ k ∣ f * u - 1) (h : HasLevel p σ f k L) : MonicAnn p σ u k (L + 1) := by
  obtain ⟨g, hg⟩ := h
  set Q : A[X] := ∑ z ∈ Finset.range (L + 1), C (g z) * X ^ (L - z) with hQ
  have hdeg : Q.degree < ((L + 1 : ℕ) : WithBot ℕ) := by
    refine (degree_sum_le _ _).trans_lt ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro z _
    refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
    exact_mod_cast Nat.lt_succ_of_le (Nat.sub_le L z)
  have hmon : (X ^ (L + 1) - Q).Monic := monic_X_pow_sub hdeg
  refine ⟨(X ^ (L + 1) - Q).map σ, hmon.map σ, ?_, ⟨_, rfl⟩, ?_⟩
  · rw [hmon.natDegree_map]
    exact natDegree_eq_of_degree_eq_some (by
      rw [degree_sub_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow])
  · have hev : ((X ^ (L + 1) - Q).map σ).eval u
        = u ^ (L + 1) - ∑ z ∈ Finset.range (L + 1), σ (g z) * u ^ (L - z) := by
      rw [eval_map, eval₂_sub, eval₂_X_pow, hQ, eval₂_finsetSum]
      simp only [eval₂_mul, eval₂_C, eval₂_X_pow]
    have hterm : ∀ z ∈ Finset.range (L + 1),
        u ^ (L + 1) * (f * (f ^ z * σ (g z))) = σ (g z) * u ^ (L - z) * (f * u) ^ (z + 1) := by
      intro z hz
      have hz' : L + 1 = (L - z) + (z + 1) := by have := Finset.mem_range.1 hz; omega
      have e : u ^ (L + 1) = u ^ (L - z) * u ^ (z + 1) := by rw [← pow_add, ← hz']
      rw [e, mul_pow]; ring
    have key : u ^ (L + 1) - ∑ z ∈ Finset.range (L + 1), σ (g z) * u ^ (L - z)
        = u ^ (L + 1) * (1 - f * ∑ z ∈ Finset.range (L + 1), f ^ z * σ (g z))
          + ∑ z ∈ Finset.range (L + 1), σ (g z) * u ^ (L - z) * ((f * u) ^ (z + 1) - 1) := by
      have h1 : u ^ (L + 1) * (f * ∑ z ∈ Finset.range (L + 1), f ^ z * σ (g z))
          = ∑ z ∈ Finset.range (L + 1), σ (g z) * u ^ (L - z) * (f * u) ^ (z + 1) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl hterm
      have h2 : ∑ z ∈ Finset.range (L + 1), σ (g z) * u ^ (L - z) * ((f * u) ^ (z + 1) - 1)
          = ∑ z ∈ Finset.range (L + 1), σ (g z) * u ^ (L - z) * (f * u) ^ (z + 1)
            - ∑ z ∈ Finset.range (L + 1), σ (g z) * u ^ (L - z) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun z _ => by ring
      rw [mul_sub, mul_one, h1, h2]; ring
    rw [hev, key]
    refine dvd_add (Dvd.dvd.mul_left hg _) (Finset.dvd_sum fun z _ => Dvd.dvd.mul_left ?_ _)
    exact hfu.trans (by simpa using sub_dvd_pow_sub_pow (f * u) 1 (z + 1))

/-- Monic form, second half: a monic annihilator of degree `L + 1` of an inverse `u` of `f`
modulo `p ^ k` gives a level `L` identity for `f`. -/
theorem MonicAnn.hasLevel {p : ℕ} {σ : A →+* A} {f u : A} {k L : ℕ}
    (hfu : (p : A) ^ k ∣ f * u - 1) (h : MonicAnn p σ u k (L + 1)) : HasLevel p σ f k L := by
  obtain ⟨P, hmon, hdeg, hB, hP⟩ := h
  rw [mem_BPoly_iff] at hB
  choose h hh using hB
  refine ⟨fun z => - h (L - z), ?_⟩
  have hev : P.eval u = ∑ i ∈ Finset.range (L + 2), P.coeff i * u ^ i := by
    rw [eval_eq_sum_range, hdeg]
  have htop : P.coeff (L + 1) = 1 := by rw [← hdeg]; exact hmon.coeff_natDegree
  have hterm : ∀ i ∈ Finset.range (L + 2),
      f ^ (L + 1) * (P.coeff i * u ^ i) - P.coeff i * f ^ (L + 1 - i) * ((f * u) ^ i - 1)
        = P.coeff i * f ^ (L + 1 - i) := by
    intro i hi
    have hi' : L + 1 = (L + 1 - i) + i := by have := Finset.mem_range.1 hi; omega
    have : f ^ (L + 1) = f ^ (L + 1 - i) * f ^ i := by rw [← pow_add, ← hi']
    rw [this, mul_pow]; ring
  have hR : f ^ (L + 1) * P.eval u
        - ∑ i ∈ Finset.range (L + 2), P.coeff i * f ^ (L + 1 - i) * ((f * u) ^ i - 1)
      = ∑ i ∈ Finset.range (L + 2), P.coeff i * f ^ (L + 1 - i) := by
    rw [hev, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl hterm
  have hL : f * ∑ z ∈ Finset.range (L + 1), f ^ z * σ (- h (L - z))
      = - ∑ i ∈ Finset.range (L + 1), P.coeff i * f ^ (L + 1 - i) := by
    rw [Finset.mul_sum, ← Finset.sum_range_reflect (fun i => P.coeff i * f ^ (L + 1 - i)) (L + 1),
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hz' := Finset.mem_range.1 hz
    have e1 : L + 1 - 1 - z = L - z := by omega
    have e2 : L + 1 - (L - z) = z + 1 := by omega
    simp only [e1, e2, map_neg, hh, pow_succ]; ring
  have key : 1 - f * ∑ z ∈ Finset.range (L + 1), f ^ z * σ (- h (L - z))
      = f ^ (L + 1) * P.eval u
        - ∑ i ∈ Finset.range (L + 2), P.coeff i * f ^ (L + 1 - i) * ((f * u) ^ i - 1) := by
    rw [hR, hL, Finset.sum_range_succ _ (L + 1), htop, Nat.sub_self, pow_zero, mul_one]; ring
  rw [key]
  refine dvd_sub (Dvd.dvd.mul_left hP _) (Finset.dvd_sum fun i _ => Dvd.dvd.mul_left ?_ _)
  exact hfu.trans (by simpa using sub_dvd_pow_sub_pow (f * u) 1 i)

/-- Monic form (note Lemma 5.2): for `u` an inverse of `f` modulo `p ^ k`, a level `L`
identity exists iff `u` has a monic annihilator of degree `L + 1` over `B` modulo `p ^ k`. -/
theorem hasLevel_iff_monicAnn [Nontrivial A] {p : ℕ} {σ : A →+* A} {f u : A} {k : ℕ}
    (hfu : (p : A) ^ k ∣ f * u - 1) (L : ℕ) :
    HasLevel p σ f k L ↔ MonicAnn p σ u k (L + 1) :=
  ⟨fun h => h.monicAnn hfu, fun h => h.hasLevel hfu⟩

/-- A monic polynomial of degree `0` is `1`, so a degree `0` annihilator means `p ^ k` is a
unit of `A`. -/
theorem not_monicAnn_zero {p : ℕ} {σ : A →+* A} {u : A} {k : ℕ} (hpk : ¬ IsUnit ((p : A) ^ k)) :
    ¬ MonicAnn p σ u k 0 := by
  rintro ⟨P, hmon, hdeg, -, hP⟩
  have : P = 1 := by
    have h1 := eq_C_of_natDegree_eq_zero hdeg
    have h2 : P.coeff 0 = 1 := by simpa [hdeg] using hmon.coeff_natDegree
    rw [h1, h2, map_one]
  rw [this, eval_one] at hP
  exact hpk (isUnit_of_dvd_one hP)

/-- `L_f(p, k) + 1` is the least degree of a monic annihilator of `u = 1/f` over `B` modulo
`p ^ k`, provided some annihilator exists and `p ^ k` is not a unit of `A`. -/
theorem levelCount_add_one [Nontrivial A] {p : ℕ} {σ : A →+* A} {f u : A} {k m : ℕ}
    (hfu : (p : A) ^ k ∣ f * u - 1) (hpk : ¬ IsUnit ((p : A) ^ k)) (hex : MonicAnn p σ u k m) :
    levelCount p σ f k + 1 = annDegree p σ u k := by
  have hmin := monicAnn_annDegree hex
  have hpos : annDegree p σ u k ≠ 0 := fun h0 => not_monicAnn_zero hpk (h0 ▸ hmin)
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  rw [hd] at hmin ⊢
  have hlev : HasLevel p σ f k d := hmin.hasLevel hfu
  have h1 : levelCount p σ f k ≤ d := levelCount_le hlev
  have h2 : annDegree p σ u k ≤ levelCount p σ f k + 1 :=
    annDegree_le ((hasLevel_levelCount hlev).monicAnn hfu)
  omega

/-- The form of ledger R-060: some `R ∈ B[X]` of degree at most `m`, with constant term a unit
of `B` and `R(f) ∈ p ^ k A`. (`L_f + 1` is the least such `m`: `levelCount_add_one_rev`.) -/
def RevAnn (p : ℕ) (σ : A →+* A) (f : A) (k m : ℕ) : Prop :=
  ∃ R : A[X], R ∈ BPoly σ ∧ R.natDegree ≤ m ∧ (∃ c ∈ frobImage σ, c * R.coeff 0 = 1) ∧
    (p : A) ^ k ∣ R.eval f

/-- The least `m` with `RevAnn p σ f k m` (`0` if there is none). -/
noncomputable def revDegree (p : ℕ) (σ : A →+* A) (f : A) (k : ℕ) : ℕ :=
  sInf {m | RevAnn p σ f k m}

/-- R-060 form = monic form: for `u` an inverse of `f` modulo `p ^ k`, `u` has a monic
annihilator of degree `m` over `B` iff some `R ∈ B[X]` of degree `≤ m` with `R(0)` a unit of `B`
has `R(f) ≡ 0` (reflect the polynomial; computed in `A ⧸ p ^ k A`, where `f` is invertible). -/
theorem monicAnn_iff_revAnn [Nontrivial A] {p : ℕ} {σ : A →+* A} {f u : A} {k : ℕ}
    (hfu : (p : A) ^ k ∣ f * u - 1) (m : ℕ) : MonicAnn p σ u k m ↔ RevAnn p σ f k m := by
  set π := Ideal.Quotient.mk (Ideal.span {(p : A) ^ k})
  have hdvd : ∀ a : A, (p : A) ^ k ∣ a ↔ π a = 0 := fun a => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have hfu' : π f * π u = 1 := by
    rw [← map_mul, ← sub_eq_zero, ← map_one π, ← map_sub]; exact (hdvd _).1 hfu
  constructor
  · rintro ⟨P, hmon, hdeg, hB, hP⟩
    refine ⟨reflect m P, ?_, natDegree_reflect_le.trans (by rw [hdeg, max_self]),
      ⟨1, one_mem _, ?_⟩, ?_⟩
    · rw [mem_BPoly_iff] at hB ⊢; intro i; rw [coeff_reflect]; exact hB _
    · rw [one_mul, coeff_reflect, revAt_zero, ← hdeg]; exact hmon.coeff_natDegree
    · let : Invertible (π u) :=
        { invOf := π f, invOf_mul_self := hfu', mul_invOf_self := by rw [mul_comm]; exact hfu' }
      have hinv : ⅟(π u) = π f := rfl
      rw [hdvd, ← eval₂_at_apply, ← hinv, eval₂_reflect_eq_zero_iff π (π u) m P hdeg.le,
        eval₂_at_apply, ← hdvd]
      exact hP
  · rintro ⟨R, hB, hdeg, ⟨c, hc, hc1⟩, hR⟩
    have hR'B : C c * R ∈ BPoly σ := by
      obtain ⟨a, rfl⟩ := hc; exact mul_mem (C_mem_BPoly σ a) hB
    have hR'deg : (C c * R).natDegree ≤ m := (natDegree_C_mul_le c R).trans hdeg
    have hR'f : (p : A) ^ k ∣ (C c * R).eval f := by
      rw [eval_mul, eval_C]; exact Dvd.dvd.mul_left hR c
    have hcm : (reflect m (C c * R)).coeff m = 1 := by
      rw [coeff_reflect, revAt_le le_rfl, Nat.sub_self, coeff_C_mul, hc1]
    have hdm : (reflect m (C c * R)).natDegree = m :=
      le_antisymm (natDegree_reflect_le.trans (max_le le_rfl hR'deg))
        (le_natDegree_of_ne_zero (by rw [hcm]; exact one_ne_zero))
    refine ⟨reflect m (C c * R), ?_, hdm, ?_, ?_⟩
    · show leadingCoeff _ = 1
      rw [leadingCoeff, hdm, hcm]
    · rw [mem_BPoly_iff] at hR'B ⊢; intro i; rw [coeff_reflect]; exact hR'B _
    · let : Invertible (π f) :=
        { invOf := π u, invOf_mul_self := by rw [mul_comm]; exact hfu', mul_invOf_self := hfu' }
      have hinv : ⅟(π f) = π u := rfl
      rw [hdvd, ← eval₂_at_apply, ← hinv, eval₂_reflect_eq_zero_iff π (π f) m _ hR'deg,
        eval₂_at_apply, ← hdvd]
      exact hR'f

/-- `L_f(p, k) + 1` in the exact form of ledger R-060: the least degree of `R ∈ B[X]` with `R(0)`
a unit of `B` and `R(f) ∈ p ^ k A`. -/
theorem levelCount_add_one_rev [Nontrivial A] {p : ℕ} {σ : A →+* A} {f u : A} {k m : ℕ}
    (hfu : (p : A) ^ k ∣ f * u - 1) (hpk : ¬ IsUnit ((p : A) ^ k)) (hex : MonicAnn p σ u k m) :
    levelCount p σ f k + 1 = revDegree p σ f k := by
  rw [levelCount_add_one hfu hpk hex, annDegree, revDegree]
  congr 1
  ext m'
  exact monicAnn_iff_revAnn hfu m'

end Abstract

/-! ## 2. The Kempner function -/

section Kempner

open scoped Nat

variable (p : ℕ) [hp : Fact p.Prime]

theorem exists_kempner (k : ℕ) : ∃ N, p ^ k ∣ N ! :=
  ⟨p * k, by
    have h := padicValNat_factorial_mul (p := p) k
    exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero _)).2 (by omega)⟩

/-- The Kempner value `S(p ^ k)`: the least `N` with `p ^ k ∣ N !`
(same definition as `FrobCong.kempner` in FrobLib/Frob6.lean). -/
noncomputable def kempner (k : ℕ) : ℕ := Nat.find (exists_kempner p k)

theorem pow_dvd_factorial_iff (k N : ℕ) : p ^ k ∣ N ! ↔ k ≤ padicValNat p N ! :=
  padicValNat_dvd_iff_le (Nat.factorial_ne_zero N)

theorem kempner_spec (k : ℕ) : k ≤ padicValNat p (kempner p k)! :=
  (pow_dvd_factorial_iff p k _).1 (Nat.find_spec (exists_kempner p k))

theorem kempner_le {k N : ℕ} (h : k ≤ padicValNat p N !) : kempner p k ≤ N :=
  Nat.find_min' (exists_kempner p k) ((pow_dvd_factorial_iff p k N).2 h)

theorem lt_kempner {k N : ℕ} (h : N < kempner p k) : padicValNat p N ! < k := by
  by_contra hc
  exact absurd (kempner_le p (not_lt.1 hc)) (not_le.2 h)

theorem kempner_pos {k : ℕ} (hk : 1 ≤ k) : 1 ≤ kempner p k := by
  by_contra hc
  have h0 : kempner p k = 0 := by omega
  have := kempner_spec p k
  rw [h0] at this
  simp at this
  omega

/-- Legendre step: `v_p(m !) = ⌊m / p⌋ + v_p(⌊m / p⌋ !)`. -/
theorem padicValNat_factorial_div (m : ℕ) :
    padicValNat p m ! = m / p + padicValNat p (m / p)! := by
  conv_lhs => rw [← Nat.div_add_mod m p]
  rw [padicValNat_factorial_mul_add (m / p) (Nat.mod_lt m hp.out.pos), padicValNat_factorial_mul,
    add_comm]

end Kempner

/-! ## 3. Power series in several variables with `σ(x_i) = x_i ^ p` -/

section PowerSeries

open MvPowerSeries

variable (p : ℕ) [hp : Fact p.Prime] {τ : Type*} {R : Type*} [CommRing R]

/-- The Frobenius lift `σ` of `R[[x_i : i ∈ τ]]` with `σ(x_i) = x_i ^ p` and `σ = id` on `R`
(Mathlib's `MvPowerSeries.expand p`, as a ring homomorphism). -/
noncomputable def frob : MvPowerSeries τ R →+* MvPowerSeries τ R :=
  (MvPowerSeries.expand (σ := τ) (R := R) p hp.out.ne_zero : MvPowerSeries τ R →+* MvPowerSeries τ R)

theorem frob_apply (f : MvPowerSeries τ R) : frob p f = MvPowerSeries.expand p hp.out.ne_zero f :=
  rfl

@[simp] theorem frob_X (i : τ) : frob p (X i : MvPowerSeries τ R) = X i ^ p :=
  MvPowerSeries.expand_X p hp.out.ne_zero i

@[simp] theorem frob_C (r : R) : frob p (C r : MvPowerSeries τ R) = C r :=
  MvPowerSeries.expand_C p hp.out.ne_zero r

/-- Coefficients of `σ f`: the coefficient at `p • m` is the coefficient of `f` at `m`. -/
@[simp] theorem coeff_frob_smul (f : MvPowerSeries τ R) (m : τ →₀ ℕ) :
    coeff (p • m) (frob p f) = coeff m f :=
  MvPowerSeries.coeff_expand_smul p hp.out.ne_zero f m

/-- Coefficients of `σ f` vanish off the exponents divisible by `p`. -/
theorem coeff_frob_of_not_dvd (f : MvPowerSeries τ R) {m : τ →₀ ℕ} {i : τ} (h : ¬ p ∣ m i) :
    coeff m (frob p f) = 0 :=
  MvPowerSeries.coeff_expand_of_not_dvd p hp.out.ne_zero f h

/-- A power series all of whose coefficients are divisible by `c` is divisible by `C c`. -/
theorem C_dvd_of_coeff {c : R} {g : MvPowerSeries τ R} (h : ∀ d, c ∣ coeff d g) :
    (C c : MvPowerSeries τ R) ∣ g := by
  choose q hq using h
  refine ⟨(show MvPowerSeries τ R from fun d => q d), ?_⟩
  ext d
  have h1 : coeff d (C c * (show MvPowerSeries τ R from fun d => q d)) = c * q d := by
    rw [coeff_C_mul]; rfl
  exact (hq d).trans h1.symm

omit hp in
theorem natCast_dvd_of_coeff {g : MvPowerSeries τ R} (h : ∀ d, (p : R) ∣ coeff d g) :
    (p : MvPowerSeries τ R) ∣ g := by
  have := C_dvd_of_coeff (τ := τ) h
  rwa [map_natCast] at this

omit hp in
theorem coeff_of_natCast_dvd {g : MvPowerSeries τ R} (h : (p : MvPowerSeries τ R) ∣ g)
    (d : τ →₀ ℕ) : (p : R) ∣ coeff d g := by
  obtain ⟨q, rfl⟩ := h
  rw [← map_natCast (C (σ := τ) (R := R)), coeff_C_mul]
  exact dvd_mul_right _ _

/-- `frob p` is a Frobenius lift on `R[[x]]` as soon as `a ^ p ≡ a (mod p R)` on `R`
(true for `ℤ` and `ℤ_[p]`: `int_pow_sub`, `padicInt_pow_sub`). -/
theorem frob_isFrobLift (hR : ∀ a : R, (p : R) ∣ a ^ p - a) :
    IsFrobLift p (frob p : MvPowerSeries τ R →+* MvPowerSeries τ R) := by
  intro f
  by_cases hu : IsUnit (p : R)
  · have : IsUnit (p : MvPowerSeries τ R) := by
      have := hu.map (C (σ := τ) (R := R))
      rwa [map_natCast] at this
    exact this.dvd
  · have : CharP (R ⧸ (Ideal.span ({(p : R)} : Set R) : Ideal R)) p := CharP.quotient R p hu
    have : ExpChar (R ⧸ (Ideal.span ({(p : R)} : Set R) : Ideal R)) p := ExpChar.prime hp.out
    set π : R →+* R ⧸ (Ideal.span ({(p : R)} : Set R) : Ideal R) := Ideal.Quotient.mk _ with hπ
    have hfrob : ∀ x : R ⧸ (Ideal.span ({(p : R)} : Set R) : Ideal R), frobenius _ p x = x := by
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [frobenius_def, ← map_pow]
      exact (Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (hR a)))
    have hmapid : ∀ g : MvPowerSeries τ (R ⧸ (Ideal.span ({(p : R)} : Set R) : Ideal R)),
        MvPowerSeries.map (frobenius _ p) g = g := by
      intro g; ext d; rw [coeff_map, hfrob]
    apply natCast_dvd_of_coeff
    intro d
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, ← hπ, ← coeff_map,
      map_sub, map_pow, frob_apply, MvPowerSeries.map_expand,
      ← MvPowerSeries.map_frobenius_expand p hp.out.ne_zero, hmapid, sub_self, map_zero]

omit hp in
/-- No `p`-torsion passes from `R` to `R[[x]]`. -/
theorem noPTorsion_mvPowerSeries (hR : NoPTorsion p R) : NoPTorsion p (MvPowerSeries τ R) := by
  intro a ha
  ext d
  have := congrArg (coeff d) ha
  rw [← map_natCast (C (σ := τ) (R := R)), coeff_C_mul, map_zero] at this
  rw [map_zero]
  exact hR _ this

omit hp in
/-- `p` is not a unit, and no power `p ^ k` with `k ≥ 1` is, in `R[[x]]` when `p` is not a unit
of `R`. -/
theorem not_isUnit_pow_mvPowerSeries (hu : ¬ IsUnit (p : R)) {k : ℕ} (hk : 1 ≤ k) :
    ¬ IsUnit ((p : MvPowerSeries τ R) ^ k) := by
  intro h
  have h1 : IsUnit (p : MvPowerSeries τ R) := (isUnit_pow_iff (by omega)).1 h
  have h2 := h1.map (constantCoeff (σ := τ) (R := R))
  rw [map_natCast] at h2
  exact hu h2

theorem int_pow_sub (a : ℤ) : ((p : ℕ) : ℤ) ∣ a ^ p - a := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.pow_card, sub_self]

theorem padicInt_pow_sub (a : ℤ_[p]) : ((p : ℕ) : ℤ_[p]) ∣ a ^ p - a := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod,
    RingHom.mem_ker, map_sub, map_pow, ZMod.pow_card, sub_self]

theorem int_noPTorsion : NoPTorsion p ℤ := by
  intro a ha
  rcases mul_eq_zero.1 ha with h | h
  · exact absurd (by exact_mod_cast h) hp.out.ne_zero
  · exact h

theorem padicInt_noPTorsion : NoPTorsion p ℤ_[p] := by
  intro a ha
  rcases mul_eq_zero.1 ha with h | h
  · exact absurd (by exact_mod_cast h) hp.out.ne_zero
  · exact h

theorem int_not_isUnit : ¬ IsUnit ((p : ℕ) : ℤ) := by
  intro h
  have := Int.isUnit_iff.1 h
  have h2 := hp.out.two_le
  omega

theorem padicInt_not_isUnit : ¬ IsUnit ((p : ℕ) : ℤ_[p]) := PadicInt.p_nonunit

end PowerSeries

end FrobLevel
