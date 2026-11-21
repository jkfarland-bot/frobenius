module

public import Mathlib
public import Frobenius.Mobius.LowerGen
public import Frobenius.Levels.A1Gen

/-!
# Theorem 6.2 over a general commutative ring (seat L11)

Numbers refer to J. S. Farland, *A proof of a conjecture of Kauers, Krattenthaler and
Müller, and exact level counts for Frobenius lifts* (2026), the larger paper.

The paper's Theorem 6.2: let `O` be a commutative ring with `p ^ (k - 1) ∉ p ^ k O`, and let
`f` have `f(1) = 1` and a set `Q` of at least `N_p(k)` primes `q` with `f(q)` a unit modulo `p O`
on whose squarefree products `f` is multiplicative. Then `L_f(p,k) ≥ S(p ^ k) - 1`.

The existing Lean (`Dir.min_le_levelCount_int` and `_padic`) proves a lower bound over `ℤ` and
`ℤ_[p]` by another route. Here `O` is general: the level identity is evaluated at the products of
`r ≤ N` primes of `Q`, which gives, in `Λ = O ⧸ p ^ k O`, the shifted slice
`∑_z g_z(1) (z + 1) ^ r = [r = 0]` (`level_apply_prod_primes`); a binomial inversion turns it into
the slice `∑_z g_z(1) z ^ r = (-1) ^ r` of Theorem 4.5 (`slice_of_shifted`), and
`FrobCong.lower_slice_shift` (seat L11, `Frobenius/Mobius/LowerGen.lean`) concludes.

* `kempner_le_of_hasLevel_mult`: the bound for every level identity, from
  `2k - 1 + (p - 2) K(p,k)` primes (the count of Remark 6.5);
* `kempner_le_levelCount_mult` (Theorem 6.2, from `N_p(k)` primes) and
  `levelCount_eq_kempner_mult` (Corollary 6.3);
* `kempner_le_levelCount_mult_shift`, `levelCount_eq_kempner_mult_shift`: the same from
  `2k - 1 + (p - 2) K(p,k)` primes;
* `levelCount_eq_kempner_mult_infinite`: `Q` infinite, every `k`;
* `not_pow_dvd_of_noPTorsion`: the alternative hypothesis (`O` without `p`-torsion, `p O ≠ O`).

Here `f(1) = 1` is the case `S = ∅` of the multiplicativity hypothesis
`f(∏_{q ∈ S} q) = ∏_{q ∈ S} f(q)` for `S ⊆ Q`, and "`f(q)` a unit modulo `p O`" is
`∃ v, p ∣ f(q) v - 1`.
-/

@[expose] public section

open Finset

namespace FrobLevel

namespace Dir

section A2

variable {O : Type*} [CommRing O]

/-- At a squarefree `n`, `(F * E_p g)(n) = F(n) g(1)`. -/
theorem mul_Ep_apply_squarefree (p : ℕ) [hp : Fact p.Prime] (F g : ArithmeticFunction O)
    {n : ℕ} (hn : Squarefree n) (hn0 : n ≠ 0) : (F * Ep p g) n = F n * g 1 := by
  rw [ArithmeticFunction.mul_apply, Finset.sum_eq_single (n, 1)]
  · rw [Ep_apply]
    have := frobPush_apply_pow (p := p) hp.out.ne_zero g one_ne_zero
    rw [one_pow] at this
    rw [this]
  · intro x hx hne
    rw [Ep_apply, frobPush_apply_of_not g, mul_zero]
    rintro ⟨j, hj⟩
    have hx' := Nat.mem_divisorsAntidiagonal.mp hx
    have hp2 := hp.out.two_le
    have e : j ^ p = j * j * j ^ (p - 2) := by
      rw [← sq, ← pow_add]; congr 1; omega
    have hj1 : IsUnit j := hn j ⟨x.1 * j ^ (p - 2), by rw [← hx'.1, ← hj, e]; ring⟩
    rw [Nat.isUnit_iff] at hj1
    apply hne
    have h2 : x.2 = 1 := by rw [← hj, hj1, one_pow]
    have h1 : x.1 = n := by rw [← hx'.1, h2, mul_one]
    exact Prod.ext h1 h2
  · intro h
    exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨mul_one n, hn0⟩) h

/-- For `φ(1) = 1` and a prime `q`, `φ ^ m (q) = m φ(q)`. -/
theorem pow_apply_prime_of_apply_one {φ : ArithmeticFunction O} (hφ1 : φ 1 = 1) {q : ℕ}
    (hq : q.Prime) (m : ℕ) : (φ ^ m) q = (m : O) * φ q := by
  induction m with
  | zero => simp [ArithmeticFunction.one_apply_ne hq.ne_one]
  | succ m ih =>
    rw [pow_succ', mul_apply_prime _ _ hq, ih, pow_apply_one, hφ1, one_pow]
    push_cast; ring

/-- Step (ii) of the proof of Theorem 6.2: if `f` is multiplicative on the products of
subsets of a finite set `S` of primes, then `f ^ m (∏_{q ∈ S} q) = m ^ |S| ∏_{q ∈ S} f(q)`. -/
theorem pow_apply_prod_primes (f : ArithmeticFunction O) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime) (hmul : ∀ T ⊆ S, f (∏ q ∈ T, q) = ∏ q ∈ T, f q) (m : ℕ) :
    (f ^ m) (∏ q ∈ S, q) = (m : O) ^ S.card * ∏ q ∈ S, f q := by
  set φ : ArithmeticFunction O := ArithmeticFunction.prodPrimeFactors (fun q => f q) with hφ
  have hφmul : φ.IsMultiplicative := ArithmeticFunction.IsMultiplicative.prodPrimeFactors _
  have hn0 : (∏ q ∈ S, q) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun q hq => (hS q hq).ne_zero)
  have hsq : Squarefree (∏ q ∈ S, q) := FrobCong.squarefree_prod_primes S hS
  have hpf : (∏ q ∈ S, q).primeFactors = S := Nat.primeFactors_prod hS
  have hagree : ∀ d ∈ (∏ q ∈ S, q).divisors, f d = φ d := by
    intro d hd
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    have hdvd : d ∣ ∏ q ∈ S, q := Nat.dvd_of_mem_divisors hd
    have hdsq : Squarefree d := Squarefree.squarefree_of_dvd hdvd hsq
    have hsub : d.primeFactors ⊆ S := hpf ▸ Nat.primeFactors_mono hdvd hn0
    rw [hφ, ArithmeticFunction.prodPrimeFactors_apply hd0]
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hdsq]
    exact hmul _ hsub
  rw [FrobCong.pow_apply_congr hagree m (∏ q ∈ S, q) (Nat.mem_divisors_self _ hn0),
    hφmul.pow.map_prod_of_prime S hS]
  have hprime : ∀ q ∈ S, (φ ^ m) q = (m : O) * f q := by
    intro q hq
    have hφq : φ q = f q := by
      rw [hφ, ArithmeticFunction.prodPrimeFactors_apply (hS q hq).ne_zero,
        (hS q hq).primeFactors, Finset.prod_singleton]
    rw [pow_apply_prime_of_apply_one hφmul.map_one (hS q hq), hφq]
  rw [Finset.prod_congr rfl hprime, Finset.prod_mul_distrib, Finset.prod_const]

/-- Steps (i) and (ii) of the proof of Theorem 6.2: the level identity's right side at the
product of the primes of `S` is `(∑_z g_z(1) (z + 1) ^ |S|) ∏_{q ∈ S} f(q)`. -/
theorem level_apply_prod_primes (p : ℕ) [Fact p.Prime] (f : ArithmeticFunction O)
    (g : ℕ → ArithmeticFunction O) (L : ℕ) (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime)
    (hmul : ∀ T ⊆ S, f (∏ q ∈ T, q) = ∏ q ∈ T, f q) :
    (f * ∑ z ∈ range (L + 1), f ^ z * Ep p (g z)) (∏ q ∈ S, q) =
      (∑ z ∈ range (L + 1), g z 1 * ((z : O) + 1) ^ S.card) * ∏ q ∈ S, f q := by
  have hn0 : (∏ q ∈ S, q) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun q hq => (hS q hq).ne_zero)
  have hsq : Squarefree (∏ q ∈ S, q) := FrobCong.squarefree_prod_primes S hS
  rw [Finset.mul_sum, FrobCong.sum_apply', Finset.sum_mul]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [← mul_assoc, ← pow_succ', mul_Ep_apply_squarefree p _ _ hsq hn0,
    pow_apply_prod_primes f S hS hmul]
  push_cast; ring

/-- Binomial inversion: the shifted slice `∑_z c_z (z + 1) ^ r = [r = 0]` for `r ≤ N` gives the
slice `∑_z c_z z ^ r = (-1) ^ r` for `r ≤ N`. -/
theorem slice_of_shifted {Λ : Type*} [CommRing Λ] (c : ℕ → Λ) (M N : ℕ)
    (h : ∀ r ≤ N, ∑ z ∈ range M, c z * ((z : Λ) + 1) ^ r = 0 ^ r) :
    ∀ r ≤ N, ∑ z ∈ range M, c z * (z : Λ) ^ r = (-1) ^ r := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro hr
  have e1 : ∑ z ∈ range M, c z * ((z : Λ) + 1) ^ r =
      ∑ j ∈ range (r + 1), (r.choose j : Λ) * ∑ z ∈ range M, c z * (z : Λ) ^ j := by
    simp only [add_pow, one_pow, mul_one, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun z _ => by ring))
  have e2 : (0 : Λ) ^ r = ∑ j ∈ range (r + 1), (r.choose j : Λ) * (-1) ^ j := by
    have := add_pow (-1 : Λ) 1 r
    rw [neg_add_cancel] at this
    rw [this]
    exact Finset.sum_congr rfl (fun j _ => by rw [one_pow, mul_one, mul_comm])
  have h1 := h r hr
  rw [e1, e2, Finset.sum_range_succ, Finset.sum_range_succ] at h1
  have hlow : ∀ j ∈ range r, (r.choose j : Λ) * ∑ z ∈ range M, c z * (z : Λ) ^ j =
      (r.choose j : Λ) * (-1) ^ j := fun j hj => by
    rw [ih j (Finset.mem_range.mp hj) (by have := Finset.mem_range.mp hj; omega)]
  rw [Finset.sum_congr rfl hlow] at h1
  simp only [Nat.choose_self, Nat.cast_one, one_mul] at h1
  exact add_left_cancel h1

/-- The alternative hypothesis of Theorem 6.2: if `O` has no `p`-torsion and `p` is not a
unit of `O` (`p O ≠ O`), then `p ^ (k - 1) ∉ p ^ k O` for `k ≥ 1`. -/
theorem not_pow_dvd_of_noPTorsion (p : ℕ) {k : ℕ} (hk : 1 ≤ k) (ht : NoPTorsion p O)
    (hu : ¬ IsUnit (p : O)) : ¬ (p : O) ^ k ∣ (p : O) ^ (k - 1) := by
  rintro ⟨a, ha⟩
  have h1 : (p : O) ^ (k - 1) * (1 - p * a) = 0 := by
    have e : (p : O) ^ k = (p : O) ^ (k - 1) * p := by rw [← pow_succ]; congr 1; omega
    rw [mul_sub, mul_one, ← mul_assoc, ← e, ← ha, sub_self]
  have h2 : ∀ j, (p : O) ^ j * (1 - p * a) = 0 → 1 - p * a = 0 := by
    intro j
    induction j with
    | zero => intro h; rwa [pow_zero, one_mul] at h
    | succ j ih =>
      intro h
      apply ih
      apply ht
      rw [← mul_assoc, ← pow_succ']
      exact h
  have h3 := h2 _ h1
  exact hu (IsUnit.of_mul_eq_one a (by linear_combination -h3))

/-- **Theorem 6.2 for a single level identity** (general commutative ring `O`): if
`p ^ (k - 1) ∉ p ^ k O`, `Q` is a finite set of primes with `f` multiplicative on the products of
subsets of `Q` and `f(q)` a unit modulo `p O` for `q ∈ Q`, and `|Q| ≥ 2k - 1 + (p - 2) K(p,k)`,
then every level `L` identity for `f` modulo `p ^ k` has `L + 1 ≥ S(p ^ k)`. -/
theorem kempner_le_of_hasLevel_mult (p : ℕ) [hp : Fact p.Prime] {k : ℕ}
    (hpk : ¬ (p : O) ^ k ∣ (p : O) ^ (k - 1)) (f : ArithmeticFunction O) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime) (hmul : ∀ S ⊆ Q, f (∏ q ∈ S, q) = ∏ q ∈ S, f q)
    (hunit : ∀ q ∈ Q, ∃ v : O, (p : O) ∣ f q * v - 1)
    (hcard : 2 * k - 1 + (p - 2) * Nat.find (FrobCong.exists_K p k) ≤ Q.card)
    {L : ℕ} (hL : HasLevel p (Ep p) f k L) : kempner p k ≤ L + 1 := by
  obtain ⟨g, hg⟩ := hL
  set I : Ideal O := Ideal.span {(p : O) ^ k} with hI
  set π : O →+* O ⧸ I := Ideal.Quotient.mk I with hπ
  have hπpk : (p : O ⧸ I) ^ k = 0 := by
    rw [← map_natCast π, ← map_pow, hπ, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have hπne : (p : O ⧸ I) ^ (k - 1) ≠ 0 := by
    rw [← map_natCast π, ← map_pow, hπ, Ne, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton]
    exact hpk
  -- the values `f(q)`, `q ∈ Q`, are units modulo `p ^ k`
  have hunitq : ∀ q ∈ Q, IsUnit (π (f q)) := by
    intro q hq
    obtain ⟨v, w, hw⟩ := hunit q hq
    have hnil : IsNilpotent (π ((p : O) * w)) :=
      ⟨k, by rw [map_mul, mul_pow, map_natCast, hπpk, zero_mul]⟩
    have h1 : π (f q) * π v = 1 + π ((p : O) * w) := by
      rw [← map_mul, ← map_one π, ← map_add]; congr 1; linear_combination hw
    exact isUnit_of_mul_isUnit_left (h1 ▸ hnil.isUnit_one_add)
  -- the shifted slice in `O ⧸ p ^ k O`
  have hshift : ∀ r ≤ Q.card,
      ∑ z ∈ range (L + 1), π (g z 1) * ((z : O ⧸ I) + 1) ^ r = 0 ^ r := by
    intro r hr
    obtain ⟨S, hSQ, hSc⟩ := Finset.exists_subset_card_eq hr
    have hS : ∀ q ∈ S, q.Prime := fun q hq => hQ q (hSQ hq)
    have hmulS : ∀ T ⊆ S, f (∏ q ∈ T, q) = ∏ q ∈ T, f q := fun T hT => hmul T (hT.trans hSQ)
    have hU : IsUnit (π (∏ q ∈ S, f q)) := by
      rw [map_prod]
      exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
        (fun q hq => hunitq q (hSQ hq))
    obtain ⟨E, hE⟩ := hg
    have hc : (p : ArithmeticFunction O) ^ k = ((p ^ k : ℕ) : ArithmeticFunction O) := by
      push_cast; rfl
    have hev : (1 - f * ∑ z ∈ range (L + 1), f ^ z * Ep p (g z)) (∏ q ∈ S, q) =
        ((p : ArithmeticFunction O) ^ k * E) (∏ q ∈ S, q) := by rw [hE]
    rw [sub_apply', level_apply_prod_primes p f g L S hS hmulS, hSc, hc, natCast_mul_apply]
      at hev
    have hev' := congrArg π hev
    rw [map_sub, map_mul, map_mul, map_natCast, Nat.cast_pow, hπpk, zero_mul, sub_eq_zero] at hev'
    have hsum : π (∑ z ∈ range (L + 1), g z 1 * ((z : O) + 1) ^ r) =
        ∑ z ∈ range (L + 1), π (g z 1) * ((z : O ⧸ I) + 1) ^ r := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun z _ => by simp)
    rcases Nat.eq_zero_or_pos r with hr0 | hr0
    · have hS0 : S = ∅ := Finset.card_eq_zero.mp (hSc.trans hr0)
      subst hr0
      rw [hS0, Finset.prod_empty, ArithmeticFunction.one_one, map_one, Finset.prod_empty,
        map_one, mul_one] at hev'
      rw [← hsum, ← hev', pow_zero]
    · have hS1 : (∏ q ∈ S, q) ≠ 1 := by
        obtain ⟨q, hq⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
        intro h1
        have hqd : q ∣ ∏ q ∈ S, q := Finset.dvd_prod_of_mem _ hq
        rw [h1, Nat.dvd_one] at hqd
        exact (hS q hq).ne_one hqd
      rw [ArithmeticFunction.one_apply_ne hS1, map_zero] at hev'
      have h0 := hev'.symm
      rw [hU.mul_left_eq_zero, hsum] at h0
      rw [h0, zero_pow (by omega)]
  have hslice := slice_of_shifted (fun z => π (g z 1)) (L + 1) Q.card hshift
  have hb := FrobCong.lower_slice_shift p hπpk hπne L (fun z => π (g z 1))
    (fun r _ hr => hslice r (hr.trans hcard))
  have e : kempner p k = p * Nat.find (FrobCong.exists_K p k) := (FrobCong.kempner_eq p k).symm
  rw [e]; exact hb

/-- `f(1) = 1` follows from the multiplicativity hypothesis (the empty product). -/
theorem apply_one_of_mult (f : ArithmeticFunction O) (Q : Finset ℕ)
    (hmul : ∀ S ⊆ Q, f (∏ q ∈ S, q) = ∏ q ∈ S, f q) : f 1 = 1 := by
  simpa using hmul ∅ (Finset.empty_subset Q)

/-- `p ^ k ∤ p ^ (k - 1)` forces `k ≥ 1`. -/
theorem one_le_of_not_pow_dvd (p : ℕ) {k : ℕ} (hpk : ¬ (p : O) ^ k ∣ (p : O) ^ (k - 1)) :
    1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · exact absurd (by rw [h0]) hpk
  · exact h0

/-- **Theorem 6.2 of the paper with the shift operator's count of primes** (Remark 6.5), over a general commutative ring `O`: from
`|Q| ≥ 2k - 1 + (p - 2) K(p,k)`, `L_f(p,k) + 1 ≥ S(p ^ k)`. -/
theorem kempner_le_levelCount_mult_shift (p : ℕ) [hp : Fact p.Prime] {k : ℕ}
    (hpk : ¬ (p : O) ^ k ∣ (p : O) ^ (k - 1)) (f : ArithmeticFunction O) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime) (hmul : ∀ S ⊆ Q, f (∏ q ∈ S, q) = ∏ q ∈ S, f q)
    (hunit : ∀ q ∈ Q, ∃ v : O, (p : O) ∣ f q * v - 1)
    (hcard : 2 * k - 1 + (p - 2) * Nat.find (FrobCong.exists_K p k) ≤ Q.card) :
    kempner p k ≤ levelCount p (Ep p) f k + 1 := by
  have hk := one_le_of_not_pow_dvd p hpk
  have hf1 : IsUnit f := by
    rw [ArithmeticFunction.isUnit_iff_isUnit_apply_one, apply_one_of_mult f Q hmul]
    exact isUnit_one
  have hex := hasLevel_kempner_any p f hf1 hk
  exact kempner_le_of_hasLevel_mult p hpk f Q hQ hmul hunit hcard (hasLevel_levelCount hex)

/-- **Theorem 6.2 of the paper** (general commutative ring `O`): suppose
`p ^ (k - 1) ∉ p ^ k O`, and `Q` is a set of at least `N_p(k) = 2k - 1 + (p - 2) p ^ (k - 1)`
primes `q` with `f(q)` a unit modulo `p O`, such that `f(q_1 ⋯ q_r) = ∏ f(q_i)` for distinct
`q_i ∈ Q` (for `r = 0` this is `f(1) = 1`). Then `L_f(p,k) ≥ S(p ^ k) - 1`. -/
theorem kempner_le_levelCount_mult (p : ℕ) [hp : Fact p.Prime] {k : ℕ}
    (hpk : ¬ (p : O) ^ k ∣ (p : O) ^ (k - 1)) (f : ArithmeticFunction O) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime) (hmul : ∀ S ⊆ Q, f (∏ q ∈ S, q) = ∏ q ∈ S, f q)
    (hunit : ∀ q ∈ Q, ∃ v : O, (p : O) ∣ f q * v - 1) (hcard : FrobCong.Np p k ≤ Q.card) :
    kempner p k ≤ levelCount p (Ep p) f k + 1 :=
  kempner_le_levelCount_mult_shift p hpk f Q hQ hmul hunit
    ((FrobCong.shift_rows_le_Np p k).trans hcard)

/-- **Corollary 6.3 of the paper** (general commutative ring `O`): under the hypotheses of
Theorem 6.2, `L_f(p,k) = S(p ^ k) - 1`. -/
theorem levelCount_eq_kempner_mult (p : ℕ) [hp : Fact p.Prime] {k : ℕ}
    (hpk : ¬ (p : O) ^ k ∣ (p : O) ^ (k - 1)) (f : ArithmeticFunction O) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime) (hmul : ∀ S ⊆ Q, f (∏ q ∈ S, q) = ∏ q ∈ S, f q)
    (hunit : ∀ q ∈ Q, ∃ v : O, (p : O) ∣ f q * v - 1) (hcard : FrobCong.Np p k ≤ Q.card) :
    levelCount p (Ep p) f k + 1 = kempner p k := by
  have h1 := kempner_le_levelCount_mult p hpk f Q hQ hmul hunit hcard
  have h2 := levelCount_add_one_le_kempner_any p f
    (by rw [apply_one_of_mult f Q hmul]; exact isUnit_one) (one_le_of_not_pow_dvd p hpk)
  omega

/-- **Corollary 6.3 with the shift operator's count of primes**. -/
theorem levelCount_eq_kempner_mult_shift (p : ℕ) [hp : Fact p.Prime] {k : ℕ}
    (hpk : ¬ (p : O) ^ k ∣ (p : O) ^ (k - 1)) (f : ArithmeticFunction O) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime) (hmul : ∀ S ⊆ Q, f (∏ q ∈ S, q) = ∏ q ∈ S, f q)
    (hunit : ∀ q ∈ Q, ∃ v : O, (p : O) ∣ f q * v - 1)
    (hcard : 2 * k - 1 + (p - 2) * Nat.find (FrobCong.exists_K p k) ≤ Q.card) :
    levelCount p (Ep p) f k + 1 = kempner p k := by
  have h1 := kempner_le_levelCount_mult_shift p hpk f Q hQ hmul hunit hcard
  have h2 := levelCount_add_one_le_kempner_any p f
    (by rw [apply_one_of_mult f Q hmul]; exact isUnit_one) (one_le_of_not_pow_dvd p hpk)
  omega

/-- **Corollary 6.3 with `Q` infinite** (the setting of the paper's instances): if `Q` is an
infinite set of primes with `f(q)` a unit modulo `p O` and `f` multiplicative on the products of
finite subsets of `Q`, then `L_f(p,k) = S(p ^ k) - 1` for every `k` with `p ^ (k - 1) ∉ p ^ k O`. -/
theorem levelCount_eq_kempner_mult_infinite (p : ℕ) [hp : Fact p.Prime] {k : ℕ}
    (hpk : ¬ (p : O) ^ k ∣ (p : O) ^ (k - 1)) (f : ArithmeticFunction O) {Q : Set ℕ}
    (hQinf : Q.Infinite) (hQ : ∀ q ∈ Q, q.Prime)
    (hmul : ∀ S : Finset ℕ, (S : Set ℕ) ⊆ Q → f (∏ q ∈ S, q) = ∏ q ∈ S, f q)
    (hunit : ∀ q ∈ Q, ∃ v : O, (p : O) ∣ f q * v - 1) :
    levelCount p (Ep p) f k + 1 = kempner p k := by
  obtain ⟨T, hTQ, hTc⟩ := hQinf.exists_subset_card_eq (FrobCong.Np p k)
  exact levelCount_eq_kempner_mult p hpk f T (fun q hq => hQ q (hTQ hq))
    (fun S hS => hmul S ((Finset.coe_subset.mpr hS).trans hTQ)) (fun q hq => hunit q (hTQ hq))
    hTc.ge

end A2

end Dir

end FrobLevel
