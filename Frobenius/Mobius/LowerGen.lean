module

public import Mathlib
public import Frobenius.Mobius.Levels

/-!
# Theorem 4.5 in full: a general ring and a finite range of rows (seat L11)

Numbers refer to J. S. Farland, *A proof of a conjecture of Kauers, Krattenthaler and
Müller, and exact level counts for Frobenius lifts* (2026), the larger paper.

The existing `FrobCong.moment_bound` and `FrobCong.level_bound` prove the lower bound of the paper's
Theorem 4.5 over `ℤ` from an identity at every `n`, using the rows `r ≥ k` without bound.
This file proves the theorem as the paper states it:

* the coefficients `c_0, ..., c_L` lie in any ring `Λ` with `p ^ k = 0` and `p ^ (k - 1) ≠ 0`
  (in particular every `ZMod (p ^ k)`-algebra with `p ^ (k - 1) ≠ 0`; commutativity is not needed);
* only the rows `k ≤ r ≤ N_p(k) = 2k - 1 + (p - 2) p ^ (k - 1)` of the slice are used.

The class `z ≡ -1 (mod p)` is isolated by the shift operator of Remark 6.5 (applying `Π(E) = ∏ (E - z')` over the `z' < p K(p,k)` with `z' mod p` in
`[1, p - 2]`), not by the character average of Step 2. This uses only the rows
`k ≤ r ≤ 2k - 1 + (p - 2) K(p,k)` (`lower_slice_shift`), which lie inside `[k, N_p(k)]` since
`K(p,k) ≤ k ≤ p ^ (k - 1)`. Steps 3 and 4 (finite differences and the null polynomial) are done
directly in `Λ`, with the rows `k ≤ r ≤ 2k - 1` (`moment_bound_ring`); the reduction of a general
`Λ` to `ZMod (p ^ k)` in the remark after the theorem is not used.

The squarefree form ("In particular" of 4.5) is `level_bound_squarefree`.
-/

@[expose] public section

open Finset Polynomial
open scoped Nat ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace FrobCong

/-- `N_p(k) = 2k - 1 + (p - 2) p ^ (k - 1)`, the last row used in Theorem 4.5. -/
def Np (p k : ℕ) : ℕ := 2 * k - 1 + (p - 2) * p ^ (k - 1)

section LowerRing

variable {Λ : Type*} [Ring Λ]

/-- An integer divisible by `p ^ k` is `0` in `Λ` when `p ^ k = 0` in `Λ`. -/
theorem intCast_eq_zero_of_pow_dvd {p k : ℕ} (hpk : (p : Λ) ^ k = 0) {x : ℤ}
    (hx : (p : ℤ) ^ k ∣ x) : (x : Λ) = 0 := by
  obtain ⟨w, rfl⟩ := hx
  rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast, hpk, zero_mul]

/-- An integer prime to `p` is a unit of `Λ` when `p ^ k = 0` in `Λ`: some integer `a` has
`x a = 1` in `Λ`. -/
theorem exists_intCast_mul_eq_one (p : ℕ) [hp : Fact p.Prime] {k : ℕ} (hpk : (p : Λ) ^ k = 0)
    {x : ℤ} (hx : ¬ (p : ℤ) ∣ x) : ∃ a : ℤ, ((x * a : ℤ) : Λ) = 1 := by
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hc : IsCoprime x ((p : ℤ) ^ k) :=
    (((Prime.coprime_iff_not_dvd hprime).mpr hx).pow_left).symm
  obtain ⟨a, b, hab⟩ := hc
  refine ⟨a, ?_⟩
  have h1 : ((a * x + b * (p : ℤ) ^ k : ℤ) : Λ) = 1 := by rw [hab, Int.cast_one]
  rw [Int.cast_add, Int.cast_mul b, Int.cast_pow, Int.cast_natCast, hpk, mul_zero, add_zero]
    at h1
  rwa [mul_comm]

/-- Step 4, the valuation step: if `N ≠ 0` vanishes in `Λ`, then `k ≤ v_p(N)`. -/
theorem le_padicValNat_of_natCast_eq_zero (p : ℕ) [hp : Fact p.Prime] {k : ℕ}
    (hpk : (p : Λ) ^ k = 0) (hne : (p : Λ) ^ (k - 1) ≠ 0) {N : ℕ} (hN0 : N ≠ 0)
    (hN : (N : Λ) = 0) : k ≤ padicValNat p N := by
  obtain ⟨u, hu⟩ := (pow_padicValNat_dvd : p ^ padicValNat p N ∣ N)
  have hpu : ¬ (p : ℤ) ∣ (u : ℤ) := by
    intro hd
    obtain ⟨w, rfl⟩ := Int.natCast_dvd_natCast.mp hd
    exact pow_succ_padicValNat_not_dvd (p := p) hN0 ⟨w, by rw [pow_succ, mul_assoc]; exact hu⟩
  obtain ⟨a, ha⟩ := exists_intCast_mul_eq_one (Λ := Λ) p hpk hpu
  have hJ : (p : Λ) ^ padicValNat p N = 0 := by
    have h1 : (N : Λ) * (a : Λ) = 0 := by rw [hN, zero_mul]
    rw [hu, Nat.cast_mul, Nat.cast_pow, mul_assoc] at h1
    have h2 : ((u : ℕ) : Λ) * (a : Λ) = 1 := by
      rw [← ha, Int.cast_mul, Int.cast_natCast]
    rwa [h2, mul_one] at h1
  by_contra hlt
  push Not at hlt
  apply hne
  rw [show k - 1 = padicValNat p N + (k - 1 - padicValNat p N) by omega, pow_add, hJ, zero_mul]

/-- `D(m, n) = ∑_t c_t (1 + u_t) ^ m u_t ^ n - [n = 0]` in `Λ`, with `u_t = -p (t + 1)`. -/
def momDR (p K0 : ℕ) (c : ℕ → Λ) (m n : ℕ) : Λ :=
  (∑ t ∈ range K0, c t * (((1 + momU p t) ^ m * momU p t ^ n : ℤ) : Λ)) - (0 : Λ) ^ n

theorem momDR_rel (p K0 : ℕ) (c : ℕ → Λ) (m n : ℕ) :
    momDR p K0 c m n = momDR p K0 c (m + 1) n - momDR p K0 c m (n + 1) := by
  unfold momDR
  have e : ∀ t, c t * (((1 + momU p t) ^ m * momU p t ^ n : ℤ) : Λ) =
      c t * (((1 + momU p t) ^ (m + 1) * momU p t ^ n : ℤ) : Λ) -
        c t * (((1 + momU p t) ^ m * momU p t ^ (n + 1) : ℤ) : Λ) := fun t => by
    rw [← mul_sub, ← Int.cast_sub]; congr 2; ring
  rw [Finset.sum_congr rfl (fun t _ => e t), Finset.sum_sub_distrib, pow_succ (0 : Λ) n, mul_zero]
  abel

/-- **Steps 3 and 4 of Theorem 4.5 over a general ring `Λ` with the finite range of rows**:
if `p ^ k = 0` and `p ^ (k - 1) ≠ 0` in `Λ` and `∑_{t=1}^{K0} c'_t (1 - p t) ^ r = 1` in `Λ` for
`k ≤ r ≤ 2k - 1` (here `c t` is the coefficient of index `t + 1`), then `k ≤ K0 + v_p(K0!)`.
(Over `ℤ` with all `r ≥ k` this is `moment_bound`.) -/
theorem moment_bound_ring (p : ℕ) [hp : Fact p.Prime] {k : ℕ} (hpk : (p : Λ) ^ k = 0)
    (hne : (p : Λ) ^ (k - 1) ≠ 0) (K0 : ℕ) (c : ℕ → Λ)
    (h : ∀ r, k ≤ r → r ≤ 2 * k - 1 →
      ∑ t ∈ range K0, c t * (((1 - (p : ℤ) * ((t : ℤ) + 1)) ^ r : ℤ) : Λ) = 1) :
    k ≤ K0 + padicValNat p (K0 !) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Nat.zero_le _
  -- the columns `m ∈ [k, 2k - 1]`, above the antidiagonal `m + n = 2k - 1`
  have hm : ∀ n m, k ≤ m → m + n ≤ 2 * k - 1 → momDR p K0 c m n = 0 := by
    intro n
    induction n with
    | zero =>
      intro m hkm hmn
      have e : ∀ t : ℕ, (1 : ℤ) + momU p t = 1 - (p : ℤ) * ((t : ℤ) + 1) := fun t => by
        unfold momU; ring
      simp only [momDR, e, pow_zero, mul_one]
      rw [h m hkm (by omega), sub_self]
    | succ n ih =>
      intro m hkm hmn
      have r := momDR_rel p K0 c m n
      rw [ih (m + 1) (by omega) (by omega), ih m hkm (by omega)] at r
      have r' := r.symm
      rwa [zero_sub, neg_eq_zero] at r'
  -- the rows `n ≥ k`
  have hn : ∀ m n, k ≤ n → momDR p K0 c m n = 0 := by
    intro m n hkn
    unfold momDR
    rw [zero_pow (by omega), sub_zero]
    apply Finset.sum_eq_zero
    intro t _
    have hu : (p : ℤ) ∣ momU p t := by
      unfold momU; exact (dvd_neg).mpr (dvd_mul_right _ _)
    rw [intCast_eq_zero_of_pow_dvd hpk (dvd_mul_of_dvd_right
      ((pow_dvd_pow (p : ℤ) hkn).trans (pow_dvd_pow_of_dvd hu n)) _), mul_zero]
  -- every entry with `m ≤ k`, by induction on `2k - m - n`
  have hall : ∀ d m n, 2 * k ≤ m + n + d → m ≤ k → momDR p K0 c m n = 0 := by
    intro d
    induction d with
    | zero =>
      intro m n hmn _
      exact hn m n (by omega)
    | succ d ih =>
      intro m n hmn hmk
      rcases le_or_gt k n with h2 | h2
      · exact hn m n h2
      rcases eq_or_lt_of_le hmk with h1 | h1
      · rw [h1]; exact hm n k le_rfl (by omega)
      rw [momDR_rel p K0 c m n, ih (m + 1) n (by omega) (by omega),
        ih m (n + 1) (by omega) h1.le, sub_zero]
  -- the moments: `∑_t c_t u_t ^ i = [i = 0]`
  have hD0 : ∀ i, ∑ t ∈ range K0, c t * ((momU p t ^ i : ℤ) : Λ) = (0 : Λ) ^ i := by
    intro i
    have h0 := hall (2 * k) 0 i (by omega) (Nat.zero_le _)
    unfold momDR at h0
    simp only [pow_zero, one_mul] at h0
    exact sub_eq_zero.mp h0
  -- linearity: `∑_t c_t H(u_t) = H(0)` for every integer polynomial `H`
  have hlin : ∀ H : Polynomial ℤ,
      ∑ t ∈ range K0, c t * ((H.eval (momU p t) : ℤ) : Λ) = ((H.eval 0 : ℤ) : Λ) := by
    intro H
    induction H using Polynomial.induction_on' with
    | add P Q hP hQ =>
      simp only [Polynomial.eval_add, Int.cast_add, mul_add, Finset.sum_add_distrib, hP, hQ]
    | monomial i a =>
      simp only [Polynomial.eval_monomial]
      have e : ∀ t, c t * ((a * momU p t ^ i : ℤ) : Λ) =
          c t * ((momU p t ^ i : ℤ) : Λ) * (a : Λ) := by
        intro t; rw [mul_comm a, Int.cast_mul, mul_assoc]
      rw [Finset.sum_congr rfl (fun t _ => e t), ← Finset.sum_mul, hD0 i]
      rcases i with _ | i
      · simp
      · simp
  -- the null polynomial `H = ∏_{s < K0} (X + p (s + 1))`
  set H : Polynomial ℤ :=
    ∏ s ∈ Finset.range K0, (Polynomial.X + Polynomial.C ((p : ℤ) * ((s : ℤ) + 1))) with hH
  have hev : ∀ y : ℤ, H.eval y = ∏ s ∈ Finset.range K0, (y + (p : ℤ) * ((s : ℤ) + 1)) := by
    intro y
    rw [hH, Polynomial.eval_prod]
    simp
  have hzero : ∀ t ∈ Finset.range K0, H.eval (momU p t) = 0 := by
    intro t ht
    rw [hev]
    apply Finset.prod_eq_zero ht
    unfold momU
    ring
  have hH0 : H.eval 0 = ((p ^ K0 * K0 ! : ℕ) : ℤ) := by
    rw [hev, ← Finset.prod_range_add_one_eq_factorial]
    simp only [zero_add]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    push_cast
    ring
  have hN : ((p ^ K0 * K0 ! : ℕ) : Λ) = 0 := by
    have h1 := hlin H
    rw [Finset.sum_eq_zero (fun t ht => by rw [hzero t ht, Int.cast_zero, mul_zero]), hH0,
      Int.cast_natCast] at h1
    exact h1.symm
  have hne0 : p ^ K0 * K0 ! ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) (Nat.factorial_ne_zero _)
  have hv := le_padicValNat_of_natCast_eq_zero p hpk hne hne0 hN
  rwa [padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) (Nat.factorial_ne_zero _),
    padicValNat.prime_pow] at hv

/-- A sum over `z < M` of a function that vanishes off the class `z ≡ -1 (mod p)` is a sum over
`z = p t + (p - 1)`, `t < M / p`. -/
theorem sum_range_class_neg_one {M' : Type*} [AddCommMonoid M'] (p : ℕ) (hp : 0 < p)
    (F : ℕ → M') (M : ℕ) (hF : ∀ z < M, z % p ≠ p - 1 → F z = 0) :
    ∑ z ∈ range M, F z = ∑ t ∈ range (M / p), F (p * t + (p - 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih (fun z hz => hF z (by omega)), Nat.succ_div]
    by_cases hd : p ∣ M + 1
    · rw [ite_eq_left hd, Finset.sum_range_succ]
      have eM : p * (M / p) + (p - 1) = M := by
        obtain ⟨q, hq⟩ := hd
        rcases q with _ | q
        · simp at hq
        · have hM : M = p * q + (p - 1) := by
            rw [Nat.mul_succ] at hq
            generalize p * q = Q at hq ⊢
            omega
          rw [hM, Nat.mul_add_div hp, Nat.div_eq_of_lt (by omega), add_zero]
      rw [eM]
    · rw [ite_eq_right hd, add_zero, hF M (by omega) ?_, add_zero]
      intro hmod
      apply hd
      refine ⟨M / p + 1, ?_⟩
      have := Nat.div_add_mod M p
      rw [mul_add, mul_one]
      generalize p * (M / p) = Q at this ⊢
      omega

/-- **The shift operator** (Remark 6.5): combining the rows
`r, r + 1, ..., r + d` of a slice with the coefficients of an integer polynomial `Π` of degree
at most `d` gives `∑_z c_z x_z ^ r Π(x_z) = y ^ r Π(y)`. -/
theorem slice_shift {ι : Type*} (s : Finset ι) (c : ι → Λ) (x : ι → ℤ) (y : ℤ)
    (P : Polynomial ℤ) (d : ℕ) (hd : P.natDegree ≤ d) (r : ℕ)
    (h : ∀ i ≤ d, ∑ z ∈ s, c z * ((x z ^ (r + i) : ℤ) : Λ) = ((y ^ (r + i) : ℤ) : Λ)) :
    ∑ z ∈ s, c z * ((x z ^ r * P.eval (x z) : ℤ) : Λ) = ((y ^ r * P.eval y : ℤ) : Λ) := by
  have hev : ∀ w : ℤ, w ^ r * P.eval w = ∑ i ∈ range (d + 1), w ^ (r + i) * P.coeff i := by
    intro w
    rw [Polynomial.eval_eq_sum_range' (by omega : P.natDegree < d + 1), Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  simp only [hev, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [← h i (by have := Finset.mem_range.mp hi; omega), Finset.sum_mul]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [mul_assoc]

/-- **Step 2 of Theorem 4.5 by the shift operator**: if `L + 1 ≤ p K` and the slice
`∑_{z ≤ L} c_z z ^ r = (-1) ^ r` holds in `Λ` for `k ≤ r ≤ 2k - 1 + (p - 2) K`, then there are
`c'_t` (`t < (L + 1) / p`) with `∑_t c'_t (1 - p (t + 1)) ^ r = 1` for `k ≤ r ≤ 2k - 1`. -/
theorem slice_isolate (p : ℕ) [hp : Fact p.Prime] {k : ℕ} (hpk : (p : Λ) ^ k = 0)
    (K L : ℕ) (hL : L + 1 ≤ p * K) (c : ℕ → Λ)
    (h : ∀ r, k ≤ r → r ≤ 2 * k - 1 + (p - 2) * K →
      ∑ z ∈ range (L + 1), c z * (z : Λ) ^ r = (-1) ^ r) :
    ∃ c' : ℕ → Λ, ∀ r, k ≤ r → r ≤ 2 * k - 1 →
      ∑ t ∈ range ((L + 1) / p), c' t * (((1 - (p : ℤ) * ((t : ℤ) + 1)) ^ r : ℤ) : Λ) = 1 := by
  classical
  have hp1 := hp.out.one_lt
  set P : Polynomial ℤ := ∏ t ∈ range K, ∏ ρ ∈ Ico 1 (p - 1),
    (X - C ((p * t + ρ : ℕ) : ℤ)) with hP
  have hdeg : P.natDegree ≤ (p - 2) * K := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum (fun t _ => Polynomial.natDegree_prod_le _ _)).trans ?_
    simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Nat.card_Ico, Finset.card_range,
      smul_eq_mul, mul_one]
    rw [show p - 1 - 1 = p - 2 by omega, mul_comm]
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hP1 : ¬ (p : ℤ) ∣ P.eval (-1) := by
    rw [hP, Polynomial.eval_prod]
    intro hd
    obtain ⟨t, -, ht⟩ := (Prime.dvd_finsetProd_iff hprime _).mp hd
    rw [Polynomial.eval_prod] at ht
    obtain ⟨ρ, hρ, hρd⟩ := (Prime.dvd_finsetProd_iff hprime _).mp ht
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hρd
    have hρ' := Finset.mem_Ico.mp hρ
    have h2 : (p : ℤ) ∣ ((ρ + 1 : ℕ) : ℤ) := by
      have e : ((ρ + 1 : ℕ) : ℤ) = -(-1 - ((p * t + ρ : ℕ) : ℤ)) - (p : ℤ) * t := by
        push_cast; ring
      rw [e]; exact dvd_sub (dvd_neg.mpr hρd) (dvd_mul_right _ _)
    have h3 := Nat.le_of_dvd (by omega) (Int.natCast_dvd_natCast.mp h2)
    omega
  obtain ⟨a, ha⟩ := exists_intCast_mul_eq_one (Λ := Λ) p hpk hP1
  -- the vanishing off the class `z ≡ -1`
  have hvan : ∀ r, k ≤ r → ∀ z < L + 1, z % p ≠ p - 1 →
      c z * ((((z : ℤ)) ^ r * P.eval (z : ℤ) : ℤ) : Λ) = 0 := by
    intro r hr z hz hzp
    by_cases h0 : z % p = 0
    · have hpz : (p : ℤ) ∣ (z : ℤ) := Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero h0)
      rw [intCast_eq_zero_of_pow_dvd hpk (dvd_mul_of_dvd_left
        ((pow_dvd_pow (p : ℤ) hr).trans (pow_dvd_pow_of_dvd hpz r)) _), mul_zero]
    · have hzK : z / p < K := (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by rw [mul_comm]; omega)
      have hmod := Nat.mod_lt z hp.out.pos
      have hPz : P.eval (z : ℤ) = 0 := by
        rw [hP, Polynomial.eval_prod]
        apply Finset.prod_eq_zero (Finset.mem_range.mpr hzK)
        rw [Polynomial.eval_prod]
        apply Finset.prod_eq_zero (i := z % p) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
        simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
        rw [Nat.div_add_mod, sub_self]
      rw [hPz, mul_zero, Int.cast_zero, mul_zero]
  refine ⟨fun t => c (p * t + (p - 1)) *
    ((P.eval ((p * t + (p - 1) : ℕ) : ℤ) * a : ℤ) : Λ), fun r hr1 hr2 => ?_⟩
  -- the filtered rows
  have hfilt := slice_shift (range (L + 1)) c (fun z => (z : ℤ)) (-1) P ((p - 2) * K) hdeg r
    (fun i hi => by
      have := h (r + i) (by omega) (by omega)
      push_cast
      exact this)
  rw [sum_range_class_neg_one p hp.out.pos _ (L + 1) (hvan r hr1)] at hfilt
  have e : ∀ t ∈ range ((L + 1) / p),
      c (p * t + (p - 1)) * ((P.eval ((p * t + (p - 1) : ℕ) : ℤ) * a : ℤ) : Λ) *
        (((1 - (p : ℤ) * ((t : ℤ) + 1)) ^ r : ℤ) : Λ) =
      c (p * t + (p - 1)) * ((((p * t + (p - 1) : ℕ) : ℤ) ^ r *
        P.eval ((p * t + (p - 1) : ℕ) : ℤ) : ℤ) : Λ) * (((-1) ^ r * a : ℤ) : Λ) := by
    intro t _
    have hw : ((p * t + (p - 1) : ℕ) : ℤ) = (p : ℤ) * t + p - 1 := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hp.out.one_le]; push_cast; ring
    have hint : P.eval ((p * t + (p - 1) : ℕ) : ℤ) * a * (1 - (p : ℤ) * ((t : ℤ) + 1)) ^ r =
        ((p * t + (p - 1) : ℕ) : ℤ) ^ r * P.eval ((p * t + (p - 1) : ℕ) : ℤ) *
          ((-1) ^ r * a) := by
      have hneg : (1 - (p : ℤ) * ((t : ℤ) + 1)) = -((p * t + (p - 1) : ℕ) : ℤ) := by
        rw [hw]; ring
      rw [hneg, neg_pow]; ring
    rw [mul_assoc, ← Int.cast_mul, hint, Int.cast_mul, ← mul_assoc]
  rw [Finset.sum_congr rfl e, ← Finset.sum_mul, hfilt, ← Int.cast_mul, ← ha]
  congr 1
  have hsq : ((-1 : ℤ) ^ r) * ((-1) ^ r) = 1 := by
    rw [← mul_pow]; norm_num
  linear_combination (P.eval (-1) * a) * hsq

/-- **Theorem 4.5 with the shift operator's range of rows** (Remark 6.5): if `p ^ k = 0` and `p ^ (k - 1) ≠ 0` in a ring `Λ` and
`∑_{z ≤ L} c_z z ^ r = (-1) ^ r` in `Λ` for `k ≤ r ≤ 2k - 1 + (p - 2) K(p,k)`, then
`L + 1 ≥ p K(p,k)`. -/
theorem lower_slice_shift (p : ℕ) [hp : Fact p.Prime] {k : ℕ} (hpk : (p : Λ) ^ k = 0)
    (hne : (p : Λ) ^ (k - 1) ≠ 0) (L : ℕ) (c : ℕ → Λ)
    (h : ∀ r, k ≤ r → r ≤ 2 * k - 1 + (p - 2) * Nat.find (exists_K p k) →
      ∑ z ∈ range (L + 1), c z * (z : Λ) ^ r = (-1) ^ r) :
    p * Nat.find (exists_K p k) ≤ L + 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨c', hc'⟩ := slice_isolate p hpk (Nat.find (exists_K p k)) L hlt.le c h
  have hb := moment_bound_ring p hpk hne ((L + 1) / p) c' hc'
  have hlt' : (L + 1) / p < Nat.find (exists_K p k) :=
    (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by rw [mul_comm]; exact hlt)
  exact Nat.find_min (exists_K p k) hlt' hb

/-- `K(p,k) ≤ k ≤ p ^ (k - 1)`. -/
theorem find_K_le_pow (p : ℕ) [hp : Fact p.Prime] (k : ℕ) :
    Nat.find (exists_K p k) ≤ p ^ (k - 1) := by
  have h1 : Nat.find (exists_K p k) ≤ k := Nat.find_min' _ (Nat.le_add_right k _)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact h1.trans (Nat.zero_le _)
  have h2 : k - 1 < 2 ^ (k - 1) := Nat.lt_two_pow_self
  have h3 : 2 ^ (k - 1) ≤ p ^ (k - 1) := Nat.pow_le_pow_left hp.out.two_le _
  omega

/-- The shift operator's range lies inside the paper's: `2k - 1 + (p - 2) K(p,k) ≤ N_p(k)`. -/
theorem shift_rows_le_Np (p : ℕ) [hp : Fact p.Prime] (k : ℕ) :
    2 * k - 1 + (p - 2) * Nat.find (exists_K p k) ≤ Np p k := by
  unfold Np
  have := Nat.mul_le_mul_left (p - 2) (find_K_le_pow p k)
  omega

/-- **Theorem 4.5 of the paper** (rows `k ≤ r ≤ N_p(k)`, any ring `Λ` with `p ^ k = 0`):
with `N_p(k) = 2k - 1 + (p - 2) p ^ (k - 1)`, if `c_0, ..., c_L ∈ Λ`, `p ^ k = 0` and
`p ^ (k - 1) ≠ 0` in `Λ`, and `∑_{z ≤ L} c_z z ^ r = (-1) ^ r` in `Λ` for every
`k ≤ r ≤ N_p(k)`, then `L + 1 ≥ p K(p,k)`. -/
theorem lower_slice (p : ℕ) [hp : Fact p.Prime] {k : ℕ} (hpk : (p : Λ) ^ k = 0)
    (hne : (p : Λ) ^ (k - 1) ≠ 0) (L : ℕ) (c : ℕ → Λ)
    (h : ∀ r, k ≤ r → r ≤ Np p k → ∑ z ∈ range (L + 1), c z * (z : Λ) ^ r = (-1) ^ r) :
    p * Nat.find (exists_K p k) ≤ L + 1 :=
  lower_slice_shift p hpk hne L c fun r h1 h2 => h r h1 (h2.trans (shift_rows_le_Np p k))

/-- **Theorem 4.5 of the paper, Kempner form**: under the hypotheses of `lower_slice`,
`L + 1 ≥ S(p ^ k)`. -/
theorem lower_slice_kempner (p : ℕ) [hp : Fact p.Prime] {k : ℕ} (hpk : (p : Λ) ^ k = 0)
    (hne : (p : Λ) ^ (k - 1) ≠ 0) (L : ℕ) (c : ℕ → Λ)
    (h : ∀ r, k ≤ r → r ≤ Np p k → ∑ z ∈ range (L + 1), c z * (z : Λ) ^ r = (-1) ^ r) :
    kempner p k ≤ L + 1 := by
  rw [← kempner_eq]; exact lower_slice p hpk hne L c h

/-- In a `ZMod (p ^ k)`-algebra, `p ^ k = 0`. -/
theorem natCast_pow_eq_zero_of_algebra (p k : ℕ) {Λ : Type*} [Ring Λ] [Algebra (ZMod (p ^ k)) Λ] :
    (p : Λ) ^ k = 0 := by
  rw [← Nat.cast_pow, ← map_natCast (algebraMap (ZMod (p ^ k)) Λ) (p ^ k), ZMod.natCast_self,
    map_zero]

/-- **Theorem 4.5 of the paper, verbatim hypotheses**: `Λ` a ring which is an algebra over
`ZMod (p ^ k)` with `p ^ (k - 1) ≠ 0` in `Λ`, and `∑_{z ≤ L} c_z z ^ r = (-1) ^ r` in `Λ` for
`k ≤ r ≤ N_p(k)`; then `L + 1 ≥ p K(p,k) = S(p ^ k)`. -/
theorem thm_lower (p : ℕ) [hp : Fact p.Prime] {k : ℕ} {Λ : Type*} [Ring Λ]
    [Algebra (ZMod (p ^ k)) Λ] (hne : (p : Λ) ^ (k - 1) ≠ 0) (L : ℕ) (c : ℕ → Λ)
    (h : ∀ r, k ≤ r → r ≤ Np p k → ∑ z ∈ range (L + 1), c z * (z : Λ) ^ r = (-1) ^ r) :
    p * Nat.find (exists_K p k) ≤ L + 1 ∧ kempner p k ≤ L + 1 :=
  ⟨lower_slice p (natCast_pow_eq_zero_of_algebra p k) hne L c h,
    lower_slice_kempner p (natCast_pow_eq_zero_of_algebra p k) hne L c h⟩

end LowerRing

section Squarefree

local notation "AF" => ArithmeticFunction ℤ

/-- Step 1 of Theorem 4.5 from an identity at the squarefree `n` only: the rows
`∑_{z ≤ L} g_z(1) z ^ r ≡ (-1) ^ r (mod p ^ k)` for every `r ≥ 0`. -/
theorem level_moments_squarefree {p : ℕ} (hp2 : 2 ≤ p) (k L : ℕ) (g : ℕ → AF)
    (h : ∀ n, Squarefree n → ((p ^ k : ℕ) : ℤ) ∣
      (μ : AF) n - (∑ z ∈ range (L + 1), (ζ : AF) ^ z * frobPush p (g z)) n) (r : ℕ) :
    (p : ℤ) ^ k ∣ (∑ z ∈ range (L + 1), g z 1 * (z : ℤ) ^ r) - (-1) ^ r := by
  obtain ⟨T, hT, hTc⟩ :=
    (Set.infinite_of_not_bddAbove Nat.not_bddAbove_setOfPred_prime).exists_subset_card_eq r
  have hTp : ∀ q ∈ T, q.Prime := fun q hq => hT hq
  have hsq : Squarefree (∏ q ∈ T, q) := squarefree_prod_primes T hTp
  have hn0 : (∏ q ∈ T, q) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun q hq => (hTp q hq).ne_zero)
  have hmu : (μ : AF) (∏ q ∈ T, q) = (-1) ^ r := by
    rw [ArithmeticFunction.IsMultiplicative.map_prod_of_prime
        ArithmeticFunction.isMultiplicative_moebius T hTp,
      Finset.prod_congr rfl (fun q hq => ArithmeticFunction.moebius_apply_prime (hTp q hq)),
      Finset.prod_const, hTc]
  have hz : ∀ z : ℕ, ((ζ : AF) ^ z) (∏ q ∈ T, q) = (z : ℤ) ^ r := by
    intro z
    rw [ArithmeticFunction.IsMultiplicative.map_prod_of_prime
        (ArithmeticFunction.isMultiplicative_zeta.natCast.pow (k := z)) T hTp,
      Finset.prod_congr rfl (fun q hq => zeta_pow_apply_prime z (hTp q hq)), Finset.prod_const,
      hTc]
  have hS : (∑ z ∈ range (L + 1), (ζ : AF) ^ z * frobPush p (g z)) (∏ q ∈ T, q) =
      ∑ z ∈ range (L + 1), g z 1 * (z : ℤ) ^ r := by
    rw [sum_apply']
    apply Finset.sum_congr rfl
    intro z _
    rw [zeta_pow_mul_frobPush_sqfree hp2 z (g z) hsq hn0, hz, mul_comm]
  have h1 := h (∏ q ∈ T, q) hsq
  rw [hmu, hS] at h1
  push_cast at h1
  have h2 := dvd_neg.mpr h1
  rwa [neg_sub] at h2

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Theorem 4.5, "In particular" (the squarefree form)**: if
`μ(n) ≡ ∑_{z ≤ L} (d_z * E_p g_z)(n) (mod p ^ k)` holds at every squarefree `n` (not necessarily
at every `n`), with integer valued `g_z`, then `L + 1 ≥ p K(p,k) = S(p ^ k)`. -/
theorem level_bound_squarefree (k L : ℕ) (g : ℕ → AF)
    (h : ∀ n, Squarefree n → ((p ^ k : ℕ) : ℤ) ∣
      (μ : AF) n - (∑ z ∈ range (L + 1), (ζ : AF) ^ z * frobPush p (g z)) n) :
    p * Nat.find (exists_K p k) ≤ L + 1 ∧ kempner p k ≤ L + 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 : Nat.find (exists_K p 0) ≤ 0 := Nat.find_min' _ (Nat.zero_le _)
    have h1 : Nat.find (exists_K p 0) = 0 := by omega
    rw [← kempner_eq, h1, mul_zero]
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  have hpk : (p : ZMod (p ^ k)) ^ k = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hne : (p : ZMod (p ^ k)) ^ (k - 1) ≠ 0 := by
    rw [← Nat.cast_pow, Ne, ZMod.natCast_eq_zero_iff,
      Nat.pow_dvd_pow_iff_le_right hp.out.one_lt]
    omega
  have hrow : ∀ r, ∑ z ∈ range (L + 1), ((g z 1 : ℤ) : ZMod (p ^ k)) * (z : ZMod (p ^ k)) ^ r =
      (-1) ^ r := by
    intro r
    have h1 := level_moments_squarefree hp.out.two_le k L g h r
    have h2 : (((∑ z ∈ range (L + 1), g z 1 * (z : ℤ) ^ r) - (-1) ^ r : ℤ) : ZMod (p ^ k)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by exact_mod_cast h1)
    push_cast at h2
    exact sub_eq_zero.mp h2
  exact ⟨lower_slice p hpk hne L _ (fun r _ _ => hrow r),
    lower_slice_kempner p hpk hne L _ (fun r _ _ => hrow r)⟩

end Squarefree

end FrobCong
