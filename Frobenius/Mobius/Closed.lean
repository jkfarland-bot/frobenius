module

public import Mathlib
public import Frobenius.Mobius.Levels

/-!
# Corollary 4.11: closed forms for `S(p ^ k)` (seat L11)

Numbers refer to J. S. Farland, *A proof of a conjecture of Kauers, Krattenthaler and
Müller, and exact level counts for Frobenius lifts* (2026), the larger paper.

Pure arithmetic about `K(p,k) = min {K ≥ 1 : K + v_p(K!) ≥ k}` (in Lean `Nat.find (exists_K p k)`)
and the Kempner value `S(p ^ k) = p K(p,k)` (`kempner p k`, `kempner_eq`). By Theorem 4.4
(`levels_sharp_kempner`), `L(p,k) = S(p ^ k) - 1`, so these are the paper's statements about
`L(p,k)`.

* (i) `find_K_closed`, `kempner_closed`, `kempner_sub_one_closed`: for `k ≤ p ^ 2 + p`,
  `K(p,k) = k - ⌊k/(p+1)⌋` and `S(p ^ k) - 1 = p (k - ⌊k/(p+1)⌋) - 1`;
  `kempner_of_le`: `S(p ^ k) = k p` for `k ≤ p`; `kempner_lt_of_lt`: `S(p ^ k) < k p`, hence
  `S(p ^ k) - 1 < k p - 1`, for every `k ≥ p + 1`.
* (ii) `kempner_bounds`: `(p - 1) k < S(p ^ k) < (p - 1) k + p + s_p(K(p,k) - 1)` for `k ≥ 1`,
  with `s_p` the base `p` digit sum; `digits_sum_le_log` and `kempner_lt_log` give the
  `O(p (1 + log_p k))` form.
-/

@[expose] public section

open scoped Nat

namespace FrobCong

section Closed

variable (p : ℕ) [hp : Fact p.Prime]

/-- `v_p(m!)` is monotone in `m`. -/
theorem padicValNat_factorial_mono {m n : ℕ} (h : m ≤ n) :
    padicValNat p m ! ≤ padicValNat p n ! :=
  (padicValNat_dvd_iff_le (Nat.factorial_ne_zero n)).mp
    ((pow_padicValNat_dvd).trans (Nat.factorial_dvd_factorial h))

/-- Below `p ^ 2`, `v_p(m!) = ⌊m / p⌋`. -/
theorem padicValNat_factorial_of_lt_sq {m : ℕ} (hm : m < p ^ 2) :
    padicValNat p m ! = m / p := by
  rw [padicValNat_factorial_floor, padicValNat_factorial_p_mul]
  have hlt : m / p < p := by
    rw [Nat.div_lt_iff_lt_mul hp.out.pos]; rwa [sq] at hm
  have h0 : padicValNat p (m / p)! = 0 :=
    padicValNat.eq_zero_of_not_dvd
      (fun hd => absurd ((Nat.Prime.dvd_factorial hp.out).mp hd) (by omega))
  rw [h0, add_zero]

/-- `K(p,k) = m` as soon as `m + v_p(m!) ≥ k` and either `m = 0` or `(m - 1) + v_p((m - 1)!) < k`. -/
theorem find_K_eq_of {k m : ℕ} (h1 : k ≤ m + padicValNat p m !)
    (h2 : m = 0 ∨ m - 1 + padicValNat p (m - 1)! < k) : Nat.find (exists_K p k) = m := by
  rw [Nat.find_eq_iff]
  refine ⟨h1, fun n hn hP => ?_⟩
  rcases h2 with h2 | h2
  · omega
  have := padicValNat_factorial_mono p (show n ≤ m - 1 by omega)
  omega

/-- **Corollary 4.11(i), the value of `K`**: for `k ≤ p ^ 2 + p`,
`K(p,k) = k - ⌊k / (p + 1)⌋`. -/
theorem find_K_closed {k : ℕ} (hk : k ≤ p ^ 2 + p) :
    Nat.find (exists_K p k) = k - k / (p + 1) := by
  have hp1 := hp.out.one_lt
  have hsq : p ^ 2 = p * p := sq p
  have hpp : p * (p - 1) = p * p - p := Nat.mul_sub_one p p
  have hple : p ≤ p * p := Nat.le_mul_self p
  have hpq1 : (p + 1) * p = p * p + p := by ring
  have hks : (p + 1) * (k / (p + 1)) + k % (p + 1) = k := Nat.div_add_mod k (p + 1)
  have hslt : k % (p + 1) < p + 1 := Nat.mod_lt k (by omega)
  have hqp : k / (p + 1) ≤ p := Nat.div_le_of_le_mul (by omega)
  generalize k / (p + 1) = q at hks hqp ⊢
  generalize k % (p + 1) = s at hks hslt
  have hPq : (p + 1) * q = p * q + q := by ring
  have hV : ∀ n, n < p ^ 2 → padicValNat p n ! = n / p :=
    fun n hn => padicValNat_factorial_of_lt_sq p hn
  have hdiv : ∀ t, t < p → (p * q + t) / p = q := fun t ht => by
    rw [Nat.mul_add_div hp.out.pos, Nat.div_eq_of_lt ht, add_zero]
  rcases Nat.lt_or_ge s p with hsp | hsp
  · rcases Nat.lt_or_ge q p with hqp' | hqp'
    · -- `s < p`, `q < p`: `K = p q + s < p ^ 2`
      have hPle : p * q ≤ p * (p - 1) := Nat.mul_le_mul_left p (by omega)
      have hm : k - q = p * q + s := by omega
      have hmlt : p * q + s < p ^ 2 := by omega
      rw [hm]
      apply find_K_eq_of p
      · rw [hV _ hmlt, hdiv s hsp]; omega
      · rcases Nat.eq_zero_or_pos (p * q + s) with h0 | h0
        · left; exact h0
        · right
          rw [hV (p * q + s - 1) (by omega)]
          have : (p * q + s - 1) / p ≤ (p * q + s) / p := Nat.div_le_div_right (by omega)
          rw [hdiv s hsp] at this
          omega
    · -- `q = p`, so `s = 0`, `k = p ^ 2 + p` and `K = p ^ 2`
      have hqe : q = p := le_antisymm hqp hqp'
      rw [hqe] at hks ⊢
      have hm : k - p = p * p := by omega
      rw [hm]
      apply find_K_eq_of p
      · rw [padicValNat_factorial_p_mul]; omega
      · right
        rw [hV (p * p - 1) (by omega)]
        have : (p * p - 1) / p < p := (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by omega)
        omega
  · -- `s = p`: `q < p` and `K = p (q + 1)`
    have hse : s = p := by omega
    have hqlt : q < p := by
      by_contra hc
      push Not at hc
      have : (p + 1) * p ≤ (p + 1) * q := Nat.mul_le_mul_left (p + 1) hc
      omega
    have hPle : p * q ≤ p * (p - 1) := Nat.mul_le_mul_left p (by omega)
    have hm : k - q = p * (q + 1) := by rw [mul_add, mul_one]; omega
    rw [hm]
    apply find_K_eq_of p
    · rw [padicValNat_factorial_p_mul, mul_add, mul_one]; omega
    · right
      have e : p * (q + 1) - 1 = p * q + (p - 1) := by rw [mul_add, mul_one]; omega
      rw [e, hV _ (by omega), hdiv (p - 1) (by omega)]
      omega

/-- **Corollary 4.11(i), Kempner form**: for `k ≤ p ^ 2 + p`,
`S(p ^ k) = p (k - ⌊k / (p + 1)⌋)`. -/
theorem kempner_closed {k : ℕ} (hk : k ≤ p ^ 2 + p) : kempner p k = p * (k - k / (p + 1)) := by
  rw [← kempner_eq, find_K_closed p hk]

/-- **Corollary 4.11(i), level form**: for `1 ≤ k ≤ p ^ 2 + p`,
`S(p ^ k) - 1 = p (k - ⌊k / (p + 1)⌋) - 1`, that is `L(p,k) = p (k - ⌊k/(p+1)⌋) - 1`. -/
theorem kempner_sub_one_closed {k : ℕ} (_hk1 : 1 ≤ k) (hk : k ≤ p ^ 2 + p) :
    kempner p k - 1 = p * (k - k / (p + 1)) - 1 := by
  rw [kempner_closed p hk]

/-- **Corollary 4.11(i), `k ≤ p`**: `S(p ^ k) = k p`, so `S(p ^ k) - 1 = k p - 1`. -/
theorem kempner_of_le {k : ℕ} (hk : k ≤ p) : kempner p k = k * p := by
  rw [kempner_closed p (by have := Nat.zero_le (p ^ 2); omega),
    Nat.div_eq_of_lt (by omega : k < p + 1), Nat.sub_zero, mul_comm]

/-- **Corollary 4.11(i), `k ≥ p + 1`**: `K(p,k) ≤ k - 1`, since `v_p((k - 1)!) ≥ 1`. -/
theorem find_K_le_sub_one {k : ℕ} (hk : p + 1 ≤ k) : Nat.find (exists_K p k) ≤ k - 1 := by
  apply Nat.find_min'
  have : 1 ≤ padicValNat p (k - 1)! :=
    one_le_padicValNat_of_dvd (Nat.factorial_ne_zero _)
      ((Nat.Prime.dvd_factorial hp.out).mpr (by omega))
  omega

/-- **Corollary 4.11(i), `k ≥ p + 1`**: `S(p ^ k) < k p` and `S(p ^ k) - 1 < k p - 1`
(for every `k ≥ p + 1`, not only `k ≤ p ^ 2 + p`). -/
theorem kempner_lt_of_lt {k : ℕ} (hk : p + 1 ≤ k) :
    kempner p k < k * p ∧ kempner p k - 1 < k * p - 1 := by
  have h1 := find_K_le_sub_one p hk
  have h2 : p * Nat.find (exists_K p k) ≤ p * (k - 1) := Nat.mul_le_mul_left p h1
  have h3 : p * (k - 1) < p * k := Nat.mul_lt_mul_of_pos_left (by omega) hp.out.pos
  have h4 := p_le_kempner p k (by omega)
  have hp1 := hp.out.one_lt
  rw [kempner_eq] at h2
  rw [mul_comm k p]
  omega

omit hp in
/-- A positive number has a positive base `p` digit sum. -/
theorem digits_sum_pos {n : ℕ} (hn : n ≠ 0) : 1 ≤ (Nat.digits p n).sum := by
  have hne : Nat.digits p n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  have h1 := Nat.getLast_digit_ne_zero p hn
  have h2 := List.le_sum_of_mem (List.getLast_mem hne)
  omega

/-- **Corollary 4.11(ii)**: for every `k ≥ 1`,
`(p - 1) k < S(p ^ k) < (p - 1) k + p + s_p(K(p,k) - 1)`, with `s_p` the base `p` digit sum
(`S(p ^ k) = L(p,k) + 1`). -/
theorem kempner_bounds {k : ℕ} (hk : 1 ≤ k) :
    (p - 1) * k < kempner p k ∧
      kempner p k < (p - 1) * k + p + (Nat.digits p (Nat.find (exists_K p k) - 1)).sum := by
  rw [← kempner_eq]
  have hP : k ≤ Nat.find (exists_K p k) + padicValNat p (Nat.find (exists_K p k))! :=
    Nat.find_spec (exists_K p k)
  have hmin := Nat.find_min (exists_K p k) (m := Nat.find (exists_K p k) - 1)
  generalize Nat.find (exists_K p k) = K at hP hmin ⊢
  have hK1 : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · rw [h0] at hP; simp at hP; omega
    · exact h0
  have hmin' : ¬ (k ≤ K - 1 + padicValNat p (K - 1)!) := hmin (by omega)
  have hL1 := sub_one_mul_padicValNat_factorial (p := p) K
  have hL2 := sub_one_mul_padicValNat_factorial (p := p) (K - 1)
  have hs1 := Nat.digit_sum_le p K
  have hs2 := Nat.digit_sum_le p (K - 1)
  have hpos := digits_sum_pos p (show K ≠ 0 by omega)
  have hp1 := hp.out.one_lt
  have hA : (p - 1) * K = p * K - K := Nat.sub_one_mul p K
  have hB : K ≤ p * K := Nat.le_mul_of_pos_left K hp.out.pos
  have hC : (p - 1) * (K - 1) = p * (K - 1) - (K - 1) := Nat.sub_one_mul p (K - 1)
  have hD : K - 1 ≤ p * (K - 1) := Nat.le_mul_of_pos_left (K - 1) hp.out.pos
  have hE : p * (K - 1) = p * K - p := Nat.mul_sub_one p K
  have hF : p ≤ p * K := Nat.le_mul_of_pos_right p (by omega)
  constructor
  · have h1 : (p - 1) * k ≤ (p - 1) * (K + padicValNat p K !) := Nat.mul_le_mul_left _ hP
    have h2 : (p - 1) * (K + padicValNat p K !) = (p - 1) * K + (p - 1) * padicValNat p K ! :=
      mul_add _ _ _
    omega
  · have h1 : (p - 1) * (K - 1 + padicValNat p (K - 1)! + 1) ≤ (p - 1) * k :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : (p - 1) * (K - 1 + padicValNat p (K - 1)! + 1) =
        (p - 1) * (K - 1) + (p - 1) * padicValNat p (K - 1)! + (p - 1) := by ring
    omega

/-- The base `p` digit sum of `n` is at most `(p - 1) (log_p n + 1)`. -/
theorem digits_sum_le_log (n : ℕ) : (Nat.digits p n).sum ≤ (p - 1) * (Nat.log p n + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h1 := List.sum_le_length_nsmul (Nat.digits p n) (p - 1)
    (fun x hx => Nat.le_sub_one_of_lt (Nat.digits_lt_base hp.out.one_lt hx))
  rw [Nat.length_digits p n hp.out.one_lt (by omega), smul_eq_mul] at h1
  rw [mul_comm]; exact h1

/-- **Corollary 4.11(ii), the `O(p (1 + log_p k))` form**: for every `k ≥ 1`,
`(p - 1) k < S(p ^ k) < (p - 1) k + p + (p - 1) (log_p k + 1)`. -/
theorem kempner_lt_log {k : ℕ} (hk : 1 ≤ k) :
    (p - 1) * k < kempner p k ∧
      kempner p k < (p - 1) * k + p + (p - 1) * (Nat.log p k + 1) := by
  have h := kempner_bounds p hk
  have h2 := digits_sum_le_log p (Nat.find (exists_K p k) - 1)
  have h3 : Nat.log p (Nat.find (exists_K p k) - 1) ≤ Nat.log p k :=
    Nat.log_mono_right (by have := Nat.find_min' (exists_K p k) (Nat.le_add_right k _); omega)
  have h4 := Nat.mul_le_mul_left (p - 1) (Nat.add_le_add_right h3 1)
  omega

end Closed

end FrobCong
