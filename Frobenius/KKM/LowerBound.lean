module

public import Frobenius.KKM.Defs
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# The lower bound of Kauers, Krattenthaler and Müller for `Φ_p`

Let `p` be a prime and let `A ∈ ℤ[z][t]` be monic in `t` of degree `d`. We show that some
coefficient of `A(z, Φ_p(z))` equals `d!` (`exists_coeff_evalPhi_eq_factorial`). Consequently, if
`A(z, Φ_p(z)) ≡ 0 (mod p ^ γ)` coefficientwise, then `p ^ γ ∣ d!`
(`pow_dvd_factorial_of_vanishesMod`). This is Lemma 1 of Kauers, Krattenthaler and Müller (2012),
also used by Krattenthaler and Müller (2025).

## Proof plan

Write `s(n)` for the sum of the base `p` digits of `n` (`digitSum p n`).

1. `s(a + b) ≤ s(a) + s(b)`, from Legendre's formula `(p - 1) v_p(n!) = n - s(n)` and
   `a! b! ∣ (a + b)!`. Also `s(p ^ k) = 1` and `s(n) ≥ 1` for `n ≥ 1`.
2. Concatenation: if `y < p ^ K` then `s(y + p ^ K x) = s(y) + s(x)`. More generally, if
   `y < p ^ K` and every element of the finset `T` is at least `K`, then
   `s(y + ∑ j ∈ T, p ^ j) = s(y) + #T`; with `y = 0` this gives `s(∑ j ∈ S, p ^ j) = #S`.
3. Support bound: if the coefficient of `z ^ M` in `Φ_p ^ i` is nonzero then `s(M) ≤ i`, since
   every such `M` is a sum of `i` powers of `p`.
4. If `k ∉ S` and `a + p ^ k = ∑ j ∈ S, p ^ j` then `#S ≤ s(a)` (adding `p ^ k` to `a` must carry).
5. Exact coefficient: the coefficient of `z ^ (∑ j ∈ S, p ^ j)` in `Φ_p ^ #S` is `#S !`. By induction
   on `#S`: removing one factor `Φ_p`, the term for `p ^ k` with `k ∈ S` contributes `(#S - 1)!` by
   induction, and the term for `p ^ k` with `k ∉ S` vanishes by 3 and 4.
6. Main step: with `D` the sum of the `z`-degrees of the coefficients of `A` and
   `N = ∑ j ∈ [D, D + d), p ^ j`, the coefficient of `z ^ N` in `A(z, Φ_p(z))` is `d!`. The leading
   term gives `d!` by 5. For `i < d` and `m ≤ D < p ^ D` we have `s(N - m) ≥ d > i` by 2, so the
   term `A_i(z) Φ_p ^ i` contributes nothing by 3.
-/

@[expose] public section

namespace Frobenius.KKM

/-! ### Digit sums -/

/-- The sum of the base `p` digits of `n`. -/
def digitSum (p n : ℕ) : ℕ := (Nat.digits p n).sum

/-- The digit sum of `0` is `0`. -/
theorem digitSum_zero (p : ℕ) : digitSum p 0 = 0 := by
  simp [digitSum]

/-- Peeling off the last base `p` digit: `s(n) = n % p + s(n / p)`. -/
theorem digitSum_eq_mod_add_div {p : ℕ} (hp : 1 < p) (n : ℕ) :
    digitSum p n = n % p + digitSum p (n / p) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [digitSum]
  · rw [digitSum, Nat.digits_def' hp hn, List.sum_cons]
    rfl

/-- The digit sum of `1` is `1`. -/
theorem digitSum_one {p : ℕ} (hp : 1 < p) : digitSum p 1 = 1 := by
  rw [digitSum_eq_mod_add_div hp, Nat.mod_eq_of_lt hp, Nat.div_eq_of_lt hp, digitSum_zero]

/-- Concatenation of base `p` expansions: if `y < p ^ K` then `s(y + p ^ K x) = s(y) + s(x)`. -/
theorem digitSum_add_pow_mul {p : ℕ} (hp : 1 < p) (K : ℕ) {y : ℕ} (hy : y < p ^ K) (x : ℕ) :
    digitSum p (y + p ^ K * x) = digitSum p y + digitSum p x := by
  induction K generalizing y with
  | zero =>
    obtain rfl : y = 0 := by simpa using hy
    simp [digitSum_zero]
  | succ K ih =>
    have hp0 : 0 < p := by omega
    have hy' : y / p < p ^ K := by
      rw [Nat.div_lt_iff_lt_mul hp0, ← pow_succ]
      exact hy
    rw [digitSum_eq_mod_add_div hp (y + _), digitSum_eq_mod_add_div hp y, pow_succ', mul_assoc,
      Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hp0, ih hy', add_assoc]

/-- A power of `p` has digit sum `1`. -/
theorem digitSum_pow {p : ℕ} (hp : 1 < p) (k : ℕ) : digitSum p (p ^ k) = 1 := by
  have h := digitSum_add_pow_mul hp k (y := 0) (pow_pos (by omega) k) 1
  simpa [digitSum_zero, digitSum_one hp] using h

/-- A positive number has positive digit sum. -/
theorem digitSum_pos {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : n ≠ 0) : 0 < digitSum p n := by
  have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hn
  rw [sub_one_mul_padicValNat_factorial] at h
  unfold digitSum
  omega

/-- Subadditivity of the digit sum, from Legendre's formula and `a! b! ∣ (a + b)!`. -/
theorem digitSum_add_le (p : ℕ) [Fact p.Prime] (a b : ℕ) :
    digitSum p (a + b) ≤ digitSum p a + digitSum p b := by
  have hv : padicValNat p a.factorial + padicValNat p b.factorial ≤
      padicValNat p (a + b).factorial := by
    rw [← padicValNat.mul (Nat.factorial_ne_zero a) (Nat.factorial_ne_zero b)]
    exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero _)).mp
      (pow_padicValNat_dvd.trans (Nat.factorial_mul_factorial_dvd_factorial_add a b))
  have ha := sub_one_mul_padicValNat_factorial (p := p) a
  have hb := sub_one_mul_padicValNat_factorial (p := p) b
  have hab := sub_one_mul_padicValNat_factorial (p := p) (a + b)
  have h1 := Nat.digit_sum_le p a
  have h2 := Nat.digit_sum_le p b
  have h3 := Nat.digit_sum_le p (a + b)
  have hm := Nat.mul_le_mul_left (p - 1) hv
  rw [mul_add] at hm
  unfold digitSum
  omega

/-- Appending distinct powers of `p` above a small number: if `y < p ^ K` and every element of `T`
is at least `K`, then `s(y + ∑ j ∈ T, p ^ j) = s(y) + #T`. -/
theorem digitSum_add_sum_pow {p : ℕ} (hp : 1 < p) (T : Finset ℕ) :
    ∀ (K y : ℕ), y < p ^ K → (∀ j ∈ T, K ≤ j) →
      digitSum p (y + ∑ j ∈ T, p ^ j) = digitSum p y + T.card := by
  induction T using Finset.induction_on_min with
  | empty => intro K y _ _; simp
  | insert m T hT ih =>
    intro K y hy hK
    have hmT : m ∉ T := fun h => lt_irrefl m (hT m h)
    have hKm : K ≤ m := hK m (Finset.mem_insert_self m T)
    have hpK : p ^ K ≤ p ^ m := Nat.pow_le_pow_right (by omega) hKm
    have h2 : 2 * p ^ m ≤ p ^ (m + 1) := by
      rw [pow_succ, mul_comm]
      exact Nat.mul_le_mul_left _ hp
    rw [Finset.sum_insert hmT, Finset.card_insert_of_notMem hmT, ← add_assoc,
      ih (m + 1) (y + p ^ m) (by omega) (fun j hj => hT j hj), ← mul_one (p ^ m),
      digitSum_add_pow_mul hp m (by omega) 1, digitSum_one hp]
    ring

/-- Claim C: a sum of distinct powers of `p` has digit sum equal to the number of terms. -/
theorem digitSum_sum_pow {p : ℕ} (hp : 1 < p) (S : Finset ℕ) :
    digitSum p (∑ j ∈ S, p ^ j) = S.card := by
  simpa [digitSum_zero] using
    digitSum_add_sum_pow hp S 0 0 (by simp) (fun j _ => Nat.zero_le j)

/-- Removing a power of `p` that is not among the summands: if `k ∉ S` and
`a + p ^ k = ∑ j ∈ S, p ^ j`, then `#S ≤ s(a)`. -/
theorem card_le_digitSum_of_add_pow_eq (p : ℕ) [hp : Fact p.Prime] (k : ℕ) (S : Finset ℕ) :
    ∀ a : ℕ, k ∉ S → a + p ^ k = ∑ j ∈ S, p ^ j → S.card ≤ digitSum p a := by
  have h1 : 1 < p := hp.out.one_lt
  induction S using Finset.induction_on_max with
  | empty => intro a _ _; simp
  | insert m T hT ih =>
    intro a hk ha
    have hmT : m ∉ T := fun h => lt_irrefl m (hT m h)
    have hkm : k ≠ m := fun h => hk (h ▸ Finset.mem_insert_self m T)
    have hkT : k ∉ T := fun h => hk (Finset.mem_insert_of_mem h)
    have hsT : ∑ j ∈ T, p ^ j < p ^ m := Nat.geomSum_lt h1 hT
    rw [Finset.sum_insert hmT] at ha
    rw [Finset.card_insert_of_notMem hmT]
    rcases lt_or_gt_of_ne hkm with hlt | hgt
    · by_cases hle : p ^ k ≤ ∑ j ∈ T, p ^ j
      · -- the borrow is absorbed below `p ^ m`
        have hIH := ih (∑ j ∈ T, p ^ j - p ^ k) hkT (by omega)
        have hsplit : a = (∑ j ∈ T, p ^ j - p ^ k) + p ^ m * 1 := by omega
        rw [hsplit, digitSum_add_pow_mul h1 m (by omega) 1, digitSum_one h1]
        omega
      · -- the borrow reaches `p ^ m`
        push Not at hle
        have hpow : p ^ m = p ^ k * p ^ (m - k) := by
          rw [← pow_add]
          congr 1
          omega
        have hge : 1 < p ^ (m - k) := one_lt_pow₀ h1 (by omega)
        have hle' : p ^ k ≤ p ^ k * p ^ (m - k) := Nat.le_mul_of_pos_right _ (by omega)
        have hsplit : a = ∑ j ∈ T, p ^ j + p ^ k * (p ^ (m - k) - 1) := by
          rw [Nat.mul_sub_one]
          omega
        rw [hsplit, digitSum_add_pow_mul h1 k hle, digitSum_sum_pow h1]
        have := digitSum_pos (p := p) (n := p ^ (m - k) - 1) (by omega)
        omega
    · -- `p ^ k` is too large
      exfalso
      have h3 : p ^ (m + 1) ≤ p ^ k := Nat.pow_le_pow_right (by omega) hgt
      have h4 : 2 * p ^ m ≤ p ^ (m + 1) := by
        rw [pow_succ, mul_comm]
        exact Nat.mul_le_mul_left _ h1
      omega

/-! ### Coefficients of powers of `Φ_p` -/

/-- The coefficient of `z ^ (p ^ k)` in `Φ_p` is `1`. -/
theorem coeff_Phi_pow_self (p k : ℕ) : PowerSeries.coeff (p ^ k) (Phi p) = 1 := by
  rw [coeff_Phi, Set.indicator_of_mem (Set.mem_range_self k), Pi.one_apply]

/-- Claim B (support bound): if the coefficient of `z ^ M` in `Φ_p ^ i` is nonzero, then the
digit sum of `M` is at most `i`. -/
theorem digitSum_le_of_coeff_Phi_pow_ne_zero (p : ℕ) [hp : Fact p.Prime] (i : ℕ) :
    ∀ M : ℕ, PowerSeries.coeff M (Phi p ^ i) ≠ 0 → digitSum p M ≤ i := by
  induction i with
  | zero =>
    intro M hM
    rw [pow_zero, PowerSeries.coeff_one] at hM
    split_ifs at hM with h
    · subst h
      simp [digitSum_zero]
    · exact absurd rfl hM
  | succ i ih =>
    intro M hM
    rw [pow_succ, PowerSeries.coeff_mul] at hM
    obtain ⟨⟨a, b⟩, hab, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hM
    rw [Finset.mem_antidiagonal] at hab
    dsimp only at hab hne
    have ha := ih a (left_ne_zero_of_mul hne)
    have hb : b ∈ Set.range (fun k : ℕ => p ^ k) := by
      have h := right_ne_zero_of_mul hne
      rw [coeff_Phi] at h
      exact Set.mem_of_indicator_ne_zero h
    obtain ⟨k, rfl⟩ := hb
    have h := digitSum_add_le p a (p ^ k)
    rw [digitSum_pow hp.out.one_lt, hab] at h
    omega

/-- Claim A (exact coefficient): the coefficient of `z ^ (∑ j ∈ S, p ^ j)` in `Φ_p ^ #S` is
`#S !`. -/
theorem coeff_sum_pow_Phi_pow (p : ℕ) [hp : Fact p.Prime] :
    ∀ (n : ℕ) (S : Finset ℕ), S.card = n →
      PowerSeries.coeff (∑ j ∈ S, p ^ j) (Phi p ^ n) = (n.factorial : ℤ) := by
  have h1 : 1 < p := hp.out.one_lt
  intro n
  induction n with
  | zero =>
    intro S hS
    rw [Finset.card_eq_zero] at hS
    subst hS
    simp
  | succ n ih =>
    intro S hS
    have hsub : S.image (fun k => ((∑ j ∈ S, p ^ j) - p ^ k, p ^ k)) ⊆
        Finset.antidiagonal (∑ j ∈ S, p ^ j) := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_antidiagonal]
      have : p ^ k ≤ ∑ j ∈ S, p ^ j := Finset.single_le_sum (fun j _ => Nat.zero_le (p ^ j)) hk
      dsimp only
      omega
    rw [pow_succ, PowerSeries.coeff_mul, ← Finset.sum_subset hsub ?_]
    · rw [Finset.sum_image ?_]
      · have hterm : ∀ k ∈ S, PowerSeries.coeff ((∑ j ∈ S, p ^ j) - p ^ k) (Phi p ^ n) *
            PowerSeries.coeff (p ^ k) (Phi p) = (n.factorial : ℤ) := by
          intro k hk
          rw [coeff_Phi_pow_self, mul_one]
          have h2 : (∑ j ∈ S, p ^ j) - p ^ k = ∑ j ∈ S.erase k, p ^ j := by
            rw [← Finset.add_sum_erase S _ hk]
            omega
          rw [h2]
          exact ih _ (by rw [Finset.card_erase_of_mem hk, hS]; rfl)
        rw [Finset.sum_congr rfl hterm, Finset.sum_const, hS, nsmul_eq_mul, Nat.factorial_succ]
        push_cast
        ring
      · intro k _ l _ hkl
        simp only [Prod.mk.injEq] at hkl
        exact Nat.pow_right_injective h1 hkl.2
    · rintro ⟨a, b⟩ hab hnot
      rw [Finset.mem_antidiagonal] at hab
      dsimp only
      by_cases hb : b ∈ Set.range (fun k : ℕ => p ^ k)
      · obtain ⟨k, rfl⟩ := hb
        dsimp only at hab
        have hkS : k ∉ S := by
          intro hk
          apply hnot
          refine Finset.mem_image.mpr ⟨k, hk, ?_⟩
          simp only [Prod.mk.injEq, and_true]
          omega
        have hle := card_le_digitSum_of_add_pow_eq p k S a hkS hab
        have hzero : PowerSeries.coeff a (Phi p ^ n) = 0 := by
          by_contra hne
          have := digitSum_le_of_coeff_Phi_pow_ne_zero p n a hne
          omega
        rw [hzero, zero_mul]
      · rw [coeff_Phi, Set.indicator_of_notMem hb, mul_zero]

/-! ### The main step -/

/-- Digit sums just below a block of consecutive powers: if `m < p ^ K` then
`d ≤ s(∑ j ∈ [K, K + d), p ^ j - m)`. -/
theorem le_digitSum_sum_Ico_sub (p : ℕ) [hp : Fact p.Prime] (K d : ℕ) {m : ℕ} (hm : m < p ^ K) :
    d ≤ digitSum p (∑ j ∈ Finset.Ico K (K + d), p ^ j - m) := by
  have h1 : 1 < p := hp.out.one_lt
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Nat.zero_le _
  rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : K < K + d)]
  have hK : p ^ K < p ^ (K + 1) := Nat.pow_lt_pow_right h1 (Nat.lt_succ_self K)
  have hsplit : p ^ K + ∑ j ∈ Finset.Ico (K + 1) (K + d), p ^ j - m =
      (p ^ K - m) + ∑ j ∈ Finset.Ico (K + 1) (K + d), p ^ j := by
    omega
  rw [hsplit, digitSum_add_sum_pow h1 _ (K + 1) (p ^ K - m) (by omega)
    (fun j hj => (Finset.mem_Ico.mp hj).1), Nat.card_Ico]
  have := digitSum_pos (p := p) (n := p ^ K - m) (by omega)
  omega

/-- For monic `A` of `t`-degree `d`, some coefficient of `A(z, Φ_p(z))` equals `d!`. -/
theorem exists_coeff_evalPhi_eq_factorial (p : ℕ) [Fact p.Prime] (A : Polynomial (Polynomial ℤ))
    (hA : A.Monic) : ∃ N : ℕ, PowerSeries.coeff N (evalPhi p A) = (A.natDegree.factorial : ℤ) := by
  have h1 : 1 < p := (Fact.out : p.Prime).one_lt
  let D := ∑ i ∈ Finset.range (A.natDegree + 1), (A.coeff i).natDegree
  refine ⟨∑ j ∈ Finset.Ico D (D + A.natDegree), p ^ j, ?_⟩
  rw [evalPhi, Polynomial.eval₂_eq_sum_range, map_sum, Finset.sum_range_succ, Finset.sum_eq_zero,
    zero_add, hA.coeff_natDegree, map_one, one_mul]
  · exact coeff_sum_pow_Phi_pow p _ _ (by simp)
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [Polynomial.coeToPowerSeries.ringHom_apply, PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨m, r⟩ hmr
    rw [Finset.mem_antidiagonal] at hmr
    dsimp only at hmr ⊢
    rw [Polynomial.coeff_coe]
    by_cases hm : m ≤ (A.coeff i).natDegree
    · have hiD : (A.coeff i).natDegree ≤ D :=
        Finset.single_le_sum (f := fun i => (A.coeff i).natDegree) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.mpr (by omega))
      have hmD : m ≤ D := hm.trans hiD
      have hmK : m < p ^ D := lt_of_le_of_lt hmD (Nat.lt_pow_self h1)
      have hr : r = ∑ j ∈ Finset.Ico D (D + A.natDegree), p ^ j - m := by omega
      have hds := le_digitSum_sum_Ico_sub p D A.natDegree hmK
      rw [← hr] at hds
      have hzero : PowerSeries.coeff r (Phi p ^ i) = 0 := by
        by_contra hne
        have := digitSum_le_of_coeff_Phi_pow_ne_zero p i r hne
        omega
      rw [hzero, mul_zero]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

/-- Lemma 1 of Kauers, Krattenthaler and Müller (2012) and Krattenthaler and Müller (2025). -/
theorem pow_dvd_factorial_of_vanishesMod (p : ℕ) [Fact p.Prime] (γ : ℕ)
    (A : Polynomial (Polynomial ℤ)) (hA : A.Monic) (hv : VanishesMod p γ A) :
    p ^ γ ∣ A.natDegree.factorial := by
  obtain ⟨N, hN⟩ := exists_coeff_evalPhi_eq_factorial p A hA
  have h := hv N
  rw [hN] at h
  exact_mod_cast h

end Frobenius.KKM
