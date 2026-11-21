module

/-
Run r25, seat L9: note Corollary `cor:muchi` for `χ = χ₄` at `p = 2` (order `p^a` with `a = 1`,
`w = 1` prime dividing the modulus), as an instance of R-084 over `ℤ` (L7's
`Dir.levelCount_infRank_int`).

`χ₄` has values in `ℤ`, so `ℤ[χ₄] = ℤ` and `p = 2` is unramified: this instance needs none of the
`ℤ[χ]` machinery (Theorem `R_π`, T1, T2), only the flag of `f = μ * χ₄` over `ℤ`:
`d(1) = 0` (direction `2`), `d(j) = 1` for `j ≥ 2` (the primes `q ≡ 3 mod 4`, infinitely many by
Dirichlet's theorem in Mathlib), `r_f` infinite. Result (`levelCount_muchi4`):

    L_f(2, k) + 1 = min {m : v_2(m!) + ⌊m/2⌋ ≥ k}     for every k ≥ 1,

which is the note's formula (eq:muchi) with p = 2, a = 1, w = 1. Concrete values for k = 1..12
(`muchi4_values`): 1, 1, 3, 3, 3, 5, 5, 7, 7, 7, 7, 9, as listed in the note.

Lean v4.33.1 with Mathlib. No sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.DirBase
public import Frobenius.Levels.DirFlag
public import Frobenius.Levels.Cor

@[expose] public section

namespace FrobLevel

namespace Dir

/-- `χ₄` as an arithmetic function with values in `ℤ`. -/
def chi4 : ArithmeticFunction ℤ := ⟨fun n => ZMod.χ₄ (n : ZMod 4), by simp⟩

theorem chi4_apply (n : ℕ) : chi4 n = ZMod.χ₄ (n : ZMod 4) := rfl

/-- `f = μ * χ₄` (Dirichlet convolution). -/
def muchi4 : ArithmeticFunction ℤ := ArithmeticFunction.moebius * chi4

/-- The indicator of `n = 2`. -/
def delta2 : ArithmeticFunction ℤ := ⟨fun n => if n = 2 then 1 else 0, by simp⟩

theorem delta2_apply (n : ℕ) : delta2 n = if n = 2 then 1 else 0 := rfl

/-- `χ₄ ≡ ζ * (ε - δ₂)` modulo `2`, pointwise. -/
theorem chi4_sub_dvd (n : ℕ) :
    (2 : ℤ) ∣ (chi4 - (ArithmeticFunction.zeta : ArithmeticFunction ℤ) * (1 - delta2)) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [sub_apply', ArithmeticFunction.coe_zeta_mul_apply]
  have hs : ∑ i ∈ n.divisors, (1 - delta2) i = 1 - (if 2 ∣ n then 1 else 0) := by
    simp only [sub_apply', ArithmeticFunction.one_apply, delta2_apply, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Nat.mem_divisors, Nat.one_dvd, true_and]
    simp [hn]
  rw [hs, chi4_apply, ZMod.χ₄_nat_eq_if_mod_four]
  by_cases h2 : n % 2 = 0
  · have : 2 ∣ n := Nat.dvd_of_mod_eq_zero h2
    simp [h2, this]
  · have : ¬ 2 ∣ n := fun h => h2 (Nat.mod_eq_zero_of_dvd h)
    simp only [h2, this, if_false]
    split_ifs <;> norm_num

/-- `μ * χ₄ ≡ ε - δ₂` modulo `2`, pointwise. -/
theorem muchi4_mod2 (n : ℕ) : (2 : ℤ) ∣ muchi4 n - (1 - delta2) n := by
  have hz : (ArithmeticFunction.moebius : ArithmeticFunction ℤ) * ArithmeticFunction.zeta = 1 :=
    ArithmeticFunction.moebius_mul_coe_zeta
  have heq : muchi4 - (1 - delta2) = (ArithmeticFunction.moebius : ArithmeticFunction ℤ) *
      (chi4 - (ArithmeticFunction.zeta : ArithmeticFunction ℤ) * (1 - delta2)) := by
    rw [muchi4, mul_sub, ← mul_assoc, hz, one_mul]
  have h2 : ((2 : ℕ) : ArithmeticFunction ℤ) ∣
      (chi4 - (ArithmeticFunction.zeta : ArithmeticFunction ℤ) * (1 - delta2)) :=
    natCast_dvd_of_apply (fun n => by exact_mod_cast chi4_sub_dvd n)
  obtain ⟨c, hc⟩ := dvd_mul_of_dvd_right h2 (ArithmeticFunction.moebius : ArithmeticFunction ℤ)
  have := congrArg (fun F : ArithmeticFunction ℤ => F n) (heq.trans hc)
  rw [← sub_apply', this, natCast_mul_apply]
  exact ⟨c n, by push_cast; ring⟩

theorem muchi4_odd_iff (n : ℕ) : ¬ (2 : ℤ) ∣ muchi4 n ↔ n = 1 ∨ n = 2 := by
  rw [dvd_iff_dvd_of_dvd_sub (muchi4_mod2 n), sub_apply', ArithmeticFunction.one_apply,
    delta2_apply]
  by_cases h1 : n = 1
  · subst h1; norm_num
  by_cases h2 : n = 2
  · subst h2; norm_num
  simp [h1, h2]

theorem muchi4_one : muchi4 1 = 1 := by
  simp [muchi4, chi4_apply]

theorem muchi4_prime {q : ℕ} (hq : q.Prime) : muchi4 q = chi4 q - 1 := by
  rw [muchi4, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b =>
    (ArithmeticFunction.moebius : ArithmeticFunction ℤ) a * chi4 b), Nat.Prime.divisors hq,
    Finset.sum_pair hq.one_lt.ne]
  simp [ArithmeticFunction.moebius_apply_prime hq, Nat.div_self hq.pos, chi4_apply]
  ring

theorem muchi4_two : muchi4 2 = -1 := by
  rw [muchi4_prime Nat.prime_two, chi4_apply]; decide

theorem muchi4_prime_three {q : ℕ} (hq : q.Prime) (h3 : (q : ZMod 4) = 3) : muchi4 q = -2 := by
  rw [muchi4_prime hq, chi4_apply, h3]; decide

theorem cls_prime {q : ℕ} (hq : q.Prime) : cls 2 q = Finsupp.single q 1 := by
  ext r
  rw [cls_apply, hq.factorization]
  by_cases h : r = q
  · subst h; simp
  · simp [Ne.symm h]

theorem cls_one : cls 2 1 = 0 := by
  ext r; simp [cls_apply]

theorem witSet_zero : witSet 2 muchi4 Set.univ 0 = {2} := by
  ext n
  simp only [witSet, Set.mem_univ, true_and, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hn0, hc, hd⟩
    have hd' : ¬ (2 : ℤ) ∣ muchi4 n := by simpa using hd
    rcases (muchi4_odd_iff n).1 hd' with rfl | rfl
    · exact absurd cls_one hc
    · rfl
  · rintro rfl
    refine ⟨by norm_num, ?_, ?_⟩
    · rw [cls_prime Nat.prime_two]; exact Finsupp.single_ne_zero.2 one_ne_zero
    · rw [muchi4_two]; norm_num

theorem rank_dSpace_zero : Module.rank (ZMod 2) (dSpace 2 muchi4 Set.univ 0) = 1 := by
  rw [dSpace, witSet_zero, Set.image_singleton, cls_prime Nat.prime_two]
  have hli : LinearIndepOn (ZMod 2) id ({Finsupp.single 2 (1 : ZMod 2)} : Set (ℕ →₀ ZMod 2)) :=
    (linearIndepOn_singleton_iff (ZMod 2)).2 (by simp)
  rw [rank_span_set hli, Cardinal.mk_singleton]

/-- The primes `q ≡ 3 (mod 4)`. -/
def P3 : Set ℕ := {q | q.Prime ∧ (q : ZMod 4) = 3}

theorem P3_infinite : P3.Infinite :=
  Nat.infinite_setOfPred_prime_and_eq_mod (q := 4) (a := 3) (by decide)

theorem single_image_indep :
    LinearIndepOn (ZMod 2) id ((fun q : ℕ => (Finsupp.single q (1 : ZMod 2))) '' P3) :=
  ((Finsupp.linearIndependent_single_one (ZMod 2) ℕ).linearIndepOn P3).id_image

theorem aleph0_le_span :
    Cardinal.aleph0 ≤ Module.rank (ZMod 2)
      (Submodule.span (ZMod 2) ((fun q : ℕ => (Finsupp.single q (1 : ZMod 2))) '' P3)) := by
  rw [rank_span_set single_image_indep]
  have hinf : ((fun q : ℕ => (Finsupp.single q (1 : ZMod 2))) '' P3).Infinite :=
    P3_infinite.image (fun a _ b _ h => by
      simpa using (Finsupp.single_left_injective (one_ne_zero : (1 : ZMod 2) ≠ 0)) h)
  exact Cardinal.aleph0_le_mk_iff.2 hinf.to_subtype

theorem image_P3_sub (S : Set ℕ) (hS : ∀ q ∈ P3, q ∈ S) :
    (fun q : ℕ => (Finsupp.single q (1 : ZMod 2))) '' P3 ⊆ cls 2 '' S := by
  rintro _ ⟨q, hq, rfl⟩
  exact ⟨q, hS q hq, cls_prime hq.1⟩

theorem aleph0_le_dSpace_one : Cardinal.aleph0 ≤ Module.rank (ZMod 2) (dSpace 2 muchi4 Set.univ 1) := by
  refine (aleph0_le_span).trans (Submodule.rank_mono (Submodule.span_mono (image_P3_sub _ ?_)))
  intro q hq
  refine ⟨Set.mem_univ _, hq.1.ne_zero, ?_, ?_⟩
  · rw [cls_prime hq.1]; exact Finsupp.single_ne_zero.2 one_ne_zero
  · rw [muchi4_prime_three hq.1 hq.2]; norm_num

theorem aleph0_le_dRank : Cardinal.aleph0 ≤ dRank 2 muchi4 Set.univ := by
  refine (aleph0_le_span).trans (Submodule.rank_mono (Submodule.span_mono (image_P3_sub _ ?_)))
  intro q hq
  refine ⟨Set.mem_univ _, hq.1.ne_zero, ?_, ?_⟩
  · rw [cls_prime hq.1]; exact Finsupp.single_ne_zero.2 one_ne_zero
  · rw [muchi4_prime_three hq.1 hq.2]; norm_num

theorem dFlag_one : dFlag 2 muchi4 Set.univ 1 = 0 := by
  rw [dFlag, if_neg one_ne_zero]
  apply Nat.sInf_eq_zero.2 (Or.inl _)
  show ((1 : ℕ) : Cardinal) ≤ _
  rw [rank_dSpace_zero]; simp

theorem dFlag_ge_two {j : ℕ} (hj : 2 ≤ j) : dFlag 2 muchi4 Set.univ j = 1 := by
  rw [dFlag, if_neg (by omega)]
  have h1 : 1 ∈ {d | (j : Cardinal) ≤ Module.rank (ZMod 2) (dSpace 2 muchi4 Set.univ d)} :=
    (Cardinal.natCast_lt_aleph0 (n := j)).le.trans aleph0_le_dSpace_one
  have h0 : 0 ∉ {d | (j : Cardinal) ≤ Module.rank (ZMod 2) (dSpace 2 muchi4 Set.univ d)} := by
    simp only [Set.mem_ofPred_eq, rank_dSpace_zero, not_le]
    exact_mod_cast (show 1 < j by omega)
  refine le_antisymm (Nat.sInf_le h1) ?_
  have hne : (Set.Nonempty {d | (j : Cardinal) ≤ Module.rank (ZMod 2) (dSpace 2 muchi4 Set.univ d)}) :=
    ⟨1, h1⟩
  have hm := Nat.sInf_mem hne
  by_contra hc
  have : sInf {d | (j : Cardinal) ≤ Module.rank (ZMod 2) (dSpace 2 muchi4 Set.univ d)} = 0 := by
    omega
  rw [this] at hm
  exact h0 hm

theorem flag_sum (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1),
      (dFlag 2 muchi4 Set.univ (j + 1) - dFlag 2 muchi4 Set.univ j) * (m / 2 ^ j) = m / 2 := by
  rw [Finset.sum_eq_single 1]
  · rw [dFlag_ge_two (le_refl 2), dFlag_one]; simp
  · intro j _ hj
    rcases Nat.lt_or_ge j 1 with h | h
    · have : j = 0 := by omega
      subst this; rw [dFlag_one]; simp [dFlag]
    · rw [dFlag_ge_two (by omega), dFlag_ge_two (by omega)]; simp
  · intro h
    have : m = 0 := by simp at h; omega
    subst this; simp

theorem muchi4_isUnit : IsUnit muchi4 :=
  ArithmeticFunction.isUnit_iff_isUnit_apply_one.2 (by rw [muchi4_one]; exact isUnit_one)

/-- **Cor `muchi` for `χ₄` at `p = 2`**: `L_f(2, k) + 1 = min {m : v_2(m!) + ⌊m/2⌋ ≥ k}`. -/
theorem levelCount_muchi4 {k : ℕ} (hk : 1 ≤ k) :
    levelCount 2 (Ep 2) muchi4 k + 1 = sInf {m | k ≤ padicValNat 2 m.factorial + m / 2} := by
  have := Fact.mk Nat.prime_two
  rw [levelCount_infRank_int 2 muchi4_isUnit hk aleph0_le_dRank]
  simp_rw [flag_sum]

theorem v2fact (m : ℕ) : padicValNat 2 m.factorial = m - (Nat.digits 2 m).sum := by
  have := Fact.mk Nat.prime_two
  have h := sub_one_mul_padicValNat_factorial (p := 2) m
  simpa using h

theorem muchi4_eq_of {k c : ℕ} (hk : 1 ≤ k) (hc : k ≤ padicValNat 2 c.factorial + c / 2)
    (hlt : ∀ m < c, padicValNat 2 m.factorial + m / 2 < k) :
    levelCount 2 (Ep 2) muchi4 k = c - 1 := by
  have h := levelCount_muchi4 hk
  have hs : sInf {m | k ≤ padicValNat 2 m.factorial + m / 2} = c :=
    le_antisymm (Nat.sInf_le hc) (le_csInf ⟨c, hc⟩ (fun m hm => not_lt.1 fun h' =>
      absurd hm (not_le.2 (hlt m h'))))
  omega

/-- The note's listed values for `χ₄` at `p = 2`, `k = 1..12`. -/
theorem muchi4_values :
    (List.range 12).map (fun i => levelCount 2 (Ep 2) muchi4 (i + 1))
      = [1, 1, 3, 3, 3, 5, 5, 7, 7, 7, 7, 9] := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
    List.cons_append]
  rw [muchi4_eq_of (c := 2) (by norm_num) (by simp only [v2fact]; norm_num)
      (by intro m hm; interval_cases m <;> simp only [v2fact] <;> norm_num),
    muchi4_eq_of (c := 2) (by norm_num) (by simp only [v2fact]; norm_num)
      (by intro m hm; interval_cases m <;> simp only [v2fact] <;> norm_num),
    muchi4_eq_of (c := 4) (by norm_num) (by simp only [v2fact]; norm_num)
      (by intro m hm; interval_cases m <;> simp only [v2fact] <;> norm_num),
    muchi4_eq_of (c := 4) (by norm_num) (by simp only [v2fact]; norm_num)
      (by intro m hm; interval_cases m <;> simp only [v2fact] <;> norm_num),
    muchi4_eq_of (c := 4) (by norm_num) (by simp only [v2fact]; norm_num)
      (by intro m hm; interval_cases m <;> simp only [v2fact] <;> norm_num),
    muchi4_eq_of (c := 6) (by norm_num) (by simp only [v2fact]; norm_num)
      (by intro m hm; interval_cases m <;> simp only [v2fact] <;> norm_num),
    muchi4_eq_of (c := 6) (by norm_num) (by simp only [v2fact]; norm_num)
      (by intro m hm; interval_cases m <;> simp only [v2fact] <;> norm_num),
    muchi4_eq_of (c := 8) (by norm_num) (by simp only [v2fact]; norm_num)
      (by intro m hm; interval_cases m <;> simp only [v2fact] <;> norm_num),
    muchi4_eq_of (c := 8) (by norm_num) (by simp only [v2fact]; norm_num)
      (by intro m hm; interval_cases m <;> simp only [v2fact] <;> norm_num),
    muchi4_eq_of (c := 8) (by norm_num) (by simp only [v2fact]; norm_num)
      (by intro m hm; interval_cases m <;> simp only [v2fact] <;> norm_num),
    muchi4_eq_of (c := 8) (by norm_num) (by simp only [v2fact]; norm_num)
      (by intro m hm; interval_cases m <;> simp only [v2fact] <;> norm_num),
    muchi4_eq_of (c := 10) (by norm_num) (by simp only [v2fact]; norm_num)
      (by intro m hm; interval_cases m <;> simp only [v2fact] <;> norm_num)]

end Dir

end FrobLevel
