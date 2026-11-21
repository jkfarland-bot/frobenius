module

/-
Seat L12: the depth flag of a multiplicative function (Lemma 7.11).

Numbers refer to J. S. Farland, *A proof of a conjecture of Kauers, Krattenthaler and
Müller, and exact level counts for Frobenius lifts* (2026), the larger paper.

For a multiplicative `f` and a prime `q`, the prime depth is
`ν_q = min {v_p f(q ^ a) : a ≥ 1, p ∤ a}` (`primeDepth`, with `v_p = emultiplicity p`, so
`ν_q = ∞` when all those values are divisible by every power of `p`, for instance when they
vanish). Lemma 7.11: `r_f` is the number of primes with `ν_q < ∞`, and `d(j)` is the `j`-th
smallest prime depth counted with multiplicity, that is the least `d` such that at least `j` primes
have `ν_q ≤ d` (`primeDepthStat`).

Main results:
* `dSpace_univ_mult`, `rank_dSpace_univ_mult`: `U_d` is spanned by the coordinate vectors of the
  primes with `ν_q ≤ d`, and `dim U_d = #{q : ν_q ≤ d}`. Over any commutative ring.
* `fSpace_univ_mult`, `dRank_univ_mult`: `r_f = #{q : ν_q < ∞}` (over any commutative ring in which
  a nonzero element is not divisible by every power of `p`, e.g. `ℤ` and `ℤ_[p]`).
* `dFlag_univ_mult`: `d(j) = primeDepthStat p f j`, the `j`-th smallest prime depth.
* `levelCount_mult_int`, `levelCount_mult_padic`: for multiplicative `f` over `ℤ` or `ℤ_[p]`,
  `L_f(p, k) + 1` is the depth-flag value built from the prime depths.
-/
public import Mathlib
public import Frobenius.Levels.DirFlag

@[expose] public section

-- As in `DirFlag.lean`: restore the v4.33 instance path for `AddCommGroup (ZMod p)`.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace FrobLevel

namespace Dir

section Mult

variable (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R]

/-- The prime depth `ν_q = min {v_p f(q ^ a) : a ≥ 1, p ∤ a}` in `ℕ∞`, with `v_p` the
multiplicity of `p` (`∞` for `0`). -/
noncomputable def primeDepth (f : ArithmeticFunction R) (q : ℕ) : ℕ∞ :=
  ⨅ (a : ℕ) (_ : 0 < a ∧ ¬ p ∣ a), emultiplicity (p : R) (f (q ^ a))

/-- The `j`-th smallest of the prime depths, counted with multiplicity over the primes `q`: the
least `d` such that at least `j` primes have `ν_q ≤ d` (`0` for `j = 0`, as `d(0) = 0`). -/
noncomputable def primeDepthStat (f : ArithmeticFunction R) (j : ℕ) : ℕ :=
  if j = 0 then 0 else
    sInf {d : ℕ | (j : Cardinal) ≤ Cardinal.mk {q : ℕ | q.Prime ∧ primeDepth p f q ≤ d}}

omit hp in
theorem primeDepth_le_iff (f : ArithmeticFunction R) (q d : ℕ) :
    primeDepth p f q ≤ d ↔ ∃ a, 0 < a ∧ ¬ p ∣ a ∧ ¬ (p : R) ^ (d + 1) ∣ f (q ^ a) := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have : ((d + 1 : ℕ) : ℕ∞) ≤ primeDepth p f q := by
      refine le_iInf₂ fun a ha => ?_
      exact pow_dvd_iff_le_emultiplicity.1 (hne a ha.1 ha.2)
    have h2 : ((d + 1 : ℕ) : ℕ∞) ≤ d := this.trans h
    push_cast at h2
    exact absurd h2 (not_le.2 (ENat.lt_add_one_iff (ENat.natCast_ne_top d) |>.2 le_rfl))
  · rintro ⟨a, ha0, hpa, hnd⟩
    refine (iInf₂_le a ⟨ha0, hpa⟩).trans ?_
    have := emultiplicity_lt_iff_not_dvd.2 hnd
    push_cast at this
    exact (ENat.lt_add_one_iff (ENat.natCast_ne_top d)).1 this

omit hp in
theorem primeDepth_lt_top_iff (hsep : ∀ a : R, a ≠ 0 → ∃ d, ¬ (p : R) ^ (d + 1) ∣ a)
    (f : ArithmeticFunction R) (q : ℕ) :
    primeDepth p f q < ⊤ ↔ ∃ a, 0 < a ∧ ¬ p ∣ a ∧ f (q ^ a) ≠ 0 := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1 h.ne
    obtain ⟨a, ha0, hpa, hnd⟩ := (primeDepth_le_iff p f q d).1 hd.symm.le
    exact ⟨a, ha0, hpa, fun h0 => hnd (h0 ▸ dvd_zero _)⟩
  · rintro ⟨a, ha0, hpa, hne⟩
    obtain ⟨d, hd⟩ := hsep _ hne
    exact lt_of_le_of_lt ((primeDepth_le_iff p f q d).2 ⟨a, ha0, hpa, hd⟩) (ENat.natCast_lt_top d)

/-- The class of a prime power: `κ(q ^ a) = (a mod p) e_q`. -/
theorem cls_prime_pow {q : ℕ} (hq : q.Prime) (a : ℕ) :
    cls p (q ^ a) = Finsupp.single q (a : ZMod p) := by
  rw [cls, hq.factorization_pow, Finsupp.mapRange_single]

/-- For multiplicative `f` and a property `P` of values inherited by left factors, the classes
`κ(n) ≠ 0` with `P (f n)` span the coordinate vectors of the primes `q` with `P (f (q ^ a))` for
some `a ≥ 1`, `p ∤ a` (the proof of Lemma 7.11: a class of depth `≤ d` has every
single-prime part of depth `≤ d`). -/
theorem span_cls_mult {f : ArithmeticFunction R} (hf : f.IsMultiplicative) (P : R → Prop)
    (hP : ∀ x y, P (x * y) → P x) :
    Submodule.span (ZMod p) (cls p '' {n | n ≠ 0 ∧ cls p n ≠ 0 ∧ P (f n)}) =
      Submodule.span (ZMod p) ((fun q => Finsupp.single q (1 : ZMod p)) ''
        {q | q.Prime ∧ ∃ a, 0 < a ∧ ¬ p ∣ a ∧ P (f (q ^ a))}) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨n, ⟨hn0, -, hPn⟩, rfl⟩
    have hsum : cls p n =
        ∑ q ∈ (cls p n).support, cls p n q • Finsupp.single q (1 : ZMod p) := by
      conv_lhs => rw [← Finsupp.sum_single (cls p n)]
      rw [Finsupp.sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [SetLike.mem_coe, hsum]
    refine Submodule.sum_mem _ fun q hq => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine ⟨q, ?_, rfl⟩
    have hq' : (n.factorization q : ZMod p) ≠ 0 := by
      rwa [Finsupp.mem_support_iff, cls_apply] at hq
    have hpa : ¬ p ∣ n.factorization q := fun h => hq' ((ZMod.natCast_eq_zero_iff _ _).2 h)
    have hpos : 0 < n.factorization q := by
      rcases Nat.eq_zero_or_pos (n.factorization q) with h | h
      · exact absurd (by rw [h, Nat.cast_zero]) hq'
      · exact h
    have hqp : q.Prime := by
      have : q ∈ n.factorization.support := Finsupp.mem_support_iff.2 hpos.ne'
      rw [Nat.support_factorization] at this
      exact Nat.prime_of_mem_primeFactors this
    refine ⟨hqp, n.factorization q, hpos, hpa, ?_⟩
    have hcop : Nat.Coprime (q ^ n.factorization q) (n / q ^ n.factorization q) :=
      (Nat.coprime_ordCompl hqp hn0).pow_left _
    have hfn : f n = f (q ^ n.factorization q) * f (n / q ^ n.factorization q) := by
      rw [← hf.map_mul_of_coprime hcop, Nat.ordProj_mul_ordCompl_eq_self]
    exact hP _ _ (hfn ▸ hPn)
  · rw [Submodule.span_le]
    rintro _ ⟨q, ⟨hq, a, ha0, hpa, hPa⟩, rfl⟩
    have ha' : (a : ZMod p) ≠ 0 := fun h => hpa ((ZMod.natCast_eq_zero_iff _ _).1 h)
    have hmem : cls p (q ^ a) ∈
        Submodule.span (ZMod p) (cls p '' {n | n ≠ 0 ∧ cls p n ≠ 0 ∧ P (f n)}) := by
      refine Submodule.subset_span ⟨q ^ a, ⟨pow_ne_zero _ hq.ne_zero, ?_, hPa⟩, rfl⟩
      rw [cls_prime_pow p hq, Ne, Finsupp.single_eq_zero]
      exact ha'
    have : Finsupp.single q (1 : ZMod p) = (a : ZMod p)⁻¹ • cls p (q ^ a) := by
      rw [cls_prime_pow p hq, Finsupp.smul_single, smul_eq_mul, inv_mul_cancel₀ ha']
    rw [SetLike.mem_coe]
    change Finsupp.single q (1 : ZMod p) ∈ _
    rw [this]
    exact Submodule.smul_mem _ _ hmem

/-- The span of the coordinate vectors of a set `S` of primes has rank `#S`. -/
theorem rank_span_single_one (S : Set ℕ) :
    Module.rank (ZMod p)
        (Submodule.span (ZMod p) ((fun q => Finsupp.single q (1 : ZMod p)) '' S)) =
      Cardinal.mk S := by
  have hinj : Function.Injective (fun q : ℕ => Finsupp.single q (1 : ZMod p)) :=
    Finsupp.single_left_injective one_ne_zero
  have hli : LinearIndependent (ZMod p) (fun q : S => Finsupp.single (q : ℕ) (1 : ZMod p)) :=
    (Finsupp.linearIndependent_single_one (ZMod p) ℕ).comp _ Subtype.val_injective
  rw [Set.image_eq_range, rank_span hli]
  exact Cardinal.mk_range_eq _ (hinj.comp Subtype.val_injective)

/-- **Lemma 7.11, the spaces `U_d`.** For multiplicative `f`, `U_d` is spanned by the
coordinate vectors of the primes with `ν_q ≤ d`. -/
theorem dSpace_univ_mult {f : ArithmeticFunction R} (hf : f.IsMultiplicative) (d : ℕ) :
    dSpace p f Set.univ d = Submodule.span (ZMod p) ((fun q => Finsupp.single q (1 : ZMod p)) ''
      {q | q.Prime ∧ primeDepth p f q ≤ d}) := by
  have h := span_cls_mult p hf (fun x => ¬ (p : R) ^ (d + 1) ∣ x)
    (fun x y h hx => h (dvd_mul_of_dvd_left hx y))
  have e1 : witSet p f Set.univ d = {n | n ≠ 0 ∧ cls p n ≠ 0 ∧ ¬ (p : R) ^ (d + 1) ∣ f n} := by
    ext n; simp [witSet]
  have e2 : {q | q.Prime ∧ primeDepth p f q ≤ d} =
      {q | q.Prime ∧ ∃ a, 0 < a ∧ ¬ p ∣ a ∧ ¬ (p : R) ^ (d + 1) ∣ f (q ^ a)} := by
    ext q; simp only [Set.mem_ofPred_eq, primeDepth_le_iff]
  rw [dSpace, e1, e2, h]

/-- **Lemma 7.11, dimensions.** For multiplicative `f`, `dim U_d = #{q prime : ν_q ≤ d}`. -/
theorem rank_dSpace_univ_mult {f : ArithmeticFunction R} (hf : f.IsMultiplicative) (d : ℕ) :
    Module.rank (ZMod p) (dSpace p f Set.univ d) =
      Cardinal.mk {q : ℕ | q.Prime ∧ primeDepth p f q ≤ d} := by
  rw [dSpace_univ_mult p hf, rank_span_single_one]

/-- For multiplicative `f`, the span of the classes `κ ≠ 0` with `f_κ ≠ 0` is spanned by the
coordinate vectors of the primes `q` with `f (q ^ a) ≠ 0` for some `a ≥ 1`, `p ∤ a`. -/
theorem fSpace_univ_mult {f : ArithmeticFunction R} (hf : f.IsMultiplicative) :
    fSpace p f Set.univ = Submodule.span (ZMod p) ((fun q => Finsupp.single q (1 : ZMod p)) ''
      {q | q.Prime ∧ ∃ a, 0 < a ∧ ¬ p ∣ a ∧ f (q ^ a) ≠ 0}) := by
  have h := span_cls_mult p hf (fun x => x ≠ 0) (fun x y h => left_ne_zero_of_mul h)
  have e1 : fullWit p f Set.univ = {n | n ≠ 0 ∧ cls p n ≠ 0 ∧ f n ≠ 0} := by
    ext n; simp [fullWit]
  rw [fSpace, e1, h]

/-- **Lemma 7.11, the rank.** For multiplicative `f` over a ring in which no nonzero
element is divisible by every power of `p` (such as `ℤ` and `ℤ_[p]`),
`r_f = #{q prime : ν_q < ∞}`. -/
theorem dRank_univ_mult (hsep : ∀ a : R, a ≠ 0 → ∃ d, ¬ (p : R) ^ (d + 1) ∣ a)
    {f : ArithmeticFunction R} (hf : f.IsMultiplicative) :
    dRank p f Set.univ = Cardinal.mk {q : ℕ | q.Prime ∧ primeDepth p f q < ⊤} := by
  have e : {q : ℕ | q.Prime ∧ primeDepth p f q < ⊤} =
      {q | q.Prime ∧ ∃ a, 0 < a ∧ ¬ p ∣ a ∧ f (q ^ a) ≠ 0} := by
    ext q; simp only [Set.mem_ofPred_eq, primeDepth_lt_top_iff p hsep]
  rw [dRank, fSpace_univ_mult p hf, rank_span_single_one, e]

/-- **Lemma 7.11, the flag.** For multiplicative `f`, `d(j)` is the `j`-th smallest prime
depth `ν_q`, counted with multiplicity. -/
theorem dFlag_univ_mult {f : ArithmeticFunction R} (hf : f.IsMultiplicative) :
    dFlag p f Set.univ = primeDepthStat p f := by
  funext j
  simp only [dFlag, primeDepthStat, rank_dSpace_univ_mult p hf]

/-- **Lemma 7.11, the depth-flag value.** For multiplicative `f` (over a ring as in
`dRank_univ_mult`), the depth-flag value of `f` is the value built from the prime depths:
`r_f = #{q : ν_q < ∞}` and `d(j)` the `j`-th smallest `ν_q`. -/
theorem dirFlagValue_mult (hsep : ∀ a : R, a ≠ 0 → ∃ d, ¬ (p : R) ^ (d + 1) ∣ a)
    {f : ArithmeticFunction R} (hf : f.IsMultiplicative) (k : ℕ) :
    dirFlagValue p f k =
      sInf {m | (∃ r : ℕ, Cardinal.mk {q : ℕ | q.Prime ∧ primeDepth p f q < ⊤} = r ∧ p ^ r ≤ m) ∨
        k ≤ padicValNat p m.factorial +
          ∑ j ∈ (Finset.range (m + 1)).filter (fun j : ℕ =>
              ((j : ℕ) : Cardinal) < Cardinal.mk {q : ℕ | q.Prime ∧ primeDepth p f q < ⊤}),
            (primeDepthStat p f (j + 1) - primeDepthStat p f j) * (m / p ^ j)} := by
  rw [dirFlagValue, dFlagValue, dRank_univ_mult p hsep hf, dFlag_univ_mult p hf]

/-- **Lemma 7.11 with Theorem 7.10 over `ℤ`.** For multiplicative `f` with
integer values, every prime `p` and every `k ≥ 1`, `L_f(p, k) + 1` is the depth-flag value
built from the prime depths `ν_q = min {v_p f(q ^ a) : a ≥ 1, p ∤ a}`: the least `m` with
`p ^ r ≤ m` (only when `r = #{q : ν_q < ∞}` is finite) or
`k ≤ v_p(m!) + ∑_{j < r, j ≤ m} (d(j+1) - d(j)) ⌊m / p ^ j⌋`, where `d(j)` is the `j`-th smallest
`ν_q` counted with multiplicity and `d(0) = 0`. -/
theorem levelCount_mult_int {f : ArithmeticFunction ℤ} (hf : f.IsMultiplicative) {k : ℕ}
    (hk : 1 ≤ k) :
    levelCount p (Ep p) f k + 1 =
      sInf {m | (∃ r : ℕ, Cardinal.mk {q : ℕ | q.Prime ∧ primeDepth p f q < ⊤} = r ∧ p ^ r ≤ m) ∨
        k ≤ padicValNat p m.factorial +
          ∑ j ∈ (Finset.range (m + 1)).filter (fun j : ℕ =>
              ((j : ℕ) : Cardinal) < Cardinal.mk {q : ℕ | q.Prime ∧ primeDepth p f q < ⊤}),
            (primeDepthStat p f (j + 1) - primeDepthStat p f j) * (m / p ^ j)} := by
  have hu : IsUnit f := by
    rw [ArithmeticFunction.isUnit_iff_isUnit_apply_one, hf.map_one]; exact isUnit_one
  rw [levelCount_eq_dirFlagValue_int p hu hk, dirFlagValue_mult p (int_sep p) hf]

/-- **Lemma 7.11 with Theorem 7.10 over `ℤ_[p]`.** As `levelCount_mult_int`,
for multiplicative `f` with values in `ℤ_[p]`. -/
theorem levelCount_mult_padic {f : ArithmeticFunction ℤ_[p]} (hf : f.IsMultiplicative) {k : ℕ}
    (hk : 1 ≤ k) :
    levelCount p (Ep p) f k + 1 =
      sInf {m | (∃ r : ℕ, Cardinal.mk {q : ℕ | q.Prime ∧ primeDepth p f q < ⊤} = r ∧ p ^ r ≤ m) ∨
        k ≤ padicValNat p m.factorial +
          ∑ j ∈ (Finset.range (m + 1)).filter (fun j : ℕ =>
              ((j : ℕ) : Cardinal) < Cardinal.mk {q : ℕ | q.Prime ∧ primeDepth p f q < ⊤}),
            (primeDepthStat p f (j + 1) - primeDepthStat p f j) * (m / p ^ j)} := by
  have hu : IsUnit f := by
    rw [ArithmeticFunction.isUnit_iff_isUnit_apply_one, hf.map_one]; exact isUnit_one
  rw [levelCount_eq_dirFlagValue_padic p hu hk, dirFlagValue_mult p (padic_sep p) hf]


/-! ## `primeDepthStat` is the `j`-th smallest prime depth -/

omit hp in
/-- In a nondecreasing list, at least `j + 1` entries are `≤ d` iff the entry at index `j` is. -/
theorem succ_le_length_filter_iff {L : List ℕ} (hL : L.Pairwise (· ≤ ·)) (d : ℕ) {j : ℕ}
    (hj : j < L.length) :
    j + 1 ≤ (L.filter (fun x => decide (x ≤ d))).length ↔ L[j] ≤ d := by
  induction L generalizing j with
  | nil => exact absurd hj (Nat.not_lt_zero _)
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    by_cases ha : a ≤ d
    · rw [List.filter_cons_of_pos (by simpa using ha), List.length_cons]
      cases j with
      | zero => simp [ha]
      | succ j =>
        rw [List.getElem_cons_succ, ← ih hL.2 (by simpa using hj)]
        omega
    · have hnil : L.filter (fun x => decide (x ≤ d)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro b hb hbd
        exact ha ((hL.1 b hb).trans (by simpa using hbd))
      rw [List.filter_cons_of_neg (by simpa using ha), hnil]
      simp only [List.length_nil, Nat.le_zero, Nat.add_one_ne_zero, false_iff, not_le]
      cases j with
      | zero => simpa using ha
      | succ j =>
        rw [List.getElem_cons_succ]
        exact lt_of_lt_of_le (not_le.1 ha) (hL.1 _ (List.getElem_mem _))

omit hp in
/-- **`d(j)` is the `j`-th smallest prime depth, counted with multiplicity.** When the primes
with `ν_q < ∞` form a finite set `T`, `primeDepthStat p f (j + 1)` is the entry at index `j` of the
nondecreasing list of the depths `ν_q`, `q ∈ T` (`j < #T`). -/
theorem primeDepthStat_eq_sort (f : ArithmeticFunction R) (T : Finset ℕ)
    (hT : ∀ q, q ∈ T ↔ q.Prime ∧ primeDepth p f q < ⊤) {j : ℕ} (hj : j < T.card) :
    primeDepthStat p f (j + 1) =
      (Multiset.sort (T.val.map fun q => (primeDepth p f q).toNat))[j]'(by
        rw [Multiset.length_sort, Multiset.card_map]; exact hj) := by
  set g : ℕ → ℕ := fun q => (primeDepth p f q).toNat with hg
  set L := Multiset.sort (T.val.map g) with hL
  have hlen : j < L.length := by rw [hL, Multiset.length_sort, Multiset.card_map]; exact hj
  have hset : ∀ d : ℕ, {q : ℕ | q.Prime ∧ primeDepth p f q ≤ d} =
      ↑(T.filter fun q => g q ≤ d) := by
    intro d
    ext q
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, hT, hg]
    constructor
    · rintro ⟨hq, hd⟩
      exact ⟨⟨hq, lt_of_le_of_lt hd (ENat.natCast_lt_top d)⟩, ENat.toNat_le_of_le_natCast hd⟩
    · rintro ⟨⟨hq, htop⟩, hd⟩
      refine ⟨hq, ?_⟩
      rw [← ENat.natCast_toNat htop.ne]
      exact_mod_cast hd
  have hcard : ∀ d : ℕ, (T.filter fun q => g q ≤ d).card =
      (L.filter fun x => decide (x ≤ d)).length := by
    intro d
    rw [Finset.card_def, Finset.filter_val, ← Multiset.card_map g,
      show Multiset.map g (Multiset.filter (fun q => g q ≤ d) T.val) =
        Multiset.filter (fun x => x ≤ d) (T.val.map g) by rw [Multiset.filter_map]; rfl,
      ← Multiset.sort_eq (T.val.map g) (fun a b => a ≤ b), ← hL, Multiset.filter_coe,
      Multiset.coe_card]
  have hiff : ∀ d : ℕ, (((j + 1 : ℕ)) : Cardinal) ≤
      Cardinal.mk {q : ℕ | q.Prime ∧ primeDepth p f q ≤ d} ↔ L[j] ≤ d := by
    intro d
    have e : (((j + 1 : ℕ)) : Cardinal) ≤
        Cardinal.mk (↑(T.filter fun q => g q ≤ d) : Set ℕ) ↔
          j + 1 ≤ (T.filter fun q => g q ≤ d).card := by simp
    rw [hset, e, hcard]
    exact succ_le_length_filter_iff (Multiset.pairwise_sort _ _) d hlen
  rw [primeDepthStat, ite_eq_right (Nat.succ_ne_zero j)]
  have : {d : ℕ | (((j + 1 : ℕ)) : Cardinal) ≤
      Cardinal.mk {q : ℕ | q.Prime ∧ primeDepth p f q ≤ d}} = Set.Ici L[j] := by
    ext d; exact hiff d
  rw [this, csInf_Ici]

/-! ## Non-vacuity: the Möbius function -/

/-- For `f = μ` every prime depth is `0` (Corollary 7.12(a)). -/
theorem primeDepth_moebius {q : ℕ} (hq : q.Prime) :
    primeDepth p (ArithmeticFunction.moebius : ArithmeticFunction ℤ) q = 0 := by
  refine nonpos_iff_eq_zero.1 ?_
  have := (primeDepth_le_iff p (ArithmeticFunction.moebius : ArithmeticFunction ℤ) q 0).2
    ⟨1, one_pos, fun h => hp.out.one_lt.ne' (Nat.dvd_one.1 h), ?_⟩
  · exact_mod_cast this
  · simp only [zero_add, pow_one]
    rw [ArithmeticFunction.moebius_apply_prime hq]
    intro h
    have := Int.eq_one_of_dvd_one (by positivity) (dvd_neg.1 h)
    exact hp.out.one_lt.ne' (by exact_mod_cast this)

/-- For `f = μ` every `d(j)` is `0`. -/
theorem primeDepthStat_moebius (j : ℕ) :
    primeDepthStat p (ArithmeticFunction.moebius : ArithmeticFunction ℤ) j = 0 := by
  rw [primeDepthStat]
  split_ifs with hj
  · rfl
  · refine Nat.eq_zero_of_le_zero (Nat.sInf_le ?_)
    rw [Set.mem_ofPred_eq]
    have : {q : ℕ | q.Prime ∧
        primeDepth p (ArithmeticFunction.moebius : ArithmeticFunction ℤ) q ≤ ((0 : ℕ) : ℕ∞)} =
        {q | q.Prime} := by
      ext q
      simp only [Set.mem_ofPred_eq, and_iff_left_iff_imp]
      intro hq
      rw [primeDepth_moebius p hq]; rfl
    have hinf : Infinite {q : ℕ | q.Prime} := Nat.infinite_setOfPred_prime.to_subtype
    rw [this, Cardinal.mk_eq_aleph0]
    exact Cardinal.natCast_lt_aleph0.le

end Mult

end Dir

end FrobLevel
