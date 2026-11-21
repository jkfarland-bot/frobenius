module

/-
Run r25, seat L7: R-084 upper half for every unit of the Dirichlet ring, in the "max over finite
sets of primes" form.

* `Dir.levelCount_le_of_res`: if every restriction `res_q f` whose prime family `q` contains a
  fixed finite set `T` has `L_(res_q f) + 1 ≤ M`, then `L_f + 1 ≤ M` (compactness, Compact.lean).
* `Dir.levelCount_eq_max_res_int`, `_padic`: for every unit `f` and `k ≥ 1`, `L_f + 1` is the
  largest of the R-083 values `flagValue p (res_q f) k` over finite families of primes, and the
  largest is attained.
* `Dir.r084_upper_int`, `_padic`: L6's open statement `open_r084_upper` (and its `ℤ` version),
  proved.

Lean v4.33.1 with Mathlib; no sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Flag
public import Frobenius.Levels.DirBase
public import Frobenius.Levels.DirTransfer
public import Frobenius.Levels.ThmF
public import Frobenius.Levels.Padic
public import Frobenius.Levels.Assemble
public import Frobenius.Levels.Compact

@[expose] public section

namespace FrobLevel

namespace Dir

open MvPowerSeries

section Enum

/-- An enumeration of a finite set of naturals, as an injective `Fin`-family. -/
noncomputable def enum (s : Finset ℕ) : Fin s.card → ℕ := fun i => s.orderEmbOfFin rfl i

theorem enum_mem (s : Finset ℕ) (i : Fin s.card) : enum s i ∈ s := s.orderEmbOfFin_mem rfl i

theorem enum_injective (s : Finset ℕ) : Function.Injective (enum s) :=
  (s.orderEmbOfFin rfl).injective

theorem enum_surj (s : Finset ℕ) {t : ℕ} (ht : t ∈ s) : ∃ i, enum s i = t := by
  have : t ∈ Set.range (s.orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact ht
  obtain ⟨i, hi⟩ := this
  exact ⟨i, hi⟩

/-- A nonzero `m` all of whose prime factors are among the `q_i` is `q`-smooth. -/
theorem smoothNum_expOf_of_primes {n : ℕ} {q : Fin n → ℕ} (hq : ∀ i, (q i).Prime)
    (hinj : Function.Injective q) {m : ℕ} (hm : m ≠ 0)
    (hpr : ∀ r, r.Prime → r ∣ m → ∃ i, q i = r) : smoothNum q (expOf q m) = m := by
  apply Nat.eq_of_factorization_eq (smoothNum_ne_zero hq _) hm
  intro r
  by_cases hr : ∃ j, q j = r
  · obtain ⟨j, rfl⟩ := hr
    rw [factorization_smoothNum_q hq hinj, expOf_apply]
  · push Not at hr
    rw [factorization_smoothNum_of_notMem hq _ hr]
    symm
    rw [Nat.factorization_eq_zero_iff]
    by_contra hc
    push Not at hc
    obtain ⟨i, hi⟩ := hpr r hc.1 hc.2.1
    exact hr i hi

/-- The primes up to `N` together with a finite set `T`. -/
noncomputable def coverSet (N : ℕ) (T : Finset ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter Nat.Prime ∪ T

theorem coverSet_prime {N : ℕ} {T : Finset ℕ} (hT : ∀ t ∈ T, t.Prime) :
    ∀ i, (enum (coverSet N T) i).Prime := by
  intro i
  have := enum_mem (coverSet N T) i
  simp only [coverSet, Finset.mem_union, Finset.mem_filter] at this
  rcases this with h | h
  · exact h.2
  · exact hT _ h

theorem coverSet_smooth (N : ℕ) (T : Finset ℕ) (hT : ∀ t ∈ T, t.Prime) :
    ∀ m, m ≠ 0 → m ≤ N → ∃ e, smoothNum (enum (coverSet N T)) e = m := by
  intro m hm hmN
  refine ⟨_, smoothNum_expOf_of_primes (coverSet_prime hT) (enum_injective _) hm ?_⟩
  intro r hr hrm
  apply enum_surj
  simp only [coverSet, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
  exact Or.inl ⟨by have := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hrm; omega, hr⟩

theorem coverSet_contains (N : ℕ) (T : Finset ℕ) {t : ℕ} (ht : t ∈ T) :
    ∃ i, enum (coverSet N T) i = t :=
  enum_surj _ (by simp only [coverSet, Finset.mem_union]; exact Or.inr ht)

end Enum

section Upper

/-- **Upper half from the restrictions (compactness).** Let `T` be a finite set of primes. If every
restriction `res_q f` to a finite family of primes `q` containing `T` has `L + 1 ≤ M`, then
`L_f + 1 ≤ M` in the Dirichlet ring. -/
theorem levelCount_le_of_res {R : Type*} [CommRing R] [Nontrivial R] (p : ℕ) [hp : Fact p.Prime]
    (hR : ∀ a : R, (p : R) ∣ a ^ p - a) {k : ℕ} (hk : 1 ≤ k)
    {M' : Type*} [CommRing M'] [Finite M'] (φ : R →+* M') (hsurj : Function.Surjective φ)
    (hker : ∀ a, φ a = 0 → (p : R) ^ k ∣ a) (hφp : φ ((p : R) ^ k) = 0)
    {f : ArithmeticFunction R} (hf : IsUnit f)
    (T : Finset ℕ) (hT : ∀ t ∈ T, t.Prime) {M : ℕ}
    (hval : ∀ (n : ℕ) (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q),
      (∀ t ∈ T, ∃ i, q i = t) → levelCount p (frob p) (res hq hinj f) k + 1 ≤ M) :
    levelCount p (Ep p) f k + 1 ≤ M := by
  have hM : 1 ≤ M := by
    have := hval _ (enum (coverSet 0 T)) (coverSet_prime hT) (enum_injective _)
      (fun t ht => coverSet_contains 0 T ht)
    omega
  have hL : HasLevel p (Ep p) f k (M - 1) := by
    apply hasLevel_of_res p φ hsurj hker hφp f
    intro N
    refine ⟨_, enum (coverSet N T), coverSet_prime hT, enum_injective _,
      coverSet_smooth N T hT, ?_⟩
    have hu : IsUnit (res (coverSet_prime hT) (enum_injective (coverSet N T)) f) :=
      hf.map (res _ _)
    have h1 := hasLevel_levelCount (hasLevel_kempner_mv p hR hu hk)
    have h2 := hval _ (enum (coverSet N T)) (coverSet_prime hT) (enum_injective _)
      (fun t ht => coverSet_contains N T ht)
    exact h1.mono (by omega)
  have := levelCount_le hL
  omega

/-- `ℤ → ZMod (p ^ k)` satisfies the hypotheses of the compactness step. -/
theorem int_hyps (p k : ℕ) :
    Function.Surjective (Int.castRingHom (ZMod (p ^ k))) ∧
      (∀ a : ℤ, Int.castRingHom (ZMod (p ^ k)) a = 0 → (p : ℤ) ^ k ∣ a) ∧
      Int.castRingHom (ZMod (p ^ k)) ((p : ℤ) ^ k) = 0 := by
  refine ⟨ZMod.intCast_surjective, fun a ha => ?_, ?_⟩
  swap
  · rw [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self]
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd a (p ^ k)).1 ha
  exact_mod_cast this

/-- `ℤ_[p] → ZMod (p ^ k)` satisfies the hypotheses of the compactness step. -/
theorem padic_hyps (p : ℕ) [Fact p.Prime] (k : ℕ) :
    Function.Surjective (PadicInt.toZModPow (p := p) k) ∧
      (∀ a : ℤ_[p], PadicInt.toZModPow k a = 0 → (p : ℤ_[p]) ^ k ∣ a) ∧
      PadicInt.toZModPow (p := p) k ((p : ℤ_[p]) ^ k) = 0 := by
  refine ⟨ZMod.ringHom_surjective _, fun a ha => ?_, ?_⟩
  swap
  · rw [map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self]
  have : a ∈ RingHom.ker (PadicInt.toZModPow (p := p) k) := ha
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at this
  exact this

end Upper

section Max

variable (p : ℕ) [hp : Fact p.Prime]

/-- R-083 for a restriction, over `ℤ`. -/
theorem levelCount_res_int {f : ArithmeticFunction ℤ} (hf : IsUnit f) {n : ℕ} {q : Fin n → ℕ}
    (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frob p) (res hq hinj f) k + 1 = flagValue p (res hq hinj f) k := by
  obtain ⟨v, hv⟩ := hf.map (res hq hinj)
  exact levelCount_eq_flagValue_int p (u := ↑v⁻¹) (by rw [← hv]; exact v.mul_inv) hk

/-- R-083 for a restriction, over `ℤ_[p]`. -/
theorem levelCount_res_padic {f : ArithmeticFunction ℤ_[p]} (hf : IsUnit f) {n : ℕ}
    {q : Fin n → ℕ} (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frob p) (res hq hinj f) k + 1 = flagValue p (res hq hinj f) k := by
  obtain ⟨v, hv⟩ := hf.map (res hq hinj)
  exact levelCount_eq_flagValue_padic p (u := ↑v⁻¹) (by rw [← hv]; exact v.mul_inv) hk

/-- **Upper half of R-084 against the restrictions, over `ℤ`**: if `flagValue p (res_q f) k ≤ M`
for every finite family of primes `q` containing `T`, then `L_f + 1 ≤ M`. -/
theorem levelCount_le_of_flagValue_res_int {f : ArithmeticFunction ℤ} (hf : IsUnit f) {k : ℕ}
    (hk : 1 ≤ k) (T : Finset ℕ) (hT : ∀ t ∈ T, t.Prime) {M : ℕ}
    (hval : ∀ (n : ℕ) (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q),
      (∀ t ∈ T, ∃ i, q i = t) → flagValue p (res hq hinj f) k ≤ M) :
    levelCount p (Ep p) f k + 1 ≤ M :=
  levelCount_le_of_res p (int_pow_sub p) hk _ (int_hyps p k).1 (int_hyps p k).2.1
    (int_hyps p k).2.2 hf T hT
    fun n q hq hinj hTq => (levelCount_res_int p hf hq hinj hk).trans_le (hval n q hq hinj hTq)

/-- The same over `ℤ_[p]`. -/
theorem levelCount_le_of_flagValue_res_padic {f : ArithmeticFunction ℤ_[p]} (hf : IsUnit f)
    {k : ℕ} (hk : 1 ≤ k) (T : Finset ℕ) (hT : ∀ t ∈ T, t.Prime) {M : ℕ}
    (hval : ∀ (n : ℕ) (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q),
      (∀ t ∈ T, ∃ i, q i = t) → flagValue p (res hq hinj f) k ≤ M) :
    levelCount p (Ep p) f k + 1 ≤ M :=
  levelCount_le_of_res p (padicInt_pow_sub p) hk _ (padic_hyps p k).1 (padic_hyps p k).2.1
    (padic_hyps p k).2.2 hf T hT
    fun n q hq hinj hTq => (levelCount_res_padic p hf hq hinj hk).trans_le (hval n q hq hinj hTq)

/-- **R-084 for every unit of the Dirichlet ring over `ℤ`, max form.** `L_f + 1` is the largest
R-083 value of a restriction to finitely many primes, and the largest is attained. -/
theorem levelCount_eq_max_res_int {f : ArithmeticFunction ℤ} (hf : IsUnit f) {k : ℕ}
    (hk : 1 ≤ k) :
    (∀ (n : ℕ) (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q),
      flagValue p (res hq hinj f) k ≤ levelCount p (Ep p) f k + 1) ∧
    ∃ (n : ℕ) (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q),
      levelCount p (Ep p) f k + 1 = flagValue p (res hq hinj f) k := by
  refine ⟨fun n q hq hinj => flagValue_res_le_int p hq hinj hf hk, ?_⟩
  let V : Set ℕ := {v | ∃ (n : ℕ) (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime)
    (hinj : Function.Injective q), v = flagValue p (res hq hinj f) k}
  have hbdd : BddAbove V := ⟨levelCount p (Ep p) f k + 1, by
    rintro v ⟨n, q, hq, hinj, rfl⟩; exact flagValue_res_le_int p hq hinj hf hk⟩
  have hne : V.Nonempty := ⟨_, 0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, rfl⟩
  obtain ⟨n, q, hq, hinj, hM⟩ := Nat.sSup_mem hne hbdd
  refine ⟨n, q, hq, hinj, le_antisymm ?_ (hM ▸ csSup_le hne fun v ⟨n', q', hq', hinj', hv⟩ =>
    hv ▸ flagValue_res_le_int p hq' hinj' hf hk)⟩
  rw [← hM]
  exact levelCount_le_of_flagValue_res_int p hf hk ∅ (by simp)
    fun n' q' hq' hinj' _ => le_csSup hbdd ⟨n', q', hq', hinj', rfl⟩

/-- **R-084 for every unit of the Dirichlet ring over `ℤ_[p]`, max form.** -/
theorem levelCount_eq_max_res_padic {f : ArithmeticFunction ℤ_[p]} (hf : IsUnit f) {k : ℕ}
    (hk : 1 ≤ k) :
    (∀ (n : ℕ) (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q),
      flagValue p (res hq hinj f) k ≤ levelCount p (Ep p) f k + 1) ∧
    ∃ (n : ℕ) (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q),
      levelCount p (Ep p) f k + 1 = flagValue p (res hq hinj f) k := by
  refine ⟨fun n q hq hinj => flagValue_res_le_padic p hq hinj hf hk, ?_⟩
  let V : Set ℕ := {v | ∃ (n : ℕ) (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime)
    (hinj : Function.Injective q), v = flagValue p (res hq hinj f) k}
  have hbdd : BddAbove V := ⟨levelCount p (Ep p) f k + 1, by
    rintro v ⟨n, q, hq, hinj, rfl⟩; exact flagValue_res_le_padic p hq hinj hf hk⟩
  have hne : V.Nonempty := ⟨_, 0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, rfl⟩
  obtain ⟨n, q, hq, hinj, hM⟩ := Nat.sSup_mem hne hbdd
  refine ⟨n, q, hq, hinj, le_antisymm ?_ (hM ▸ csSup_le hne fun v ⟨n', q', hq', hinj', hv⟩ =>
    hv ▸ flagValue_res_le_padic p hq' hinj' hf hk)⟩
  rw [← hM]
  exact levelCount_le_of_flagValue_res_padic p hf hk ∅ (by simp)
    fun n' q' hq' hinj' _ => le_csSup hbdd ⟨n', q', hq', hinj', rfl⟩

/-- **L6's `open_r084_upper`, proved** (statement copied verbatim from L6/Open.lean). -/
theorem r084_upper_padic {f : ArithmeticFunction ℤ_[p]} (hf : IsUnit f) {k : ℕ} (hk : 1 ≤ k) :
    ∃ (n : ℕ) (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q),
      levelCount p (Dir.Ep p) f k + 1 ≤ flagValue p (Dir.res hq hinj f) k := by
  obtain ⟨n, q, hq, hinj, h⟩ := (levelCount_eq_max_res_padic p hf hk).2
  exact ⟨n, q, hq, hinj, h.le⟩

/-- The same over `ℤ`. -/
theorem r084_upper_int {f : ArithmeticFunction ℤ} (hf : IsUnit f) {k : ℕ} (hk : 1 ≤ k) :
    ∃ (n : ℕ) (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q),
      levelCount p (Dir.Ep p) f k + 1 ≤ flagValue p (Dir.res hq hinj f) k := by
  obtain ⟨n, q, hq, hinj, h⟩ := (levelCount_eq_max_res_int p hf hk).2
  exact ⟨n, q, hq, hinj, h.le⟩

end Max

end Dir

end FrobLevel
