module

/-
Run r25, seat L1: R-080 stage (a), the upper bound L_f + 1 ≤ min(p ^ n, S(p ^ k)),
and the upper half of stage (d) (the value for f = ∏ (1 - x_i)⁻¹).

1. `exists_monic_tower`: for every `m` and every `u` there is a monic `P ∈ B[X]` of degree `m`
   with `p ^ v_p(m!) ∣ P(u)` (the δ-tower, one recursion: `m = p q + r`, `w = -δ(u)`,
   `P = X ^ r * (scaleRoots P' p).comp (X ^ p - σ u)` with `P'` the tower of degree `q` at `w`).
2. `monicAnn_kempner`: hence a monic annihilator of degree `S(p ^ k)` (ledger R-058 T1).
3. `exists_monic_eval_eq_zero_of_span`: if `t` spans `A` over `B` then `u` has an exact monic
   annihilator over `B` of degree `#t` (Cayley-Hamilton; ledger R-058 T2 with spanning in
   place of freeness).
4. `eq_sum_digit`: `R[[x_1..x_n]]` is spanned over `σ(R[[x]])` by the `p ^ n` monomials `x ^ e`,
   `0 ≤ e_i < p`.
5. `levelCount_le_min`: for a unit `f` of `R[[x_1..x_n]]` and `k ≥ 1`,
   `L_f(p, k) + 1 ≤ min (p ^ n) (S(p ^ k))`; `levelCount_zeta_le` is the case
   `f = ∏ (1 - x_i)⁻¹` (upper half of stage (d)), with `R = ℤ_[p]` in `levelCount_zeta_le_padic`.
-/
public import Mathlib
public import Frobenius.Levels.Found

@[expose] public section

namespace FrobLevel

/-! ## 1. The δ-tower and the Kempner bound (abstract) -/

section Tower

open Polynomial

variable {A : Type*} [CommRing A]

theorem comp_mem_BPoly {σ : A →+* A} {P Q : A[X]} (hP : P ∈ BPoly σ) (hQ : Q ∈ BPoly σ) :
    P.comp Q ∈ BPoly σ := by
  obtain ⟨P0, rfl⟩ := hP
  obtain ⟨Q0, rfl⟩ := hQ
  exact ⟨P0.comp Q0, by simp [Polynomial.map_comp]⟩

theorem scaleRoots_mem_BPoly {σ : A →+* A} {P : A[X]} (hP : P ∈ BPoly σ) (n : ℕ) :
    P.scaleRoots (n : A) ∈ BPoly σ := by
  rw [mem_BPoly_iff] at hP ⊢
  intro i
  rw [coeff_scaleRoots]
  exact mul_mem (hP i) (pow_mem (natCast_mem _ n) _)

variable [Nontrivial A]

/-- The δ-tower: for every `m` and every `u` there is a monic `P ∈ B[X]` of degree `m` with
`p ^ v_p(m!) ∣ P(u)`. Only the Frobenius lift property is used (no torsion hypothesis). -/
theorem exists_monic_tower {p : ℕ} [hp : Fact p.Prime] {σ : A →+* A} (h : IsFrobLift p σ)
    (m : ℕ) : ∀ u : A, ∃ P : A[X], P.Monic ∧ P.natDegree = m ∧ P ∈ BPoly σ ∧
      (p : A) ^ (padicValNat p m.factorial) ∣ P.eval u := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro u
  by_cases hq : m / p = 0
  · refine ⟨X ^ m, monic_X_pow m, natDegree_X_pow m, pow_mem (X_mem_BPoly σ) m, ?_⟩
    have : padicValNat p m.factorial = 0 := by
      rw [padicValNat_factorial_div p m, hq]; simp
    rw [this, pow_zero]; exact one_dvd _
  · have hp1 := hp.out.one_lt
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun h0 => hq (by simp [h0])
    have hlt : m / p < m := Nat.div_lt_self hm0 hp1
    obtain ⟨P', hmon', hdeg', hB', hP'⟩ := ih (m / p) hlt (- delta h u)
    set Q : A[X] := P'.scaleRoots (p : A) with hQ
    set Y : A[X] := X ^ p - C (σ u) with hY
    have hYm : Y.Monic := monic_X_pow_sub_C (σ u) hp.out.ne_zero
    have hYd : Y.natDegree = p := natDegree_X_pow_sub_C
    have hQm : Q.Monic := (monic_scaleRoots_iff _).2 hmon'
    have hQd : Q.natDegree = m / p := by rw [hQ, natDegree_scaleRoots, hdeg']
    have hQYm : (Q.comp Y).Monic := hQm.comp hYm (by rw [hYd]; exact hp.out.ne_zero)
    have hQYd : (Q.comp Y).natDegree = m / p * p := by
      rw [natDegree_comp_eq_of_mul_ne_zero (by rw [hQm.leadingCoeff, hYm.leadingCoeff]; simp),
        hQd, hYd]
    refine ⟨X ^ (m % p) * Q.comp Y, (monic_X_pow _).mul hQYm, ?_, ?_, ?_⟩
    · rw [(monic_X_pow _).natDegree_mul hQYm, natDegree_X_pow, hQYd]
      rw [Nat.mul_comm (m / p) p]; exact Nat.mod_add_div m p
    · exact mul_mem (pow_mem (X_mem_BPoly σ) _)
        (comp_mem_BPoly (scaleRoots_mem_BPoly hB' p)
          (sub_mem (pow_mem (X_mem_BPoly σ) _) (C_mem_BPoly σ u)))
    · have hYu : Y.eval u = (p : A) * (- delta h u) := by
        rw [hY, eval_sub, eval_pow, eval_X, eval_C, mul_neg, p_mul_delta]; ring
      have hev : (X ^ (m % p) * Q.comp Y).eval u
          = u ^ (m % p) * ((p : A) ^ (m / p) * P'.eval (- delta h u)) := by
        rw [eval_mul, eval_pow, eval_X, eval_comp, hYu, hQ]
        have := scaleRoots_eval₂_mul (p := P') (RingHom.id A) (- delta h u) (p : A)
        simp only [eval₂_id, RingHom.id_apply] at this
        rw [this, hdeg']
      rw [hev, padicValNat_factorial_div p m, pow_add]
      exact Dvd.dvd.mul_left (mul_dvd_mul_left _ hP') _

/-- The Kempner bound (ledger R-058 T1): every `u` has a monic annihilator over `B` modulo
`p ^ k` of degree `S(p ^ k)`. -/
theorem monicAnn_kempner {p : ℕ} [Fact p.Prime] {σ : A →+* A} (h : IsFrobLift p σ) (u : A)
    (k : ℕ) : MonicAnn p σ u k (kempner p k) := by
  obtain ⟨P, hm, hd, hB, hP⟩ := exists_monic_tower h (kempner p k) u
  exact ⟨P, hm, hd, hB, (pow_dvd_pow _ (kempner_spec p k)).trans hP⟩

/-! ## 2. The rank bound (Cayley-Hamilton over `B`) -/

/-- If the family `b i` (`i ∈ t`) spans `A` over `B = σ(A)`, then every `u` is killed by a
monic polynomial over `B` of degree `#t` (exactly, not only modulo a power of `p`). -/
theorem exists_monic_eval_eq_zero_of_span {σ : A →+* A} {ι : Type*} (t : Finset ι) (b : ι → A)
    (hs : ∀ a : A, ∃ c : ι → A, a = ∑ i ∈ t, σ (c i) * b i) (u : A) :
    ∃ P : A[X], P.Monic ∧ P.natDegree = t.card ∧ P ∈ BPoly σ ∧ P.eval u = 0 := by
  classical
  set B : Subring A := frobImage σ
  have hspan : Submodule.span B (↑(t.image b) : Set A) = ⊤ := by
    refine eq_top_iff.2 fun a _ => ?_
    obtain ⟨c, hc⟩ := hs a
    rw [hc]
    refine Submodule.sum_mem _ fun i hi => ?_
    have hmem : b i ∈ Submodule.span B (↑(t.image b) : Set A) :=
      Submodule.subset_span (by simpa using ⟨i, hi, rfl⟩)
    have := Submodule.smul_mem _ (⟨σ (c i), c i, rfl⟩ : B) hmem
    simpa [Subring.smul_def] using this
  have hfin : Module.Finite B A := ⟨⟨t.image b, hspan⟩⟩
  obtain ⟨q, hqm, hqd, hq⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero B (Algebra.lmul B A u)
  have hrank : (⊤ : Submodule B A).spanFinrank ≤ t.card := by
    rw [← hspan]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)).trans ?_
    rw [Set.ncard_coe_finset]
    exact Finset.card_image_le
  have hev : (q.map B.subtype).eval u = 0 := by
    have h2 := Polynomial.aeval_algHom_apply (Algebra.lmul B A) u q
    rw [hq] at h2
    have h3 : Polynomial.aeval u q = 0 := by
      have := congrArg (fun φ : Module.End B A => φ 1) h2
      simpa using this.symm
    rw [aeval_def, Algebra.algebraMap_ofSubring] at h3
    rw [eval_map]; exact h3
  have hPm : (q.map B.subtype).Monic := hqm.map _
  have hPB : q.map B.subtype ∈ BPoly σ := by
    rw [mem_BPoly_iff]; intro i; rw [coeff_map]; exact (q.coeff i).2
  -- raise the degree from `spanFinrank` to `#t` by multiplying with `X`
  refine ⟨q.map B.subtype * X ^ (t.card - q.natDegree), hPm.mul (monic_X_pow _), ?_,
    mul_mem hPB (pow_mem (X_mem_BPoly σ) _), by rw [eval_mul, hev, zero_mul]⟩
  rw [hPm.natDegree_mul (monic_X_pow _), hqm.natDegree_map, natDegree_X_pow]
  omega

theorem monicAnn_of_span {p : ℕ} {σ : A →+* A} {ι : Type*} (t : Finset ι) (b : ι → A)
    (hs : ∀ a : A, ∃ c : ι → A, a = ∑ i ∈ t, σ (c i) * b i) (u : A) (k : ℕ) :
    MonicAnn p σ u k t.card := by
  obtain ⟨P, hm, hd, hB, hP⟩ := exists_monic_eval_eq_zero_of_span t b hs u
  exact ⟨P, hm, hd, hB, by rw [hP]; exact dvd_zero _⟩

/-- Abstract upper bound: if `f u ≡ 1 (mod p ^ k)`, `k ≥ 1` and `A` is spanned over `B` by `d`
elements, then `L_f(p, k) + 1 ≤ min d S(p ^ k)`. -/
theorem levelCount_le_min_of_span {p : ℕ} [Fact p.Prime] {σ : A →+* A} (h : IsFrobLift p σ)
    {ι : Type*} (t : Finset ι) (b : ι → A)
    (hs : ∀ a : A, ∃ c : ι → A, a = ∑ i ∈ t, σ (c i) * b i)
    {f u : A} {k : ℕ} (hk : 1 ≤ k) (hfu : (p : A) ^ k ∣ f * u - 1) :
    levelCount p σ f k + 1 ≤ min t.card (kempner p k) := by
  have hK := kempner_pos p hk
  have hann : MonicAnn p σ u k (min t.card (kempner p k)) := by
    rcases le_total t.card (kempner p k) with hle | hle
    · rw [min_eq_left hle]; exact monicAnn_of_span t b hs u k
    · rw [min_eq_right hle]; exact monicAnn_kempner h u k
  have hpos : 1 ≤ min t.card (kempner p k) := by
    rcases le_total t.card (kempner p k) with hle | hle
    · rw [min_eq_left hle]
      by_contra h0
      have h0' : t.card = 0 := by omega
      obtain ⟨P, hm, hd, -, hP⟩ := hann
      rw [min_eq_left hle, h0'] at hd
      -- a monic annihilator of degree 0 exactly: P = 1, so 1 = 0 in A
      obtain ⟨P', hm', hd', -, hP'⟩ := exists_monic_eval_eq_zero_of_span t b hs u
      rw [h0'] at hd'
      have : P' = 1 := by
        rw [eq_C_of_natDegree_eq_zero hd']
        have := hm'.coeff_natDegree; rw [hd'] at this; rw [this, map_one]
      rw [this, eval_one] at hP'
      exact one_ne_zero hP'
    · rw [min_eq_right hle]; exact hK
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' hpos
  rw [hd] at hann ⊢
  exact Nat.succ_le_succ (levelCount_le (hann.hasLevel hfu))

end Tower

/-! ## 3. The `p ^ n` monomials span `R[[x_1..x_n]]` over its Frobenius image -/

section Span

open MvPowerSeries

variable (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R] (n : ℕ)

/-- The exponents `e` with `0 ≤ e_i < p` for every `i`. -/
noncomputable def digitExps : Finset (Fin n →₀ ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.range p).map
    (Finsupp.equivFunOnFinite (α := Fin n) (M := ℕ)).symm.toEmbedding

omit hp in
theorem card_digitExps : (digitExps p n).card = p ^ n := by
  simp [digitExps]

omit hp in
theorem mem_digitExps {e : Fin n →₀ ℕ} : e ∈ digitExps p n ↔ ∀ i, e i < p := by
  simp only [digitExps, Finset.mem_map, Fintype.mem_piFinset, Finset.mem_range,
    Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨g, hg, rfl⟩ i; simpa using hg i
  · intro he; exact ⟨e, by simpa using he, by simp⟩

variable {n}

/-- The class part `a_e`: `coeff d a_e = coeff (p d + e) a`. -/
noncomputable def classPart (a : MvPowerSeries (Fin n) R) (e : Fin n →₀ ℕ) : MvPowerSeries (Fin n) R :=
  fun d => coeff (p • d + e) a

omit hp in
theorem coeff_classPart (a : MvPowerSeries (Fin n) R) (e d : Fin n →₀ ℕ) :
    coeff d (classPart p a e) = coeff (p • d + e) a := rfl

/-- `a = ∑_{0 ≤ e_i < p} σ(a_e) x ^ e`. -/
theorem eq_sum_digit (a : MvPowerSeries (Fin n) R) :
    a = ∑ e ∈ digitExps p n, frob p (classPart p a e) * monomial e 1 := by
  classical
  ext m
  rw [map_sum]
  set e0 : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => m i % p with he0
  set d0 : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => m i / p with hd0
  have hpos := hp.out.pos
  have he0m : e0 ≤ m := fun i => by simp [he0, Nat.mod_le]
  have hsplit : p • d0 + e0 = m := by
    ext i; simp [he0, hd0, Nat.div_add_mod]
  have hsub : m - e0 = p • d0 := by
    ext i
    have := Nat.div_add_mod (m i) p
    have h1 : e0 i = m i % p := by simp [he0]
    have h2 : d0 i = m i / p := by simp [hd0]
    rw [Finsupp.tsub_apply, Finsupp.smul_apply, smul_eq_mul, h1, h2]
    omega
  rw [Finset.sum_eq_single e0]
  · rw [mul_comm, coeff_monomial_mul, if_pos he0m, one_mul, hsub, coeff_frob_smul,
      coeff_classPart, hsplit]
  · intro e he hne
    rw [mul_comm, coeff_monomial_mul]
    split_ifs with hle
    · rw [one_mul]
      have hlt := (mem_digitExps p n).1 he
      have : ∃ i, e i ≠ m i % p := by
        by_contra hall
        push Not at hall
        exact hne (Finsupp.ext fun i => by simp [he0, hall i])
      obtain ⟨i, hi⟩ := this
      apply coeff_frob_of_not_dvd p _ (i := i)
      intro hdvd
      apply hi
      have hle' : e i ≤ m i := hle i
      have h1 : (m - e) i = m i - e i := by simp
      rw [h1] at hdvd
      have := (Nat.modEq_iff_dvd' hle').2 hdvd
      rw [Nat.ModEq, Nat.mod_eq_of_lt (hlt i)] at this
      exact this
    · rfl
  · intro h0
    exact absurd ((mem_digitExps p n).2 fun i => by simp [he0, Nat.mod_lt _ hpos]) h0

/-- Abstract form of the spanning statement, as used by `levelCount_le_min_of_span`. -/
theorem span_digit (a : MvPowerSeries (Fin n) R) :
    ∃ c : (Fin n →₀ ℕ) → MvPowerSeries (Fin n) R,
      a = ∑ e ∈ digitExps p n, frob p (c e) * monomial e 1 :=
  ⟨classPart p a, eq_sum_digit p a⟩

end Span

/-! ## 4. Stage (a) and the upper half of stage (d) -/

section Main

open MvPowerSeries

variable (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R] [Nontrivial R] {n : ℕ}

/-- R-080 stage (a): for `R` with `a ^ p ≡ a (mod p)` (e.g. `ℤ`, `ℤ_[p]`), `f` a unit of
`R[[x_1..x_n]]`, `σ(x_i) = x_i ^ p` and `k ≥ 1`: `L_f(p, k) + 1 ≤ min (p ^ n) (S(p ^ k))`. -/
theorem levelCount_le_min (hR : ∀ a : R, (p : R) ∣ a ^ p - a)
    {f : MvPowerSeries (Fin n) R} (hf : IsUnit f) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frob p) f k + 1 ≤ min (p ^ n) (kempner p k) := by
  obtain ⟨v, rfl⟩ := hf
  have h := levelCount_le_min_of_span (frob_isFrobLift p hR) (digitExps p n)
    (fun e => (monomial e 1 : MvPowerSeries (Fin n) R)) (span_digit p) hk
    (f := (v : MvPowerSeries (Fin n) R)) (u := ((v⁻¹ : (MvPowerSeries (Fin n) R)ˣ) : _))
    (by rw [Units.mul_inv, sub_self]; exact dvd_zero _)
  rwa [card_digitExps] at h

/-- `∏_{i < n} (1 - x_i)`; its inverse is `ζ_n = ∏ (1 - x_i)⁻¹` of ledger R-060 and R-080. -/
noncomputable def zetaDen (n : ℕ) : MvPowerSeries (Fin n) R := ∏ i, (1 - X i)

omit [Nontrivial R] in
theorem constantCoeff_zetaDen (n : ℕ) : constantCoeff (zetaDen (R := R) n) = 1 := by
  simp [zetaDen, map_prod]

/-- `ζ_n = ∏_{i < n} (1 - x_i)⁻¹`. -/
noncomputable def zeta (n : ℕ) : MvPowerSeries (Fin n) R := invOfUnit (zetaDen n) 1

omit [Nontrivial R] in
theorem zetaDen_mul_zeta (n : ℕ) : zetaDen (R := R) n * zeta n = 1 :=
  mul_invOfUnit _ _ (by rw [constantCoeff_zetaDen, Units.val_one])

omit [Nontrivial R] in
theorem isUnit_zeta (n : ℕ) : IsUnit (zeta (R := R) n) :=
  ⟨⟨zeta n, zetaDen n, by rw [mul_comm]; exact zetaDen_mul_zeta n, zetaDen_mul_zeta n⟩, rfl⟩

/-- Upper half of R-080 stage (d): `L(ζ_n; p, k) ≤ min (p ^ n - 1) (S(p ^ k) - 1)`, written
`L + 1 ≤ min (p ^ n) (S(p ^ k))`. -/
theorem levelCount_zeta_le (hR : ∀ a : R, (p : R) ∣ a ^ p - a) (n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frob p) (zeta (R := R) n) k + 1 ≤ min (p ^ n) (kempner p k) :=
  levelCount_le_min p hR (isUnit_zeta n) hk

/-- The ledger's setting `A = ℤ_[p][[x_1..x_n]]`. -/
theorem levelCount_zeta_le_padic (n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frob p) (zeta (R := ℤ_[p]) n) k + 1 ≤ min (p ^ n) (kempner p k) :=
  levelCount_zeta_le p (padicInt_pow_sub p) n hk

theorem levelCount_le_min_padic {f : MvPowerSeries (Fin n) ℤ_[p]} (hf : IsUnit f) {k : ℕ}
    (hk : 1 ≤ k) : levelCount p (frob p) f k + 1 ≤ min (p ^ n) (kempner p k) :=
  levelCount_le_min p (padicInt_pow_sub p) hf hk

end Main

end FrobLevel
