module

/-
Run r25, seat L4: ledger R-086 Theorem R (two-sided bound for every lift) and Theorem M
(monomial images), the parts that are formalized.

* `exists_monic_of_subring_span` / `levelCount_le_of_subring` (Theorem R, upper bound, abstract):
  if `u = 1/f` lies in a subring `C ⊇ B` spanned over `B` by `N` elements, then
  `L_f + 1 ≤ min(N, S(p ^ k))`. With `C = B[u]`, `N = p ^ r_f` this is the upper half of
  Theorem R once `B[u]` is known to be spanned by `p ^ r_f` elements (the normality step,
  not formalized).
* `levelCount_le_kempner_series`: `L_f + 1 ≤ S(p ^ k)` for every lift and every unit.
* `levelCount_ge_p_of_pderiv` (Theorem R, lower bound, case `ρ_σ(f) ≥ 1`): if `d f̄ ≠ 0`, i.e. some
  partial derivative of `f mod p` is nonzero, then `L_f + 1 ≥ p = min(p ^ 1, S(p ^ k))`.
* `levelCount_eq_of_fullRank_conj` (Theorem R equality `ρ = r = n` and Theorem M, for every lift
  whose image is `θ(B_std)` for a ring automorphism `θ`): `L_g + 1 = min(p ^ n, S(p ^ k))` when
  `θ⁻¹(1/g)` has full rank (L1's `levelCount_eq_of_fullRank_padic`, transported by Prop T).
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Basis
public import Frobenius.Levels.Lower
public import Frobenius.Levels.LowerPadic
public import Frobenius.Levels.PropT
public import Frobenius.Levels.G1
public import Frobenius.Levels.G1Series

@[expose] public section

-- Port (Mathlib v4.35.0-rc2): restore the v4.33 instance path for `AddCommGroup (ZMod p)`.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace FrobLevel

section CayleyHamilton

open Polynomial

variable {R : Type*} [CommRing R] [Nontrivial R]

/-- Cayley-Hamilton over a subring: if `R` is spanned over the subring `S` by `#t` elements,
every `u` has a monic annihilator of degree `#t` with coefficients in `S`. -/
theorem exists_monic_of_span_subring (S : Subring R) {ι : Type*} (t : Finset ι) (b : ι → R)
    (hs : ∀ a : R, ∃ c : ι → R, (∀ i, c i ∈ S) ∧ a = ∑ i ∈ t, c i * b i) (u : R) :
    ∃ P : R[X], P.Monic ∧ P.natDegree = t.card ∧ (∀ i, P.coeff i ∈ S) ∧ P.eval u = 0 := by
  classical
  have hspan : Submodule.span S (↑(t.image b) : Set R) = ⊤ := by
    refine eq_top_iff.2 fun a _ => ?_
    obtain ⟨c, hcS, hc⟩ := hs a
    rw [hc]
    refine Submodule.sum_mem _ fun i hi => ?_
    have hmem : b i ∈ Submodule.span S (↑(t.image b) : Set R) :=
      Submodule.subset_span (by simpa using ⟨i, hi, rfl⟩)
    have := Submodule.smul_mem _ (⟨c i, hcS i⟩ : S) hmem
    simpa [Subring.smul_def] using this
  have hfin : Module.Finite S R := ⟨⟨t.image b, hspan⟩⟩
  obtain ⟨q, hqm, hqd, hq⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_aeval_eq_zero S (Algebra.lmul S R u)
  have hrank : (⊤ : Submodule S R).spanFinrank ≤ t.card := by
    rw [← hspan]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Finset.finite_toSet _)).trans ?_
    rw [Set.ncard_coe_finset]
    exact Finset.card_image_le
  have hev : (q.map S.subtype).eval u = 0 := by
    have h2 := Polynomial.aeval_algHom_apply (Algebra.lmul S R) u q
    rw [hq] at h2
    have h3 : Polynomial.aeval u q = 0 := by
      have := congrArg (fun φ : Module.End S R => φ 1) h2
      simpa using this.symm
    rw [aeval_def, Algebra.algebraMap_ofSubring] at h3
    rw [eval_map]; exact h3
  have hPm : (q.map S.subtype).Monic := hqm.map _
  refine ⟨q.map S.subtype * X ^ (t.card - q.natDegree), hPm.mul (monic_X_pow _), ?_, ?_,
    by rw [eval_mul, hev, zero_mul]⟩
  · rw [hPm.natDegree_mul (monic_X_pow _), hqm.natDegree_map, natDegree_X_pow]
    omega
  · intro i
    rw [coeff_mul_X_pow', coeff_map]
    split_ifs
    · exact (q.coeff _).2
    · exact zero_mem _

end CayleyHamilton

section Abstract

open Polynomial

variable {A : Type*} [CommRing A] [Nontrivial A]

/-- **Theorem R, upper bound, abstract.** If `u` (an inverse of `f` modulo `p ^ k`) lies in a
subring `C ⊇ B` that is spanned over `B` by `#t` elements of `C`, then
`L_f(p, k) + 1 ≤ min(#t, S(p ^ k))` (`p ^ k` not a unit of `A`). -/
theorem levelCount_le_of_subring {p : ℕ} [Fact p.Prime] {σ : A →+* A} (h : IsFrobLift p σ)
    (C : Subring A) (hBC : frobImage σ ≤ C) {ι : Type*} (t : Finset ι) (b : ι → A)
    (hb : ∀ i, b i ∈ C)
    (hspan : ∀ c ∈ C, ∃ q : ι → A, (∀ i, q i ∈ frobImage σ) ∧ c = ∑ i ∈ t, q i * b i)
    {f u : A} (hu : u ∈ C) {k : ℕ} (hfu : (p : A) ^ k ∣ f * u - 1)
    (hpk : ¬ IsUnit ((p : A) ^ k)) :
    levelCount p σ f k + 1 ≤ min t.card (kempner p k) := by
  classical
  -- work in the ring `C`, over the subring `B' = B ∩ C = B`
  set S : Subring C := (frobImage σ).comap C.subtype
  have hs : ∀ a : C, ∃ c : ι → C, (∀ i, c i ∈ S) ∧ a = ∑ i ∈ t, c i * ⟨b i, hb i⟩ := by
    intro a
    obtain ⟨q, hq, hqa⟩ := hspan a a.2
    refine ⟨fun i => ⟨q i, hBC (hq i)⟩, fun i => hq i, ?_⟩
    apply Subtype.ext
    simp [hqa]
  obtain ⟨P, hPm, hPd, hPS, hPu⟩ := exists_monic_of_span_subring S t (fun i => ⟨b i, hb i⟩) hs
    ⟨u, hu⟩
  -- push the annihilator to `A[X]`
  set P' : A[X] := P.map C.subtype
  have hP'm : P'.Monic := hPm.map _
  have hP'd : P'.natDegree = t.card := by rw [hPm.natDegree_map, hPd]
  have hP'B : P' ∈ BPoly σ := by
    rw [mem_BPoly_iff]; intro i; rw [coeff_map]; exact hPS i
  have hP'u : P'.eval u = 0 := by
    have := congrArg C.subtype hPu
    rw [map_zero, ← eval_map_apply (f := C.subtype)] at this
    exact this
  have hrank : MonicAnn p σ u k t.card := ⟨P', hP'm, hP'd, hP'B, by rw [hP'u]; exact dvd_zero _⟩
  have hkem : MonicAnn p σ u k (kempner p k) := monicAnn_kempner h u k
  rw [levelCount_add_one hfu hpk hkem]
  exact le_min (annDegree_le hrank) (annDegree_le hkem)

end Abstract

open MvPowerSeries

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

/-- **Theorem R, upper bound `S(p ^ k)`**: every Frobenius lift of `ℤ_[p][[x_1..x_n]]`, every unit
`f`, every `k ≥ 1`: `L_f(p, k) + 1 ≤ S(p ^ k)`. -/
theorem levelCount_le_kempner_series
    {σ : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p]} (h : IsFrobLift p σ)
    {f : MvPowerSeries (Fin n) ℤ_[p]} (hf : IsUnit f) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p σ f k + 1 ≤ kempner p k := by
  have := levelCount_le (hasLevel_exists h hf hk)
  have := kempner_pos p hk
  omega

/-- **Theorem R, lower bound, case `ρ_σ(f) ≥ 1`** (every lift, every `n`): if some partial
derivative of `f mod p` is nonzero (`d f̄ ≠ 0`), then `L_f(p, k) + 1 ≥ p`; with the upper bound
`S(p ^ k) ≥ p` this is `min(p ^ 1, S(p ^ k)) ≤ L_f + 1`. -/
theorem levelCount_ge_p_of_pderiv
    {σ : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p]} (h : IsFrobLift p σ)
    {f : MvPowerSeries (Fin n) ℤ_[p]} (hf : IsUnit f) {k : ℕ} (hk : 1 ≤ k)
    {i : Fin n} (hi : pderiv (R := ZMod p) i (redp p f) ≠ 0) :
    p ≤ levelCount p σ f k + 1 := by
  refine G1_ge_p (J := 0) h hf hk ⟨0, by simp⟩ ?_ (Or.inl rfl)
  rintro ⟨b, hb⟩
  rw [zero_add, pow_one] at hb
  apply hi
  have : redp p f = redp p (σ b) := by
    rw [← sub_eq_zero, ← map_sub]; exact (redp_eq_zero_iff p _).2 hb
  rw [this]
  exact deriv_frob_eq_zero h _ (redp p) redp_p b

/-- **Theorem R equality for `ρ = r = n`, and Theorem M for images `θ(B_std)`.** Let `σ'` be any
endomorphism of `ℤ_[p][[x_1..x_n]]` whose image is `θ(B)` with `B` the image of the standard lift
and `θ` a ring automorphism. If `g = θ f` with `f u = 1` and `u` of full rank, then
`L_g(p, k) + 1 = min(p ^ n, S(p ^ k))` for every `k ≥ 1`. -/
theorem levelCount_eq_of_fullRank_conj
    (θ : MvPowerSeries (Fin n) ℤ_[p] ≃+* MvPowerSeries (Fin n) ℤ_[p])
    (σ' : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p])
    (hrange : σ'.range = (frob p : MvPowerSeries (Fin n) ℤ_[p] →+* _).range.map
      (θ : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p]))
    {f u : MvPowerSeries (Fin n) ℤ_[p]} (hfu : f * u = 1) (hu : FullRank p u) {k : ℕ}
    (hk : 1 ≤ k) :
    levelCount p σ' (θ f) k + 1 = min (p ^ n) (kempner p k) := by
  rw [levelCount_eq_of_range_eq_map θ (frob p) σ' hrange]
  exact levelCount_eq_of_fullRank_padic p hfu hu hk

end FrobLevel
