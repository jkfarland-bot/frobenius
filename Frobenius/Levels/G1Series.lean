module

/-
Run r25, seat L4: ledger R-086 Theorem G1 and R-087 Theorem G1n (proved part) for
`A = ℤ_[p][[x_1, ..., x_n]]` and EVERY Frobenius lift `σ` (any ring endomorphism with
`σ a ≡ a ^ p (mod p)`; no continuity or form `x_i ↦ x_i ^ p + p h_i` is assumed).

`J_B(f) = J` is expressed by `(∃ b, p ^ J ∣ f - σ b) ∧ ¬ (∃ b, p ^ (J + 1) ∣ f - σ b)`.

* `G1_lower`: every unit `f` with `J_B(f) = J`, every `n`, every lift: a level `L` identity
  modulo `p ^ k` has `p ≤ L + 1` or `k ≤ J (L + 1)`; so `L_f + 1 ≥ min(p, ⌈k / J⌉)`
  (`≥ p` when `J = 0`).
* `G1_upper`: `J ≥ 1`: an identity of level `⌈k / J⌉ - 1` exists (every lift, every `n`).
* `levelCount_G1_of_cdiv_le`: hence `L_f + 1 = ⌈k / J⌉` whenever `1 ≤ J` and `⌈k / J⌉ ≤ p`
  (every lift, every `n`).
* `levelCount_G1_of_span`: one variable, any lift for which `1, x, ..., x ^ (p - 1)` span `A`
  over `B`: `L_f + 1 = p` for `J = 0` and `min(p, ⌈k / J⌉)` for `J ≥ 1`;
  `levelCount_G1_std`: the same for the standard lift, unconditionally.
* `levelCount_eq_zero_of_mem`: `f ∈ B + p ^ k A` gives `L_f = 0`.

The reduction modulo `p` is `redp : ℤ_[p][[x]] → 𝔽_p[[x]]` (a domain); the derivations are
Mathlib's partial derivatives `MvPowerSeries.pderiv`.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Basis
public import Frobenius.Levels.PropT
public import Frobenius.Levels.G1

@[expose] public section

-- Port (Mathlib v4.35.0-rc2): restore the v4.33 instance path for `AddCommGroup (ZMod p)`.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace FrobLevel

open MvPowerSeries

variable (p : ℕ) [hp : Fact p.Prime] {n : ℕ}

/-- Reduction modulo `p`, coefficientwise. -/
noncomputable def redp : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) (ZMod p) :=
  MvPowerSeries.map PadicInt.toZMod

theorem toZMod_eq_zero_iff (x : ℤ_[p]) : PadicInt.toZMod x = 0 ↔ (p : ℤ_[p]) ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

theorem redp_eq_zero_iff (a : MvPowerSeries (Fin n) ℤ_[p]) :
    redp p a = 0 ↔ ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ∣ a := by
  constructor
  · intro h
    refine natCast_dvd_of_coeff p fun d => ?_
    have := congrArg (coeff d) h
    rw [redp, coeff_map, map_zero] at this
    exact (toZMod_eq_zero_iff p _).1 this
  · intro h
    ext d
    rw [redp, coeff_map, map_zero]
    exact (toZMod_eq_zero_iff p _).2 (coeff_of_natCast_dvd p h d)

theorem redp_natCast_ne_zero (d : ℕ) (hd0 : 0 < d) (hdp : d < p) :
    ((d : ℕ) : MvPowerSeries (Fin n) (ZMod p)) ≠ 0 := by
  intro h
  have := congrArg constantCoeff h
  rw [map_natCast, map_zero, ZMod.natCast_eq_zero_iff] at this
  exact absurd (Nat.le_of_dvd hd0 this) (by omega)

theorem isUnit_padic_iff (x : ℤ_[p]) : IsUnit x ↔ PadicInt.toZMod x ≠ 0 := by
  rw [← IsLocalRing.notMem_maximalIdeal, ← PadicInt.ker_toZMod, RingHom.mem_ker]

theorem isUnit_iff_redp (a : MvPowerSeries (Fin n) ℤ_[p]) : IsUnit a ↔ IsUnit (redp p a) := by
  rw [isUnit_iff_constantCoeff, isUnit_iff_constantCoeff (φ := redp p a), redp,
    constantCoeff_map, isUnit_padic_iff, isUnit_iff_ne_zero]

variable {p}

/-- If every partial derivative of `y ∈ 𝔽_p[[x]]` vanishes then `y` is a `p`-th power. -/
theorem exists_pow_of_pderiv_eq_zero (y : MvPowerSeries (Fin n) (ZMod p))
    (hy : ∀ i, pderiv (R := ZMod p) i y = 0) : ∃ c, c ^ p = y := by
  classical
  let c : MvPowerSeries (Fin n) (ZMod p) := fun d => coeff (p • d) y
  refine ⟨c, ?_⟩
  have hexp : expand p hp.out.ne_zero c = y := by
    ext m
    by_cases hm : ∀ i, p ∣ m i
    · set m' : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => m i / p)
      have hmm : p • m' = m := by
        ext i; simp [m', Nat.mul_div_cancel' (hm i)]
      rw [← hmm, coeff_expand_smul]
      rfl
    · push Not at hm
      obtain ⟨i, hi⟩ := hm
      rw [coeff_expand_of_not_dvd _ _ _ hi]
      have hmi : 1 ≤ m i := by
        rcases Nat.eq_zero_or_pos (m i) with h0 | h0
        · exact absurd (h0 ▸ dvd_zero p) hi
        · exact h0
      set m'' := m - Finsupp.single i 1
      have hm'' : m'' + Finsupp.single i 1 = m := by
        ext j
        by_cases hj : j = i
        · subst hj; simp [m'']; omega
        · simp [m'', Ne.symm hj]
      have h1 := congrArg (coeff m'') (hy i)
      rw [coeff_pderiv, hm'', map_zero] at h1
      have h2 : (m'' i + 1 : ZMod p) = (m i : ZMod p) := by
        rw [← hm'']; simp
      rw [h2] at h1
      rcases mul_eq_zero.1 h1 with h | h
      · exact h.symm
      · exact absurd ((ZMod.natCast_eq_zero_iff _ _).1 h) hi
  rw [← map_frobenius_expand (p := p) (hp := hp.out.ne_zero), ZMod.frobenius_zmod, map_id,
    RingHom.id_apply, hexp]

/-- Every element of `𝔽_p[[x]]` lifts to `ℤ_[p][[x]]`. -/
theorem redp_surjective (c : MvPowerSeries (Fin n) (ZMod p)) : ∃ a, redp p a = c := by
  let a : MvPowerSeries (Fin n) ℤ_[p] := fun d => ((coeff d c).val : ℤ_[p])
  refine ⟨a, ?_⟩
  ext d
  show PadicInt.toZMod (((coeff d c).val : ℕ) : ℤ_[p]) = coeff d c
  rw [map_natCast, ZMod.natCast_zmod_val]

/-- **The `J_B` bridge.** For every Frobenius lift: if all partial derivatives of `e mod p`
vanish, then `e ∈ B + p A`. -/
theorem mem_B_add_of_pderiv {σ : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p]}
    (h : IsFrobLift p σ) (e : MvPowerSeries (Fin n) ℤ_[p])
    (he : ∀ i, pderiv (R := ZMod p) i (redp p e) = 0) :
    ∃ c, ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ∣ e - σ c := by
  obtain ⟨c0, hc0⟩ := exists_pow_of_pderiv_eq_zero _ he
  obtain ⟨a, ha⟩ := redp_surjective c0
  refine ⟨a, (redp_eq_zero_iff p _).1 ?_⟩
  have hπp : redp p ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) = 0 :=
    (redp_eq_zero_iff p _).2 dvd_rfl
  rw [map_sub, map_frob h (redp p) hπp, ha, hc0, sub_self]

section Lift

variable {σ : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p]}

theorem redp_p : redp p ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) = 0 :=
  (redp_eq_zero_iff p _).2 dvd_rfl

/-- If `f` is a unit and `f ≡ σ b (mod p)` then `b` is a unit. -/
theorem isUnit_of_dvd_sub_frob (h : IsFrobLift p σ) {f b : MvPowerSeries (Fin n) ℤ_[p]}
    (hf : IsUnit f) (hb : ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ∣ f - σ b) : IsUnit b := by
  rw [isUnit_iff_redp] at hf ⊢
  have : redp p f = redp p b ^ p := by
    rw [← map_frob h (redp p) redp_p, ← sub_eq_zero, ← map_sub]
    exact (redp_eq_zero_iff p _).2 hb
  rw [this] at hf
  exact (isUnit_pow_iff hp.out.ne_zero).1 hf

theorem noPTorsion_series : NoPTorsion p (MvPowerSeries (Fin n) ℤ_[p]) :=
  noPTorsion_mvPowerSeries p (padicInt_noPTorsion p)

theorem not_isUnit_p_series : ¬ IsUnit ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) := by
  have := not_isUnit_pow_mvPowerSeries p (τ := Fin n) (padicInt_not_isUnit p) (k := 1) le_rfl
  simpa using this

/-- **G1 / G1n, lower bound, every lift, every `n`.** -/
theorem G1_lower (h : IsFrobLift p σ) {f : MvPowerSeries (Fin n) ℤ_[p]} (hf : IsUnit f)
    {J k L : ℕ} (hJ : ∃ b, ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ J ∣ f - σ b)
    (hJ1 : ¬ ∃ b, ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ (J + 1) ∣ f - σ b)
    (hL : HasLevel p σ f k L) : p ≤ L + 1 ∨ k ≤ J * (L + 1) := by
  have ht := noPTorsion_series (p := p) (n := n)
  have hπ := redp_eq_zero_iff p (n := n)
  have hs : PSat p σ := pSat_of_domain h (redp p) hπ
  have hchar : ∀ d : ℕ, 0 < d → d < p → (d : MvPowerSeries (Fin n) (ZMod p)) ≠ 0 :=
    redp_natCast_ne_zero p
  rcases Nat.eq_zero_or_pos J with rfl | hJpos
  · -- `J = 0`: `s = 1`, `τ = f - 1`
    have hD : ∃ i, pderiv (R := ZMod p) i (redp p (f - 1)) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨c, hc⟩ := mem_B_add_of_pderiv h _ hcon
      exact hJ1 ⟨1 + c, by rw [zero_add, pow_one, map_add, map_one]; convert hc using 1; ring⟩
    obtain ⟨i, hi⟩ := hD
    exact le_of_hasLevel_decomp ht hs not_isUnit_p_series (s := 1) (τ := f - 1) (one_mem _)
      (by ring) (pIndep_of_deriv h (redp p) hπ hchar (pderiv (R := ZMod p) i) hi) hL
  · obtain ⟨b, e, he⟩ := hJ
    have hbu : IsUnit b := isUnit_of_dvd_sub_frob h hf
      (by rw [he]; exact Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _)
    obtain ⟨bu, rfl⟩ := hbu
    set bi : MvPowerSeries (Fin n) ℤ_[p] := (↑(bu⁻¹) : MvPowerSeries (Fin n) ℤ_[p])
    have hbb : σ bu * σ bi = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have hD : ∃ i, pderiv (R := ZMod p) i (redp p e) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨c, hc⟩ := mem_B_add_of_pderiv h _ hcon
      refine hJ1 ⟨bu + (p : MvPowerSeries (Fin n) ℤ_[p]) ^ J * c, ?_⟩
      have : f - σ (bu + (p : MvPowerSeries (Fin n) ℤ_[p]) ^ J * c)
          = (p : MvPowerSeries (Fin n) ℤ_[p]) ^ J * (e - σ c) := by
        rw [map_add, map_mul, map_pow, map_natCast]
        linear_combination he
      rw [this, pow_succ]
      exact mul_dvd_mul_left _ hc
    obtain ⟨i, hi⟩ := hD
    set τ := σ bi * e
    have hτ : pderiv (R := ZMod p) i (redp p τ) ≠ 0 := by
      rw [map_mul, Derivation.leibniz, deriv_frob_eq_zero h _ (redp p) redp_p, smul_zero,
        add_zero, smul_eq_mul]
      refine mul_ne_zero ?_ hi
      have hu : IsUnit (redp p (σ bi)) := (Units.isUnit (bu⁻¹)).map σ |>.map (redp p)
      exact hu.ne_zero
    refine le_of_hasLevel_decomp ht hs not_isUnit_p_series (s := σ bu) (τ := τ) ⟨bu, rfl⟩
      ?_ (pIndep_of_deriv h (redp p) hπ hchar (pderiv (R := ZMod p) i) hτ) hL
    have hf' : f = σ bu + (p : MvPowerSeries (Fin n) ℤ_[p]) ^ J * e := by
      linear_combination he
    rw [hf']
    linear_combination (-(p : MvPowerSeries (Fin n) ℤ_[p]) ^ J * e) * hbb

/-- **G1, upper bound `⌈k / J⌉`, every lift, every `n`.** -/
theorem G1_upper (h : IsFrobLift p σ) {f : MvPowerSeries (Fin n) ℤ_[p]} (hf : IsUnit f)
    {J k : ℕ} (hJ : 1 ≤ J) (hk : 1 ≤ k)
    (hJb : ∃ b, ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ J ∣ f - σ b) :
    HasLevel p σ f k (cdiv k J - 1) := by
  obtain ⟨b, hb⟩ := hJb
  have hbu : IsUnit b := isUnit_of_dvd_sub_frob h hf
    ((dvd_pow_self _ (by omega)).trans hb)
  obtain ⟨bu, rfl⟩ := hbu
  refine hasLevel_geom (s := σ bu) (s' := σ ((bu⁻¹ : (MvPowerSeries (Fin n) ℤ_[p])ˣ) : _))
    ⟨_, rfl⟩ ?_ hb (one_le_cdiv (by omega) hk) (by rw [mul_comm]; exact le_mul_cdiv (by omega))
  rw [← map_mul, Units.inv_mul, map_one, sub_self]; exact dvd_zero _

/-- `f ∈ B + p ^ k A` (with `f` a unit) gives `L_f(p, k) = 0`. -/
theorem levelCount_eq_zero_of_mem (h : IsFrobLift p σ) {f : MvPowerSeries (Fin n) ℤ_[p]}
    (hf : IsUnit f) {k : ℕ} (hk : 1 ≤ k)
    (hb : ∃ b, ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ k ∣ f - σ b) :
    levelCount p σ f k = 0 := by
  have := G1_upper h hf hk hk hb
  have h1 : cdiv k k = 1 := le_antisymm ((cdiv_le_iff (by omega)).2 (by omega))
    (one_le_cdiv (by omega) hk)
  rw [h1] at this
  exact Nat.le_zero.1 (levelCount_le this)

/-- **G1 / G1n, exact value in the range `⌈k / J⌉ ≤ p`, every lift, every `n`.** For a unit `f`
with `J_B(f) = J ≥ 1` and `k ≤ p J`: `L_f(p, k) + 1 = ⌈k / J⌉`. -/
theorem levelCount_G1_of_cdiv_le (h : IsFrobLift p σ) {f : MvPowerSeries (Fin n) ℤ_[p]}
    (hf : IsUnit f) {J k : ℕ} (hJ : 1 ≤ J) (hk : 1 ≤ k)
    (hJb : ∃ b, ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ J ∣ f - σ b)
    (hJ1 : ¬ ∃ b, ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ (J + 1) ∣ f - σ b)
    (hcp : cdiv k J ≤ p) :
    levelCount p σ f k + 1 = cdiv k J := by
  have hup := G1_upper h hf hJ hk hJb
  have hc1 := one_le_cdiv (J := J) (by omega) hk
  have h1 := levelCount_le hup
  rcases G1_lower h hf hJb hJ1 (hasLevel_levelCount hup) with h2 | h2
  · omega
  · have := (cdiv_le_iff (by omega)).2 h2; omega

/-- An identity of some level always exists (the δ-tower: degree `S(p ^ k)`). -/
theorem hasLevel_exists (h : IsFrobLift p σ) {f : MvPowerSeries (Fin n) ℤ_[p]} (hf : IsUnit f)
    {k : ℕ} (hk : 1 ≤ k) : HasLevel p σ f k (kempner p k - 1) := by
  obtain ⟨v, rfl⟩ := hf
  have hK := kempner_pos p hk
  have hann := monicAnn_kempner h ((v⁻¹ : (MvPowerSeries (Fin n) ℤ_[p])ˣ) : _) k
  rw [show kempner p k = kempner p k - 1 + 1 by omega] at hann
  exact hann.hasLevel (by rw [Units.mul_inv, sub_self]; exact dvd_zero _)

/-- **G1n lower half in the remaining range**: `J = 0`, or `k > p J`: `L_f(p, k) + 1 ≥ p`. -/
theorem G1_ge_p (h : IsFrobLift p σ) {f : MvPowerSeries (Fin n) ℤ_[p]} (hf : IsUnit f)
    {J k : ℕ} (hk : 1 ≤ k) (hJb : ∃ b, ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ J ∣ f - σ b)
    (hJ1 : ¬ ∃ b, ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ (J + 1) ∣ f - σ b)
    (hcase : J = 0 ∨ p * J < k) :
    p ≤ levelCount p σ f k + 1 := by
  rcases G1_lower h hf hJb hJ1 (hasLevel_levelCount (hasLevel_exists h hf hk)) with h2 | h2
  · exact h2
  · rcases hcase with h0 | h0
    · subst h0; omega
    · by_contra hlt
      have : J * (levelCount p σ f k + 1) ≤ J * p := Nat.mul_le_mul_left J (by omega)
      rw [mul_comm J p] at this; omega


/-- **G1 (R-086), one variable**, for every Frobenius lift `σ` of `ℤ_[p][[x]]` for which
`1, x, ..., x ^ (p - 1)` span `A` over `B = σ(A)` (on paper this holds for every continuous lift,
R-086; in Lean it is a hypothesis): `L_f(p, k) + 1 = p` if `J_B(f) = 0`, and
`min(p, ⌈k / J_B(f)⌉)` if `J_B(f) ≥ 1`. -/
theorem levelCount_G1_of_span
    {σ : MvPowerSeries (Fin 1) ℤ_[p] →+* MvPowerSeries (Fin 1) ℤ_[p]} (h : IsFrobLift p σ)
    (hspan : ∀ a : MvPowerSeries (Fin 1) ℤ_[p], ∃ c : (Fin 1 →₀ ℕ) → MvPowerSeries (Fin 1) ℤ_[p],
      a = ∑ e ∈ digitExps p 1, σ (c e) * monomial e 1)
    {f : MvPowerSeries (Fin 1) ℤ_[p]} (hf : IsUnit f) {J k : ℕ} (hk : 1 ≤ k)
    (hJb : ∃ b, ((p : ℕ) : MvPowerSeries (Fin 1) ℤ_[p]) ^ J ∣ f - σ b)
    (hJ1 : ¬ ∃ b, ((p : ℕ) : MvPowerSeries (Fin 1) ℤ_[p]) ^ (J + 1) ∣ f - σ b) :
    levelCount p σ f k + 1 = if J = 0 then p else min p (cdiv k J) := by
  obtain ⟨v, hv⟩ := hf
  have hup := levelCount_le_min_of_span h (digitExps p 1)
    (fun e => (monomial e 1 : MvPowerSeries (Fin 1) ℤ_[p])) hspan hk
    (f := f) (u := ((v⁻¹ : (MvPowerSeries (Fin 1) ℤ_[p])ˣ) : _))
    (by rw [← hv, Units.mul_inv, sub_self]; exact dvd_zero _)
  rw [card_digitExps, pow_one] at hup
  have hup' := hup.trans (min_le_left _ _)
  have hf : IsUnit f := ⟨v, hv⟩
  split_ifs with hJ0
  · have := G1_ge_p h hf hk hJb hJ1 (Or.inl hJ0); omega
  · rcases le_or_gt (cdiv k J) p with hc | hc
    · rw [min_eq_right hc]; exact levelCount_G1_of_cdiv_le h hf (by omega) hk hJb hJ1 hc
    · rw [min_eq_left hc.le]
      have hkJ : p * J < k := by
        by_contra hcon
        have := (cdiv_le_iff (k := k) (J := J) (m := p) (by omega)).2 (by rw [mul_comm]; omega)
        omega
      have := G1_ge_p h hf hk hJb hJ1 (Or.inr hkJ); omega

/-- **G1 for the standard lift `x ↦ x ^ p`**, one variable, unconditional. -/
theorem levelCount_G1_std {f : MvPowerSeries (Fin 1) ℤ_[p]} (hf : IsUnit f) {J k : ℕ}
    (hk : 1 ≤ k) (hJb : ∃ b, ((p : ℕ) : MvPowerSeries (Fin 1) ℤ_[p]) ^ J ∣ f - frob p b)
    (hJ1 : ¬ ∃ b, ((p : ℕ) : MvPowerSeries (Fin 1) ℤ_[p]) ^ (J + 1) ∣ f - frob p b) :
    levelCount p (frob p) f k + 1 = if J = 0 then p else min p (cdiv k J) :=
  levelCount_G1_of_span (frob_isFrobLift p (padicInt_pow_sub p)) (span_digit p) hf hk hJb hJ1

end Lift

end FrobLevel
