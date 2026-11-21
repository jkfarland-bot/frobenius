module

/-
Run r25, seat L10: R-086 Theorem M (monomial images) for monomial data of ORIGIN TYPE.

Setting: `A = ℤ_[p][[x_1..x_n]]` with the product (coefficientwise) topology, `σ` a continuous
ring endomorphism with `σ(a) ≡ a ^ p (mod p)`, `B = σ(A)`.  Monomial data of origin type: a
continuous ring automorphism `θ` of `A` with `m_i := θ(x_i)` and `m_i ^ p ∈ B` for every `i`
(note Definition `monomial` with `c_i = m_i(0)` in `p ℤ_p`, the coordinates being
`t_i = m_i - c_i`; a continuous automorphism has `θ(x_i)(0) ∈ p ℤ_p`).

* `map_frob_le_range`: `θ(B_std) ≤ B` (B is closed since `A` is compact; polynomials are dense).
* `range_eq_of_frob_le`: a lift whose image contains `B_std` has image exactly `B_std`
  (from L8's freeness for every lift).
* `range_eq_map_frob`: `B = θ(B_std)`.
* `thmM_origin`: `L_f + 1 = flagValue p (θ⁻¹ f) k` for every unit `f`, every `k ≥ 1`
  (L4's Prop T transport plus L5's R-083 for the standard lift).
* `thmM_origin_mclasses`: the same with the flag read from ANY decomposition
  `f = ∑_{c digit} m ^ c b_c`, `b_c ∈ B`, class `c` getting depth `v_p(b_c)` (the note's wording);
  `exists_mDecomp`: such a decomposition exists.

Not covered here: monomial data with some `c_i` a unit (torus type), see Open.lean.
Lean v4.33.1 with Mathlib; no sorry, no axioms beyond propext, Classical.choice, Quot.sound.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Flag
public import Frobenius.Levels.Padic
public import Frobenius.Levels.PropT
public import Frobenius.Levels.Span
public import Frobenius.Levels.Free

@[expose] public section

namespace L10

open MvPowerSeries MvPowerSeries.WithPiTopology FrobLevel

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

/-- Every ring endomorphism of `ℤ_[p][[x]]` fixes constants (same proof as L8v's `sigma_C_eq`). -/
theorem ringHom_C (σ : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p]) (c : ℤ_[p]) :
    σ (C c) = C c := by
  rw [← sub_eq_zero]
  apply FrobLevel.series_sep
  intro K
  have h := PadicInt.appr_spec K c
  rw [Ideal.mem_span_singleton] at h
  obtain ⟨e, he⟩ := h
  have hc : C c = ((c.appr K : ℕ) : MvPowerSeries (Fin n) ℤ_[p])
      + ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ K * C e := by
    have : c = (c.appr K : ℤ_[p]) + (p : ℤ_[p]) ^ K * e := by rw [← he]; ring
    conv_lhs => rw [this]
    simp [map_add, map_mul, map_pow, map_natCast]
  refine ⟨σ (C e) - C e, ?_⟩
  rw [hc, map_add, map_mul, map_pow, map_natCast, map_natCast]
  ring

instance compactSpace_series : CompactSpace (MvPowerSeries (Fin n) ℤ_[p]) :=
  inferInstanceAs (CompactSpace ((Fin n →₀ ℕ) → ℤ_[p]))

/-- The image of a continuous endomorphism is closed (`A` is compact Hausdorff). -/
theorem isClosed_range {σ : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p]}
    (hσ : Continuous σ) : IsClosed (σ.range : Set (MvPowerSeries (Fin n) ℤ_[p])) := by
  have : (σ.range : Set (MvPowerSeries (Fin n) ℤ_[p])) = Set.range σ := by
    ext a; simp
  rw [this]
  exact (isCompact_range hσ).isClosed

/-- The standard lift is continuous. -/
theorem continuous_frob : Continuous (frob p : MvPowerSeries (Fin n) ℤ_[p] → _) := by
  refine continuous_pi fun d => ?_
  show Continuous fun g => coeff d (frob p g)
  by_cases h : ∀ i, p ∣ d i
  · set d' : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => d i / p with hd'
    have hd : p • d' = d := by
      ext i; simp [hd', Nat.mul_div_cancel' (h i)]
    have : (fun g : MvPowerSeries (Fin n) ℤ_[p] => coeff d (frob p g))
        = fun g => coeff d' g := by
      funext g; rw [← hd, coeff_frob_smul]
    rw [this]
    exact continuous_coeff ℤ_[p] d'
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have : (fun g : MvPowerSeries (Fin n) ℤ_[p] => coeff d (frob p g)) = fun _ => 0 := by
      funext g; exact coeff_frob_of_not_dvd p g hi
    rw [this]
    exact continuous_const

/-- A closed set containing every polynomial is everything. -/
theorem forall_of_poly {S : Set (MvPowerSeries (Fin n) ℤ_[p])} (hS : IsClosed S)
    (hP : ∀ P : MvPolynomial (Fin n) ℤ_[p], (P : MvPowerSeries (Fin n) ℤ_[p]) ∈ S) :
    ∀ a, a ∈ S := by
  have hdense : Dense (Set.range (MvPolynomial.toMvPowerSeries (σ := Fin n) (R := ℤ_[p]))) :=
    MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries
  have hsub : Set.range (MvPolynomial.toMvPowerSeries (σ := Fin n) (R := ℤ_[p])) ⊆ S := by
    rintro _ ⟨Q, rfl⟩; exact hP Q
  have := closure_minimal hsub hS
  rw [hdense.closure_eq] at this
  exact fun a => this (Set.mem_univ a)

section Ident

variable {σ : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p]}

/-- **`θ(B_std) ≤ B`** when `σ` and `θ` are continuous and every `θ(x_i) ^ p` lies in `B`. -/
theorem map_frob_le_range (hσc : Continuous σ)
    (θ : MvPowerSeries (Fin n) ℤ_[p] ≃+* MvPowerSeries (Fin n) ℤ_[p]) (hθc : Continuous θ)
    (hm : ∀ i, θ (X i) ^ p ∈ σ.range) :
    (frob p).range.map (θ : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p])
      ≤ σ.range := by
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  let S : Set (MvPowerSeries (Fin n) ℤ_[p]) := {g | θ (frob p g) ∈ σ.range}
  have hS : IsClosed S := (isClosed_range hσc).preimage (hθc.comp continuous_frob)
  have hP : ∀ P : MvPolynomial (Fin n) ℤ_[p], (P : MvPowerSeries (Fin n) ℤ_[p]) ∈ S := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a =>
      show θ (frob p ((MvPolynomial.C a : MvPolynomial (Fin n) ℤ_[p]) :
        MvPowerSeries (Fin n) ℤ_[p])) ∈ σ.range
      rw [MvPolynomial.coe_C, frob_C]
      have h1 : θ (C a) = C a := ringHom_C (θ : MvPowerSeries (Fin n) ℤ_[p] →+* _) a
      rw [h1]
      exact ⟨C a, ringHom_C σ a⟩
    | add f g hf hg =>
      show θ (frob p ((f + g : MvPolynomial (Fin n) ℤ_[p]) : MvPowerSeries (Fin n) ℤ_[p]))
        ∈ σ.range
      rw [MvPolynomial.coe_add, map_add, map_add]
      exact add_mem hf hg
    | mul_X f i hf =>
      show θ (frob p ((f * MvPolynomial.X i : MvPolynomial (Fin n) ℤ_[p]) :
        MvPowerSeries (Fin n) ℤ_[p])) ∈ σ.range
      rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, map_mul, frob_X, map_pow]
      exact mul_mem hf (hm i)
  exact forall_of_poly hS hP g

/-- **A lift whose image contains `B_std` has image `B_std`** (L8's freeness for every lift). -/
theorem range_eq_of_frob_le (hσ : IsFrobLift p σ) (hle : (frob p).range ≤ σ.range) :
    σ.range = (frob p).range := by
  classical
  refine le_antisymm ?_ hle
  rintro _ ⟨b0, rfl⟩
  have hdec := eq_sum_digit p (σ b0)
  have hex : ∀ e, ∃ x, σ x = frob p (classPart p (σ b0) e) :=
    fun e => RingHom.mem_range.1 (hle (RingHom.mem_range.2 ⟨_, rfl⟩))
  choose d hd using hex
  have h0 : (0 : Fin n →₀ ℕ) ∈ digitExps p n := (mem_digitExps p n).2 fun _ => hp.out.pos
  have h1 : σ b0 = ∑ e ∈ digitExps p n, σ (d e) * monomial e 1 := by
    conv_lhs => rw [hdec]
    exact Finset.sum_congr rfl fun e _ => by rw [hd e]
  have h2 : σ b0 = ∑ e ∈ digitExps p n, σ (if e = 0 then b0 else 0) * monomial e 1 := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro e _ hne; simp [hne]
    · intro h; exact absurd h0 h
  have huniq := (free_every_lift hσ (σ b0)).2 _ _ h1 h2
  rw [hdec, Finset.sum_eq_single 0]
  · exact ⟨classPart p (σ b0) 0, by simp⟩
  · intro e he hne
    rw [← hd e, huniq e he, if_neg hne, map_zero, zero_mul]
  · intro h; exact absurd h0 h

/-- **Identification of a monomial image (origin type): `B = θ(B_std)`.** -/
theorem range_eq_map_frob (hσ : IsFrobLift p σ) (hσc : Continuous σ)
    (θ : MvPowerSeries (Fin n) ℤ_[p] ≃+* MvPowerSeries (Fin n) ℤ_[p]) (hθc : Continuous θ)
    (hm : ∀ i, θ (X i) ^ p ∈ σ.range) :
    σ.range = (frob p).range.map (θ : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p]) := by
  -- the conjugate lift `σ' = θ⁻¹ σ θ`
  set σ' : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p] :=
    ((θ.symm : MvPowerSeries (Fin n) ℤ_[p] →+* _).comp (σ.comp (θ : _ →+* _))) with hσ'
  have hσ'app : ∀ a, σ' a = θ.symm (σ (θ a)) := fun a => rfl
  have hlift' : IsFrobLift p σ' := by
    intro a
    rw [hσ'app]
    have h := map_dvd θ.symm.toRingHom (hσ (θ a))
    simpa [map_sub, map_pow, map_natCast] using h
  have hle' : (frob p).range ≤ σ'.range := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨w, hw⟩ := RingHom.mem_range.1
      (map_frob_le_range hσc θ hθc hm ⟨frob p g, ⟨g, rfl⟩, rfl⟩)
    refine ⟨θ.symm w, ?_⟩
    rw [hσ'app, RingEquiv.apply_symm_apply, hw]
    simp
  have heq := range_eq_of_frob_le hlift' hle'
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    have : σ' (θ.symm a) ∈ (frob p).range := heq ▸ ⟨θ.symm a, rfl⟩
    refine ⟨σ' (θ.symm a), this, ?_⟩
    simp [hσ'app]
  · rintro ⟨c, hc, rfl⟩
    rw [← heq] at hc
    obtain ⟨a, rfl⟩ := hc
    exact ⟨θ a, by simp [hσ'app]⟩

/-- **R-086 Theorem M, origin type**: for every unit `f` and `k ≥ 1`,
`L_f + 1 = flagValue p (θ⁻¹ f) k`, the R-083 value of `θ⁻¹ f` under the standard lift. -/
theorem thmM_origin (hσ : IsFrobLift p σ) (hσc : Continuous σ)
    (θ : MvPowerSeries (Fin n) ℤ_[p] ≃+* MvPowerSeries (Fin n) ℤ_[p]) (hθc : Continuous θ)
    (hm : ∀ i, θ (X i) ^ p ∈ σ.range) {f u : MvPowerSeries (Fin n) ℤ_[p]} (hfu : f * u = 1)
    {k : ℕ} (hk : 1 ≤ k) :
    levelCount p σ f k + 1 = flagValue p (θ.symm f) k := by
  have h := levelCount_eq_of_range_eq_map (p := p) θ (frob p) σ
    (range_eq_map_frob hσ hσc θ hθc hm) (θ.symm f) k
  rw [RingEquiv.apply_symm_apply] at h
  rw [h]
  exact levelCount_eq_flagValue_padic p (u := θ.symm u)
    (by rw [← map_mul, hfu, map_one]) hk

end Ident

/-! ### The flag read in the `m`-classes -/

/-- `U_d` in the `m`-classes: the span of the classes `c ≠ 0` with `v_p(b_c) ≤ d`. -/
noncomputable def mDepthSpace (b : (Fin n →₀ ℕ) → MvPowerSeries (Fin n) ℤ_[p]) (d : ℕ) :
    Submodule (ZMod p) (Fin n → ZMod p) :=
  Submodule.span (ZMod p) (classVec p '' {κ | κ ∈ digitExps p n ∧ κ ≠ 0 ∧
    ¬ ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ (d + 1) ∣ b κ})

/-- The span of the classes `c ≠ 0` with `b_c ≠ 0`. -/
noncomputable def mFullSpace (b : (Fin n →₀ ℕ) → MvPowerSeries (Fin n) ℤ_[p]) :
    Submodule (ZMod p) (Fin n → ZMod p) :=
  Submodule.span (ZMod p) (classVec p '' {κ | κ ∈ digitExps p n ∧ κ ≠ 0 ∧ b κ ≠ 0})

/-- `r_f` in the `m`-classes. -/
noncomputable def mRank (b : (Fin n →₀ ℕ) → MvPowerSeries (Fin n) ℤ_[p]) : ℕ :=
  Module.finrank (ZMod p) (mFullSpace (p := p) b)

/-- `d(j)` in the `m`-classes. -/
noncomputable def mFlag (b : (Fin n →₀ ℕ) → MvPowerSeries (Fin n) ℤ_[p]) (j : ℕ) : ℕ :=
  if j = 0 then 0 else sInf {d | j ≤ Module.finrank (ZMod p) (mDepthSpace (p := p) b d)}

/-- `d(j + 1) - d(j)` in the `m`-classes. -/
noncomputable def mJump (b : (Fin n →₀ ℕ) → MvPowerSeries (Fin n) ℤ_[p]) (j : ℕ) : ℕ :=
  mFlag (p := p) b (j + 1) - mFlag (p := p) b j

/-- The right side of the flag formula, with the flag read in the `m`-classes. -/
noncomputable def mFlagValue (b : (Fin n →₀ ℕ) → MvPowerSeries (Fin n) ℤ_[p]) (k : ℕ) : ℕ :=
  sInf {m | p ^ mRank (p := p) b ≤ m ∨ k ≤ padicValNat p m.factorial
    + ∑ j ∈ Finset.range (mRank (p := p) b), mJump (p := p) b j * (m / p ^ j)}

theorem pow_dvd_frob_iff (K : ℕ) (β : MvPowerSeries (Fin n) ℤ_[p]) :
    ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ K ∣ frob p β
      ↔ ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ K ∣ β := by
  rw [series_dvd_iff, series_dvd_iff]
  constructor
  · intro h d
    have := h (p • d)
    rwa [coeff_frob_smul] at this
  · intro h d
    by_cases hd : ∀ i, p ∣ d i
    · set d' : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun i => d i / p with hd'
      have he : p • d' = d := by
        ext i; simp [hd', Nat.mul_div_cancel' (hd i)]
      rw [← he, coeff_frob_smul]; exact h d'
    · push Not at hd
      obtain ⟨i, hi⟩ := hd
      rw [coeff_frob_of_not_dvd p β hi]; exact dvd_zero _

theorem frob_eq_zero_iff (β : MvPowerSeries (Fin n) ℤ_[p]) : frob p β = 0 ↔ β = 0 := by
  constructor
  · intro h; ext d
    have := congrArg (coeff (p • d)) h
    rwa [coeff_frob_smul, map_zero] at this
  · rintro rfl; exact map_zero _

theorem pow_dvd_equiv_iff (θ : MvPowerSeries (Fin n) ℤ_[p] ≃+* MvPowerSeries (Fin n) ℤ_[p])
    (K : ℕ) (y : MvPowerSeries (Fin n) ℤ_[p]) :
    ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ K ∣ θ y
      ↔ ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ K ∣ y := by
  constructor
  · intro h
    have := map_dvd θ.symm.toRingHom h
    simpa [map_pow, map_natCast] using this
  · intro h
    have := map_dvd θ.toRingHom h
    simpa [map_pow, map_natCast] using this

section MClasses

variable {σ : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p]}

/-- If `B = θ(B_std)` and `f = ∑ θ(x ^ c) b_c` with `b_c ∈ B`, the standard flag data of `θ⁻¹ f`
are the `m`-class data of `b`. -/
theorem flagValue_symm_eq_mFlagValue
    (θ : MvPowerSeries (Fin n) ℤ_[p] ≃+* MvPowerSeries (Fin n) ℤ_[p])
    (hB : σ.range = (frob p).range.map (θ : MvPowerSeries (Fin n) ℤ_[p] →+* _))
    (b : (Fin n →₀ ℕ) → MvPowerSeries (Fin n) ℤ_[p]) (hb : ∀ c ∈ digitExps p n, b c ∈ σ.range)
    {f : MvPowerSeries (Fin n) ℤ_[p]}
    (hf : f = ∑ c ∈ digitExps p n, θ (monomial c 1) * b c) (k : ℕ) :
    flagValue p (θ.symm f) k = mFlagValue (p := p) b k := by
  classical
  have hex : ∀ c ∈ digitExps p n, ∃ β, θ (frob p β) = b c := by
    intro c hc
    have := hb c hc
    rw [hB] at this
    obtain ⟨_, ⟨β, rfl⟩, hβ⟩ := this
    exact ⟨β, hβ⟩
  choose! β hβ using hex
  have hsymm : θ.symm f = ∑ c ∈ digitExps p n, frob p (β c) * monomial c 1 := by
    rw [hf, map_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [map_mul, RingEquiv.symm_apply_apply, ← hβ c hc, RingEquiv.symm_apply_apply, mul_comm]
  have hcp : ∀ κ ∈ digitExps p n, classPart p (θ.symm f) κ = β κ := by
    intro κ hκ
    ext d
    rw [coeff_classPart, hsymm, coeff_classPart_sum hκ]
  have hdvd : ∀ κ ∈ digitExps p n, ∀ K,
      (((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ K ∣ classPart p (θ.symm f) κ
        ↔ ((p : ℕ) : MvPowerSeries (Fin n) ℤ_[p]) ^ K ∣ b κ) := by
    intro κ hκ K
    rw [hcp κ hκ, ← hβ κ hκ, pow_dvd_equiv_iff, pow_dvd_frob_iff]
  have hne : ∀ κ ∈ digitExps p n, (classPart p (θ.symm f) κ ≠ 0 ↔ b κ ≠ 0) := by
    intro κ hκ
    rw [hcp κ hκ, ← hβ κ hκ]
    constructor
    · intro h h0
      exact h ((frob_eq_zero_iff _).1 (θ.injective (h0.trans (map_zero θ).symm)))
    · intro h h0
      exact h (by rw [h0, map_zero, map_zero])
  have hD : ∀ d, depthSpace p (θ.symm f) d = mDepthSpace (p := p) b d := by
    intro d
    unfold depthSpace mDepthSpace
    congr 2
    ext κ
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, fun h => h3 ?_⟩
      have := (hdvd κ h1 (d + 1)).2 h
      simpa using this
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, fun h => h3 ?_⟩
      exact (hdvd κ h1 (d + 1)).1 (by simpa using h)
  have hF : fullSpace p (θ.symm f) = mFullSpace (p := p) b := by
    unfold fullSpace mFullSpace
    congr 2
    ext κ
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (hne κ h1).1 h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (hne κ h1).2 h3⟩
  have hD' : ∀ d, Module.finrank (ZMod p) (depthSpace p (θ.symm f) d)
      = Module.finrank (ZMod p) (mDepthSpace (p := p) b d) := fun d => by rw [hD]
  have hF' : Module.finrank (ZMod p) (fullSpace p (θ.symm f))
      = Module.finrank (ZMod p) (mFullSpace (p := p) b) := by rw [hF]
  simp only [flagValue, rankF, flagJump, depthFlag, hD', hF', mFlagValue, mRank, mJump, mFlag]

/-- **R-086 Theorem M, origin type, in the note's wording**: if `f = ∑_{c digit} m ^ c b_c` with
`b_c ∈ B` (`m ^ c = θ(x ^ c)`), the flag formula holds with class `c` of depth `v_p(b_c)`. -/
theorem thmM_origin_mclasses (hσ : IsFrobLift p σ) (hσc : Continuous σ)
    (θ : MvPowerSeries (Fin n) ℤ_[p] ≃+* MvPowerSeries (Fin n) ℤ_[p]) (hθc : Continuous θ)
    (hm : ∀ i, θ (X i) ^ p ∈ σ.range)
    (b : (Fin n →₀ ℕ) → MvPowerSeries (Fin n) ℤ_[p]) (hb : ∀ c ∈ digitExps p n, b c ∈ σ.range)
    {f u : MvPowerSeries (Fin n) ℤ_[p]}
    (hf : f = ∑ c ∈ digitExps p n, θ (monomial c 1) * b c) (hfu : f * u = 1)
    {k : ℕ} (hk : 1 ≤ k) :
    levelCount p σ f k + 1 = mFlagValue (p := p) b k := by
  rw [thmM_origin hσ hσc θ hθc hm hfu hk,
    flagValue_symm_eq_mFlagValue θ (range_eq_map_frob hσ hσc θ hθc hm) b hb hf]

/-- Such a decomposition `f = ∑_{c digit} m ^ c b_c`, `b_c ∈ B`, exists for every `f`. -/
theorem exists_mDecomp (hσ : IsFrobLift p σ) (hσc : Continuous σ)
    (θ : MvPowerSeries (Fin n) ℤ_[p] ≃+* MvPowerSeries (Fin n) ℤ_[p]) (hθc : Continuous θ)
    (hm : ∀ i, θ (X i) ^ p ∈ σ.range) (f : MvPowerSeries (Fin n) ℤ_[p]) :
    ∃ b : (Fin n →₀ ℕ) → MvPowerSeries (Fin n) ℤ_[p], (∀ c ∈ digitExps p n, b c ∈ σ.range) ∧
      f = ∑ c ∈ digitExps p n, θ (monomial c 1) * b c := by
  refine ⟨fun c => θ (frob p (classPart p (θ.symm f) c)), fun c _ => ?_, ?_⟩
  · rw [range_eq_map_frob hσ hσc θ hθc hm]
    exact ⟨_, ⟨_, rfl⟩, rfl⟩
  · conv_lhs => rw [← RingEquiv.apply_symm_apply θ f, eq_sum_digit p (θ.symm f)]
    rw [map_sum]
    exact Finset.sum_congr rfl fun c _ => by rw [map_mul, mul_comm]

end MClasses

end L10
