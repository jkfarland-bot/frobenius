module

/-
Run r25, seat L7: R-084 for every unit of the Dirichlet ring with the depth flag of `f` itself,
read over ALL primes (note Theorem `thm:dirichlet`).

Definitions (note Theorem `thm:dirichlet`, Definition `def:flag` with `V = ⊕_q F_p`):
* `cls p n`: the class `κ(n) = (v_q(n) mod p)_q`, a finitely supported vector `ℕ →₀ ZMod p`
  (the coordinate `q` is used only at primes; it is `0` elsewhere).
* `witSet p f X d`: the `n ∈ X`, `n ≠ 0`, with `κ(n) ≠ 0` and `p ^ (d+1) ∤ f(n)`.
  So `κ` has a witness iff `p ^ (d+1) ∤ f_κ`, `f_κ` the restriction of `f` to the class `κ`.
* `dSpace p f X d = U_d`: the span of their classes; `fSpace p f X`: span of the classes `κ ≠ 0`
  with `f_κ ≠ 0`; `dRank p f X = r_f`: its rank as a cardinal (`ℵ₀` when infinite).
* `dFlag p f X j = d(j)` (`d(0) = 0`, `d(j)` the least `d` with `j ≤ dim U_d`).
* `dFlagValue p f X k`: the least `m` with `p ^ r_f ≤ m` (only when `r_f` is finite: `p^∞ = ∞`),
  or `k ≤ v_p(m!) + ∑_{j < r_f, j ≤ m} (d(j+1) - d(j)) ⌊m/p^j⌋`. The terms with `j > m` vanish
  (`p ^ j > m`), so this is the note's sum over `j < r_f`, also when `r_f = ∞`.
* `dirFlagValue p f k = dFlagValue p f univ k`: the flag over all primes.

Main results:
* `Dir.flagValue_res_eq`: R-083's `flagValue` of the restriction `res_q f` is `dFlagValue` with
  witnesses restricted to the `q`-smooth numbers.
* `Dir.exists_stable`: a finite set `W` of witnesses such that every `X ⊇ W` gives the same
  value as `X = univ` (needs only `a ≠ 0 → ∃ d, p ^ (d+1) ∤ a`).
* `Dir.levelCount_eq_dirFlagValue_int`, `_padic`: **R-084**: for every unit `f` of the
  Dirichlet ring over `ℤ` or `ℤ_[p]`, every prime `p` and every `k ≥ 1`,
  `L_f(p, k) + 1 = dirFlagValue p f k`.

Lean v4.33.1 with Mathlib; no sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Flag
public import Frobenius.Levels.DirBase
public import Frobenius.Levels.DirTransfer
public import Frobenius.Levels.Cap
public import Frobenius.Levels.ThmF
public import Frobenius.Levels.Padic
public import Frobenius.Levels.Assemble
public import Frobenius.Levels.Compact
public import Frobenius.Levels.Sup

@[expose] public section

-- Port (Mathlib v4.35.0-rc2): restore the v4.33 instance path for `AddCommGroup (ZMod p)`.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace FrobLevel

namespace Dir

open MvPowerSeries

section Defs

variable (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R]

/-- The class `κ(n) = (v_q(n) mod p)_q`. -/
noncomputable def cls (n : ℕ) : ℕ →₀ ZMod p :=
  Finsupp.mapRange (fun a : ℕ => (a : ZMod p)) Nat.cast_zero n.factorization

theorem cls_apply (n r : ℕ) : cls p n r = (n.factorization r : ZMod p) :=
  Finsupp.mapRange_apply

/-- Witnesses of depth `≤ d` in `X`: `n ∈ X`, `n ≠ 0`, `κ(n) ≠ 0`, `p ^ (d+1) ∤ f(n)`. -/
def witSet (f : ArithmeticFunction R) (X : Set ℕ) (d : ℕ) : Set ℕ :=
  {n | n ∈ X ∧ n ≠ 0 ∧ cls p n ≠ 0 ∧ ¬ (p : R) ^ (d + 1) ∣ f n}

/-- Witnesses of a nonzero class part: `n ∈ X`, `n ≠ 0`, `κ(n) ≠ 0`, `f(n) ≠ 0`. -/
def fullWit (f : ArithmeticFunction R) (X : Set ℕ) : Set ℕ :=
  {n | n ∈ X ∧ n ≠ 0 ∧ cls p n ≠ 0 ∧ f n ≠ 0}

/-- `U_d`, read from witnesses in `X`. -/
noncomputable def dSpace (f : ArithmeticFunction R) (X : Set ℕ) (d : ℕ) :
    Submodule (ZMod p) (ℕ →₀ ZMod p) :=
  Submodule.span (ZMod p) (cls p '' witSet p f X d)

/-- The span of the classes `κ ≠ 0` with `f_κ ≠ 0`, read from witnesses in `X`. -/
noncomputable def fSpace (f : ArithmeticFunction R) (X : Set ℕ) :
    Submodule (ZMod p) (ℕ →₀ ZMod p) :=
  Submodule.span (ZMod p) (cls p '' fullWit p f X)

/-- `r_f` as a cardinal (finite or `ℵ₀`). -/
noncomputable def dRank (f : ArithmeticFunction R) (X : Set ℕ) : Cardinal :=
  Module.rank (ZMod p) (fSpace p f X)

/-- The depth flag `d(j)`, `d(0) = 0`. -/
noncomputable def dFlag (f : ArithmeticFunction R) (X : Set ℕ) (j : ℕ) : ℕ :=
  if j = 0 then 0 else sInf {d | (j : Cardinal) ≤ Module.rank (ZMod p) (dSpace p f X d)}

/-- The right side of the depth-flag formula, with `p ^ ∞ = ∞`. -/
noncomputable def dFlagValue (f : ArithmeticFunction R) (X : Set ℕ) (k : ℕ) : ℕ :=
  sInf {m | (∃ r : ℕ, dRank p f X = r ∧ p ^ r ≤ m) ∨
    k ≤ padicValNat p m.factorial +
      ∑ j ∈ (Finset.range (m + 1)).filter (fun j : ℕ => ((j : ℕ) : Cardinal) < dRank p f X),
        (dFlag p f X (j + 1) - dFlag p f X j) * (m / p ^ j)}

/-- **The Dirichlet depth-flag value**, the flag read over all primes. -/
noncomputable abbrev dirFlagValue (f : ArithmeticFunction R) (k : ℕ) : ℕ :=
  dFlagValue p f Set.univ k

end Defs

section Transport

variable (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R] {n : ℕ} {q : Fin n → ℕ}

/-- The `q`-smooth numbers. -/
def smoothSet (q : Fin n → ℕ) : Set ℕ := {m | ∃ e, smoothNum q e = m}

/-- `v ↦ ∑_i v_i e_(q_i)`. -/
noncomputable def psi (q : Fin n → ℕ) : (Fin n → ZMod p) →ₗ[ZMod p] (ℕ →₀ ZMod p) :=
  ∑ i, (Finsupp.lsingle (q i)).comp (LinearMap.proj i)

theorem psi_apply (v : Fin n → ZMod p) (r : ℕ) :
    psi p q v r = ∑ i, if q i = r then v i else 0 := by
  simp [psi, Finsupp.single_apply]

theorem psi_injective (hinj : Function.Injective q) : Function.Injective (psi p q) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  funext j
  have := congrArg (fun w : ℕ →₀ ZMod p => w (q j)) hv
  simp only [psi_apply, Finsupp.coe_zero, Pi.zero_apply, hinj.eq_iff] at this
  simpa using this

variable (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q)
include hq

theorem cls_smoothNum (e : Fin n →₀ ℕ) : cls p (smoothNum q e) = psi p q (classVec p e) := by
  ext r
  rw [cls_apply, psi_apply, factorization_smoothNum hq, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [classVec]

omit hq in
theorem classVec_ne_zero {κ : Fin n →₀ ℕ} (hκ : κ ∈ digitExps p n) (h0 : κ ≠ 0) :
    classVec p κ ≠ 0 := by
  intro h
  apply h0
  ext i
  have hi := congrFun h i
  simp only [classVec, Pi.zero_apply, ZMod.natCast_eq_zero_iff] at hi
  have hlt := (mem_digitExps p n).1 hκ i
  simpa using Nat.eq_zero_of_dvd_of_lt hi hlt

omit hq hp in
theorem pow_dvd_mv_iff (c : ℕ) (a : MvPowerSeries (Fin n) R) :
    (p : MvPowerSeries (Fin n) R) ^ c ∣ a ↔ ∀ e, (p : R) ^ c ∣ coeff e a := by
  have hC : (p : MvPowerSeries (Fin n) R) ^ c = C ((p : R) ^ c) := by
    rw [map_pow, map_natCast]
  rw [hC]
  exact ⟨fun h e => coeff_dvd_of_dvd h e, fun h => C_dvd_of_coeff h⟩

include hinj

/-- The classes of the restriction's witnesses are the classes of the `q`-smooth witnesses. -/
theorem psi_image_depth (f : ArithmeticFunction R) (d : ℕ) :
    psi p q '' (classVec p '' {κ | κ ∈ digitExps p n ∧ κ ≠ 0 ∧
      ¬ (p : MvPowerSeries (Fin n) R) ^ (d + 1) ∣ classPart p (res hq hinj f) κ}) =
      cls p '' witSet p f (smoothSet q) d := by
  ext v
  constructor
  · rintro ⟨_, ⟨κ, ⟨hκd, hκ0, hdiv⟩, rfl⟩, rfl⟩
    rw [pow_dvd_mv_iff] at hdiv
    push Not at hdiv
    obtain ⟨d', hd'⟩ := hdiv
    rw [coeff_classPart, coeff_res] at hd'
    refine ⟨smoothNum q (p • d' + κ), ⟨⟨_, rfl⟩, smoothNum_ne_zero hq _, ?_, hd'⟩, ?_⟩
    · rw [cls_smoothNum p hq, classVec_smul_add]
      exact fun h => classVec_ne_zero p hκd hκ0 (psi_injective p hinj (by rw [h, map_zero]))
    · rw [cls_smoothNum p hq, classVec_smul_add]
  · rintro ⟨m, ⟨⟨e, rfl⟩, hm0, hcls, hdv⟩, rfl⟩
    refine ⟨classVec p (lowDigits p e), ⟨lowDigits p e, ⟨lowDigits_mem p e, ?_, ?_⟩, rfl⟩, ?_⟩
    · intro h
      apply hcls
      rw [cls_smoothNum p hq, ← classVec_lowDigits, h]
      have : classVec p (0 : Fin n →₀ ℕ) = 0 := by funext i; simp [classVec]
      rw [this, map_zero]
    · rw [pow_dvd_mv_iff]
      intro h
      apply hdv
      have := h (highPart p e)
      rwa [coeff_classPart, split_exp, coeff_res] at this
    · rw [cls_smoothNum p hq, classVec_lowDigits]

/-- The same for the full span. -/
theorem psi_image_full (f : ArithmeticFunction R) :
    psi p q '' (classVec p '' {κ | κ ∈ digitExps p n ∧ κ ≠ 0 ∧
      classPart p (res hq hinj f) κ ≠ 0}) = cls p '' fullWit p f (smoothSet q) := by
  ext v
  constructor
  · rintro ⟨_, ⟨κ, ⟨hκd, hκ0, hne⟩, rfl⟩, rfl⟩
    have : ∃ d', coeff d' (classPart p (res hq hinj f) κ) ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hne (MvPowerSeries.ext hc)
    obtain ⟨d', hd'⟩ := this
    rw [coeff_classPart, coeff_res] at hd'
    refine ⟨smoothNum q (p • d' + κ), ⟨⟨_, rfl⟩, smoothNum_ne_zero hq _, ?_, hd'⟩, ?_⟩
    · rw [cls_smoothNum p hq, classVec_smul_add]
      exact fun h => classVec_ne_zero p hκd hκ0 (psi_injective p hinj (by rw [h, map_zero]))
    · rw [cls_smoothNum p hq, classVec_smul_add]
  · rintro ⟨m, ⟨⟨e, rfl⟩, hm0, hcls, hdv⟩, rfl⟩
    refine ⟨classVec p (lowDigits p e), ⟨lowDigits p e, ⟨lowDigits_mem p e, ?_, ?_⟩, rfl⟩, ?_⟩
    · intro h
      apply hcls
      rw [cls_smoothNum p hq, ← classVec_lowDigits, h]
      have : classVec p (0 : Fin n →₀ ℕ) = 0 := by funext i; simp [classVec]
      rw [this, map_zero]
    · intro h
      apply hdv
      have := congrArg (coeff (highPart p e)) h
      rwa [coeff_classPart, split_exp, coeff_res, map_zero] at this
    · rw [cls_smoothNum p hq, classVec_lowDigits]

theorem rank_dSpace_smooth (f : ArithmeticFunction R) (d : ℕ) :
    Module.rank (ZMod p) (dSpace p f (smoothSet q) d) =
      (Module.finrank (ZMod p) (depthSpace p (res hq hinj f) d) : Cardinal) := by
  have hmap : dSpace p f (smoothSet q) d = (depthSpace p (res hq hinj f) d).map (psi p q) := by
    rw [dSpace, depthSpace, Submodule.map_span, psi_image_depth p hq hinj]
  rw [hmap, ← (Submodule.equivMapOfInjective _ (psi_injective p hinj) _).rank_eq,
    Module.finrank_eq_rank]

theorem rank_fSpace_smooth (f : ArithmeticFunction R) :
    dRank p f (smoothSet q) = (rankF p (res hq hinj f) : Cardinal) := by
  have hmap : fSpace p f (smoothSet q) = (fullSpace p (res hq hinj f)).map (psi p q) := by
    rw [fSpace, fullSpace, Submodule.map_span, psi_image_full p hq hinj]
  rw [dRank, rankF, hmap, ← (Submodule.equivMapOfInjective _ (psi_injective p hinj) _).rank_eq,
    Module.finrank_eq_rank]

omit hq hinj in
theorem sum_range_eq_filter (g : ℕ → ℕ) (r m : ℕ) (hg : ∀ j, m < j → g j = 0) :
    ∑ j ∈ Finset.range r, g j =
      ∑ j ∈ (Finset.range (m + 1)).filter (fun j : ℕ => ((j : ℕ) : Cardinal) < r), g j := by
  have h1 : ∑ j ∈ Finset.range r, g j =
      ∑ j ∈ (Finset.range r).filter (fun j => j < m + 1), g j := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with h
    · rfl
    · exact hg j (by omega)
  rw [h1]
  apply Finset.sum_congr
  · ext j; simp only [Finset.mem_filter, Finset.mem_range, Nat.cast_lt]; omega
  · intro _ _; rfl

/-- **R-083's value of a restriction is the Dirichlet value read on `q`-smooth witnesses.** -/
theorem flagValue_res_eq (f : ArithmeticFunction R) (k : ℕ) :
    flagValue p (res hq hinj f) k = dFlagValue p f (smoothSet q) k := by
  have hr := rank_fSpace_smooth p hq hinj f
  have hD : ∀ j, dFlag p f (smoothSet q) j = depthFlag p (res hq hinj f) j := by
    intro j
    unfold dFlag depthFlag
    split_ifs
    · rfl
    · congr 1
      ext d
      simp only [Set.mem_setOf_eq, rank_dSpace_smooth p hq hinj, Nat.cast_le]
  unfold flagValue dFlagValue
  congr 1
  ext m
  simp only [Set.mem_setOf_eq, hr, hD, Nat.cast_inj, exists_eq_left']
  rw [sum_range_eq_filter _ (rankF p (res hq hinj f)) m]
  · rfl
  · intro j hj
    rw [Nat.div_eq_of_lt (lt_of_lt_of_le hj (Nat.lt_pow_self hp.out.one_lt).le), mul_zero]

end Transport

section Stable

variable (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R]

theorem witSet_mono {f : ArithmeticFunction R} {X Y : Set ℕ} (h : X ⊆ Y) (d : ℕ) :
    witSet p f X d ⊆ witSet p f Y d := fun _ ⟨h1, h2⟩ => ⟨h h1, h2⟩

theorem witSet_mono_d {f : ArithmeticFunction R} {X : Set ℕ} {d d' : ℕ} (h : d ≤ d') :
    witSet p f X d ⊆ witSet p f X d' := fun _ ⟨h1, h2, h3, h4⟩ =>
  ⟨h1, h2, h3, fun h' => h4 ((pow_dvd_pow _ (by omega)).trans h')⟩

theorem witSet_sub_full {f : ArithmeticFunction R} {X : Set ℕ} (d : ℕ) :
    witSet p f X d ⊆ fullWit p f X := fun n ⟨h1, h2, h3, h4⟩ =>
  ⟨h1, h2, h3, fun h => h4 (by rw [h]; exact dvd_zero _)⟩

theorem fullWit_mono {f : ArithmeticFunction R} {X Y : Set ℕ} (h : X ⊆ Y) :
    fullWit p f X ⊆ fullWit p f Y := fun _ ⟨h1, h2⟩ => ⟨h h1, h2⟩

/-- A family of `j` independent classes inside a span is reached by finitely many witnesses. -/
theorem exists_finite_wit (W : Set ℕ) {j : ℕ}
    (h : (j : Cardinal) ≤ Module.rank (ZMod p) (Submodule.span (ZMod p) (cls p '' W))) :
    ∃ W' ⊆ W, W'.Finite ∧
      (j : Cardinal) ≤ Module.rank (ZMod p) (Submodule.span (ZMod p) (cls p '' W')) := by
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent (ZMod p) (cls p '' W)
  have hli' : LinearIndepOn (ZMod p) id b := hli
  rw [← hspan, rank_span_set hli'] at h
  obtain ⟨t, htb, hct⟩ := Cardinal.le_mk_iff_exists_subset.1 h
  have htfin : t.Finite := by
    rw [← Cardinal.lt_aleph0_iff_set_finite, hct]; exact Cardinal.natCast_lt_aleph0
  have : ∃ t' ⊆ cls p '' W, t'.Finite ∧
      (j : Cardinal) ≤ Module.rank (ZMod p) (Submodule.span (ZMod p) t') :=
    ⟨t, htb.trans hbs, htfin, by rw [rank_span_set (hli'.mono htb), hct]⟩
  exact Set.exists_subset_image_finite_and.1 this

/-- Over a `p`-adically separated ring, `r_f ≥ j` gives some `U_d` of dimension `≥ j`. -/
theorem exists_depth_of_rank (hsep : ∀ a : R, a ≠ 0 → ∃ d, ¬ (p : R) ^ (d + 1) ∣ a)
    (f : ArithmeticFunction R) (X : Set ℕ) {j : ℕ} (h : (j : Cardinal) ≤ dRank p f X) :
    ∃ d, (j : Cardinal) ≤ Module.rank (ZMod p) (dSpace p f X d) := by
  obtain ⟨W', hW', hfin, hj⟩ := exists_finite_wit p (fullWit p f X) h
  have hd : ∀ w ∈ W', ∃ d, w ∈ witSet p f X d := by
    intro w hw
    obtain ⟨h1, h2, h3, h4⟩ := hW' hw
    obtain ⟨d, hd⟩ := hsep _ h4
    exact ⟨d, h1, h2, h3, hd⟩
  choose! D hD using hd
  refine ⟨hfin.toFinset.sup D, hj.trans (Submodule.rank_mono (Submodule.span_mono ?_))⟩
  apply Set.image_mono
  intro w hw
  exact witSet_mono_d p (Finset.le_sup (f := D) (hfin.mem_toFinset.2 hw)) (hD w hw)

theorem sInf_congr_of_le {A B : Set ℕ} {m : ℕ} (hm : m ∈ A) (hmA : sInf A = m)
    (h : ∀ x ≤ m, x ∈ B ↔ x ∈ A) : sInf B = sInf A := by
  have hmB : m ∈ B := (h m le_rfl).2 hm
  have h1 : sInf B ≤ m := Nat.sInf_le hmB
  have h2 : sInf B ∈ A := (h _ h1).1 (Nat.sInf_mem ⟨m, hmB⟩)
  rw [hmA]
  exact le_antisymm h1 (hmA ▸ Nat.sInf_le h2)

/-- **Stabilization.** Over a `p`-adically separated ring there is a finite set `W` of nonzero
witnesses such that every `X ⊇ W` gives the same flag value as all of `ℕ`. -/
theorem exists_stable (hsep : ∀ a : R, a ≠ 0 → ∃ d, ¬ (p : R) ^ (d + 1) ∣ a)
    (f : ArithmeticFunction R) (k : ℕ) :
    ∃ W : Set ℕ, W.Finite ∧ (∀ w ∈ W, w ≠ 0) ∧
      ∀ X, W ⊆ X → dFlagValue p f X k = dirFlagValue p f k := by
  classical
  set A : Set ℕ := {m | (∃ r : ℕ, dRank p f Set.univ = r ∧ p ^ r ≤ m) ∨
    k ≤ padicValNat p m.factorial +
      ∑ j ∈ (Finset.range (m + 1)).filter (fun j : ℕ => ((j : ℕ) : Cardinal) < dRank p f Set.univ),
        (dFlag p f Set.univ (j + 1) - dFlag p f Set.univ j) * (m / p ^ j)} with hA
  have hAne : kempner p k ∈ A := Or.inr ((kempner_spec p k).trans (Nat.le_add_right _ _))
  set ms := sInf A with hms
  have hmsA : ms ∈ A := Nat.sInf_mem ⟨_, hAne⟩
  set r := dRank p f Set.univ with hr
  -- the number `J` of flag entries that matter
  obtain ⟨J, hJr, hcase⟩ : ∃ J : ℕ, (J : Cardinal) ≤ r ∧ (r = J ∨ J = ms + 1) := by
    by_cases h : r < ((ms + 1 : ℕ) : Cardinal)
    · obtain ⟨J, hJ⟩ := Cardinal.lt_aleph0.1 (h.trans Cardinal.natCast_lt_aleph0)
      exact ⟨J, hJ.symm.le, Or.inl hJ⟩
    · exact ⟨ms + 1, not_lt.1 h, Or.inr rfl⟩
  -- witnesses for `j ≤ J`
  have hex : ∀ j ∈ Finset.Icc 1 J, ∃ W ⊆ witSet p f Set.univ (dFlag p f Set.univ j), W.Finite ∧
      (j : Cardinal) ≤ Module.rank (ZMod p) (Submodule.span (ZMod p) (cls p '' W)) := by
    intro j hj
    have hj' := Finset.mem_Icc.1 hj
    have hjr : (j : Cardinal) ≤ r := (Nat.cast_le.2 hj'.2).trans hJr
    obtain ⟨d, hd⟩ := exists_depth_of_rank p hsep f Set.univ hjr
    have hmem : dFlag p f Set.univ j ∈
        {d | (j : Cardinal) ≤ Module.rank (ZMod p) (dSpace p f Set.univ d)} := by
      rw [dFlag, if_neg (by omega)]
      exact Nat.sInf_mem ⟨d, hd⟩
    exact exists_finite_wit p _ hmem
  choose! Wj hWsub hWfin hWrank using hex
  refine ⟨⋃ j ∈ (Finset.Icc 1 J : Set ℕ), Wj j, Set.Finite.biUnion (Finset.finite_toSet _)
    fun j hj => hWfin j hj, ?_, ?_⟩
  · intro w hw
    simp only [Set.mem_iUnion] at hw
    obtain ⟨j, hj, hw⟩ := hw
    exact (hWsub j hj hw).2.1
  intro X hWX
  have hXu : X ⊆ Set.univ := Set.subset_univ X
  -- ranks of `U_d` in `X` and in `univ`
  have hrkle : ∀ d, Module.rank (ZMod p) (dSpace p f X d) ≤
      Module.rank (ZMod p) (dSpace p f Set.univ d) :=
    fun d => Submodule.rank_mono (Submodule.span_mono (Set.image_mono (witSet_mono p hXu d)))
  have hrkge : ∀ j ∈ Finset.Icc 1 J,
      (j : Cardinal) ≤ Module.rank (ZMod p) (dSpace p f X (dFlag p f Set.univ j)) := by
    intro j hj
    refine (hWrank j hj).trans (Submodule.rank_mono (Submodule.span_mono (Set.image_mono ?_)))
    intro w hw
    have h1 := hWsub j hj hw
    have h2 : w ∈ X := hWX (Set.mem_biUnion (Finset.mem_coe.2 hj) hw)
    exact ⟨h2, h1.2⟩
  -- the flags agree on `1..J`
  have hflag : ∀ j ≤ J, dFlag p f X j = dFlag p f Set.univ j := by
    intro j hjJ
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp [dFlag]
    have hj : j ∈ Finset.Icc 1 J := Finset.mem_Icc.2 ⟨hj0, hjJ⟩
    rw [dFlag, dFlag, if_neg (by omega), if_neg (by omega)]
    have hsub : {d | (j : Cardinal) ≤ Module.rank (ZMod p) (dSpace p f X d)} ⊆
        {d | (j : Cardinal) ≤ Module.rank (ZMod p) (dSpace p f Set.univ d)} :=
      fun d hd => (show (j : Cardinal) ≤ _ from hd).trans (hrkle d)
    have hin : dFlag p f Set.univ j ∈
        {d | (j : Cardinal) ≤ Module.rank (ZMod p) (dSpace p f X d)} := hrkge j hj
    rw [dFlag, if_neg (by omega)] at hin
    exact le_antisymm (Nat.sInf_le hin) (csInf_le_csInf (OrderBot.bddBelow _) ⟨_, hin⟩ hsub)
  -- ranks
  have hrX : dRank p f X ≤ r :=
    Submodule.rank_mono (Submodule.span_mono (Set.image_mono (fullWit_mono p hXu)))
  have hrXJ : (J : Cardinal) ≤ dRank p f X := by
    rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
    · rw [hJ0, Nat.cast_zero]; exact zero_le
    have := hrkge J (Finset.mem_Icc.2 ⟨hJ0, le_rfl⟩)
    refine this.trans (Submodule.rank_mono (Submodule.span_mono (Set.image_mono ?_)))
    exact witSet_sub_full p _
  -- the predicates agree below `ms`
  show sInf _ = sInf A
  refine sInf_congr_of_le hmsA rfl ?_
  intro m hm
  simp only [Set.mem_setOf_eq, hA]
  rcases hcase with hrJ | hJ
  · -- finite rank `J`
    have hXJ : dRank p f X = J := le_antisymm (hrX.trans hrJ.le) hrXJ
    rw [hXJ, hrJ]
    have hsum : ∑ j ∈ (Finset.range (m + 1)).filter (fun j : ℕ => ((j : ℕ) : Cardinal) < (J : Cardinal)),
        (dFlag p f X (j + 1) - dFlag p f X j) * (m / p ^ j) =
        ∑ j ∈ (Finset.range (m + 1)).filter (fun j : ℕ => ((j : ℕ) : Cardinal) < (J : Cardinal)),
        (dFlag p f Set.univ (j + 1) - dFlag p f Set.univ j) * (m / p ^ j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjJ : j < J := by
        have := (Finset.mem_filter.1 hj).2; exact_mod_cast this
      rw [hflag (j + 1) (by omega), hflag j (by omega)]
    rw [hsum]
  · -- rank at least `ms + 1`
    subst hJ
    have hno : ∀ s : Cardinal, ((ms + 1 : ℕ) : Cardinal) ≤ s → ¬ ∃ r' : ℕ, s = r' ∧ p ^ r' ≤ m := by
      rintro s hs ⟨r', rfl, hr'⟩
      have h1 : ms + 1 ≤ r' := by exact_mod_cast hs
      have h2 := Nat.lt_pow_self (n := r') hp.out.one_lt
      omega
    have hfilt : ∀ s : Cardinal, ((ms + 1 : ℕ) : Cardinal) ≤ s →
        (Finset.range (m + 1)).filter (fun j : ℕ => ((j : ℕ) : Cardinal) < s) = Finset.range (m + 1) := by
      intro s hs
      apply Finset.filter_true_of_mem
      intro j hj
      have : j < ms + 1 := by have := Finset.mem_range.1 hj; omega
      exact lt_of_lt_of_le (by exact_mod_cast this) hs
    rw [hfilt _ hrXJ, hfilt _ hJr]
    have hsum : ∑ j ∈ Finset.range (m + 1), (dFlag p f X (j + 1) - dFlag p f X j) * (m / p ^ j) =
        ∑ j ∈ Finset.range (m + 1),
          (dFlag p f Set.univ (j + 1) - dFlag p f Set.univ j) * (m / p ^ j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have := Finset.mem_range.1 hj
      rw [hflag (j + 1) (by omega), hflag j (by omega)]
    rw [hsum]
    constructor
    · rintro (h | h)
      · exact absurd h (hno _ hrXJ)
      · exact Or.inr h
    · rintro (h | h)
      · exact absurd h (hno _ hJr)
      · exact Or.inr h

end Stable

section Main

variable (p : ℕ) [hp : Fact p.Prime]

theorem int_sep (a : ℤ) (ha : a ≠ 0) : ∃ d, ¬ (p : ℤ) ^ (d + 1) ∣ a := by
  refine ⟨a.natAbs, fun h => ?_⟩
  have h1 := Int.natAbs_dvd_natAbs.2 h
  rw [Int.natAbs_pow, Int.natAbs_natCast] at h1
  have h2 := Nat.le_of_dvd (Int.natAbs_pos.2 ha) h1
  have h3 := Nat.lt_pow_self (n := a.natAbs + 1) hp.out.one_lt
  omega

theorem padic_sep (a : ℤ_[p]) (ha : a ≠ 0) : ∃ d, ¬ (p : ℤ_[p]) ^ (d + 1) ∣ a := by
  refine ⟨a.valuation, fun h => ?_⟩
  have : a ∈ Ideal.span {(p : ℤ_[p]) ^ (a.valuation + 1)} := Ideal.mem_span_singleton.2 h
  rw [PadicInt.mem_span_pow_iff_le_valuation a ha] at this
  omega

/-- The stable witnesses give a finite set of primes `T`; every family containing `T` has
R-083 value `dirFlagValue`. -/
theorem exists_stable_primes {R : Type*} [CommRing R]
    (hsep : ∀ a : R, a ≠ 0 → ∃ d, ¬ (p : R) ^ (d + 1) ∣ a) (f : ArithmeticFunction R) (k : ℕ) :
    ∃ T : Finset ℕ, (∀ t ∈ T, t.Prime) ∧
      ∀ (n : ℕ) (q : Fin n → ℕ) (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q),
        (∀ t ∈ T, ∃ i, q i = t) → flagValue p (res hq hinj f) k = dirFlagValue p f k := by
  obtain ⟨W, hWfin, hW0, hst⟩ := exists_stable p hsep f k
  refine ⟨hWfin.toFinset.biUnion Nat.primeFactors, ?_, ?_⟩
  · intro t ht
    obtain ⟨w, _, hw⟩ := Finset.mem_biUnion.1 ht
    exact Nat.prime_of_mem_primeFactors hw
  intro n q hq hinj hT
  rw [flagValue_res_eq p hq hinj]
  apply hst
  intro w hw
  refine ⟨_, smoothNum_expOf_of_primes hq hinj (hW0 w hw) ?_⟩
  intro r hr hrw
  apply hT
  exact Finset.mem_biUnion.2 ⟨w, hWfin.mem_toFinset.2 hw,
    Nat.mem_primeFactors.2 ⟨hr, hrw, hW0 w hw⟩⟩

/-- **R-084 over `ℤ`**: for every unit `f` of the Dirichlet ring over `ℤ` (that is, `f(1) = ±1`),
every prime `p` and every `k ≥ 1`, `L_f(p, k) + 1` is the depth-flag value of `f`, with the flag
read over all primes (`r_f` finite or infinite). -/
theorem levelCount_eq_dirFlagValue_int {f : ArithmeticFunction ℤ} (hf : IsUnit f) {k : ℕ}
    (hk : 1 ≤ k) : levelCount p (Ep p) f k + 1 = dirFlagValue p f k := by
  obtain ⟨T, hT, hval⟩ := exists_stable_primes p (int_sep p) f k
  apply le_antisymm
  · exact levelCount_le_of_flagValue_res_int p hf hk T hT
      fun n q hq hinj hTq => (hval n q hq hinj hTq).le
  · have hq := coverSet_prime (N := 0) hT
    rw [← hval _ _ hq (enum_injective _) (fun t ht => coverSet_contains 0 T ht)]
    exact flagValue_res_le_int p hq (enum_injective _) hf hk

/-- **R-084 over `ℤ_[p]`**: for every unit `f` of the Dirichlet ring over `ℤ_[p]` (that is,
`f(1)` a unit), every prime `p` and every `k ≥ 1`, `L_f(p, k) + 1 = dirFlagValue p f k`. -/
theorem levelCount_eq_dirFlagValue_padic {f : ArithmeticFunction ℤ_[p]} (hf : IsUnit f) {k : ℕ}
    (hk : 1 ≤ k) : levelCount p (Ep p) f k + 1 = dirFlagValue p f k := by
  obtain ⟨T, hT, hval⟩ := exists_stable_primes p (padic_sep p) f k
  apply le_antisymm
  · exact levelCount_le_of_flagValue_res_padic p hf hk T hT
      fun n q hq hinj hTq => (hval n q hq hinj hTq).le
  · have hq := coverSet_prime (N := 0) hT
    rw [← hval _ _ hq (enum_injective _) (fun t ht => coverSet_contains 0 T ht)]
    exact flagValue_res_le_padic p hq (enum_injective _) hf hk

end Main

end Dir

end FrobLevel
