module

/-
Run r25, seat L5: Theorem F of R-083 in valuation form, and R-083 for every unit of `ℤ[[x]]`.

* `delta_step`: `T' = T ^ p - p ^ (p γ) σ(w)` (with `T(u) = p ^ γ w`) is monic of degree `p deg T`
  in `B[X]` with `p ^ (p γ + 1) ∣ T'(u)` (any ring with a Frobenius lift).
* `strictSpace p f ξ`: the span of the classes `κ ≠ 0` with `p ^ ξ ∤ f_κ` (depth `< ξ`).
  `depthSpace p f d = strictSpace p f (d + 1)`.
* Bookkeeping for `a = projW U u`, `U = strictSpace u ξ`: its classes span `U`, its depth spaces
  are those of `u` below `ξ` and `U` above, so its flag is the first `dim U` entries of `u`'s.
* `thmF_valTower_int`: every `u ∈ ℤ[[x_1..x_n]]` has a valuation tower of length `r_u` with
  `γ = flagGamma p (flagJump p u)`: norm levels (Norm.lean) where the flag jumps (and at level 0),
  δ steps inside blocks.
* `levelCount_eq_flagValue_int`: **R-083 for every unit of `ℤ[[x_1..x_n]]`**, every prime `p`,
  every `k ≥ 1`: `L_f + 1 = min(p ^ r_f, min {m : v_p(m!) + ∑_j (d(j+1) - d(j)) ⌊m/p^j⌋ ≥ k})`.

Lean v4.33.1 with Mathlib; no sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Lower
public import Frobenius.Levels.Basis
public import Frobenius.Levels.Digit
public import Frobenius.Levels.PropP
public import Frobenius.Levels.Flag
public import Frobenius.Levels.Cap
public import Frobenius.Levels.ValTower
public import Frobenius.Levels.TraceCore
public import Frobenius.Levels.TraceFlag
public import Frobenius.Levels.Norm

@[expose] public section

namespace FrobLevel

open MvPowerSeries

open scoped Classical

/-! ## δ steps -/

section Delta

open Polynomial

variable {A : Type*} [CommRing A] [Nontrivial A] {p : ℕ} [hp : Fact p.Prime] {σ : A →+* A}

theorem delta_step (h : IsFrobLift p σ) {T : A[X]} (hm : T.Monic) {q : ℕ} (hq : 1 ≤ q)
    (hd : T.natDegree = q) (hB : T ∈ BPoly σ) {γ : ℕ} {u : A} (hdiv : (p : A) ^ γ ∣ T.eval u) :
    ∃ T' : A[X], T'.Monic ∧ T'.natDegree = p * q ∧ T' ∈ BPoly σ ∧
      (p : A) ^ (p * γ + 1) ∣ T'.eval u := by
  obtain ⟨w, hw⟩ := hdiv
  have hdeg : (T ^ p).natDegree = p * q := by rw [hm.natDegree_pow, hd]
  have hpos : 0 < p * q := Nat.mul_pos hp.out.pos hq
  refine ⟨T ^ p - Polynomial.C (σ ((p : A) ^ (p * γ) * w)), ?_, ?_, ?_, ?_⟩
  · refine (hm.pow p).sub_of_left (lt_of_le_of_lt degree_C_le ?_)
    rw [Polynomial.degree_eq_natDegree (hm.pow p).ne_zero, hdeg]
    exact_mod_cast hpos
  · rw [natDegree_sub_C, hdeg]
  · exact sub_mem (pow_mem hB p) (C_mem_BPoly σ _)
  · obtain ⟨t, ht⟩ := h w
    rw [eval_sub, eval_pow, eval_C, hw, map_mul, map_pow, map_natCast]
    refine ⟨-t, ?_⟩
    have : σ w = w ^ p + p * t := by rw [← ht]; ring
    rw [this, mul_pow, ← pow_mul, mul_comm γ p, pow_succ]
    ring

end Delta

/-! ## Strict depth spaces and the `U`-part -/

section Strict

variable (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R] {n : ℕ}

/-- The span of the classes `κ ≠ 0` with `p ^ ξ ∤ f_κ`. -/
noncomputable def strictSpace (f : MvPowerSeries (Fin n) R) (ξ : ℕ) :
    Submodule (ZMod p) (Fin n → ZMod p) :=
  Submodule.span (ZMod p) (classVec p '' {κ | κ ∈ digitExps p n ∧ κ ≠ 0 ∧
    ¬ (p : MvPowerSeries (Fin n) R) ^ ξ ∣ classPart p f κ})

theorem strictSpace_succ (f : MvPowerSeries (Fin n) R) (d : ℕ) :
    strictSpace p f (d + 1) = depthSpace p f d := rfl

theorem strictSpace_zero (f : MvPowerSeries (Fin n) R) : strictSpace p f 0 = ⊥ := by
  rw [strictSpace, Submodule.span_eq_bot]
  rintro _ ⟨κ, ⟨_, _, h⟩, rfl⟩
  exact absurd (by rw [pow_zero]; exact one_dvd _) h

theorem strictSpace_le_iff {W : Submodule (ZMod p) (Fin n → ZMod p)} {f : MvPowerSeries (Fin n) R}
    {ξ : ℕ} : strictSpace p f ξ ≤ W ↔ WDiv p W ((p : R) ^ ξ) f := by
  constructor
  · intro h m hm
    rw [coeff_eq_classPart p f m]
    set e := lowDigits p m
    have he : classVec p e ∉ W := by rwa [classVec_lowDigits]
    have hdiv : (p : MvPowerSeries (Fin n) R) ^ ξ ∣ classPart p f e := by
      by_contra hnd
      have he0 : e ≠ 0 := by
        intro h0; apply he; rw [h0, classVec_zero]; exact W.zero_mem
      exact he (h (Submodule.subset_span ⟨e, ⟨lowDigits_mem p m, he0, hnd⟩, rfl⟩))
    rw [natCast_pow_eq_C] at hdiv
    obtain ⟨q, hq⟩ := hdiv
    rw [hq, coeff_C_mul]
    exact dvd_mul_right _ _
  · intro h
    refine Submodule.span_le.2 ?_
    rintro _ ⟨κ, ⟨_, _, hnd⟩, rfl⟩
    by_contra hW
    apply hnd
    rw [natCast_pow_eq_C]
    refine C_dvd_of_coeff fun q => ?_
    rw [coeff_classPart]
    exact h _ (by rwa [classVec_smul_add])

theorem classPart_projW (W : Submodule (ZMod p) (Fin n → ZMod p)) (f : MvPowerSeries (Fin n) R)
    (κ : Fin n →₀ ℕ) :
    classPart p (projW p W f) κ = if classVec p κ ∈ W then classPart p f κ else 0 := by
  ext q
  rw [coeff_classPart, coeff_projW, classVec_smul_add]
  split_ifs
  · rfl
  · rw [map_zero]

theorem strictSpace_mono (f : MvPowerSeries (Fin n) R) {ξ ξ' : ℕ} (h : ξ ≤ ξ') :
    strictSpace p f ξ ≤ strictSpace p f ξ' := by
  refine Submodule.span_mono ?_
  rintro _ ⟨κ, ⟨h1, h2, h3⟩, rfl⟩
  exact ⟨κ, ⟨h1, h2, fun h4 => h3 ((pow_dvd_pow _ h).trans h4)⟩, rfl⟩

theorem depthSpace_projW_lt (f : MvPowerSeries (Fin n) R) {ξ d : ℕ} (hd : d + 1 ≤ ξ) :
    depthSpace p (projW p (strictSpace p f ξ) f) d = depthSpace p f d := by
  unfold depthSpace
  congr 2
  ext κ
  simp only [Set.mem_ofPred_eq, classPart_projW]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, fun h4 => h3 ?_⟩
    split_ifs
    · exact h4
    · exact dvd_zero _
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, ?_⟩
    have hmem : classVec p κ ∈ strictSpace p f ξ :=
      strictSpace_mono p f hd (Submodule.subset_span ⟨κ, ⟨h1, h2, h3⟩, rfl⟩)
    rw [if_pos hmem]
    exact h3

theorem depthSpace_projW_ge (f : MvPowerSeries (Fin n) R) {ξ d : ℕ} (hd : ξ ≤ d + 1) :
    depthSpace p (projW p (strictSpace p f ξ) f) d = strictSpace p f ξ := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨κ, ⟨_, _, h3⟩, rfl⟩
    rw [classPart_projW] at h3
    split_ifs at h3 with hκ
    · exact hκ
    · exact absurd (dvd_zero _) h3
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨κ, ⟨h1, h2, h3⟩, rfl⟩
    have hmem : classVec p κ ∈ strictSpace p f ξ := Submodule.subset_span ⟨κ, ⟨h1, h2, h3⟩, rfl⟩
    refine Submodule.subset_span ⟨κ, ⟨h1, h2, ?_⟩, rfl⟩
    rw [classPart_projW, if_pos hmem]
    exact fun h4 => h3 ((pow_dvd_pow _ hd).trans h4)

theorem fullSpace_projW (f : MvPowerSeries (Fin n) R) (ξ : ℕ) :
    fullSpace p (projW p (strictSpace p f ξ) f) = strictSpace p f ξ := by
  apply le_antisymm
  · exact (fullSpace_le_iff p).2 (wDiv_projW _ f)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨κ, ⟨h1, h2, h3⟩, rfl⟩
    have hmem : classVec p κ ∈ strictSpace p f ξ := Submodule.subset_span ⟨κ, ⟨h1, h2, h3⟩, rfl⟩
    refine Submodule.subset_span ⟨κ, ⟨h1, h2, ?_⟩, rfl⟩
    rw [classPart_projW, if_pos hmem]
    intro h0; rw [h0] at h3; exact h3 (dvd_zero _)

end Strict

/-! ## The flag of `u` -/

section FlagFacts

variable (p : ℕ) [hp : Fact p.Prime] {n : ℕ}

theorem exists_depth_full_int (u : MvPowerSeries (Fin n) ℤ) :
    ∃ D0, rankF p u ≤ Module.finrank (ZMod p) (depthSpace p u D0) := by
  obtain ⟨D0, hD0⟩ := exists_depth_full p u (not_pow_dvd_int_series p)
  exact ⟨D0, Submodule.finrank_mono hD0⟩

theorem depthFlag_eq_fl (u : MvPowerSeries (Fin n) ℤ) (j : ℕ) :
    depthFlag p u j = fl (fun d => Module.finrank (ZMod p) (depthSpace p u d)) j := rfl

theorem depthFlag_mem (u : MvPowerSeries (Fin n) ℤ) {j : ℕ} (hj : j ≤ rankF p u) :
    j ≤ Module.finrank (ZMod p) (depthSpace p u (depthFlag p u j)) := by
  by_cases h0 : j = 0
  · subst h0; exact Nat.zero_le _
  · obtain ⟨D0, hD0⟩ := exists_depth_full_int p u
    have hne : ({d | j ≤ Module.finrank (ZMod p) (depthSpace p u d)} : Set ℕ).Nonempty :=
      ⟨D0, by simp only [Set.mem_ofPred_eq]; omega⟩
    have := Nat.sInf_mem hne
    have hdf : depthFlag p u j = sInf {d | j ≤ Module.finrank (ZMod p) (depthSpace p u d)} := by
      simp only [depthFlag, if_neg h0]
    rw [hdf]
    exact this

theorem depthFlag_le (u : MvPowerSeries (Fin n) ℤ) {j d : ℕ}
    (h : j ≤ Module.finrank (ZMod p) (depthSpace p u d)) : depthFlag p u j ≤ d := by
  by_cases h0 : j = 0
  · subst h0; simp [depthFlag]
  · simp only [depthFlag, if_neg h0]
    exact Nat.sInf_le h

theorem depthFlag_mono (u : MvPowerSeries (Fin n) ℤ) {j : ℕ} (hj : j < rankF p u) :
    depthFlag p u j ≤ depthFlag p u (j + 1) := by
  obtain ⟨D0, hD0⟩ := exists_depth_full_int p u
  exact fl_mono _ hD0 hj

theorem finrank_depthSpace_mono (u : MvPowerSeries (Fin n) ℤ) {d d' : ℕ} (h : d ≤ d') :
    Module.finrank (ZMod p) (depthSpace p u d) ≤ Module.finrank (ZMod p) (depthSpace p u d') :=
  Submodule.finrank_mono (depthSpace_mono p u h)

theorem sum_flagJump (u : MvPowerSeries (Fin n) ℤ) {m : ℕ} (hm : m ≤ rankF p u) :
    ∑ j ∈ Finset.range m, flagJump p u j = depthFlag p u m := by
  induction m with
  | zero => simp [depthFlag]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih (by omega), flagJump]
    have := depthFlag_mono p u (j := m) (by omega)
    omega

theorem finrank_strict_le (u : MvPowerSeries (Fin n) ℤ) {b : ℕ} (hb : b < rankF p u) :
    Module.finrank (ZMod p) (strictSpace p u (depthFlag p u (b + 1))) ≤ b := by
  set ξ := depthFlag p u (b + 1)
  rcases Nat.eq_zero_or_pos ξ with h0 | hpos
  · rw [h0, strictSpace_zero, finrank_bot]; exact Nat.zero_le _
  · obtain ⟨c, hc⟩ : ∃ c, ξ = c + 1 := ⟨ξ - 1, by omega⟩
    rw [hc, strictSpace_succ]
    by_contra hlt
    push Not at hlt
    have := depthFlag_le p u (j := b + 1) (d := c) (by omega)
    omega

theorem finrank_strict_ge (u : MvPowerSeries (Fin n) ℤ) {b : ℕ} (hb : b < rankF p u)
    (hjump : b = 0 ∨ depthFlag p u b < depthFlag p u (b + 1)) :
    b ≤ Module.finrank (ZMod p) (strictSpace p u (depthFlag p u (b + 1))) := by
  rcases hjump with h0 | hlt
  · rw [h0]; exact Nat.zero_le _
  · set ξ := depthFlag p u (b + 1)
    obtain ⟨c, hc⟩ : ∃ c, ξ = c + 1 := ⟨ξ - 1, by omega⟩
    rw [hc, strictSpace_succ]
    have h1 := depthFlag_mem p u (j := b) (by omega)
    exact h1.trans (finrank_depthSpace_mono p u (by omega))

theorem depthFlag_projW (u : MvPowerSeries (Fin n) ℤ) {b : ℕ} (hb : b < rankF p u)
    (hfr : Module.finrank (ZMod p) (strictSpace p u (depthFlag p u (b + 1))) = b) {j : ℕ}
    (hj : j ≤ b) :
    depthFlag p (projW p (strictSpace p u (depthFlag p u (b + 1))) u) j = depthFlag p u j := by
  set ξ := depthFlag p u (b + 1) with hξ
  by_cases h0 : j = 0
  · subst h0; simp [depthFlag]
  · simp only [depthFlag, if_neg h0]
    congr 1
    ext d
    simp only [Set.mem_ofPred_eq]
    by_cases hd : d + 1 ≤ ξ
    · rw [depthSpace_projW_lt p u hd]
    · rw [depthSpace_projW_ge p u (by omega), hfr]
      have h1 := depthFlag_mem p u (j := b + 1) (by omega)
      rw [← hξ] at h1
      have h2 := finrank_depthSpace_mono p u (show ξ ≤ d by omega)
      constructor
      · intro _; omega
      · intro _; exact hj

theorem charDep_projW_lt (u : MvPowerSeries (Fin n) ℤ) (ξ : ℕ)
    (φ : Module.Dual (ZMod p) (fullSpace p (projW p (strictSpace p u ξ) u))) (hφ : φ ≠ 0) :
    charDep p (projW p (strictSpace p u ξ) u) φ < ξ := by
  by_contra hge
  push Not at hge
  apply hφ
  rcases Nat.eq_zero_or_pos ξ with h0 | hpos
  · subst h0
    ext w
    have hw := (strictSpace_zero p u).le ((fullSpace_projW p u 0).le w.2)
    have hw0 : w = 0 := Subtype.ext ((Submodule.mem_bot _).1 hw)
    rw [hw0, map_zero, LinearMap.zero_apply]
  · have hlt : ξ - 1 < charDep p (projW p (strictSpace p u ξ) u) φ := by omega
    have hann := (lt_charDep_iff p hφ (ξ - 1)).1 hlt
    rw [Submodule.mem_dualAnnihilator] at hann
    ext w
    rw [LinearMap.zero_apply]
    refine hann w ?_
    simp only [Submodule.mem_comap, Submodule.subtype_apply]
    rw [depthSpace_projW_ge p u (by omega)]
    exact (fullSpace_projW p u ξ).le w.2

/-- `(p - 1) γ_b = (p - 1) d(b+1) + p ^ b - 1 + (p - 1) ∑_{j<b} δ_j (p ^ (b - j) - 1)`, in `ℤ`. -/
theorem flagGamma_mul (δ : ℕ → ℕ) (b : ℕ) :
    ((p : ℤ) - 1) * (flagGamma p δ b : ℤ)
      = ((p : ℤ) - 1) * ∑ j ∈ Finset.range (b + 1), (δ j : ℤ) + ((p : ℤ) ^ b - 1)
        + ((p : ℤ) - 1) * ∑ j ∈ Finset.range b, (δ j : ℤ) * ((p : ℤ) ^ (b - j) - 1) := by
  induction b with
  | zero => simp [flagGamma_zero]
  | succ b ih =>
    rw [flagGamma_succ]
    push_cast
    have hS : ∑ j ∈ Finset.range (b + 1), (δ j : ℤ) * ((p : ℤ) ^ (b + 1 - j) - 1)
        = (p : ℤ) * ∑ j ∈ Finset.range b, (δ j : ℤ) * ((p : ℤ) ^ (b - j) - 1)
          + ((p : ℤ) - 1) * ∑ j ∈ Finset.range (b + 1), (δ j : ℤ) := by
      have h1 : ∀ j ∈ Finset.range (b + 1), (δ j : ℤ) * ((p : ℤ) ^ (b + 1 - j) - 1)
          = (p : ℤ) * ((δ j : ℤ) * ((p : ℤ) ^ (b - j) - 1)) + ((p : ℤ) - 1) * (δ j : ℤ) := by
        intro j hj
        rw [show b + 1 - j = (b - j) + 1 by have := Finset.mem_range.1 hj; omega, pow_succ]
        ring
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        Finset.sum_range_succ (fun j => (δ j : ℤ) * ((p : ℤ) ^ (b - j) - 1)), Nat.sub_self,
        pow_zero, sub_self, mul_zero, add_zero]
    rw [hS, Finset.sum_range_succ (fun j => (δ j : ℤ)) (b + 1)]
    linear_combination (p : ℤ) * ih

end FlagFacts

/-! ## Theorem F (valuation form) and R-083 over `ℤ` -/

section ThmF

variable (p : ℕ) [hp : Fact p.Prime] {n : ℕ}

/-- The norm level at `b` (when `b = 0` or the flag jumps at `b`). -/
theorem norm_case (u : MvPowerSeries (Fin n) ℤ) {b : ℕ} (hb : b < rankF p u)
    (hjump : b = 0 ∨ depthFlag p u b < depthFlag p u (b + 1)) :
    ∃ T : Polynomial (MvPowerSeries (Fin n) ℤ), T.Monic ∧ T.natDegree = p ^ b ∧
      T ∈ BPoly (frob p) ∧
      (p : MvPowerSeries (Fin n) ℤ) ^ (flagGamma p (flagJump p u) b) ∣ T.eval u := by
  set ξ := depthFlag p u (b + 1) with hξ
  set U := strictSpace p u ξ
  set a := projW p U u
  have hfr : Module.finrank (ZMod p) U = b :=
    le_antisymm (finrank_strict_le p u hb) (finrank_strict_ge p u hb hjump)
  have hrank : rankF p a = b := by
    unfold rankF; rw [fullSpace_projW]; exact hfr
  have hjumps : ∀ j < b, flagJump p a j = flagJump p u j := fun j hj => by
    unfold flagJump
    rw [depthFlag_projW p u hb hfr (by omega), depthFlag_projW p u hb hfr (by omega)]
  have hsum : ∑ φ ∈ Finset.univ.erase (0 : Module.Dual (ZMod p) (fullSpace p a)), charDep p a φ
      = ∑ j ∈ Finset.range b, flagJump p u j * (p ^ (b - j) - 1) := by
    rw [sum_charDep, hrank]
    exact Finset.sum_congr rfl fun j hj => by rw [hjumps j (Finset.mem_range.1 hj)]
  have hξsum : ξ = ∑ j ∈ Finset.range (b + 1), flagJump p u j := (sum_flagJump p u hb).symm
  have he : (p - 1) * flagGamma p (flagJump p u) b ≤ (p - 1) * ξ + (p ^ rankF p a - 1)
      + (p - 1) * ∑ φ ∈ Finset.univ.erase (0 : Module.Dual (ZMod p) (fullSpace p a)),
        charDep p a φ := by
    rw [hsum, hrank, hξsum]
    apply le_of_eq
    have h := flagGamma_mul p (flagJump p u) b
    have hp1 : 1 ≤ p := hp.out.one_lt.le
    have hpb : 1 ≤ p ^ b := Nat.one_le_pow _ _ (by omega)
    zify [hp1, hpb]
    rw [h]
    congr 1
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have : 1 ≤ p ^ (b - j) := Nat.one_le_pow _ _ (by omega)
    push_cast [this]
    ring
  obtain ⟨T, hTm, hTd, hTB, hTu⟩ := norm_level_int p u U ξ ((strictSpace_le_iff p).1 le_rfl)
    (charDep_projW_lt p u ξ) he
  exact ⟨T, hTm, by rw [hTd, hrank], hTB, hTu⟩

/-- **Theorem F (valuation form)**: every `u ∈ ℤ[[x_1..x_n]]` has, for each `b < r_u`, a monic
`T_b ∈ B[X]` of degree `p ^ b` with `p ^ γ_b ∣ T_b(u)`, `γ` from the depth flag of `u`. -/
theorem thmF_level_int (u : MvPowerSeries (Fin n) ℤ) :
    ∀ b < rankF p u, ∃ T : Polynomial (MvPowerSeries (Fin n) ℤ), T.Monic ∧ T.natDegree = p ^ b ∧
      T ∈ BPoly (frob p) ∧
      (p : MvPowerSeries (Fin n) ℤ) ^ (flagGamma p (flagJump p u) b) ∣ T.eval u := by
  intro b
  induction b with
  | zero => intro hb; exact norm_case p u hb (Or.inl rfl)
  | succ b ih =>
    intro hb
    by_cases hj : depthFlag p u (b + 1) < depthFlag p u (b + 1 + 1)
    · exact norm_case p u hb (Or.inr hj)
    · have hmono := depthFlag_mono p u (j := b + 1) hb
      have h0 : flagJump p u (b + 1) = 0 := by unfold flagJump; omega
      obtain ⟨T, hTm, hTd, hTB, hTu⟩ := ih (by omega)
      obtain ⟨T', h1, h2, h3, h4⟩ := delta_step (frob_isFrobLift p (int_pow_sub p)) hTm
        (Nat.one_le_pow _ _ hp.out.pos) hTd hTB hTu
      refine ⟨T', h1, by rw [h2, pow_succ, mul_comm], h3, ?_⟩
      rw [flagGamma_succ, h0, add_zero]
      exact h4

theorem thmF_valTower_int (u : MvPowerSeries (Fin n) ℤ) :
    ∃ T : ℕ → Polynomial (MvPowerSeries (Fin n) ℤ),
      ValTower p (frob p) (rankF p u) T (flagGamma p (flagJump p u)) u := by
  choose! T hT using thmF_level_int p u
  exact ⟨T, fun b hb => hT b hb⟩

/-- **R-083 for every unit of `ℤ[[x_1..x_n]]`** (`σ(x_i) = x_i ^ p`, every prime `p`, every
`k ≥ 1`): `L_f(p, k) + 1 = min(p ^ r_f, min {m : v_p(m!) + ∑_{j<r_f} (d(j+1) - d(j)) ⌊m/p^j⌋ ≥ k})`,
with the depth flag of `f` itself. -/
theorem levelCount_eq_flagValue_int {f u : MvPowerSeries (Fin n) ℤ} (hfu : f * u = 1) {k : ℕ}
    (hk : 1 ≤ k) : levelCount p (frob p) f k + 1 = flagValue p f k := by
  have hr := rankF_inv (p := p) hfu
  have hJ : flagJump p u = flagJump p f := funext (flagJump_inv hfu)
  obtain ⟨T, hT⟩ := thmF_valTower_int p u
  have htop := topBound_flag_int p u
  rw [hr, hJ] at hT htop
  exact levelCount_eq_flagValue_of_top p (int_not_isUnit p) hfu hk ⟨T, hT⟩ htop

end ThmF

end FrobLevel
