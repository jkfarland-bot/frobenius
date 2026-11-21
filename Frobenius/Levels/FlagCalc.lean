module

/-
Run r25, seat L6: tools for computing depth flags (L2's `depthSpace`, `depthFlag`, `rankF`,
`flagValue`) of explicit power series, used with L5's R-083 (`levelCount_eq_flagValue_int`,
`_padic`).

* `pow_dvd_C_iff`: `p ^ j ∣ C c` in `R[[x]]` iff `p ^ j ∣ c` in `R`.
* `classPart_add`, `classPart_C_mul`, `classPart_monomial`, `classPart_frob`: class parts of sums,
  constant multiples, monomials with small exponents, and elements of `B = σ(A)`.
* `depthSpace_shift_lt`, `depthSpace_shift`, `fullSpace_shift`: for `u = σ(b) + p ^ J τ` (no
  `p`-torsion), `U_d(u) = 0` for `d < J` and `U_{J+d}(u) = U_d(τ)`; same full span.
* `depthSpace_frob_mul`, `fullSpace_frob_mul`: multiplying by `σ(s)`, `s` a unit, keeps the spaces.
* `sInf_eq_of_iff`, `finrank_span_single`, `classVec_single`: arithmetic helpers.

Lean v4.33.1 with Mathlib; no sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Basis
public import Frobenius.Levels.Digit
public import Frobenius.Levels.Flag
public import Frobenius.Levels.Cap
public import Frobenius.Levels.TraceFlag
public import Frobenius.Levels.Padic
public import Frobenius.Levels.Assemble

@[expose] public section

namespace FrobLevel

open MvPowerSeries

section Calc

variable (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R] {n : ℕ}

theorem pow_dvd_C_iff (j : ℕ) (c : R) :
    (p : MvPowerSeries (Fin n) R) ^ j ∣ C c ↔ (p : R) ^ j ∣ c := by
  rw [natCast_pow_eq_C]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨coeff 0 q, ?_⟩
    have := congrArg (coeff (0 : Fin n →₀ ℕ)) hq
    rwa [coeff_zero_C, coeff_C_mul] at this
  · rintro ⟨q, rfl⟩
    exact ⟨C q, by rw [map_mul]⟩

omit hp in
theorem classPart_add (a b : MvPowerSeries (Fin n) R) (κ : Fin n →₀ ℕ) :
    classPart p (a + b) κ = classPart p a κ + classPart p b κ := by
  ext d; simp only [coeff_classPart, map_add]

omit hp in
theorem classPart_C_mul (c : R) (a : MvPowerSeries (Fin n) R) (κ : Fin n →₀ ℕ) :
    classPart p (C c * a) κ = C c * classPart p a κ := by
  ext d; simp only [coeff_classPart, coeff_C_mul]

theorem classPart_natCast_pow_mul (J : ℕ) (a : MvPowerSeries (Fin n) R) (κ : Fin n →₀ ℕ) :
    classPart p ((p : MvPowerSeries (Fin n) R) ^ J * a) κ
      = (p : MvPowerSeries (Fin n) R) ^ J * classPart p a κ := by
  rw [natCast_pow_eq_C, classPart_C_mul]

/-- `p • d + κ = e` with `e` a digit exponent forces `d = 0`. -/
theorem eq_zero_of_smul_add_eq {d κ e : Fin n →₀ ℕ} (he : e ∈ digitExps p n)
    (h : p • d + κ = e) : d = 0 := by
  have hlt := (mem_digitExps p n).1 he
  ext i
  have h1 := congrArg (· i) h
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h1
  have h2 := hlt i
  have hp1 := hp.out.one_lt
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  by_contra hne
  have : p ≤ p * d i := Nat.le_mul_of_pos_right p (Nat.pos_of_ne_zero hne)
  omega

/-- Class parts of a monomial with digit exponent. -/
theorem classPart_monomial {e κ : Fin n →₀ ℕ} (he : e ∈ digitExps p n) (c : R) :
    classPart p (monomial e c) κ = if κ = e then C c else 0 := by
  ext d
  rw [coeff_classPart, coeff_monomial]
  by_cases h : p • d + κ = e
  · have hd := eq_zero_of_smul_add_eq p he h
    subst hd
    simp only [smul_zero, zero_add] at h
    subst h
    simp
  · rw [if_neg h]
    split_ifs with hκ
    · subst hκ
      rw [coeff_C, if_neg]
      rintro rfl
      exact h (by simp)
    · simp

/-- Class parts of `σ(b)` vanish off the class `0`. -/
theorem classPart_frob {κ : Fin n →₀ ℕ} (hκ : κ ∈ digitExps p n) (hne : κ ≠ 0)
    (b : MvPowerSeries (Fin n) R) : classPart p (frob p b) κ = 0 := by
  have hlt := (mem_digitExps p n).1 hκ
  obtain ⟨i, hi⟩ : ∃ i, κ i ≠ 0 := by
    by_contra h; push Not at h; exact hne (Finsupp.ext h)
  ext d
  rw [coeff_classPart, map_zero]
  apply coeff_frob_of_not_dvd p b (i := i)
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  intro hdvd
  have h1 : p ∣ κ i := (Nat.dvd_add_right (dvd_mul_right p (d i))).1 hdvd
  have h2 := hlt i
  exact hi (Nat.eq_zero_of_dvd_of_lt h1 h2)

theorem classPart_one {κ : Fin n →₀ ℕ} (hκ : κ ∈ digitExps p n) (hne : κ ≠ 0) :
    classPart p (1 : MvPowerSeries (Fin n) R) κ = 0 := by
  rw [← map_one (frob p (τ := Fin n) (R := R))]
  exact classPart_frob p hκ hne 1

/-- `u = σ(b) + p ^ J τ`: off the class `0`, `u_κ = p ^ J τ_κ`. -/
theorem classPart_shift {u b τ : MvPowerSeries (Fin n) R} {J : ℕ}
    (hu : u = frob p b + (p : MvPowerSeries (Fin n) R) ^ J * τ) {κ : Fin n →₀ ℕ}
    (hκ : κ ∈ digitExps p n) (hne : κ ≠ 0) :
    classPart p u κ = (p : MvPowerSeries (Fin n) R) ^ J * classPart p τ κ := by
  rw [hu, classPart_add, classPart_frob p hκ hne, zero_add, classPart_natCast_pow_mul]

theorem depthSpace_shift_lt {u b τ : MvPowerSeries (Fin n) R} {J : ℕ}
    (hu : u = frob p b + (p : MvPowerSeries (Fin n) R) ^ J * τ) {d : ℕ} (hd : d < J) :
    depthSpace p u d = ⊥ := by
  rw [depthSpace, Submodule.span_eq_bot]
  rintro _ ⟨κ, ⟨hκ, hne, hnd⟩, rfl⟩
  exfalso
  apply hnd
  rw [classPart_shift p hu hκ hne]
  exact (pow_dvd_pow _ (by omega)).trans (dvd_mul_right _ _)

theorem depthSpace_shift (ht : NoPTorsion p R) {u b τ : MvPowerSeries (Fin n) R} {J : ℕ}
    (hu : u = frob p b + (p : MvPowerSeries (Fin n) R) ^ J * τ) (d : ℕ) :
    depthSpace p u (J + d) = depthSpace p τ d := by
  have htA := noPTorsion_mvPowerSeries (τ := Fin n) p ht
  unfold depthSpace
  congr 2
  ext κ
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hκ, hne, hnd⟩
    refine ⟨hκ, hne, fun h => hnd ?_⟩
    rw [classPart_shift p hu hκ hne, show J + d + 1 = J + (d + 1) by omega, pow_add]
    exact mul_dvd_mul_left _ h
  · rintro ⟨hκ, hne, hnd⟩
    refine ⟨hκ, hne, fun h => hnd ?_⟩
    rw [classPart_shift p hu hκ hne, show J + d + 1 = J + (d + 1) by omega] at h
    exact dvd_of_pow_mul_dvd htA h

theorem fullSpace_shift (ht : NoPTorsion p R) {u b τ : MvPowerSeries (Fin n) R} {J : ℕ}
    (hu : u = frob p b + (p : MvPowerSeries (Fin n) R) ^ J * τ) :
    fullSpace p u = fullSpace p τ := by
  have htA := noPTorsion_mvPowerSeries (τ := Fin n) p ht
  unfold fullSpace
  congr 2
  ext κ
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hκ, hne, hnz⟩
    refine ⟨hκ, hne, fun h => hnz ?_⟩
    rw [classPart_shift p hu hκ hne, h, mul_zero]
  · rintro ⟨hκ, hne, hnz⟩
    refine ⟨hκ, hne, fun h => hnz ?_⟩
    rw [classPart_shift p hu hκ hne] at h
    exact cancel_pow htA (by rw [h, mul_zero])

/-- Multiplying by an element of `B` keeps `C_W + c A`. -/
theorem wDiv_frob_mul {W : Submodule (ZMod p) (Fin n → ZMod p)} {c : R}
    {g : MvPowerSeries (Fin n) R} (hg : WDiv p W c g) (s : MvPowerSeries (Fin n) R) :
    WDiv p W c (frob p s * g) := by
  intro m hm
  rw [coeff_mul]
  refine Finset.dvd_sum fun x hx => ?_
  by_cases h0 : coeff x.1 (frob p s) = 0
  · rw [h0, zero_mul]; exact dvd_zero _
  · have hdiv : ∀ i, p ∣ x.1 i := by
      intro i; by_contra hi; exact h0 (coeff_frob_of_not_dvd p s hi)
    have hcv : classVec p x.1 = 0 := by
      funext i
      simp only [classVec, Pi.zero_apply]
      exact (ZMod.natCast_eq_zero_iff _ _).2 (hdiv i)
    have hx2 : classVec p x.2 ∉ W := by
      rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hx, classVec_add, hcv, zero_add] at hm
      exact hm
    exact dvd_mul_of_dvd_right (hg _ hx2) _

theorem depthSpace_frob_mul {s : MvPowerSeries (Fin n) R} (hs : IsUnit s)
    (g : MvPowerSeries (Fin n) R) (d : ℕ) :
    depthSpace p (frob p s * g) d = depthSpace p g d := by
  obtain ⟨v, rfl⟩ := hs
  have hinv : g = frob p (↑v⁻¹ : MvPowerSeries (Fin n) R) * (frob p ↑v * g) := by
    rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  refine le_antisymm ?_ ?_
  · exact (depthSpace_le_iff p).2 (wDiv_frob_mul p ((depthSpace_le_iff p).1 le_rfl) _)
  · conv_lhs => rw [hinv]
    exact (depthSpace_le_iff p).2 (wDiv_frob_mul p ((depthSpace_le_iff p).1 le_rfl) _)

theorem fullSpace_frob_mul {s : MvPowerSeries (Fin n) R} (hs : IsUnit s)
    (g : MvPowerSeries (Fin n) R) :
    fullSpace p (frob p s * g) = fullSpace p g := by
  obtain ⟨v, rfl⟩ := hs
  have hinv : g = frob p (↑v⁻¹ : MvPowerSeries (Fin n) R) * (frob p ↑v * g) := by
    rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  refine le_antisymm ?_ ?_
  · exact (fullSpace_le_iff p).2 (wDiv_frob_mul p ((fullSpace_le_iff p).1 le_rfl) _)
  · conv_lhs => rw [hinv]
    exact (fullSpace_le_iff p).2 (wDiv_frob_mul p ((fullSpace_le_iff p).1 le_rfl) _)

omit hp in
theorem sInf_eq_of_iff {P : ℕ → Prop} {c : ℕ} (h : ∀ d, P d ↔ c ≤ d) : sInf {d | P d} = c := by
  have : {d | P d} = Set.Ici c := by ext d; simp [h]
  rw [this, csInf_Ici]

theorem classVec_single (i : Fin n) :
    classVec p (Finsupp.single i 1) = (Pi.single i 1 : Fin n → ZMod p) := by
  funext j
  simp only [classVec, Finsupp.single_apply, Pi.single_apply]
  split_ifs with h1 h2 h2
  · simp
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

theorem single_mem_digitExps (i : Fin n) : Finsupp.single i 1 ∈ digitExps p n := by
  rw [mem_digitExps]
  intro j
  have := hp.out.one_lt
  simp only [Finsupp.single_apply]
  split_ifs <;> omega

omit hp in
theorem finrank_span_single {K : Type*} [Field K] (T : Finset (Fin n)) :
    Module.finrank K (Submodule.span K
      ((fun i => (Pi.single i 1 : Fin n → K)) '' (T : Set (Fin n)))) = T.card := by
  have hli : LinearIndependent K (fun i : (T : Set (Fin n)) => (Pi.single (i : Fin n) 1 : Fin n → K)) := by
    have := (Pi.basisFun K (Fin n)).linearIndependent.comp (fun i : (T : Set (Fin n)) => (i : Fin n))
      Subtype.val_injective
    simpa [Function.comp_def, Pi.basisFun_apply] using this
  have h := finrank_span_eq_card hli
  rw [Set.image_eq_range, h]
  simp

end Calc

end FrobLevel
