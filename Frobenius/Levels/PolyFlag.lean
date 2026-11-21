module

/-
Run r25, seat L6: the depth flag of a power series that is a sum of monomials with digit
exponents (every exponent entry `< p`) and coefficients powers of `p`:
`powPoly ex val = ∑_t p ^ (val t) x ^ (ex t)`, `ex` injective, over a domain `R` with `p ≠ 0`
not a unit (`ℤ`, `ℤ_[p]`).

* `classPart_powPoly_ex`, `classPart_powPoly_off`: `u_κ = p ^ (val t)` at `κ = ex t`, else `0`.
* `depthSpace_powPoly`: `U_d = span {class of ex t : ex t ≠ 0, val t ≤ d}`.
* `fullSpace_powPoly`: the full span is `span {class of ex t : ex t ≠ 0}`.
* `finrank_span_eq_card`: a set of vectors with the same span as `{e_i : i ∈ T}` has rank `#T`.

Lean v4.33.1 with Mathlib; no sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Flag
public import Frobenius.Levels.Cap
public import Frobenius.Levels.FlagCalc

@[expose] public section

namespace FrobLevel

open MvPowerSeries

section PolyFlag

variable (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R] {n : ℕ} {T : Type*} [Fintype T]

/-- `∑_t p ^ (val t) x ^ (ex t)`. -/
noncomputable def powPoly (ex : T → (Fin n →₀ ℕ)) (val : T → ℕ) : MvPowerSeries (Fin n) R :=
  ∑ t, monomial (ex t) ((p : R) ^ val t)

omit hp [Fintype T] in
theorem classPart_finset_sum (s : Finset T) (g : T → MvPowerSeries (Fin n) R) (κ : Fin n →₀ ℕ) :
    classPart p (∑ t ∈ s, g t) κ = ∑ t ∈ s, classPart p (g t) κ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext d; simp [coeff_classPart]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, classPart_add, ih]

variable {p}

theorem classPart_powPoly {ex : T → (Fin n →₀ ℕ)} (hex : ∀ t, ex t ∈ digitExps p n)
    (val : T → ℕ) (κ : Fin n →₀ ℕ) :
    classPart p (powPoly (R := R) p ex val) κ
      = ∑ t, if κ = ex t then C ((p : R) ^ val t) else 0 := by
  rw [powPoly, classPart_finset_sum]
  exact Finset.sum_congr rfl fun t _ => classPart_monomial p (hex t) _

theorem classPart_powPoly_ex {ex : T → (Fin n →₀ ℕ)} (hex : ∀ t, ex t ∈ digitExps p n)
    (hinj : Function.Injective ex) (val : T → ℕ) (t : T) :
    classPart p (powPoly (R := R) p ex val) (ex t) = C ((p : R) ^ val t) := by
  rw [classPart_powPoly hex, Finset.sum_eq_single t]
  · rw [if_pos rfl]
  · intro s _ hs; rw [if_neg (fun h => hs (hinj h).symm)]
  · intro h; exact absurd (Finset.mem_univ t) h

theorem classPart_powPoly_off {ex : T → (Fin n →₀ ℕ)} (hex : ∀ t, ex t ∈ digitExps p n)
    (val : T → ℕ) {κ : Fin n →₀ ℕ} (hκ : ∀ t, ex t ≠ κ) :
    classPart p (powPoly (R := R) p ex val) κ = 0 := by
  rw [classPart_powPoly hex]
  exact Finset.sum_eq_zero fun t _ => by rw [if_neg (fun h => hκ t h.symm)]

variable [IsDomain R]

theorem depthSpace_powPoly (hp0 : (p : R) ≠ 0) (hpu : ¬ IsUnit (p : R))
    {ex : T → (Fin n →₀ ℕ)} (hex : ∀ t, ex t ∈ digitExps p n) (hinj : Function.Injective ex)
    (val : T → ℕ) (d : ℕ) :
    depthSpace p (powPoly (R := R) p ex val) d
      = Submodule.span (ZMod p) ((fun t => classVec p (ex t)) '' {t | ex t ≠ 0 ∧ val t ≤ d}) := by
  unfold depthSpace
  congr 1
  ext v
  constructor
  · rintro ⟨κ, ⟨hκ, hne, hnd⟩, rfl⟩
    by_cases h : ∃ t, ex t = κ
    · obtain ⟨t, rfl⟩ := h
      refine ⟨t, ⟨hne, ?_⟩, rfl⟩
      rw [classPart_powPoly_ex hex hinj, pow_dvd_C_iff, pow_dvd_pow_iff hp0 hpu] at hnd
      omega
    · push Not at h
      exact absurd (by rw [classPart_powPoly_off hex val h]; exact dvd_zero _) hnd
  · rintro ⟨t, ⟨hne, hle⟩, rfl⟩
    refine ⟨ex t, ⟨hex t, hne, ?_⟩, rfl⟩
    rw [classPart_powPoly_ex hex hinj, pow_dvd_C_iff, pow_dvd_pow_iff hp0 hpu]
    omega

theorem fullSpace_powPoly (hp0 : (p : R) ≠ 0) {ex : T → (Fin n →₀ ℕ)}
    (hex : ∀ t, ex t ∈ digitExps p n) (hinj : Function.Injective ex) (val : T → ℕ) :
    fullSpace p (powPoly (R := R) p ex val)
      = Submodule.span (ZMod p) ((fun t => classVec p (ex t)) '' {t | ex t ≠ 0}) := by
  unfold fullSpace
  congr 1
  ext v
  constructor
  · rintro ⟨κ, ⟨hκ, hne, hnz⟩, rfl⟩
    by_cases h : ∃ t, ex t = κ
    · obtain ⟨t, rfl⟩ := h
      exact ⟨t, hne, rfl⟩
    · push Not at h
      exact absurd (classPart_powPoly_off hex val h) hnz
  · rintro ⟨t, hne, rfl⟩
    refine ⟨ex t, ⟨hex t, hne, ?_⟩, rfl⟩
    rw [classPart_powPoly_ex hex hinj]
    intro h
    have := congrArg (coeff (0 : Fin n →₀ ℕ)) h
    rw [coeff_zero_C, map_zero] at this
    exact pow_ne_zero _ hp0 this

end PolyFlag

section Span

variable {K : Type*} [Field K] {n : ℕ}

theorem finrank_span_eq_card {S : Set (Fin n → K)} {Tf : Finset (Fin n)}
    (h1 : ∀ v ∈ S, v ∈ Submodule.span K ((fun i => (Pi.single i 1 : Fin n → K)) '' (Tf : Set (Fin n))))
    (h2 : ∀ i ∈ Tf, (Pi.single i 1 : Fin n → K) ∈ Submodule.span K S) :
    Module.finrank K (Submodule.span K S) = Tf.card := by
  have : Submodule.span K S
      = Submodule.span K ((fun i => (Pi.single i 1 : Fin n → K)) '' (Tf : Set (Fin n))) := by
    refine le_antisymm (Submodule.span_le.2 h1) (Submodule.span_le.2 ?_)
    rintro _ ⟨i, hi, rfl⟩
    exact h2 i hi
  rw [this, finrank_span_single]

end Span

end FrobLevel
