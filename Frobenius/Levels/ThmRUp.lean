module

/-
Run r25, seat L10: R-086 Theorem R, upper half, reduced to the minimal-polynomial step.

`levelCount_le_of_monic_root`: for any commutative ring, any endomorphism `σ` and `f u = 1`:
a monic `P ∈ B[X]` with `P(u) = 0` gives `L_f + 1 ≤ deg P` (for every `k` with `p ^ k` not a unit).
So Theorem R's bound `L_f + 1 ≤ p ^ (r_f)` follows once the minimal polynomial of `u` over
`Frac B` (degree `p ^ (r_f)` by definition of `r_f`) is shown to have coefficients in `B`.
That step (normality of `B`) is stated open in Open.lean (`open_thmR_minpoly`).

Lean v4.33.1 with Mathlib; no sorry, no axioms beyond propext, Classical.choice, Quot.sound.
-/
public import Mathlib
public import Frobenius.Levels.Found

@[expose] public section

namespace L10

open FrobLevel Polynomial

theorem levelCount_le_of_monic_root {A : Type*} [CommRing A] [Nontrivial A] {p : ℕ}
    {σ : A →+* A} {f u : A} {k : ℕ} (hfu : f * u = 1) (hpk : ¬ IsUnit ((p : A) ^ k))
    {P : A[X]} (hmon : P.Monic) (hB : P ∈ BPoly σ) (hP : P.eval u = 0) :
    levelCount p σ f k + 1 ≤ P.natDegree := by
  have hex : MonicAnn p σ u k P.natDegree := ⟨P, hmon, rfl, hB, by rw [hP]; exact dvd_zero _⟩
  rw [levelCount_add_one (by rw [hfu, sub_self]; exact dvd_zero _) hpk hex]
  exact annDegree_le hex

/-- The same in `ℤ_[p][[x_1..x_n]]`, every endomorphism, every `k ≥ 1`. -/
theorem levelCount_le_of_monic_root_series {p : ℕ} [Fact p.Prime] {n : ℕ}
    {σ : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p]}
    {f u : MvPowerSeries (Fin n) ℤ_[p]} (hfu : f * u = 1) {k : ℕ} (hk : 1 ≤ k)
    {P : (MvPowerSeries (Fin n) ℤ_[p])[X]} (hmon : P.Monic) (hB : P ∈ BPoly σ)
    (hP : P.eval u = 0) : levelCount p σ f k + 1 ≤ P.natDegree :=
  levelCount_le_of_monic_root hfu (not_isUnit_pow_mvPowerSeries p (padicInt_not_isUnit p) hk)
    hmon hB hP

end L10
