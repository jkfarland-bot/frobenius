module

/-
Run r25, seat L2: Theorem M of ledger R-082 (2) for the family `u = 1 + x + p ^ J y`, in Lean,
and the arithmetic of Theorem M for any adapted tower with `γ = (0, J + 1)`.

Theorem M (ledger): if `ρ(f) = 1 < r_f`, `J = d(2)`, then `L_f + 1 = p ⌈k / (J + 1)⌉` while
`⌈k / (J + 1)⌉ ≤ p - 1`, and `L_f + 1 ≥ p ^ 2` beyond (`= p ^ 2` when `r_f = 2`).
Here: `sInf_thmM` (the arithmetic: the digit formula with `γ = (0, J + 1)`, `N = 2`, is that
value), `levelCount_thmM_of_tower` (every `u` with such a tower and the cap), and
`levelCount_thmM_family` (the units `f = 1/(1 + x + p ^ J y)`, `J ≥ 1`, of `ℤ_[p][[x, y]]`, for
every `k ≥ 1`, unconditionally). The existence of the tower for every unit with `ρ = 1 < r_f`
is not proved in Lean (Open.lean).

Lean v4.33.1 with Mathlib; no sorry, no axioms beyond propext, Classical.choice, Quot.sound.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Basis
public import Frobenius.Levels.Digit
public import Frobenius.Levels.PropP

@[expose] public section

namespace FrobLevel

open MvPowerSeries

/-- The arithmetic of Theorem M: with `c = ⌈k / (J + 1)⌉ = (k + J) / (J + 1)`,
`min(p ^ 2, min {m : e_1(m) (J + 1) ≥ k}) = p c` if `c ≤ p - 1`, and `p ^ 2` otherwise. -/
theorem sInf_thmM {p : ℕ} (hp : 2 ≤ p) {J k : ℕ} (hk : 1 ≤ k) :
    sInf {m | p ^ 2 ≤ m ∨ k ≤ digit p 1 m * (J + 1)}
      = if (k + J) / (J + 1) ≤ p - 1 then p * ((k + J) / (J + 1)) else p ^ 2 := by
  obtain ⟨c, hc⟩ : ∃ c, c = (k + J) / (J + 1) := ⟨_, rfl⟩
  rw [← hc]
  -- `k ≤ c (J + 1)` and `d (J + 1) < k` for `d < c`
  have hdm := Nat.div_add_mod (k + J) (J + 1)
  have hmod := Nat.mod_lt (k + J) (show 0 < J + 1 by omega)
  rw [← hc] at hdm
  have hdm' : c * J + c + (k + J) % (J + 1) = k + J := by
    have : (J + 1) * c = c * J + c := by ring
    omega
  have hc1 : k ≤ c * (J + 1) := by
    have : c * (J + 1) = c * J + c := by ring
    omega
  have hc2 : ∀ d, d < c → d * (J + 1) < k := by
    intro d hd
    have h1 : (d + 1) * J ≤ c * J := Nat.mul_le_mul_right J (by omega)
    have h2 : (d + 1) * J = d * J + J := by ring
    have h3 : d * (J + 1) = d * J + d := by ring
    omega
  have hp0 : 0 < p := by omega
  have hdig_lt : ∀ m, m < p * c → digit p 1 m < c := by
    intro m hm
    have h1 : digit p 1 m ≤ m / p := by rw [digit, pow_one]; exact Nat.mod_le _ _
    have h2 : m / p < c := (Nat.div_lt_iff_lt_mul hp0).2 (by rwa [Nat.mul_comm] at hm)
    omega
  have key : ∀ m0, m0 ∈ {m | p ^ 2 ≤ m ∨ k ≤ digit p 1 m * (J + 1)} →
      (∀ m < m0, m ∉ {m | p ^ 2 ≤ m ∨ k ≤ digit p 1 m * (J + 1)}) →
      sInf {m | p ^ 2 ≤ m ∨ k ≤ digit p 1 m * (J + 1)} = m0 :=
    fun m0 h1 h2 => le_antisymm (Nat.sInf_le h1)
      (le_csInf ⟨m0, h1⟩ fun m hm => by by_contra h; push Not at h; exact h2 m h hm)
  split_ifs with hcp
  · apply key
    · right
      have : digit p 1 (p * c) = c := by
        rw [digit, pow_one, Nat.mul_div_cancel_left _ hp0, Nat.mod_eq_of_lt (by omega)]
      rw [this]; exact hc1
    · intro m hm hmem
      rcases hmem with h | h
      · have : p * c ≤ p * (p - 1) := Nat.mul_le_mul_left p hcp
        have : p * (p - 1) < p ^ 2 := by
          rw [pow_two]; exact Nat.mul_lt_mul_of_pos_left (by omega) hp0
        omega
      · exact absurd h (not_le.2 (hc2 _ (hdig_lt m hm)))
  · apply key
    · exact Or.inl le_rfl
    · intro m hm hmem
      rcases hmem with h | h
      · omega
      · have : digit p 1 m < c := by
          have := digit_lt hp0 1 m
          omega
        exact absurd h (not_le.2 (hc2 _ this))

section Tower

variable {A : Type*} [CommRing A] {p : ℕ} {σ : A →+* A}

/-- Theorem M from a tower (conditional): if `u = 1/f` has an adapted tower of length `2` with
`γ = (0, J + 1)` and a degree `p ^ 2` annihilator exists, then
`L_f + 1 = p ⌈k / (J + 1)⌉` if `⌈k / (J + 1)⌉ ≤ p - 1`, else `p ^ 2`. -/
theorem levelCount_thmM_of_tower [Nontrivial A] (hp : 2 ≤ p) (ht : NoPTorsion p A)
    (hs : PSat p σ) (hpu : ¬ IsUnit (p : A)) {T : ℕ → Polynomial A} {J : ℕ} {w : ℕ → A}
    {f u : A} (htow : AdaptedTower p σ 2 T (fun b => if b = 0 then 0 else J + 1) w u) {k : ℕ}
    (hk : 1 ≤ k) (hfu : (p : A) ^ k ∣ f * u - 1) (hpk : ¬ IsUnit ((p : A) ^ k))
    (hcap : MonicAnn p σ u k (p ^ 2)) :
    levelCount p σ f k + 1
      = if (k + J) / (J + 1) ≤ p - 1 then p * ((k + J) / (J + 1)) else p ^ 2 := by
  rw [levelCount_eq_digit ht hs hpu htow hfu hpk hcap, ← sInf_thmM hp hk]
  congr 1
  ext m
  simp [digitVal, Finset.sum_range_succ]

end Tower

/-- **Theorem M for `f = 1/(1 + x + p ^ J y)`** (`J ≥ 1`, `ρ(f) = 1 < r_f = 2`, `d = (0, J)`), in
`ℤ_[p][[x, y]]`, every `k ≥ 1`: `L_f + 1 = p ⌈k / (J + 1)⌉` while `⌈k / (J + 1)⌉ ≤ p - 1`,
and `p ^ 2` beyond. -/
theorem levelCount_thmM_family (p : ℕ) [hp : Fact p.Prime] {J : ℕ} (hJ : 1 ≤ J)
    {f : MvPowerSeries (Fin 2) ℤ_[p]}
    (hfu : f * (1 + X 0 + (p : MvPowerSeries (Fin 2) ℤ_[p]) ^ J * X 1) = 1) {k : ℕ}
    (hk : 1 ≤ k) :
    levelCount p (frob p) f k + 1
      = if (k + J) / (J + 1) ≤ p - 1 then p * ((k + J) / (J + 1)) else p ^ 2 := by
  have hu : uP p 0 J = (1 + X 0 + (p : MvPowerSeries (Fin 2) ℤ_[p]) ^ J * X 1) := by
    simp [uP]
  rw [levelCount_propP_padic p (by omega : 0 < J) (by rw [hu]; exact hfu) hk,
    ← sInf_thmM hp.out.two_le hk]
  congr 1
  ext m
  simp

end FrobLevel
