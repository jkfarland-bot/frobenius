module

/-
Run r25, seat L2: the depth flag of ledger R-083 (note Definition 6.2) in Lean, and R-083's digit
formula as a theorem CONDITIONAL on two stated hypotheses (Theorem F's tower and the rank cap
`p ^ r_f`), neither of which is proved in Lean (see Open.lean).

For `f ∈ R[[x_1..x_n]]` and a class `κ ∈ [0, p) ^ n`, `f_κ` is L1's `classPart p f κ` (so
`f = ∑_κ σ(f_κ) x ^ κ`); `v_p(f_κ) ≤ d` is `¬ p ^ (d + 1) ∣ f_κ`.
* `depthSpace p f d` = `U_d`, the `F_p`-span of the classes `κ ≠ 0` with `v_p(f_κ) ≤ d`;
* `rankF p f` = `r_f`, the dimension of the span of the classes `κ ≠ 0` with `f_κ ≠ 0`;
* `depthFlag p f j` = `d(j) = min {d : dim U_d ≥ j}` (`d(0) = 0`), `flagJump p f j = d(j+1) - d(j)`;
* `flagValue p f k` = `min(p ^ r_f, min {m : v_p(m!) + ∑_{j < r_f} (d(j+1) - d(j)) ⌊m/p^j⌋ ≥ k})`.

`levelCount_eq_flagValue`: if `u = 1/f` has an adapted tower of length `r_f` with the `γ` of the
flag recursion, and a monic annihilator of degree `p ^ r_f`, then `L_f + 1 = flagValue p f k`.

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

variable (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R] {n : ℕ}

/-- The class of an exponent vector modulo `p`, as a vector over `F_p`. -/
def classVec (κ : Fin n →₀ ℕ) : Fin n → ZMod p := fun i => (κ i : ZMod p)

/-- `U_d`: the span of the classes `κ ≠ 0` with `v_p(f_κ) ≤ d`. -/
noncomputable def depthSpace (f : MvPowerSeries (Fin n) R) (d : ℕ) :
    Submodule (ZMod p) (Fin n → ZMod p) :=
  Submodule.span (ZMod p) (classVec p '' {κ | κ ∈ digitExps p n ∧ κ ≠ 0 ∧
    ¬ (p : MvPowerSeries (Fin n) R) ^ (d + 1) ∣ classPart p f κ})

/-- The span of all classes `κ ≠ 0` with `f_κ ≠ 0`. -/
noncomputable def fullSpace (f : MvPowerSeries (Fin n) R) : Submodule (ZMod p) (Fin n → ZMod p) :=
  Submodule.span (ZMod p) (classVec p '' {κ | κ ∈ digitExps p n ∧ κ ≠ 0 ∧ classPart p f κ ≠ 0})

/-- `r_f`. -/
noncomputable def rankF (f : MvPowerSeries (Fin n) R) : ℕ := Module.finrank (ZMod p) (fullSpace p f)

/-- The depth flag `d(j)`, `d(0) = 0`. -/
noncomputable def depthFlag (f : MvPowerSeries (Fin n) R) (j : ℕ) : ℕ :=
  if j = 0 then 0 else sInf {d | j ≤ Module.finrank (ZMod p) (depthSpace p f d)}

/-- `d(j + 1) - d(j)`. -/
noncomputable def flagJump (f : MvPowerSeries (Fin n) R) (j : ℕ) : ℕ :=
  depthFlag p f (j + 1) - depthFlag p f j

/-- The right side of R-083's formula. -/
noncomputable def flagValue (f : MvPowerSeries (Fin n) R) (k : ℕ) : ℕ :=
  sInf {m | p ^ rankF p f ≤ m ∨ k ≤ padicValNat p m.factorial
    + ∑ j ∈ Finset.range (rankF p f), flagJump p f j * (m / p ^ j)}

/-- **R-083, conditional**: the digit formula follows from an adapted tower of length `r_f`
whose `γ` follows the flag recursion (Theorem F) and a monic annihilator of degree `p ^ r_f`
(the cap). Both hypotheses are open in Lean. -/
theorem levelCount_eq_flagValue [Nontrivial R] (htor : NoPTorsion p R) (hpu : ¬ IsUnit (p : R))
    {f u : MvPowerSeries (Fin n) R} (hfu : f * u = 1) {k : ℕ} (hk : 1 ≤ k)
    (hF : ∃ (T : ℕ → Polynomial (MvPowerSeries (Fin n) R)) (w : ℕ → MvPowerSeries (Fin n) R),
      AdaptedTower p (frob p) (rankF p f) T (flagGamma p (flagJump p f)) w u)
    (hcap : MonicAnn p (frob p) u k (p ^ rankF p f)) :
    levelCount p (frob p) f k + 1 = flagValue p f k := by
  obtain ⟨T, w, htow⟩ := hF
  have hpuA : ¬ IsUnit (p : MvPowerSeries (Fin n) R) := by
    have := not_isUnit_pow_mvPowerSeries p (τ := Fin n) hpu (le_refl 1)
    rwa [pow_one] at this
  exact levelCount_eq_flag (noPTorsion_mvPowerSeries p htor) (psat_frob p) hpuA htow
    (by rw [hfu, sub_self]; exact dvd_zero _) (not_isUnit_pow_mvPowerSeries p hpu hk) hcap

/-- When `r_f = n` the cap is L1's Cayley-Hamilton bound, so only Theorem F remains. -/
theorem levelCount_eq_flagValue_of_full [Nontrivial R] (htor : NoPTorsion p R)
    (hpu : ¬ IsUnit (p : R)) {f u : MvPowerSeries (Fin n) R} (hfu : f * u = 1) {k : ℕ}
    (hk : 1 ≤ k) (hr : rankF p f = n)
    (hF : ∃ (T : ℕ → Polynomial (MvPowerSeries (Fin n) R)) (w : ℕ → MvPowerSeries (Fin n) R),
      AdaptedTower p (frob p) (rankF p f) T (flagGamma p (flagJump p f)) w u) :
    levelCount p (frob p) f k + 1 = flagValue p f k := by
  refine levelCount_eq_flagValue p htor hpu hfu hk hF ?_
  have hs : ∀ a : MvPowerSeries (Fin n) R, ∃ c : (Fin n →₀ ℕ) → MvPowerSeries (Fin n) R,
      a = ∑ e ∈ digitExps p n, frob p (c e) * (monomial e 1 : MvPowerSeries (Fin n) R) :=
    fun a => span_digit p a
  have := monicAnn_of_span (p := p) (digitExps p n)
    (fun e => (monomial e 1 : MvPowerSeries (Fin n) R)) hs u k
  rw [card_digitExps] at this
  rwa [hr]

end FrobLevel
