module

/-
Run r25, seat L6: a step toward R-084 equality beyond finitely many primes.

* Uses seat L4's `levelCount_congr` (PropT.lean, any commutative ring, any endomorphism `σ`):
  the level count `L_f(p, k)` depends only on `f` modulo `p ^ k`.
* `Dir.levelCount_dir_congr_int`, `_padic`: **R-084 equality for every unit `f` of the Dirichlet
  ring that is supported on finitely many primes MODULO `p ^ k`**: if `p ^ k ∣ f(N)` for every
  `N` that is not `{q_1..q_n}`-smooth, then `L_f(p, k) + 1 = flagValue p (res f) k` (R-083's
  formula for the restriction of `f`). The support of `f` itself may be infinite: for example
  `f = ζ_S + p ^ k g` for any `g`. This extends L5's `Dir.levelCount_dir_smooth_*`.

R-084 for a general unit (infinitely many primes with `p ^ k ∤ f(N)`) is NOT proved here; see
Open.lean (`open_r084_upper`).

Lean v4.33.1 with Mathlib; no sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Flag
public import Frobenius.Levels.DirBase
public import Frobenius.Levels.DirMain
public import Frobenius.Levels.DirTransfer
public import Frobenius.Levels.Cap
public import Frobenius.Levels.Padic
public import Frobenius.Levels.Assemble
public import Frobenius.Levels.PropT

@[expose] public section

namespace FrobLevel

namespace Dir

section DirCongr

variable (p : ℕ) [hp : Fact p.Prime] {n : ℕ} {q : Fin n → ℕ}
variable (hq : ∀ i, (q i).Prime) (hinj : Function.Injective q)

/-- `f ≡ iota (res f)` modulo `p ^ k` when `p ^ k` divides `f` off the smooth arguments. -/
theorem dvd_sub_iota_res {R : Type*} [CommRing R] {f : ArithmeticFunction R} {k : ℕ}
    (hcong : ∀ N, (∀ e, smoothNum q e ≠ N) → (p : R) ^ k ∣ f N) :
    (p : ArithmeticFunction R) ^ k ∣ f - iota hq hinj (res hq hinj f) := by
  have h := natCast_dvd_of_apply (m := p ^ k) (D := f - iota hq hinj (res hq hinj f)) (fun N => by
    rw [sub_apply', Nat.cast_pow]
    by_cases hN : ∃ e, smoothNum q e = N
    · obtain ⟨e, rfl⟩ := hN
      rw [iota_apply_smooth, coeff_res, sub_self]
      exact dvd_zero _
    · push Not at hN
      show (p : R) ^ k ∣ f N - iotaFun q hq (res hq hinj f) N
      rw [iotaFun_of_not hq _ hN, sub_zero]
      exact hcong N hN)
  rwa [Nat.cast_pow] at h

theorem iota_supp {R : Type*} [CommRing R] (a : MvPowerSeries (Fin n) R) :
    ∀ N, iota hq hinj a N ≠ 0 → ∃ e, smoothNum q e = N := by
  intro N hN
  by_contra h
  push Not at h
  exact hN (iotaFun_of_not hq a h)

/-- **R-084 equality, over `ℤ`, for every unit whose values off the `{q_i}`-smooth arguments are
divisible by `p ^ k`.** -/
theorem levelCount_dir_congr_int {f : ArithmeticFunction ℤ} (hf : IsUnit f) {k : ℕ} (hk : 1 ≤ k)
    (hcong : ∀ N, (∀ e, smoothNum q e ≠ N) → (p : ℤ) ^ k ∣ f N) :
    levelCount p (Ep p) f k + 1 = flagValue p (res hq hinj f) k := by
  have hu : IsUnit (iota hq hinj (res hq hinj f)) := (hf.map (res hq hinj)).map (iota hq hinj)
  rw [levelCount_congr (dvd_sub_iota_res p hq hinj hcong),
    levelCount_dir_smooth_int p hq hinj hu (iota_supp hq hinj _) hk, res_iota]

/-- The same over `ℤ_[p]`. -/
theorem levelCount_dir_congr_padic {f : ArithmeticFunction ℤ_[p]} (hf : IsUnit f) {k : ℕ}
    (hk : 1 ≤ k) (hcong : ∀ N, (∀ e, smoothNum q e ≠ N) → (p : ℤ_[p]) ^ k ∣ f N) :
    levelCount p (Ep p) f k + 1 = flagValue p (res hq hinj f) k := by
  have hu : IsUnit (iota hq hinj (res hq hinj f)) := (hf.map (res hq hinj)).map (iota hq hinj)
  rw [levelCount_congr (dvd_sub_iota_res p hq hinj hcong),
    levelCount_dir_smooth_padic p hq hinj hu (iota_supp hq hinj _) hk, res_iota]

end DirCongr

end Dir

end FrobLevel
