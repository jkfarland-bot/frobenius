module

/-
Run r25, seat L8: instances showing the hypotheses of the claimed theorems are satisfiable, with
non-trivial data, and one new named value.

* `levelCount_liftPX_one_add_X`: under `x ↦ x ^ p + p x`, `f = 1 + x` has `J_B(f) = 0`, so by G1
  for every lift `L_f + 1 = p` for every `k ≥ 1` (new named value; uses `span_every_lift`).
* `nv_d1`, `nv_thmN`, `nv_monoB`, `nv_idem`: at `p = 2`, `x ↦ x ^ 2 + 2x` (the torus lift
  `(1 + x) ^ 2 - 1`) and `m = 1 + x`, with `m ^ 2 ∈ B`, `m(0) = 1`, linear part `1` and `h = x`
  (so `Λ = 1`), the hypotheses of `d1_linear_test_gen`, `thmN_fixed_frobForm`,
  `monotests_b_frobForm` and `lambda_idempotent` hold.

Lean v4.33.1 with Mathlib; no sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Basis
public import Frobenius.Levels.PropT
public import Frobenius.Levels.G1
public import Frobenius.Levels.G1Series
public import Frobenius.Levels.ThmR
public import Frobenius.Levels.Lifts
public import Frobenius.Levels.D1Linear
public import Frobenius.Levels.Span
public import Frobenius.Levels.D1Gen
public import Frobenius.Levels.Chain
public import Frobenius.Levels.ThmN

@[expose] public section

namespace FrobLevel

open MvPowerSeries

section G1

variable {p : ℕ} [hp : Fact p.Prime]

theorem levelCount_liftPX_one_add_X {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (liftPX (p := p)) (1 + X 0 : MvPowerSeries (Fin 1) ℤ_[p]) k + 1 = p := by
  have hσ := liftPX_isFrobLift (p := p)
  have hf : IsUnit (1 + X 0 : MvPowerSeries (Fin 1) ℤ_[p]) := by
    rw [isUnit_iff_constantCoeff]; simp
  have hJ1 := not_exists_dvd_of_pderiv hσ (f := 1 + X 0) (b₀ := 0) (e := 1 + X 0) (J := 0)
    (by simp) (i := 0) (by
      rw [map_add, map_one, redp_X, map_add, pderiv_one, pderiv_X_self, zero_add]
      exact one_ne_zero)
  have := levelCount_G1_every_lift hσ hf hk ⟨0, by simp⟩ hJ1
  simpa using this

end G1

section Two

theorem liftPX_two_X : liftPX (p := 2) (X 0) = X 0 ^ 2 + ((2 : ℕ) : MvPowerSeries (Fin 1) ℤ_[2]) * X 0 :=
  liftPX_X

theorem nv_mem : (1 + X 0 : MvPowerSeries (Fin 1) ℤ_[2]) ^ 2 ∈ frobImage (liftPX (p := 2)) :=
  ⟨1 + X 0, by rw [map_add, map_one, liftPX_two_X]; push_cast; ring⟩

/-- D1 test hypotheses satisfied (p = 2, torus lift, m = 1 + x). -/
theorem nv_d1 : (2 : ℤ_[2]) ∣ ∑ i, coeff (Finsupp.single i 1) (1 + X 0 : MvPowerSeries (Fin 1) ℤ_[2])
      * coeff (Finsupp.single 0 1) ((fun _ => (X 0 : MvPowerSeries (Fin 1) ℤ_[2])) i)
      - constantCoeff (1 + X 0 : MvPowerSeries (Fin 1) ℤ_[2]) ^ (2 - 1)
        * coeff (Finsupp.single 0 1) (1 + X 0 : MvPowerSeries (Fin 1) ℤ_[2]) := by
  have := d1_linear_test_gen (p := 2) liftPX_isFrobLift (fun _ => X 0)
    (fun i => by fin_cases i; exact liftPX_two_X) nv_mem 0
  simpa using this

theorem nv_redp_ne : redp 2 (1 + X 0 : MvPowerSeries (Fin 1) ℤ_[2]) ≠ 0 := by
  intro h
  have := congrArg constantCoeff h
  rw [redp, constantCoeff_map] at this
  simp at this

/-- Theorem N hypotheses satisfied: `d m̄ / m̄ = dx / (1 + x)` is `F_σ`-fixed. -/
theorem nv_thmN : Fsig (fun i => redp 2 ((fun _ => (X 0 : MvPowerSeries (Fin 1) ℤ_[2])) i))
      (dlog (redp 2 (1 + X 0 : MvPowerSeries (Fin 1) ℤ_[2])))
      = dlog (redp 2 (1 + X 0 : MvPowerSeries (Fin 1) ℤ_[2])) :=
  thmN_fixed_frobForm (fun _ => X 0) (fun _ => constantCoeff_X 0) nv_mem nv_redp_ne

theorem nv_linMat : IsUnit (linMat (p := 2) (fun _ : Fin 1 => (1 + X 0 : MvPowerSeries (Fin 1) ℤ_[2]))) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_unique, isUnit_iff_ne_zero]
  simp [linMat, coeff_X, coeff_one]

/-- Prop `monotests` (b) hypotheses satisfied (one variable, torus lift at `p = 2`). -/
theorem nv_monoB :
    (∀ i : Fin 1, Fsig (fun i => redp 2 ((fun _ => (X 0 : MvPowerSeries (Fin 1) ℤ_[2])) i))
      (dlog (redp 2 ((fun _ => (1 + X 0 : MvPowerSeries (Fin 1) ℤ_[2])) i)))
      = dlog (redp 2 ((fun _ => (1 + X 0 : MvPowerSeries (Fin 1) ℤ_[2])) i))) ∧
    Submodule.span (FractionRing (MvPowerSeries (Fin 1) (ZMod 2)))
      (Set.range fun i : Fin 1 => dlog (redp 2 ((fun _ => (1 + X 0 : MvPowerSeries (Fin 1) ℤ_[2])) i)))
      = ⊤ := monotests_b_frobForm (p := 2) (fun _ => X 0) (fun _ => constantCoeff_X 0)
  (fun _ => 1 + X 0) (fun _ => nv_mem) nv_linMat

/-- `lambda_idempotent` hypotheses satisfied. -/
theorem nv_idem : Λmat (p := 2) (fun _ : Fin 1 => (X 0 : MvPowerSeries (Fin 1) ℤ_[2]))
    * Λmat (fun _ => X 0) = Λmat (fun _ => X 0) := lambda_idempotent (p := 2) liftPX_isFrobLift (fun _ => X 0)
  (fun i => by fin_cases i; exact liftPX_two_X) (fun _ => 1 + X 0) (fun _ => nv_mem) nv_linMat

end Two

end FrobLevel
