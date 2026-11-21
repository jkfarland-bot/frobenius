module

public import Mathlib
public import Frobenius.Levels.Span

@[expose] public section

/-! L8v remark: every ring endomorphism of `ℤ_[p][[x_1..x_n]]` FIXES constants (so it is
`ℤ_[p]`-linear); L8's `sigma_C_sub` ("moves constants only by p^2 A") is true but understated. -/
namespace L8v
open MvPowerSeries
variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

theorem sigma_C_eq (σ : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p]) (c : ℤ_[p]) :
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

theorem sigma_algHom_compat (σ : MvPowerSeries (Fin n) ℤ_[p] →+* MvPowerSeries (Fin n) ℤ_[p])
    (c : ℤ_[p]) (f : MvPowerSeries (Fin n) ℤ_[p]) : σ (c • f) = c • σ f := by
  rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, sigma_C_eq]

end L8v
