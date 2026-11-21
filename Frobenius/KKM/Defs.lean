module

public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# The series `Φ_p` of Kauers, Krattenthaler and Müller

`Φ_p(z) = ∑_{n ≥ 0} z ^ (p ^ n)` in `ℤ⟦z⟧`. A polynomial `A ∈ ℤ[z][t]` (outer variable `t`,
coefficients in `ℤ[z]`) is evaluated at `t = Φ_p(z)`, and `VanishesMod p γ A` says that every
coefficient of `A(z, Φ_p(z))` is divisible by `p ^ γ`.

References: M. Kauers, C. Krattenthaler and T. W. Müller, Electron. J. Combin. 18(2) (2012), P37;
C. Krattenthaler and T. W. Müller, Aequationes Math. 99 (2025), 2505 to 2547.
-/

@[expose] public section

namespace Frobenius.KKM

/-- `Φ_p(z) = ∑_{n ≥ 0} z ^ (p ^ n)`: the coefficient of `z ^ m` is `1` if `m` is a power of `p`,
and `0` otherwise. -/
noncomputable def Phi (p : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (Set.indicator (Set.range fun k : ℕ => p ^ k) 1)

/-- `A(z, Φ_p(z))` for `A ∈ ℤ[z][t]`: the outer variable `t` is replaced by `Φ_p(z)` and each
coefficient in `ℤ[z]` is read as a power series. -/
noncomputable def evalPhi (p : ℕ) (A : Polynomial (Polynomial ℤ)) : PowerSeries ℤ :=
  A.eval₂ Polynomial.coeToPowerSeries.ringHom (Phi p)

/-- `A(z, Φ_p(z)) ≡ 0 (mod p ^ γ)`, coefficientwise. -/
def VanishesMod (p γ : ℕ) (A : Polynomial (Polynomial ℤ)) : Prop :=
  ∀ n : ℕ, (p : ℤ) ^ γ ∣ PowerSeries.coeff n (evalPhi p A)

theorem exists_kempner (p k : ℕ) [hp : Fact p.Prime] : ∃ N : ℕ, p ^ k ∣ N.factorial :=
  ⟨p ^ k, Nat.dvd_factorial (pow_pos hp.out.pos k) le_rfl⟩

/-- The Kempner value `S(p ^ k)`: the least `N` with `p ^ k ∣ N!`. -/
noncomputable def kempner (p k : ℕ) [Fact p.Prime] : ℕ :=
  open Classical in Nat.find (exists_kempner p k)

theorem coeff_Phi (p m : ℕ) :
    PowerSeries.coeff m (Phi p) = Set.indicator (Set.range fun k : ℕ => p ^ k) 1 m := by
  simp [Phi]

end Frobenius.KKM
