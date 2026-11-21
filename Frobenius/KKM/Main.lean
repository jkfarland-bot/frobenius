module

public import Frobenius.KKM.UpperBound
public import Frobenius.KKM.LowerBound

/-!
# Conjecture 4 of Kauers, Krattenthaler and Müller

For a prime `p` and `γ ≥ 0`, a monic `A ∈ ℤ[z][t]` of `t`-degree `d` with
`A(z, Φ_p(z)) ≡ 0 (mod p ^ γ)` exists if and only if `p ^ γ ∣ d!`. Hence the least such degree is
the Kempner value `S(p ^ γ)`, the least `d` with `p ^ γ ∣ d!`: this is Conjecture 4 of
M. Kauers, C. Krattenthaler and T. W. Müller (2012, `p = 2`) and of C. Krattenthaler and
T. W. Müller (2025, every `p`).

The `if` direction is the delta tower (`UpperBound.lean`); the `only if` direction is their
Lemma 1, proved here by exhibiting a coefficient equal to `d!` (`LowerBound.lean`).
-/

@[expose] public section

namespace Frobenius.KKM

variable (p : ℕ) [Fact p.Prime]

/-- The `t`-degrees of the monic `A ∈ ℤ[z][t]` with `A(z, Φ_p) ≡ 0 (mod p ^ γ)` are exactly the
`d` with `p ^ γ ∣ d!`. -/
theorem degrees_vanishesMod (γ : ℕ) :
    {d : ℕ | ∃ A : Polynomial (Polynomial ℤ), A.Monic ∧ A.natDegree = d ∧ VanishesMod p γ A} =
      {d : ℕ | p ^ γ ∣ d.factorial} := by
  ext d
  constructor
  · rintro ⟨A, hm, rfl, hv⟩
    exact pow_dvd_factorial_of_vanishesMod p γ A hm hv
  · intro h
    exact exists_monic_vanishesMod_of_dvd p γ d h

/-- **Conjecture 4 of Kauers, Krattenthaler and Müller.** The least `t`-degree of a monic
`A ∈ ℤ[z][t]` with `A(z, Φ_p) ≡ 0 (mod p ^ γ)` is `S(p ^ γ)`. -/
theorem minimal_degree_eq_kempner (γ : ℕ) :
    IsLeast {d : ℕ | ∃ A : Polynomial (Polynomial ℤ), A.Monic ∧ A.natDegree = d ∧
      VanishesMod p γ A} (kempner p γ) := by
  rw [degrees_vanishesMod]
  unfold kempner
  exact ⟨Nat.find_spec (exists_kempner p γ), fun d hd => Nat.find_min' _ hd⟩

/-- For each `d`, the largest `γ` for which some monic `A` of `t`-degree `d` has
`A(z, Φ_p) ≡ 0 (mod p ^ γ)` is `v_p(d!)`. -/
theorem isGreatest_vanishesMod (d : ℕ) :
    IsGreatest {γ : ℕ | ∃ A : Polynomial (Polynomial ℤ), A.Monic ∧ A.natDegree = d ∧
      VanishesMod p γ A} (padicValNat p d.factorial) := by
  refine ⟨exists_monic_vanishesMod_factorial p d, ?_⟩
  rintro γ ⟨A, hm, rfl, hv⟩
  exact (padicValNat_dvd_iff_le (Nat.factorial_ne_zero _)).mp
    (pow_dvd_factorial_of_vanishesMod p γ A hm hv)

end Frobenius.KKM
