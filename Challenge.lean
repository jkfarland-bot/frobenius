module

public import Mathlib

@[expose] public section

/-!
# Kempner levels: the KKM conjecture and the divisor levels of the Möbius function

This file is the statement surface for the Palomar registry. It defines, with docstrings, the
objects the results are about, using only Mathlib, and states each headline result with `sorry`.
`Solution.lean` proves every statement below with the same name and type. Its definitions come
from `Frobenius/Statements.lean`, a byte-identical copy of the definitions in this file, and
Comparator checks them against the definitions here constant by constant, bodies included.

## Objects

* `kempner p k` is the Kempner value `S(p ^ k)`, the least `N` with `p ^ k ∣ N!`.
* `frobPush p` is the Frobenius pushforward `E_p` of the Dirichlet ring: `(E_p f)(j ^ p) = f(j)`
  and `0` off the `p`th powers. It is a ring endomorphism lifting Frobenius modulo `p`.
* `HasLevel p σ f k L` says that `1/f ≡ ∑_{z ≤ L} f ^ z σ(g_z) (mod p ^ k)` for some `g_z`
  (written as `p ^ k ∣ 1 - f ∑ f ^ z σ(g_z)`), and `levelCount p σ f k` is the least such `L`,
  the level count `L_f(p, k)` of the preprint (Definition 4.1 and Sections 6 and 7).
* `Phi p`, `evalPhi p A`, `VanishesMod p γ A`: the series `Φ_p(z) = ∑ z ^ (p ^ n)`, the series
  `A(z, Φ_p(z))` for `A ∈ ℤ[z][t]`, and the congruence `A(z, Φ_p) ≡ 0 (mod p ^ γ)`.
* `flagValue p f k` is the right side of the depth-flag formula for `f ∈ R[[x_1, …, x_n]]`
  (Definition 7.3: the class parts `f_κ`, the spaces `U_d`, `r_f` and the flag `d(j)`), and
  `Dir.dirFlagValue p f k` the same for the Dirichlet ring, where the class of `n` is
  `(v_q(n) mod p)_q`.

## Results

Each theorem's docstring names its result in the accompanying preprint (J. S. Farland, 2026):
Theorems 4.4, 5.1, 6.1, 7.4 and 7.7 and Corollary 7.8. CLAIMS.md maps every result to Lean.
-/

open Finset
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius Nat

namespace Frobenius

/-! ### The Kempner value -/

/-- The Kempner value `S(p ^ k)`: the least `N` with `p ^ k ∣ N!`. -/
noncomputable def kempner (p k : ℕ) : ℕ := sInf {N : ℕ | p ^ k ∣ N !}

/-! ### The Dirichlet ring -/

/-- The Frobenius pushforward `E_p` on arithmetic functions: `(E_p f)(j ^ p) = f(j)`, and
`(E_p f)(n) = 0` when `n` is not a `p`th power. -/
def frobPush {R : Type*} [CommRing R] (p : ℕ) (f : ArithmeticFunction R) :
    ArithmeticFunction R :=
  ⟨fun n => ∑ d ∈ n.divisors, if d ^ p = n then f d else 0, by simp⟩

/-! ### Level identities and the level count -/

/-- A level `L` identity for `f` modulo `p ^ k` with respect to a map `σ` (in the preprint a
Frobenius lift): there are `g_0, …, g_L` with `1/f ≡ ∑_{z ≤ L} f ^ z σ(g_z) (mod p ^ k)`,
written without the inverse as `p ^ k ∣ 1 - f ∑_{z ≤ L} f ^ z σ(g_z)`. For the Dirichlet ring
with `σ = E_p`, divisibility by `p ^ k` means that every value is divisible by `p ^ k`. -/
def HasLevel {A : Type*} [CommRing A] (p : ℕ) (σ : A → A) (f : A) (k L : ℕ) : Prop :=
  ∃ g : ℕ → A, (p : A) ^ k ∣ 1 - f * ∑ z ∈ range (L + 1), f ^ z * σ (g z)

/-- The level count `L_f(p, k)`: the least `L` with a level `L` identity (`0` if there is none,
so upper bounds are stated together with `HasLevel`). -/
noncomputable def levelCount {A : Type*} [CommRing A] (p : ℕ) (σ : A → A) (f : A) (k : ℕ) : ℕ :=
  sInf {L | HasLevel p σ f k L}

/-! ### The series `Φ_p` of Section 5 -/

/-- `Φ_p(z) = ∑_{n ≥ 0} z ^ (p ^ n) ∈ ℤ[[z]]`: the coefficient of `z ^ m` is `1` if `m` is a
power of `p` and `0` otherwise. -/
noncomputable def Phi (p : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (Set.indicator (Set.range fun k : ℕ => p ^ k) 1)

/-- `A(z, Φ_p(z)) ∈ ℤ[[z]]` for `A ∈ ℤ[z][t]` (the outer variable is `t`). -/
noncomputable def evalPhi (p : ℕ) (A : Polynomial (Polynomial ℤ)) : PowerSeries ℤ :=
  A.eval₂ Polynomial.coeToPowerSeries.ringHom (Phi p)

/-- `A(z, Φ_p(z)) ≡ 0 (mod p ^ γ)`: every coefficient is divisible by `p ^ γ`. -/
def VanishesMod (p γ : ℕ) (A : Polynomial (Polynomial ℤ)) : Prop :=
  ∀ n : ℕ, (p : ℤ) ^ γ ∣ PowerSeries.coeff n (evalPhi p A)

/-! ### The depth flag in `R[[x_1, …, x_n]]` (Definition 7.3) -/

section Flag

open MvPowerSeries

variable (p : ℕ) {R : Type*} [CommRing R]

/-- The exponents `e` with `0 ≤ e_i < p` for every `i`. -/
noncomputable def digitExps (n : ℕ) : Finset (Fin n →₀ ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.range p).map
    (Finsupp.equivFunOnFinite (α := Fin n) (M := ℕ)).symm.toEmbedding

variable {n : ℕ}

/-- The class part `a_e` of `a`, for `e ∈ digitExps p n`: `coeff d a_e = coeff (p d + e) a`, so
that `a = ∑_e x ^ e σ(a_e)`. -/
noncomputable def classPart (a : MvPowerSeries (Fin n) R) (e : Fin n →₀ ℕ) :
    MvPowerSeries (Fin n) R :=
  fun d => coeff (p • d + e) a

/-- The class of an exponent vector modulo `p`, as a vector over `𝔽_p`. -/
def classVec (κ : Fin n →₀ ℕ) : Fin n → ZMod p := fun i => (κ i : ZMod p)

/-- `U_d`: the span of the classes `κ ≠ 0` with `v_p(f_κ) ≤ d`. -/
noncomputable def depthSpace (f : MvPowerSeries (Fin n) R) (d : ℕ) :
    Submodule (ZMod p) (Fin n → ZMod p) :=
  Submodule.span (ZMod p) (classVec p '' {κ | κ ∈ digitExps p n ∧ κ ≠ 0 ∧
    ¬ (p : MvPowerSeries (Fin n) R) ^ (d + 1) ∣ classPart p f κ})

/-- The span of all classes `κ ≠ 0` with `f_κ ≠ 0`. -/
noncomputable def fullSpace (f : MvPowerSeries (Fin n) R) : Submodule (ZMod p) (Fin n → ZMod p) :=
  Submodule.span (ZMod p) (classVec p '' {κ | κ ∈ digitExps p n ∧ κ ≠ 0 ∧ classPart p f κ ≠ 0})

/-- `r_f`, the dimension of `fullSpace p f`. -/
noncomputable def rankF (f : MvPowerSeries (Fin n) R) : ℕ := Module.finrank (ZMod p) (fullSpace p f)

/-- The depth flag `d(j) = min {d : dim U_d ≥ j}`, with `d(0) = 0`. -/
noncomputable def depthFlag (f : MvPowerSeries (Fin n) R) (j : ℕ) : ℕ :=
  if j = 0 then 0 else sInf {d | j ≤ Module.finrank (ZMod p) (depthSpace p f d)}

/-- The jump `d(j + 1) - d(j)`. -/
noncomputable def flagJump (f : MvPowerSeries (Fin n) R) (j : ℕ) : ℕ :=
  depthFlag p f (j + 1) - depthFlag p f j

/-- The right side of the depth-flag formula (eq. (7.5)):
`min (p ^ r_f, min {m : v_p(m!) + ∑_{j < r_f} (d(j+1) - d(j)) ⌊m / p ^ j⌋ ≥ k})`. -/
noncomputable def flagValue (f : MvPowerSeries (Fin n) R) (k : ℕ) : ℕ :=
  sInf {m | p ^ rankF p f ≤ m ∨ k ≤ padicValNat p m.factorial
    + ∑ j ∈ Finset.range (rankF p f), flagJump p f j * (m / p ^ j)}

end Flag

/-! ### The depth flag in the Dirichlet ring (Theorem 7.7) -/

namespace Dir

section Defs

variable (p : ℕ) {R : Type*} [CommRing R]

/-- The class `κ(n) = (v_q(n) mod p)_q`. -/
noncomputable def cls (n : ℕ) : ℕ →₀ ZMod p :=
  Finsupp.mapRange (fun a : ℕ => (a : ZMod p)) Nat.cast_zero n.factorization

/-- Witnesses of depth `≤ d` in `X`: `n ∈ X`, `n ≠ 0`, `κ(n) ≠ 0`, `p ^ (d+1) ∤ f(n)`. -/
def witSet (f : ArithmeticFunction R) (X : Set ℕ) (d : ℕ) : Set ℕ :=
  {n | n ∈ X ∧ n ≠ 0 ∧ cls p n ≠ 0 ∧ ¬ (p : R) ^ (d + 1) ∣ f n}

/-- Witnesses of a nonzero class part: `n ∈ X`, `n ≠ 0`, `κ(n) ≠ 0`, `f(n) ≠ 0`. -/
def fullWit (f : ArithmeticFunction R) (X : Set ℕ) : Set ℕ :=
  {n | n ∈ X ∧ n ≠ 0 ∧ cls p n ≠ 0 ∧ f n ≠ 0}

/-- `U_d`, read from witnesses in `X`. -/
noncomputable def dSpace (f : ArithmeticFunction R) (X : Set ℕ) (d : ℕ) :
    Submodule (ZMod p) (ℕ →₀ ZMod p) :=
  Submodule.span (ZMod p) (cls p '' witSet p f X d)

/-- The span of the classes `κ ≠ 0` with `f_κ ≠ 0`, read from witnesses in `X`. -/
noncomputable def fSpace (f : ArithmeticFunction R) (X : Set ℕ) :
    Submodule (ZMod p) (ℕ →₀ ZMod p) :=
  Submodule.span (ZMod p) (cls p '' fullWit p f X)

/-- `r_f` as a cardinal (finite or `ℵ₀`). -/
noncomputable def dRank (f : ArithmeticFunction R) (X : Set ℕ) : Cardinal :=
  Module.rank (ZMod p) (fSpace p f X)

/-- The depth flag `d(j)`, `d(0) = 0`. -/
noncomputable def dFlag (f : ArithmeticFunction R) (X : Set ℕ) (j : ℕ) : ℕ :=
  if j = 0 then 0 else sInf {d | (j : Cardinal) ≤ Module.rank (ZMod p) (dSpace p f X d)}

/-- The right side of the depth-flag formula, with `p ^ ∞ = ∞`. -/
noncomputable def dFlagValue (f : ArithmeticFunction R) (X : Set ℕ) (k : ℕ) : ℕ :=
  sInf {m | (∃ r : ℕ, dRank p f X = r ∧ p ^ r ≤ m) ∨
    k ≤ padicValNat p m.factorial +
      ∑ j ∈ (Finset.range (m + 1)).filter (fun j : ℕ => ((j : ℕ) : Cardinal) < dRank p f X),
        (dFlag p f X (j + 1) - dFlag p f X j) * (m / p ^ j)}

/-- The Dirichlet depth-flag value, the flag read over all positive integers. -/
noncomputable abbrev dirFlagValue (f : ArithmeticFunction R) (k : ℕ) : ℕ :=
  dFlagValue p f Set.univ k

end Defs

end Dir

/-! ## Headline results -/

/-- **Theorem 4.4.** `L(p, k) = S(p ^ k) - 1`: modulo `p ^ k`, `μ` is a sum of `ζ ^ z * E_p(g_z)` over the
levels `z ≤ S(p ^ k) - 1` (`ζ ^ z` the Dirichlet power), and every such identity, valid at
every `n`, has `S(p ^ k) ≤ L + 1`. -/
theorem mobius_levels (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k) :
    (∃ g : ℕ → ArithmeticFunction ℤ, ∀ n, (p : ℤ) ^ k ∣ (μ : ArithmeticFunction ℤ) n -
        (∑ z ∈ range (kempner p k - 1 + 1), (ζ : ArithmeticFunction ℤ) ^ z * frobPush p (g z)) n) ∧
    ∀ (L : ℕ) (g : ℕ → ArithmeticFunction ℤ),
      (∀ n, (p : ℤ) ^ k ∣ (μ : ArithmeticFunction ℤ) n -
        (∑ z ∈ range (L + 1), (ζ : ArithmeticFunction ℤ) ^ z * frobPush p (g z)) n) →
      kempner p k ≤ L + 1 := by
  sorry

/-- **Theorem 5.1.** The `t`-degrees of the monic `A ∈ ℤ[z][t]` with `A(z, Φ_p) ≡ 0 (mod p ^ γ)` are
exactly the `d` with `p ^ γ ∣ d!`. -/
theorem kkm_degrees (p : ℕ) [Fact p.Prime] (γ : ℕ) :
    {d : ℕ | ∃ A : Polynomial (Polynomial ℤ), A.Monic ∧ A.natDegree = d ∧ VanishesMod p γ A} =
      {d : ℕ | p ^ γ ∣ d !} := by
  sorry

/-- **Theorem 5.1 (Conjecture 4 of Kauers, Krattenthaler and Müller).** The least `t`-degree of a
monic `A ∈ ℤ[z][t]` with `A(z, Φ_p) ≡ 0 (mod p ^ γ)` is `S(p ^ γ)`. -/
theorem kkm_conjecture4 (p : ℕ) [Fact p.Prime] (γ : ℕ) :
    IsLeast {d : ℕ | ∃ A : Polynomial (Polynomial ℤ), A.Monic ∧ A.natDegree = d ∧
      VanishesMod p γ A} (kempner p γ) := by
  sorry

/-- **Theorem 5.1, the best modulus.** For each `d`, the largest `γ` for which some monic `A` of `t`-degree `d` has
`A(z, Φ_p) ≡ 0 (mod p ^ γ)` is `v_p(d!)`. -/
theorem kkm_greatest_modulus (p : ℕ) [Fact p.Prime] (d : ℕ) :
    IsGreatest {γ : ℕ | ∃ A : Polynomial (Polynomial ℤ), A.Monic ∧ A.natDegree = d ∧
      VanishesMod p γ A} (padicValNat p d !) := by
  sorry

/-- **Theorem 6.1, the identity.** For every commutative ring `R` and every `f` with `f(1)` a unit,
`f` has a level identity at level `S(p ^ k) - 1` with respect to `E_p`. -/
theorem dirichlet_identity {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime]
    (f : ArithmeticFunction R) (hf : IsUnit (f 1)) {k : ℕ} (hk : 1 ≤ k) :
    HasLevel p (frobPush p) f k (kempner p k - 1) := by
  sorry

/-- **Theorem 6.1.** `L_f(p, k) ≤ S(p ^ k) - 1` for every commutative ring `R` and every `f` with
`f(1)` a unit. -/
theorem dirichlet_upper {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime]
    (f : ArithmeticFunction R) (hf : IsUnit (f 1)) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frobPush p) f k + 1 ≤ kempner p k := by
  sorry

/-- **Corollary 7.8 over `ℤ`, the lower bound:** `n` distinct primes `q_i` with
`p ∤ f(q_i)` give `L_f(p, k) + 1 ≥ min (p ^ n, S(p ^ k))`; no multiplicativity is assumed. -/
theorem dirichlet_lower_int (p : ℕ) [Fact p.Prime] (f : ArithmeticFunction ℤ)
    (hf : IsUnit (f 1)) {n : ℕ} {q : Fin n → ℕ} (hq : ∀ i, (q i).Prime)
    (hinj : Function.Injective q) (hfq : ∀ i, ¬ (p : ℤ) ∣ f (q i)) {k : ℕ} (hk : 1 ≤ k) :
    min (p ^ n) (kempner p k) ≤ levelCount p (frobPush p) f k + 1 := by
  sorry

/-- **Corollary 7.8 over `ℤ`, the exact value:** if moreover `S(p ^ k) ≤ p ^ n`, then
`L_f(p, k) = S(p ^ k) - 1`. -/
theorem dirichlet_exact_int (p : ℕ) [Fact p.Prime] (f : ArithmeticFunction ℤ)
    (hf : IsUnit (f 1)) {n : ℕ} {q : Fin n → ℕ} (hq : ∀ i, (q i).Prime)
    (hinj : Function.Injective q) (hfq : ∀ i, ¬ (p : ℤ) ∣ f (q i)) {k : ℕ} (hk : 1 ≤ k)
    (hn : kempner p k ≤ p ^ n) :
    levelCount p (frobPush p) f k + 1 = kempner p k := by
  sorry

/-- **Corollary 7.8 over `ℤ_[p]`, the lower bound.** -/
theorem dirichlet_lower_padic (p : ℕ) [Fact p.Prime] (f : ArithmeticFunction ℤ_[p])
    (hf : IsUnit (f 1)) {n : ℕ} {q : Fin n → ℕ} (hq : ∀ i, (q i).Prime)
    (hinj : Function.Injective q) (hfq : ∀ i, ¬ (p : ℤ_[p]) ∣ f (q i)) {k : ℕ} (hk : 1 ≤ k) :
    min (p ^ n) (kempner p k) ≤ levelCount p (frobPush p) f k + 1 := by
  sorry

/-- **Corollary 7.8 over `ℤ_[p]`, the exact value.** -/
theorem dirichlet_exact_padic (p : ℕ) [Fact p.Prime] (f : ArithmeticFunction ℤ_[p])
    (hf : IsUnit (f 1)) {n : ℕ} {q : Fin n → ℕ} (hq : ∀ i, (q i).Prime)
    (hinj : Function.Injective q) (hfq : ∀ i, ¬ (p : ℤ_[p]) ∣ f (q i)) {k : ℕ} (hk : 1 ≤ k)
    (hn : kempner p k ≤ p ^ n) :
    levelCount p (frobPush p) f k + 1 = kempner p k := by
  sorry

/-- **Theorem 7.4 over `ℤ`.** For every unit `f` of `ℤ[[x_1, …, x_n]]` with the lift
`σ(x_i) = x_i ^ p`, every prime `p` and every `k ≥ 1`, the least level `L_f(p, k)` of an
identity exists and `L_f(p, k) + 1` is the value of the depth-flag formula. -/
theorem flag_formula_int (p : ℕ) [hp : Fact p.Prime] {n : ℕ} {f u : MvPowerSeries (Fin n) ℤ}
    (hfu : f * u = 1) {k : ℕ} (hk : 1 ≤ k) :
    IsLeast {L | HasLevel p ⇑(MvPowerSeries.expand (σ := Fin n) (R := ℤ) p hp.out.ne_zero) f k L}
      (flagValue p f k - 1) := by
  sorry

/-- **Theorem 7.4 over `ℤ_[p]`.** -/
theorem flag_formula_padic (p : ℕ) [hp : Fact p.Prime] {n : ℕ}
    {f u : MvPowerSeries (Fin n) ℤ_[p]} (hfu : f * u = 1) {k : ℕ} (hk : 1 ≤ k) :
    IsLeast {L | HasLevel p ⇑(MvPowerSeries.expand (σ := Fin n) (R := ℤ_[p]) p
      hp.out.ne_zero) f k L} (flagValue p f k - 1) := by
  sorry

/-- **Theorem 7.7 over `ℤ`.** For every `f` with `f(1)` a unit and every `k ≥ 1`, the level count of
`f` in the Dirichlet ring is the depth-flag value, with a flag of finite or infinite length. -/
theorem dirichlet_flag_formula_int (p : ℕ) [Fact p.Prime] {f : ArithmeticFunction ℤ}
    (h1 : IsUnit (f 1)) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frobPush p) f k + 1 = Dir.dirFlagValue p f k := by
  sorry

/-- **Theorem 7.7 over `ℤ_[p]`.** -/
theorem dirichlet_flag_formula_padic (p : ℕ) [Fact p.Prime] {f : ArithmeticFunction ℤ_[p]}
    (h1 : IsUnit (f 1)) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frobPush p) f k + 1 = Dir.dirFlagValue p f k := by
  sorry

end Frobenius
