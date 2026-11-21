module

/-
Run r25, seat L5: Theorem A' without p-independence.

A *valuation tower* of length `N` for `u` is a family of monic `T_b ∈ B[X]` of degree `p ^ b` with
`p ^ γ_b ∣ T_b(u)` (`ValTower`; no condition on the residues). The *top bound* says that a monic
annihilator of degree `p ^ N - 1` modulo `p ^ k` forces `k ≤ ∑_{b<N} (p - 1) γ_b` (`TopBound`).

`monicAnn_iff_digit_of_top`: a valuation tower and the top bound give, for `m < p ^ N`,
`MonicAnn u k m ↔ k ≤ ∑_b e_b(m) γ_b`. The lower half multiplies a degree `m` annihilator by the
digit complement `∏_b T_b ^ (p - 1 - e_b(m))` of degree `p ^ N - 1 - m`.
So the p-independence in L2's `AdaptedTower` can be replaced by the top bound, which seat L5
proves by the trace route (TraceCore.lean, TraceFlag.lean).

Lean v4.33.1 with Mathlib; no sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Basis
public import Frobenius.Levels.Digit
public import Frobenius.Levels.PropP
public import Frobenius.Levels.Flag
public import Frobenius.Levels.Cap

@[expose] public section

namespace FrobLevel

open Polynomial

section ValTower

variable {A : Type*} [CommRing A] {p : ℕ} {σ : A →+* A}

/-- A valuation tower of length `N` (monic levels of degree `p ^ b` in `B[X]`, `p ^ γ_b ∣ T_b(u)`). -/
def ValTower (p : ℕ) (σ : A →+* A) (N : ℕ) (T : ℕ → A[X]) (γ : ℕ → ℕ) (u : A) : Prop :=
  ∀ b < N, (T b).Monic ∧ (T b).natDegree = p ^ b ∧ T b ∈ BPoly σ ∧ (p : A) ^ (γ b) ∣ (T b).eval u

/-- `∑_{b < N} (p - 1) γ_b`, the digit value of `p ^ N - 1`. -/
def topVal (p N : ℕ) (γ : ℕ → ℕ) : ℕ := ∑ b ∈ Finset.range N, (p - 1) * γ b

/-- The top bound: no monic annihilator of degree `p ^ N - 1` modulo `p ^ k` with `k > topVal`. -/
def TopBound (p : ℕ) (σ : A →+* A) (N : ℕ) (γ : ℕ → ℕ) (u : A) : Prop :=
  ∀ k, MonicAnn p σ u k (p ^ N - 1) → k ≤ topVal p N γ

/-- Products of tower levels. -/
noncomputable def prodPoly (N : ℕ) (T : ℕ → A[X]) (e : ℕ → ℕ) : A[X] :=
  ∏ b ∈ Finset.range N, T b ^ e b

theorem prodPoly_spec [Nontrivial A] {N : ℕ} {T : ℕ → A[X]} {γ : ℕ → ℕ} {u : A}
    (htow : ValTower p σ N T γ u) (e : ℕ → ℕ) :
    (prodPoly N T e).Monic ∧ (prodPoly N T e).natDegree = ∑ b ∈ Finset.range N, e b * p ^ b ∧
      prodPoly N T e ∈ BPoly σ ∧
      (p : A) ^ (∑ b ∈ Finset.range N, e b * γ b) ∣ (prodPoly N T e).eval u := by
  refine ⟨monic_prod_of_monic _ _ fun b hb => (htow b (Finset.mem_range.1 hb)).1.pow _, ?_,
    Subring.prod_mem _ fun b hb => pow_mem (htow b (Finset.mem_range.1 hb)).2.2.1 _, ?_⟩
  · rw [prodPoly, natDegree_prod_of_monic _ _ fun b hb =>
      (htow b (Finset.mem_range.1 hb)).1.pow _]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [(htow b (Finset.mem_range.1 hb)).1.natDegree_pow, (htow b (Finset.mem_range.1 hb)).2.1]
  · rw [prodPoly, eval_prod, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_dvd_prod_of_dvd _ _ fun b hb => ?_
    rw [eval_pow, mul_comm, pow_mul]
    exact pow_dvd_pow_of_dvd (htow b (Finset.mem_range.1 hb)).2.2.2 _

theorem sum_geom_pred (p N : ℕ) (hp : 1 ≤ p) :
    ∑ b ∈ Finset.range N, (p - 1) * p ^ b = p ^ N - 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have h1 : 1 ≤ p ^ N := Nat.one_le_pow _ _ hp
    have h2 : (p - 1) * p ^ N + p ^ N = p ^ N * p := by
      rw [mul_comm, ← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hp]
    omega

/-- **Theorem A' without independence**: a valuation tower of length `N` and the top bound give,
for `m < p ^ N`, a monic annihilator of degree `m` modulo `p ^ k` iff `k ≤ ∑_b e_b(m) γ_b`. -/
theorem monicAnn_iff_digit_of_top [Nontrivial A] (hp : 1 ≤ p) {N : ℕ} {T : ℕ → A[X]}
    {γ : ℕ → ℕ} {u : A} (htow : ValTower p σ N T γ u) (htop : TopBound p σ N γ u) {m k : ℕ}
    (hm : m < p ^ N) : MonicAnn p σ u k m ↔ k ≤ digitVal p N γ m := by
  have hdig : ∀ b, digit p b m ≤ p - 1 := fun b => by
    have := digit_lt (p := p) (by omega) b m; omega
  constructor
  · rintro ⟨P, hPm, hPd, hPB, hPu⟩
    set e : ℕ → ℕ := fun b => p - 1 - digit p b m with he
    obtain ⟨hQm, hQd, hQB, hQu⟩ := prodPoly_spec htow e
    have hdeg : P.natDegree + (prodPoly N T e).natDegree = p ^ N - 1 := by
      rw [hPd, hQd, ← sum_geom_pred p N hp]
      conv_lhs => rw [← sum_digit_mul_pow_of_lt hm]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [he, ← add_mul, Nat.add_sub_cancel' (hdig b)]
    have hann : MonicAnn p σ u (k + ∑ b ∈ Finset.range N, e b * γ b) (p ^ N - 1) := by
      refine ⟨P * prodPoly N T e, hPm.mul hQm, ?_, mul_mem hPB hQB, ?_⟩
      · rw [hPm.natDegree_mul hQm, hdeg]
      · rw [eval_mul, pow_add]; exact mul_dvd_mul hPu hQu
    have h1 := htop _ hann
    have h2 : topVal p N γ = digitVal p N γ m + ∑ b ∈ Finset.range N, e b * γ b := by
      rw [topVal, digitVal, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [he, ← add_mul, Nat.add_sub_cancel' (hdig b)]
    omega
  · intro hk
    obtain ⟨hQm, hQd, hQB, hQu⟩ := prodPoly_spec htow (fun b => digit p b m)
    refine ⟨prodPoly N T (fun b => digit p b m), hQm, by rw [hQd, sum_digit_mul_pow_of_lt hm],
      hQB, (pow_dvd_pow _ hk).trans hQu⟩

theorem annDegree_eq_digit_of_top [Nontrivial A] (hp : 1 ≤ p) {N : ℕ} {T : ℕ → A[X]}
    {γ : ℕ → ℕ} {u : A} (htow : ValTower p σ N T γ u) (htop : TopBound p σ N γ u) {k : ℕ}
    (hcap : MonicAnn p σ u k (p ^ N)) :
    annDegree p σ u k = sInf {m | p ^ N ≤ m ∨ k ≤ digitVal p N γ m} := by
  set S := {m | p ^ N ≤ m ∨ k ≤ digitVal p N γ m}
  have hne : (p ^ N) ∈ S := Or.inl le_rfl
  apply le_antisymm
  · have hmem : sInf S ∈ S := Nat.sInf_mem ⟨_, hne⟩
    rcases hmem with h | h
    · exact (annDegree_le hcap).trans h
    · by_cases hlt : sInf S < p ^ N
      · exact annDegree_le ((monicAnn_iff_digit_of_top hp htow htop hlt).2 h)
      · exact (annDegree_le hcap).trans (not_lt.1 hlt)
  · apply Nat.sInf_le
    by_cases hlt : annDegree p σ u k < p ^ N
    · exact Or.inr ((monicAnn_iff_digit_of_top hp htow htop hlt).1 (monicAnn_annDegree hcap))
    · exact Or.inl (not_lt.1 hlt)

/-- The level count from a valuation tower, the top bound and the cap. -/
theorem levelCount_eq_digit_of_top [Nontrivial A] (hp : 1 ≤ p) {N : ℕ} {T : ℕ → A[X]}
    {γ : ℕ → ℕ} {f u : A} (htow : ValTower p σ N T γ u) (htop : TopBound p σ N γ u) {k : ℕ}
    (hfu : (p : A) ^ k ∣ f * u - 1) (hpk : ¬ IsUnit ((p : A) ^ k))
    (hcap : MonicAnn p σ u k (p ^ N)) :
    levelCount p σ f k + 1 = sInf {m | p ^ N ≤ m ∨ k ≤ digitVal p N γ m} := by
  rw [levelCount_add_one hfu hpk hcap, annDegree_eq_digit_of_top hp htow htop hcap]

/-- The flag form: with `γ = flagGamma p δ`, the digit value is the Legendre-type sum. -/
theorem levelCount_eq_flag_of_top [Fact p.Prime] [Nontrivial A] {N : ℕ} {T : ℕ → A[X]}
    {δ : ℕ → ℕ} {f u : A} (htow : ValTower p σ N T (flagGamma p δ) u)
    (htop : TopBound p σ N (flagGamma p δ) u) {k : ℕ} (hfu : (p : A) ^ k ∣ f * u - 1)
    (hpk : ¬ IsUnit ((p : A) ^ k)) (hcap : MonicAnn p σ u k (p ^ N)) :
    levelCount p σ f k + 1 = sInf {m | p ^ N ≤ m ∨
      k ≤ padicValNat p m.factorial + ∑ j ∈ Finset.range N, δ j * (m / p ^ j)} := by
  rw [levelCount_eq_digit_of_top (Fact.out : p.Prime).one_lt.le htow htop hfu hpk hcap]
  congr 1
  ext m
  simp only [Set.mem_ofPred_eq]
  by_cases hm : m < p ^ N
  · rw [digitVal_flagGamma δ hm]
  · simp [not_lt.1 hm]

/-- An adapted tower (L2) is a valuation tower. -/
theorem AdaptedTower.valTower {N : ℕ} {T : ℕ → A[X]} {γ : ℕ → ℕ} {w : ℕ → A} {u : A}
    (h : AdaptedTower p σ N T γ w u) : ValTower p σ N T γ u := fun b hb =>
  ⟨(h.1 b hb).1, (h.1 b hb).2.1, (h.1 b hb).2.2.1, ⟨w b, (h.1 b hb).2.2.2⟩⟩

end ValTower

section Series

open MvPowerSeries

variable (p : ℕ) [hp : Fact p.Prime] {R : Type*} [CommRing R] {n : ℕ}

/-- **R-083 for power series, reduced to a valuation tower and the top bound.** For `f u = 1` in
`R[[x_1..x_n]]` (`p` not a unit in `R`, `k ≥ 1`): if `u` has a valuation tower
of length `r_f` with the flag `γ` and the top bound holds, then `L_f + 1` is R-083's value.
The cap is proved (`monicAnn_cap`); no `p`-independence is assumed. -/
theorem levelCount_eq_flagValue_of_top [Nontrivial R]
    (hpu : ¬ IsUnit (p : R)) {f u : MvPowerSeries (Fin n) R} (hfu : f * u = 1) {k : ℕ} (hk : 1 ≤ k)
    (hF : ∃ T : ℕ → Polynomial (MvPowerSeries (Fin n) R),
      ValTower p (frob p) (rankF p f) T (flagGamma p (flagJump p f)) u)
    (htop : TopBound p (frob p) (rankF p f) (flagGamma p (flagJump p f)) u) :
    levelCount p (frob p) f k + 1 = flagValue p f k := by
  obtain ⟨T, htow⟩ := hF
  rw [levelCount_eq_flag_of_top htow htop (by rw [hfu, sub_self]; exact dvd_zero _)
    (not_isUnit_pow_mvPowerSeries p hpu hk) (monicAnn_cap p hfu k)]
  rfl

/-- L2's conditional R-083 with the cap hypothesis discharged (`monicAnn_cap`): only Theorem F's
adapted tower remains as a hypothesis. -/
theorem levelCount_eq_flagValue_of_adapted [Nontrivial R] (htor : NoPTorsion p R)
    (hpu : ¬ IsUnit (p : R)) {f u : MvPowerSeries (Fin n) R} (hfu : f * u = 1) {k : ℕ} (hk : 1 ≤ k)
    (hF : ∃ (T : ℕ → Polynomial (MvPowerSeries (Fin n) R)) (w : ℕ → MvPowerSeries (Fin n) R),
      AdaptedTower p (frob p) (rankF p f) T (flagGamma p (flagJump p f)) w u) :
    levelCount p (frob p) f k + 1 = flagValue p f k :=
  levelCount_eq_flagValue p htor hpu hfu hk hF (monicAnn_cap p hfu k)

end Series

end FrobLevel
