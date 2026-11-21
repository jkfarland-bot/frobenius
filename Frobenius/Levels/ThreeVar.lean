module

/-
Run r25, seat L6: L2's three-variable example (ledger R-082 (1), third example):
`u = (1 + z)(1 + 2x + 4y)` at `p = 2` (variables `x = X 0`, `y = X 1`, `z = X 2`).

* `u3_eq_powPoly`: `u = 1 + z + 2x + 4y + 2xz + 4yz`.
* `finrank_depthSpace_u3`, `rankF_u3`: `dim U_0 = 1` (class of `z`), `dim U_1 = 2` (`z, x, xz`),
  `dim U_d = 3` for `d ≥ 2`; `r = 3`. Flag `(0, 1, 2)` (`depthFlag_u3`).
* `flagGamma_u3`: `γ = (0, 2, 6)`.
* `levelCount_u3_int`, `_padic`: for `f = 1/u` and every `k ≥ 1`,
  `L_f(2, k) + 1 = min(8, min {m : 2 e_1(m) + 6 e_2(m) ≥ k})`.
* `levelCount_ce_three_vars`, `_int`: `L_f(2, 6) + 1 = 4`; this is exactly the statement
  `open_ce_three_vars` of L2's and L5's Open.lean, now proved.

Lean v4.33.1 with Mathlib; no sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Basis
public import Frobenius.Levels.Digit
public import Frobenius.Levels.Flag
public import Frobenius.Levels.Cap
public import Frobenius.Levels.Padic
public import Frobenius.Levels.Assemble
public import Frobenius.Levels.FlagCalc
public import Frobenius.Levels.PolyFlag
public import Frobenius.Levels.PropPAll

@[expose] public section

namespace FrobLevel

open MvPowerSeries

section ThreeVar

/-- The exponents `1, z, x, y, xz, yz`. -/
noncomputable def ex3 : Fin 6 → (Fin 3 →₀ ℕ) :=
  ![0, Finsupp.single 2 1, Finsupp.single 0 1, Finsupp.single 1 1,
    Finsupp.single 0 1 + Finsupp.single 2 1, Finsupp.single 1 1 + Finsupp.single 2 1]

/-- Their `2`-adic valuations: `1, 1, 2, 4, 2, 4`. -/
def val3 : Fin 6 → ℕ := ![0, 0, 1, 2, 1, 2]

theorem fin6_cases (t : Fin 6) : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 := by
  fin_cases t <;> simp

theorem ex3_zero : ex3 0 = 0 := rfl
theorem ex3_one : ex3 1 = Finsupp.single 2 1 := rfl
theorem ex3_two : ex3 2 = Finsupp.single 0 1 := rfl
theorem ex3_three : ex3 3 = Finsupp.single 1 1 := rfl
theorem ex3_four : ex3 4 = Finsupp.single 0 1 + Finsupp.single 2 1 := rfl
theorem ex3_five : ex3 5 = Finsupp.single 1 1 + Finsupp.single 2 1 := rfl

theorem ex3_apply (t : Fin 6) (i : Fin 3) :
    ex3 t i = ![![0, 0, 0], ![0, 0, 1], ![1, 0, 0], ![0, 1, 0], ![1, 0, 1], ![0, 1, 1]] t i := by
  rcases fin6_cases t with rfl | rfl | rfl | rfl | rfl | rfl <;> fin_cases i <;>
    simp [ex3, Finsupp.single_apply]

theorem ex3_mem (t : Fin 6) : ex3 t ∈ digitExps 2 3 := by
  rw [mem_digitExps]
  intro i
  rw [ex3_apply]
  fin_cases t <;> fin_cases i <;> decide

theorem ex3_inj : Function.Injective ex3 := by
  intro s t h
  have h0 := congrArg (· 0) h
  have h1 := congrArg (· 1) h
  have h2 := congrArg (· 2) h
  simp only [ex3_apply] at h0 h1 h2
  fin_cases s <;> fin_cases t <;> first | rfl | (exfalso; revert h0 h1 h2; decide)

variable {R : Type*} [CommRing R]

/-- `(1 + z)(1 + 2x + 4y) = ∑_t 2 ^ (val3 t) x ^ (ex3 t)`. -/
theorem u3_eq_powPoly :
    ((1 + X 2) * (1 + 2 * X 0 + 4 * X 1) : MvPowerSeries (Fin 3) R) = powPoly 2 ex3 val3 := by
  have hm : ∀ (e : Fin 3 →₀ ℕ) (c : R), monomial e c = C c * monomial e 1 := by
    intro e c
    rw [← monomial_zero_eq_C_apply, monomial_mul_monomial, zero_add, mul_one]
  have hXX : ∀ i j : Fin 3, (X i * X j : MvPowerSeries (Fin 3) R)
      = monomial (Finsupp.single i 1 + Finsupp.single j 1) 1 := by
    intro i j; rw [X_def, X_def, monomial_mul_monomial, mul_one]
  have hC : ∀ c : R, (C c : MvPowerSeries (Fin 3) R) * 1 = C c := fun c => mul_one _
  have t0 : monomial (ex3 0) ((2 : R) ^ val3 0) = (1 : MvPowerSeries (Fin 3) R) := by
    rw [ex3_zero, show val3 0 = 0 from rfl, pow_zero, monomial_zero_eq_C_apply, map_one]
  have t1 : monomial (ex3 1) ((2 : R) ^ val3 1) = (X 2 : MvPowerSeries (Fin 3) R) := by
    rw [ex3_one, show val3 1 = 0 from rfl, pow_zero, ← X_def]
  have t2 : monomial (ex3 2) ((2 : R) ^ val3 2) = (C 2 * X 0 : MvPowerSeries (Fin 3) R) := by
    rw [ex3_two, show val3 2 = 1 from rfl, pow_one, hm, ← X_def]
  have t3 : monomial (ex3 3) ((2 : R) ^ val3 3) = (C 4 * X 1 : MvPowerSeries (Fin 3) R) := by
    rw [ex3_three, show val3 3 = 2 from rfl, hm, ← X_def]; norm_num
  have t4 : monomial (ex3 4) ((2 : R) ^ val3 4)
      = (C 2 * (X 0 * X 2) : MvPowerSeries (Fin 3) R) := by
    rw [ex3_four, show val3 4 = 1 from rfl, pow_one, hm, hXX]
  have t5 : monomial (ex3 5) ((2 : R) ^ val3 5)
      = (C 4 * (X 1 * X 2) : MvPowerSeries (Fin 3) R) := by
    rw [ex3_five, show val3 5 = 2 from rfl, hm, hXX]; norm_num
  have e2 : (C 2 : MvPowerSeries (Fin 3) R) = 2 := map_ofNat C 2
  have e4 : (C 4 : MvPowerSeries (Fin 3) R) = 4 := map_ofNat C 4
  rw [powPoly, Fin.sum_univ_six]
  simp only [Nat.cast_ofNat]
  rw [t0, t1, t2, t3, t4, t5, e2, e4]
  ring

theorem classVec_ex3_one : classVec 2 (ex3 1) = Pi.single 2 1 := by
  rw [ex3_one, classVec_single]
theorem classVec_ex3_two : classVec 2 (ex3 2) = Pi.single 0 1 := by
  rw [ex3_two, classVec_single]
theorem classVec_ex3_three : classVec 2 (ex3 3) = Pi.single 1 1 := by
  rw [ex3_three, classVec_single]
theorem classVec_ex3_four : classVec 2 (ex3 4) = Pi.single 0 1 + Pi.single 2 1 := by
  rw [ex3_four, classVec_add, classVec_single, classVec_single]
theorem classVec_ex3_five : classVec 2 (ex3 5) = Pi.single 1 1 + Pi.single 2 1 := by
  rw [ex3_five, classVec_add, classVec_single, classVec_single]

/-- The span of the classes of `ex3 t` over a set `S` of indices, when `S` is squeezed between
the indices needed and all nonzero ones. -/
theorem finrank_ex3 (S : Set (Fin 6)) (Tf : Finset (Fin 3))
    (hS0 : (0 : Fin 6) ∉ S)
    (h1 : ∀ t ∈ S, classVec 2 (ex3 t) ∈ Submodule.span (ZMod 2)
      ((fun i => (Pi.single i 1 : Fin 3 → ZMod 2)) '' (Tf : Set (Fin 3))))
    (h2 : ∀ i ∈ Tf, ∃ t ∈ S, classVec 2 (ex3 t) = Pi.single i 1) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ((fun t => classVec 2 (ex3 t)) '' S))
      = Tf.card := by
  refine finrank_span_eq_card ?_ ?_
  · rintro _ ⟨t, ht, rfl⟩; exact h1 t ht
  · intro i hi
    obtain ⟨t, ht, he⟩ := h2 i hi
    rw [← he]
    exact Submodule.subset_span ⟨t, ht, rfl⟩

theorem single_mem_span3 {Tf : Finset (Fin 3)} {i : Fin 3} (hi : i ∈ Tf) :
    (Pi.single i 1 : Fin 3 → ZMod 2) ∈ Submodule.span (ZMod 2)
      ((fun i => (Pi.single i 1 : Fin 3 → ZMod 2)) '' (Tf : Set (Fin 3))) :=
  Submodule.subset_span ⟨i, hi, rfl⟩

variable [IsDomain R]

/-- `dim U_d` for `u = (1 + z)(1 + 2x + 4y)`. -/
theorem finrank_depthSpace_u3 (hp0 : (2 : R) ≠ 0) (hpu : ¬ IsUnit (2 : R)) (d : ℕ) :
    Module.finrank (ZMod 2)
      (depthSpace 2 ((1 + X 2) * (1 + 2 * X 0 + 4 * X 1) : MvPowerSeries (Fin 3) R) d)
      = if d = 0 then 1 else if d = 1 then 2 else 3 := by
  have hp0' : ((2 : ℕ) : R) ≠ 0 := by exact_mod_cast hp0
  have hpu' : ¬ IsUnit ((2 : ℕ) : R) := by exact_mod_cast hpu
  rw [u3_eq_powPoly, depthSpace_powPoly hp0' hpu' ex3_mem ex3_inj]
  have hS0 : (0 : Fin 6) ∉ {t | ex3 t ≠ 0 ∧ val3 t ≤ d} := fun h => h.1 rfl
  split_ifs with hd0 hd1
  · subst hd0
    rw [finrank_ex3 _ {2} hS0]
    · rfl
    · rintro t ⟨hne, hle⟩
      rcases fin6_cases t with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [val3] at hle
      · exact absurd rfl hne
      · rw [classVec_ex3_one]; exact single_mem_span3 (by simp)
    · intro i hi
      rw [Finset.mem_singleton] at hi; subst hi
      exact ⟨1, ⟨by simp [ex3], by simp [val3]⟩, classVec_ex3_one⟩
  · subst hd1
    rw [finrank_ex3 _ {0, 2} hS0]
    · rfl
    · rintro t ⟨hne, hle⟩
      rcases fin6_cases t with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [val3] at hle
      · exact absurd rfl hne
      · rw [classVec_ex3_one]; exact single_mem_span3 (by simp)
      · rw [classVec_ex3_two]; exact single_mem_span3 (by simp)
      · rw [classVec_ex3_four]
        exact Submodule.add_mem _ (single_mem_span3 (by simp)) (single_mem_span3 (by simp))
    · intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact ⟨2, ⟨by simp [ex3], by simp [val3]⟩, classVec_ex3_two⟩
      · exact ⟨1, ⟨by simp [ex3], by simp [val3]⟩, classVec_ex3_one⟩
  · have hd2 : 2 ≤ d := by omega
    rw [finrank_ex3 _ Finset.univ hS0]
    · rfl
    · rintro t ⟨hne, _⟩
      rcases fin6_cases t with rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl hne
      · rw [classVec_ex3_one]; exact single_mem_span3 (by simp)
      · rw [classVec_ex3_two]; exact single_mem_span3 (by simp)
      · rw [classVec_ex3_three]; exact single_mem_span3 (by simp)
      · rw [classVec_ex3_four]
        exact Submodule.add_mem _ (single_mem_span3 (by simp)) (single_mem_span3 (by simp))
      · rw [classVec_ex3_five]
        exact Submodule.add_mem _ (single_mem_span3 (by simp)) (single_mem_span3 (by simp))
    · intro i _
      fin_cases i
      · exact ⟨2, ⟨by simp [ex3], by simp [val3]; omega⟩, classVec_ex3_two⟩
      · exact ⟨3, ⟨by simp [ex3], by simp [val3]; omega⟩, classVec_ex3_three⟩
      · exact ⟨1, ⟨by simp [ex3], by simp [val3]⟩, classVec_ex3_one⟩

theorem rankF_u3 (hp0 : (2 : R) ≠ 0) :
    rankF 2 ((1 + X 2) * (1 + 2 * X 0 + 4 * X 1) : MvPowerSeries (Fin 3) R) = 3 := by
  have hp0' : ((2 : ℕ) : R) ≠ 0 := by exact_mod_cast hp0
  rw [rankF, u3_eq_powPoly, fullSpace_powPoly hp0' ex3_mem ex3_inj]
  have hS0 : (0 : Fin 6) ∉ {t | ex3 t ≠ 0} := fun h => h rfl
  rw [finrank_ex3 _ Finset.univ hS0]
  · rfl
  · rintro t hne
    rcases fin6_cases t with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd rfl hne
    · rw [classVec_ex3_one]; exact single_mem_span3 (by simp)
    · rw [classVec_ex3_two]; exact single_mem_span3 (by simp)
    · rw [classVec_ex3_three]; exact single_mem_span3 (by simp)
    · rw [classVec_ex3_four]
      exact Submodule.add_mem _ (single_mem_span3 (by simp)) (single_mem_span3 (by simp))
    · rw [classVec_ex3_five]
      exact Submodule.add_mem _ (single_mem_span3 (by simp)) (single_mem_span3 (by simp))
  · intro i _
    fin_cases i
    · exact ⟨2, by simp [ex3], classVec_ex3_two⟩
    · exact ⟨3, by simp [ex3], classVec_ex3_three⟩
    · exact ⟨1, by simp [ex3], classVec_ex3_one⟩

/-- **The flag of `(1 + z)(1 + 2x + 4y)` at `p = 2` is `(0, 1, 2)`.** -/
theorem depthFlag_u3 (hp0 : (2 : R) ≠ 0) (hpu : ¬ IsUnit (2 : R)) :
    depthFlag 2 ((1 + X 2) * (1 + 2 * X 0 + 4 * X 1) : MvPowerSeries (Fin 3) R) 1 = 0 ∧
    depthFlag 2 ((1 + X 2) * (1 + 2 * X 0 + 4 * X 1) : MvPowerSeries (Fin 3) R) 2 = 1 ∧
    depthFlag 2 ((1 + X 2) * (1 + 2 * X 0 + 4 * X 1) : MvPowerSeries (Fin 3) R) 3 = 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [depthFlag, if_neg (by norm_num)]
    refine sInf_eq_of_iff fun d => ?_
    rw [finrank_depthSpace_u3 hp0 hpu]
    split_ifs <;> omega

/-- **`γ = (0, 2, 6)`.** -/
theorem flagGamma_u3 (hp0 : (2 : R) ≠ 0) (hpu : ¬ IsUnit (2 : R)) :
    flagGamma 2 (flagJump 2 ((1 + X 2) * (1 + 2 * X 0 + 4 * X 1) : MvPowerSeries (Fin 3) R)) 0 = 0 ∧
    flagGamma 2 (flagJump 2 ((1 + X 2) * (1 + 2 * X 0 + 4 * X 1) : MvPowerSeries (Fin 3) R)) 1 = 2 ∧
    flagGamma 2 (flagJump 2 ((1 + X 2) * (1 + 2 * X 0 + 4 * X 1) : MvPowerSeries (Fin 3) R)) 2 = 6 := by
  obtain ⟨h1, h2, h3⟩ := depthFlag_u3 hp0 hpu
  set u : MvPowerSeries (Fin 3) R := (1 + X 2) * (1 + 2 * X 0 + 4 * X 1)
  have h0 : depthFlag 2 u 0 = 0 := by simp [depthFlag]
  have j0 : flagJump 2 u 0 = 0 := by
    show depthFlag 2 u (0 + 1) - depthFlag 2 u 0 = 0; rw [h1, h0]
  have j1 : flagJump 2 u 1 = 1 := by
    show depthFlag 2 u (1 + 1) - depthFlag 2 u 1 = 1; rw [h2, h1]
  have j2 : flagJump 2 u 2 = 1 := by
    show depthFlag 2 u (2 + 1) - depthFlag 2 u 2 = 1; rw [h3, h2]
  have g0 : flagGamma 2 (flagJump 2 u) 0 = 0 := by rw [flagGamma_zero, j0]
  have g1 : flagGamma 2 (flagJump 2 u) 1 = 2 := by rw [flagGamma_succ, g0, j1]
  have g2 : flagGamma 2 (flagJump 2 u) 2 = 6 := by rw [flagGamma_succ, g1, j2]
  exact ⟨g0, g1, g2⟩

/-- R-083's value for `u = (1 + z)(1 + 2x + 4y)`, every `k`. -/
theorem flagValue_u3 (hp0 : (2 : R) ≠ 0) (hpu : ¬ IsUnit (2 : R)) (k : ℕ) :
    flagValue 2 ((1 + X 2) * (1 + 2 * X 0 + 4 * X 1) : MvPowerSeries (Fin 3) R) k
      = sInf {m | 8 ≤ m ∨ k ≤ digit 2 1 m * 2 + digit 2 2 m * 6} := by
  obtain ⟨g0, g1, g2⟩ := flagGamma_u3 hp0 hpu
  unfold flagValue
  rw [rankF_u3 hp0, ← sInf_digit_eq_flag 2]
  congr 1
  ext m
  simp only [Set.mem_ofPred_eq, digitVal, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    g0, g1, g2, mul_zero]
  norm_num

end ThreeVar

section ThreeVarLevel

/-- For every `k ≥ 1`: `L_f(2, k) + 1 = min(8, min {m : 2 e_1(m) + 6 e_2(m) ≥ k})`. -/
theorem levelCount_u3_padic {f : MvPowerSeries (Fin 3) ℤ_[2]}
    (hfu : f * ((1 + X 2) * (1 + 2 * X 0 + 4 * X 1)) = 1) {k : ℕ} (hk : 1 ≤ k) :
    levelCount 2 (frob 2) f k + 1 = sInf {m | 8 ≤ m ∨ k ≤ digit 2 1 m * 2 + digit 2 2 m * 6} := by
  rw [levelCount_eq_flagValue_padic 2 hfu hk, ← flagValue_inv hfu,
    flagValue_u3 (by exact_mod_cast padicInt_natCast_ne_zero 2)
      (by exact_mod_cast padicInt_not_isUnit 2)]

theorem levelCount_u3_int {f : MvPowerSeries (Fin 3) ℤ}
    (hfu : f * ((1 + X 2) * (1 + 2 * X 0 + 4 * X 1)) = 1) {k : ℕ} (hk : 1 ≤ k) :
    levelCount 2 (frob 2) f k + 1 = sInf {m | 8 ≤ m ∨ k ≤ digit 2 1 m * 2 + digit 2 2 m * 6} := by
  rw [levelCount_eq_flagValue_int 2 hfu hk, ← flagValue_inv hfu,
    flagValue_u3 (by norm_num) (by exact_mod_cast int_not_isUnit 2)]

theorem sInf_u3_six : sInf {m | 8 ≤ m ∨ 6 ≤ digit 2 1 m * 2 + digit 2 2 m * 6} = 4 := by
  refine sInf_eq_of_mem ?_ ?_
  · right; decide
  · intro m hm
    interval_cases m <;> decide

/-- **L2's open `open_ce_three_vars`, proved**: `p = 2`, `u = (1 + z)(1 + 2x + 4y)`, `k = 6`,
`L + 1 = 4`. -/
theorem levelCount_ce_three_vars {f : MvPowerSeries (Fin 3) ℤ_[2]}
    (hfu : f * ((1 + X 2) * (1 + 2 * X 0 + 4 * X 1)) = 1) :
    levelCount 2 (frob 2) f 6 + 1 = 4 := by
  rw [levelCount_u3_padic hfu (by norm_num), sInf_u3_six]

theorem levelCount_ce_three_vars_int {f : MvPowerSeries (Fin 3) ℤ}
    (hfu : f * ((1 + X 2) * (1 + 2 * X 0 + 4 * X 1)) = 1) :
    levelCount 2 (frob 2) f 6 + 1 = 4 := by
  rw [levelCount_u3_int hfu (by norm_num), sInf_u3_six]

end ThreeVarLevel

end FrobLevel
