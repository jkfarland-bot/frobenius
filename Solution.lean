module

public import Frobenius.Statements
public import Frobenius

@[expose] public section

/-!
# Proved solution

Each headline theorem below has exactly the statement of its counterpart in `Challenge.lean`.
The definitions it uses come from `Frobenius/Statements.lean`, a byte-identical copy of the
Challenge's definitions, and the bridge lemmas in `Frobenius.Bridge` identify them with the
definitions of the development (`FrobCong`, `Frobenius.KKM`, `FrobLevel`), mostly by `rfl`.
-/

open Finset
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius Nat

namespace Frobenius

/-! ### Bridges between the statement definitions and the development -/

namespace Bridge

theorem sInf_eq_find {P : ℕ → Prop} [DecidablePred P] (h : ∃ n, P n) :
    sInf {n | P n} = Nat.find h :=
  le_antisymm (Nat.sInf_le (Nat.find_spec h)) (Nat.find_min' h (Nat.sInf_mem h))

theorem kempner_eq_cong (p : ℕ) [Fact p.Prime] (k : ℕ) :
    kempner p k = FrobCong.kempner p k :=
  sInf_eq_find (FrobCong.exists_kempner p k)

theorem kempner_eq_level (p : ℕ) [Fact p.Prime] (k : ℕ) :
    kempner p k = FrobLevel.kempner p k :=
  sInf_eq_find (FrobLevel.exists_kempner p k)

theorem kempner_eq_kkm (p : ℕ) [Fact p.Prime] (k : ℕ) :
    kempner p k = Frobenius.KKM.kempner p k := by
  classical
  unfold Frobenius.KKM.kempner
  exact sInf_eq_find (Frobenius.KKM.exists_kempner p k)

theorem frobPush_eq_cong (p : ℕ) (f : ArithmeticFunction ℤ) :
    frobPush p f = FrobCong.frobPush p f := rfl

theorem levelCount_dir {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime]
    (f : ArithmeticFunction R) (k : ℕ) :
    levelCount p (frobPush p) f k = FrobLevel.levelCount p (FrobLevel.Dir.Ep p) f k := rfl

theorem hasLevel_dir {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime]
    (f : ArithmeticFunction R) (k L : ℕ) :
    HasLevel p (frobPush p) f k L ↔ FrobLevel.HasLevel p (FrobLevel.Dir.Ep p) f k L := Iff.rfl

theorem levelCount_series {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime] {n : ℕ}
    (f : MvPowerSeries (Fin n) R) (k : ℕ) :
    levelCount p ⇑(MvPowerSeries.expand (σ := Fin n) (R := R) p hp.out.ne_zero) f k =
      FrobLevel.levelCount p (FrobLevel.frob p) f k := rfl

theorem flagValue_eq {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] {n : ℕ}
    (f : MvPowerSeries (Fin n) R) (k : ℕ) :
    flagValue p f k = FrobLevel.flagValue p f k := rfl

theorem dirFlagValue_eq {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime]
    (f : ArithmeticFunction R) (k : ℕ) :
    Dir.dirFlagValue p f k = FrobLevel.Dir.dirFlagValue p f k := rfl

theorem vanishesMod_eq (p γ : ℕ) (A : Polynomial (Polynomial ℤ)) :
    VanishesMod p γ A ↔ Frobenius.KKM.VanishesMod p γ A := Iff.rfl

theorem cong_iff (p k : ℕ) (A B : ArithmeticFunction ℤ) :
    (∀ n, (p : ℤ) ^ k ∣ A n - B n) ↔ FrobCong.Cong (p ^ k) A B := by
  simp only [FrobCong.Cong, Nat.cast_pow]

end Bridge

open Bridge

theorem mobius_levels (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 1 ≤ k) :
    (∃ g : ℕ → ArithmeticFunction ℤ, ∀ n, (p : ℤ) ^ k ∣ (μ : ArithmeticFunction ℤ) n -
        (∑ z ∈ range (kempner p k - 1 + 1), (ζ : ArithmeticFunction ℤ) ^ z * frobPush p (g z)) n) ∧
    ∀ (L : ℕ) (g : ℕ → ArithmeticFunction ℤ),
      (∀ n, (p : ℤ) ^ k ∣ (μ : ArithmeticFunction ℤ) n -
        (∑ z ∈ range (L + 1), (ζ : ArithmeticFunction ℤ) ^ z * frobPush p (g z)) n) →
      kempner p k ≤ L + 1 := by
  obtain ⟨⟨g, hg⟩, hlow⟩ := FrobCong.levels_sharp_kempner p k hk
  rw [kempner_eq_cong]
  exact ⟨⟨g, (cong_iff p k _ _).2 hg⟩, fun L g h => hlow L g ((cong_iff p k _ _).1 h)⟩

theorem kkm_degrees (p : ℕ) [Fact p.Prime] (γ : ℕ) :
    {d : ℕ | ∃ A : Polynomial (Polynomial ℤ), A.Monic ∧ A.natDegree = d ∧ VanishesMod p γ A} =
      {d : ℕ | p ^ γ ∣ d !} :=
  Frobenius.KKM.degrees_vanishesMod p γ

theorem kkm_conjecture4 (p : ℕ) [Fact p.Prime] (γ : ℕ) :
    IsLeast {d : ℕ | ∃ A : Polynomial (Polynomial ℤ), A.Monic ∧ A.natDegree = d ∧
      VanishesMod p γ A} (kempner p γ) := by
  rw [kempner_eq_kkm]
  exact Frobenius.KKM.minimal_degree_eq_kempner p γ

theorem kkm_greatest_modulus (p : ℕ) [Fact p.Prime] (d : ℕ) :
    IsGreatest {γ : ℕ | ∃ A : Polynomial (Polynomial ℤ), A.Monic ∧ A.natDegree = d ∧
      VanishesMod p γ A} (padicValNat p d !) :=
  Frobenius.KKM.isGreatest_vanishesMod p d

theorem dirichlet_identity {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime]
    (f : ArithmeticFunction R) (hf : IsUnit (f 1)) {k : ℕ} (hk : 1 ≤ k) :
    HasLevel p (frobPush p) f k (kempner p k - 1) := by
  rw [kempner_eq_level, hasLevel_dir]
  exact FrobLevel.Dir.hasLevel_kempner_any p f
    (ArithmeticFunction.isUnit_iff_isUnit_apply_one.2 hf) hk

theorem dirichlet_upper {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime]
    (f : ArithmeticFunction R) (hf : IsUnit (f 1)) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frobPush p) f k + 1 ≤ kempner p k := by
  rw [kempner_eq_level, levelCount_dir]
  exact FrobLevel.Dir.levelCount_add_one_le_kempner_any p f hf hk

theorem dirichlet_lower_int (p : ℕ) [Fact p.Prime] (f : ArithmeticFunction ℤ)
    (hf : IsUnit (f 1)) {n : ℕ} {q : Fin n → ℕ} (hq : ∀ i, (q i).Prime)
    (hinj : Function.Injective q) (hfq : ∀ i, ¬ (p : ℤ) ∣ f (q i)) {k : ℕ} (hk : 1 ≤ k) :
    min (p ^ n) (kempner p k) ≤ levelCount p (frobPush p) f k + 1 := by
  rw [kempner_eq_level, levelCount_dir]
  exact FrobLevel.Dir.min_le_levelCount_int p f
    (ArithmeticFunction.isUnit_iff_isUnit_apply_one.2 hf) hq hinj hfq hk

theorem dirichlet_exact_int (p : ℕ) [Fact p.Prime] (f : ArithmeticFunction ℤ)
    (hf : IsUnit (f 1)) {n : ℕ} {q : Fin n → ℕ} (hq : ∀ i, (q i).Prime)
    (hinj : Function.Injective q) (hfq : ∀ i, ¬ (p : ℤ) ∣ f (q i)) {k : ℕ} (hk : 1 ≤ k)
    (hn : kempner p k ≤ p ^ n) :
    levelCount p (frobPush p) f k + 1 = kempner p k := by
  rw [kempner_eq_level] at hn ⊢
  rw [levelCount_dir]
  exact FrobLevel.Dir.levelCount_eq_kempner_int p f
    (ArithmeticFunction.isUnit_iff_isUnit_apply_one.2 hf) hq hinj hfq hk hn

theorem dirichlet_lower_padic (p : ℕ) [Fact p.Prime] (f : ArithmeticFunction ℤ_[p])
    (hf : IsUnit (f 1)) {n : ℕ} {q : Fin n → ℕ} (hq : ∀ i, (q i).Prime)
    (hinj : Function.Injective q) (hfq : ∀ i, ¬ (p : ℤ_[p]) ∣ f (q i)) {k : ℕ} (hk : 1 ≤ k) :
    min (p ^ n) (kempner p k) ≤ levelCount p (frobPush p) f k + 1 := by
  rw [kempner_eq_level, levelCount_dir]
  exact FrobLevel.Dir.min_le_levelCount_padic p f
    (ArithmeticFunction.isUnit_iff_isUnit_apply_one.2 hf) hq hinj hfq hk

theorem dirichlet_exact_padic (p : ℕ) [Fact p.Prime] (f : ArithmeticFunction ℤ_[p])
    (hf : IsUnit (f 1)) {n : ℕ} {q : Fin n → ℕ} (hq : ∀ i, (q i).Prime)
    (hinj : Function.Injective q) (hfq : ∀ i, ¬ (p : ℤ_[p]) ∣ f (q i)) {k : ℕ} (hk : 1 ≤ k)
    (hn : kempner p k ≤ p ^ n) :
    levelCount p (frobPush p) f k + 1 = kempner p k := by
  rw [kempner_eq_level] at hn ⊢
  rw [levelCount_dir]
  exact FrobLevel.Dir.levelCount_eq_kempner_padic p f
    (ArithmeticFunction.isUnit_iff_isUnit_apply_one.2 hf) hq hinj hfq hk hn

theorem flag_formula_int (p : ℕ) [hp : Fact p.Prime] {n : ℕ} {f u : MvPowerSeries (Fin n) ℤ}
    (hfu : f * u = 1) {k : ℕ} (hk : 1 ≤ k) :
    IsLeast {L | HasLevel p ⇑(MvPowerSeries.expand (σ := Fin n) (R := ℤ) p hp.out.ne_zero) f k L}
      (flagValue p f k - 1) := by
  have h2 : levelCount p ⇑(MvPowerSeries.expand (σ := Fin n) (R := ℤ) p hp.out.ne_zero) f k + 1 =
      flagValue p f k := by
    rw [levelCount_series, flagValue_eq]
    exact FrobLevel.levelCount_eq_flagValue_int p hfu hk
  have h0 : FrobLevel.HasLevel p (FrobLevel.frob p) f k (FrobLevel.kempner p k - 1) :=
    FrobLevel.MonicAnn.hasLevel (by rw [hfu, sub_self]; exact dvd_zero _)
      (by rw [Nat.sub_add_cancel (FrobLevel.kempner_pos p hk)]
          exact FrobLevel.monicAnn_kempner
            (FrobLevel.frob_isFrobLift (τ := Fin n) p (FrobLevel.int_pow_sub p)) u k)
  rw [← h2, Nat.add_sub_cancel]
  exact ⟨FrobLevel.hasLevel_levelCount h0, fun L hL => Nat.sInf_le hL⟩

theorem flag_formula_padic (p : ℕ) [hp : Fact p.Prime] {n : ℕ}
    {f u : MvPowerSeries (Fin n) ℤ_[p]} (hfu : f * u = 1) {k : ℕ} (hk : 1 ≤ k) :
    IsLeast {L | HasLevel p ⇑(MvPowerSeries.expand (σ := Fin n) (R := ℤ_[p]) p
      hp.out.ne_zero) f k L} (flagValue p f k - 1) := by
  have h2 : levelCount p ⇑(MvPowerSeries.expand (σ := Fin n) (R := ℤ_[p]) p hp.out.ne_zero) f k
      + 1 = flagValue p f k := by
    rw [levelCount_series, flagValue_eq]
    exact FrobLevel.levelCount_eq_flagValue_padic p hfu hk
  have h0 : FrobLevel.HasLevel p (FrobLevel.frob p) f k (FrobLevel.kempner p k - 1) :=
    FrobLevel.MonicAnn.hasLevel (by rw [hfu, sub_self]; exact dvd_zero _)
      (by rw [Nat.sub_add_cancel (FrobLevel.kempner_pos p hk)]
          exact FrobLevel.monicAnn_kempner
            (FrobLevel.frob_isFrobLift (τ := Fin n) p (FrobLevel.padicInt_pow_sub p)) u k)
  rw [← h2, Nat.add_sub_cancel]
  exact ⟨FrobLevel.hasLevel_levelCount h0, fun L hL => Nat.sInf_le hL⟩

theorem dirichlet_flag_formula_int (p : ℕ) [Fact p.Prime] {f : ArithmeticFunction ℤ}
    (h1 : IsUnit (f 1)) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frobPush p) f k + 1 = Dir.dirFlagValue p f k := by
  rw [levelCount_dir, dirFlagValue_eq]
  exact FrobLevel.Dir.levelCount_eq_dirFlagValue_int' p h1 hk

theorem dirichlet_flag_formula_padic (p : ℕ) [Fact p.Prime] {f : ArithmeticFunction ℤ_[p]}
    (h1 : IsUnit (f 1)) {k : ℕ} (hk : 1 ≤ k) :
    levelCount p (frobPush p) f k + 1 = Dir.dirFlagValue p f k := by
  rw [levelCount_dir, dirFlagValue_eq]
  exact FrobLevel.Dir.levelCount_eq_dirFlagValue_padic' p h1 hk

end Frobenius
