module

/-
Run r25, seat L5: the top bound for every unit of `ℤ[[x_1..x_n]]`, with the depth flag.

The characters are `G = Dual(W)`, `W` the span of the classes of `u`; `secM` is a linear section
of the restriction `F_p ^ n → Dual(W)` (dot product), so that `⟨secM φ, κ⟩ = φ κ` on `W`.
`charDep u φ` is the least depth of a monomial of `u` on which the character `φ` is nontrivial.
* `lt_charDep_iff`: `d < charDep u φ ↔ φ` vanishes on `U_d`.
* `card_lt_charDep`: `#{φ ≠ 0 : d < charDep u φ} = p ^ (r - dim U_d) - 1`.
* `sum_charDep`: `∑_{φ ≠ 0} charDep u φ = ∑_{j < r} (d(j+1) - d(j)) (p ^ (r - j) - 1)`.
* `topBound_flag_int`: R-083's top bound for `u`: `TopBound p (frob p) r_u (flagGamma p δ_u) u`.

Lean v4.33.1 with Mathlib; no sorry.
-/
public import Mathlib
public import Frobenius.Levels.Found
public import Frobenius.Levels.Upper
public import Frobenius.Levels.Lower
public import Frobenius.Levels.Basis
public import Frobenius.Levels.Digit
public import Frobenius.Levels.PropP
public import Frobenius.Levels.Flag
public import Frobenius.Levels.Cap
public import Frobenius.Levels.ValTower
public import Frobenius.Levels.TraceCore

@[expose] public section

-- Port (Mathlib v4.35.0-rc2): restore the v4.33 instance path for `AddCommGroup (ZMod p)`.
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace FrobLevel

open MvPowerSeries

open scoped Classical

section Dual

variable (p : ℕ) [hp : Fact p.Prime] {n : ℕ}

/-- The dot product on `F_p ^ n` as a bilinear map. -/
noncomputable def dotL : (Fin n → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p) →ₗ[ZMod p] ZMod p :=
  LinearMap.mk₂ (ZMod p) (fun v w => ∑ i, v i * w i)
    (fun v v' w => by simp [add_mul, Finset.sum_add_distrib])
    (fun c v w => by simp [Finset.mul_sum, mul_assoc])
    (fun v w w' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c v w => by simp [Finset.mul_sum, mul_left_comm])

theorem dotL_apply (v w : Fin n → ZMod p) : dotL p v w = ∑ i, v i * w i := rfl

theorem pair_eq_dotL (v : Fin n → ZMod p) (m : Fin n →₀ ℕ) :
    pair v m = dotL p v (classVec p m) := rfl

/-- Restriction of the dot product to `W`: `F_p ^ n → Dual(W)`. -/
noncomputable def restrictDual (W : Submodule (ZMod p) (Fin n → ZMod p)) :
    (Fin n → ZMod p) →ₗ[ZMod p] Module.Dual (ZMod p) W :=
  (dotL p).compl₂ W.subtype

theorem restrictDual_surjective (W : Submodule (ZMod p) (Fin n → ZMod p)) :
    Function.Surjective (restrictDual p W) := by
  intro φ
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend φ
  refine ⟨fun i => ψ (fun j => if i = j then 1 else 0), ?_⟩
  ext w
  have h1 := LinearMap.pi_apply_eq_sum_univ ψ (w : Fin n → ZMod p)
  have h2 : ψ (w : Fin n → ZMod p) = φ w := by rw [← hψ]; rfl
  rw [← h2, h1]
  show dotL p _ (w : Fin n → ZMod p) = _
  rw [dotL_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul, mul_comm]

/-- A linear section of `restrictDual`. -/
noncomputable def secM (W : Submodule (ZMod p) (Fin n → ZMod p)) :
    Module.Dual (ZMod p) W →ₗ[ZMod p] (Fin n → ZMod p) :=
  Classical.choose (LinearMap.exists_rightInverse_of_surjective (restrictDual p W)
    (LinearMap.range_eq_top.2 (restrictDual_surjective p W)))

theorem secM_spec (W : Submodule (ZMod p) (Fin n → ZMod p)) (φ : Module.Dual (ZMod p) W)
    (w : W) : dotL p (secM p W φ) w = φ w := by
  have h := Classical.choose_spec (LinearMap.exists_rightInverse_of_surjective (restrictDual p W)
    (LinearMap.range_eq_top.2 (restrictDual_surjective p W)))
  have := congrArg (fun f => f φ w) h
  unfold secM
  simpa [restrictDual] using this

end Dual

section Dep

variable (p : ℕ) [hp : Fact p.Prime] {n : ℕ}

/-- The depth of the character `φ` on `u`: the least `d` such that some coefficient of `u` at a
monomial on which `φ` is nontrivial is not divisible by `p ^ (d + 1)`. -/
noncomputable def charDep (u : MvPowerSeries (Fin n) ℤ)
    (φ : Module.Dual (ZMod p) (fullSpace p u)) : ℕ :=
  sInf {d | ∃ m, pair (secM p (fullSpace p u) φ) m ≠ 0 ∧ ¬ (p : ℤ) ^ (d + 1) ∣ coeff m u}

theorem exists_not_pow_dvd {x : ℤ} (hx : x ≠ 0) : ∃ d, ¬ (p : ℤ) ^ (d + 1) ∣ x := by
  refine ⟨x.natAbs, fun h => ?_⟩
  have h1 := Int.natAbs_dvd_natAbs.2 h
  rw [Int.natAbs_pow, Int.natAbs_natCast] at h1
  have h2 := Nat.le_of_dvd (Int.natAbs_pos.2 hx) h1
  have h3 : x.natAbs < p ^ (x.natAbs + 1) :=
    (Nat.lt_pow_self hp.out.one_lt).trans (Nat.pow_lt_pow_right hp.out.one_lt (by omega))
  omega

theorem mem_ker_dotL_iff (v : Fin n → ZMod p) (m : Fin n →₀ ℕ) :
    classVec p m ∈ LinearMap.ker (dotL p v) ↔ pair v m = 0 := by
  rw [LinearMap.mem_ker, pair_eq_dotL]

theorem exists_charDep_witness {u : MvPowerSeries (Fin n) ℤ}
    {φ : Module.Dual (ZMod p) (fullSpace p u)} (hφ : φ ≠ 0) :
    ∃ m, pair (secM p (fullSpace p u) φ) m ≠ 0 ∧ coeff m u ≠ 0 := by
  by_contra h
  push Not at h
  apply hφ
  have hle : fullSpace p u ≤ LinearMap.ker (dotL p (secM p (fullSpace p u) φ)) :=
    (fullSpace_le_iff p).2 fun m hm => by
      rw [zero_dvd_iff]
      exact h m (by rwa [mem_ker_dotL_iff] at hm)
  ext w
  rw [← secM_spec p _ φ w]
  exact hle w.2

theorem charDep_set_nonempty {u : MvPowerSeries (Fin n) ℤ}
    {φ : Module.Dual (ZMod p) (fullSpace p u)} (hφ : φ ≠ 0) :
    {d | ∃ m, pair (secM p (fullSpace p u) φ) m ≠ 0 ∧ ¬ (p : ℤ) ^ (d + 1) ∣ coeff m u}.Nonempty := by
  obtain ⟨m, hm1, hm2⟩ := exists_charDep_witness p hφ
  obtain ⟨d, hd⟩ := exists_not_pow_dvd p hm2
  exact ⟨d, m, hm1, hd⟩

theorem lt_charDep_iff_dvd {u : MvPowerSeries (Fin n) ℤ}
    {φ : Module.Dual (ZMod p) (fullSpace p u)} (hφ : φ ≠ 0) (d : ℕ) :
    d < charDep p u φ ↔
      ∀ m, pair (secM p (fullSpace p u) φ) m ≠ 0 → (p : ℤ) ^ (d + 1) ∣ coeff m u := by
  constructor
  · intro hlt m hm
    by_contra hnd
    have : charDep p u φ ≤ d := Nat.sInf_le ⟨m, hm, hnd⟩
    omega
  · intro h
    by_contra hle
    push Not at hle
    obtain ⟨m, hm1, hm2⟩ := Nat.sInf_mem (charDep_set_nonempty p hφ)
    exact hm2 ((pow_dvd_pow _ (by unfold charDep at hle; omega)).trans (h m hm1))

theorem charDep_hdiv {u : MvPowerSeries (Fin n) ℤ}
    {φ : Module.Dual (ZMod p) (fullSpace p u)} (hφ : φ ≠ 0) (m : Fin n →₀ ℕ)
    (hm : pair (secM p (fullSpace p u) φ) m ≠ 0) : (p : ℤ) ^ (charDep p u φ) ∣ coeff m u := by
  rcases Nat.eq_zero_or_pos (charDep p u φ) with h0 | hpos
  · rw [h0, pow_zero]; exact one_dvd _
  · obtain ⟨d, hd⟩ : ∃ d, charDep p u φ = d + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    rw [hd]
    exact (lt_charDep_iff_dvd p hφ d).1 (by omega) m hm

theorem charDep_hstar {u : MvPowerSeries (Fin n) ℤ}
    {φ : Module.Dual (ZMod p) (fullSpace p u)} (hφ : φ ≠ 0) :
    ∃ m, pair (secM p (fullSpace p u) φ) m ≠ 0 ∧ ¬ (p : ℤ) ^ (charDep p u φ + 1) ∣ coeff m u :=
  Nat.sInf_mem (charDep_set_nonempty p hφ)

theorem depthSpace_le_fullSpace {R : Type*} [CommRing R] (f : MvPowerSeries (Fin n) R) (d : ℕ) :
    depthSpace p f d ≤ fullSpace p f := by
  refine Submodule.span_mono ?_
  rintro _ ⟨κ, ⟨h1, h2, h3⟩, rfl⟩
  refine ⟨κ, ⟨h1, h2, fun h0 => h3 ?_⟩, rfl⟩
  rw [h0]; exact dvd_zero _

theorem depthSpace_mono {R : Type*} [CommRing R] (f : MvPowerSeries (Fin n) R) {d d' : ℕ}
    (h : d ≤ d') : depthSpace p f d ≤ depthSpace p f d' := by
  refine Submodule.span_mono ?_
  rintro _ ⟨κ, ⟨h1, h2, h3⟩, rfl⟩
  exact ⟨κ, ⟨h1, h2, fun h4 => h3 ((pow_dvd_pow _ (by omega)).trans h4)⟩, rfl⟩

/-- `d < charDep u φ` iff `φ` vanishes on `U_d`. -/
theorem lt_charDep_iff {u : MvPowerSeries (Fin n) ℤ}
    {φ : Module.Dual (ZMod p) (fullSpace p u)} (hφ : φ ≠ 0) (d : ℕ) :
    d < charDep p u φ ↔ φ ∈ ((depthSpace p u d).comap (fullSpace p u).subtype).dualAnnihilator := by
  rw [lt_charDep_iff_dvd p hφ, Submodule.mem_dualAnnihilator]
  constructor
  · intro h w hw
    have hle : depthSpace p u d ≤ LinearMap.ker (dotL p (secM p (fullSpace p u) φ)) :=
      (depthSpace_le_iff p).2 fun m hm => h m (by rwa [mem_ker_dotL_iff] at hm)
    rw [← secM_spec p _ φ w]
    exact hle hw
  · intro h
    have hle : depthSpace p u d ≤ LinearMap.ker (dotL p (secM p (fullSpace p u) φ)) := by
      intro x hx
      have hxW := depthSpace_le_fullSpace p u d hx
      rw [LinearMap.mem_ker]
      have := secM_spec p _ φ ⟨x, hxW⟩
      rw [this]
      exact h ⟨x, hxW⟩ hx
    intro m hm
    exact (depthSpace_le_iff p).1 hle m (by rwa [mem_ker_dotL_iff])

end Dep


section Count

variable (p : ℕ) [hp : Fact p.Prime] {n : ℕ}

noncomputable instance dualFintype (W : Submodule (ZMod p) (Fin n → ZMod p)) :
    Fintype (Module.Dual (ZMod p) W) :=
  haveI : Finite (Module.Dual (ZMod p) W) := Module.finite_of_finite (ZMod p)
  Fintype.ofFinite _

theorem card_dual (W : Submodule (ZMod p) (Fin n → ZMod p)) :
    Fintype.card (Module.Dual (ZMod p) W) = p ^ Module.finrank (ZMod p) W := by
  rw [@Module.card_eq_pow_finrank (ZMod p) (Module.Dual (ZMod p) W), ZMod.card,
    Subspace.dual_finrank_eq]

theorem card_filter_mem {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Fintype V]
    (A : Submodule (ZMod p) V) :
    (Finset.univ.filter (fun x => x ∈ A)).card = p ^ Module.finrank (ZMod p) A := by
  rw [← Fintype.card_subtype, @Module.card_eq_pow_finrank (ZMod p) A, ZMod.card]

theorem finrank_comap_subtype {W U : Submodule (ZMod p) (Fin n → ZMod p)} (h : U ≤ W) :
    Module.finrank (ZMod p) (U.comap W.subtype) = Module.finrank (ZMod p) U := by
  rw [← Submodule.finrank_map_subtype_eq W (U.comap W.subtype), Submodule.map_comap_subtype,
    inf_of_le_right h]

/-- `#{φ ≠ 0 : d < charDep u φ} = p ^ (r - dim U_d) - 1`. -/
theorem card_lt_charDep (u : MvPowerSeries (Fin n) ℤ) (d : ℕ) :
    ((Finset.univ.erase (0 : Module.Dual (ZMod p) (fullSpace p u))).filter
      (fun φ => d < charDep p u φ)).card
      = p ^ (rankF p u - Module.finrank (ZMod p) (depthSpace p u d)) - 1 := by
  set W := fullSpace p u
  set A := ((depthSpace p u d).comap W.subtype).dualAnnihilator with hA
  have hset : (Finset.univ.erase (0 : Module.Dual (ZMod p) W)).filter (fun φ => d < charDep p u φ)
      = (Finset.univ.filter (fun φ => φ ∈ A)).erase 0 := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
    constructor
    · rintro ⟨h0, h1⟩; exact ⟨h0, (lt_charDep_iff p h0 d).1 h1⟩
    · rintro ⟨h0, h1⟩; exact ⟨h0, (lt_charDep_iff p h0 d).2 h1⟩
  rw [hset, Finset.card_erase_of_mem (by simp [A.zero_mem]), card_filter_mem]
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq ((depthSpace p u d).comap W.subtype)
  rw [finrank_comap_subtype p (depthSpace_le_fullSpace p u d)] at h1
  rw [← hA] at h1
  have h2 : Module.finrank (ZMod p) A
      = Module.finrank (ZMod p) W - Module.finrank (ZMod p) (depthSpace p u d) := by omega
  rw [h2]
  rfl

/-- Some depth `D0` with `U_(D0) = W`. -/
theorem exists_depth_full {R : Type*} [CommRing R] (f : MvPowerSeries (Fin n) R)
    (hnot : ∀ x : MvPowerSeries (Fin n) R, x ≠ 0 → ∃ d, ¬ (p : MvPowerSeries (Fin n) R) ^ (d + 1) ∣ x) :
    ∃ D0, fullSpace p f ≤ depthSpace p f D0 := by
  have hex : ∀ e : Fin n →₀ ℕ, ∃ d, classPart p f e ≠ 0 →
      ¬ (p : MvPowerSeries (Fin n) R) ^ (d + 1) ∣ classPart p f e := by
    intro e
    by_cases h : classPart p f e = 0
    · exact ⟨0, fun h' => absurd h h'⟩
    · obtain ⟨d, hd⟩ := hnot _ h; exact ⟨d, fun _ => hd⟩
  choose dd hdd using hex
  refine ⟨∑ e ∈ digitExps p n, dd e, Submodule.span_le.2 ?_⟩
  rintro _ ⟨κ, ⟨h1, h2, h3⟩, rfl⟩
  refine Submodule.subset_span ⟨κ, ⟨h1, h2, fun h4 => hdd κ h3 ?_⟩, rfl⟩
  exact (pow_dvd_pow _ (by
    have := Finset.single_le_sum (f := dd) (fun _ _ => Nat.zero_le _) h1
    omega)).trans h4

theorem not_pow_dvd_int_series (x : MvPowerSeries (Fin n) ℤ) (hx : x ≠ 0) :
    ∃ d, ¬ (p : MvPowerSeries (Fin n) ℤ) ^ (d + 1) ∣ x := by
  obtain ⟨m, hm⟩ : ∃ m, coeff m x ≠ 0 := by
    by_contra h; push Not at h; exact hx (MvPowerSeries.ext fun m => by rw [h m, map_zero])
  obtain ⟨d, hd⟩ := exists_not_pow_dvd p hm
  refine ⟨d, fun h => hd ?_⟩
  rw [natCast_pow_eq_C] at h
  obtain ⟨q, hq⟩ := h
  rw [hq, coeff_C_mul]; exact dvd_mul_right _ _

/-- `∑_{x ∈ s} f x = ∑_{d < D} #{x ∈ s : d < f x}` when `f ≤ D` on `s`. -/
theorem sum_eq_sum_card {α : Type*} (s : Finset α) (f : α → ℕ) (D : ℕ) (hf : ∀ x ∈ s, f x ≤ D) :
    ∑ x ∈ s, f x = ∑ d ∈ Finset.range D, (s.filter (fun x => d < f x)).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [← Finset.card_filter]
  have : (Finset.range D).filter (fun d => d < f x) = Finset.range (f x) := by
    ext d; simp only [Finset.mem_filter, Finset.mem_range]; have := hf x hx; omega
  rw [this, Finset.card_range]

/-- The flag of a monotone dimension function `a`: `fl a 0 = 0`, `fl a j = min {d : j ≤ a d}`. -/
noncomputable def fl (a : ℕ → ℕ) (j : ℕ) : ℕ := if j = 0 then 0 else sInf {d | j ≤ a d}

theorem card_filter_le_eq_fl (a : ℕ → ℕ) (ha : Monotone a) {N D0 : ℕ} (hD0 : N ≤ a D0) {j : ℕ}
    (hj : j < N) : ((Finset.range D0).filter (fun d => a d ≤ j)).card = fl a (j + 1) := by
  have hne : ({d | j + 1 ≤ a d} : Set ℕ).Nonempty := ⟨D0, by simp only [Set.mem_ofPred_eq]; omega⟩
  have hfl : fl a (j + 1) = sInf {d | j + 1 ≤ a d} := by simp [fl]
  have hmem := Nat.sInf_mem hne
  have hle : fl a (j + 1) ≤ D0 := by rw [hfl]; exact Nat.sInf_le (by simp only [Set.mem_ofPred_eq]; omega)
  have : (Finset.range D0).filter (fun d => a d ≤ j) = Finset.range (fl a (j + 1)) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, h2⟩
      by_contra h3
      push Not at h3
      have := ha (show sInf {d | j + 1 ≤ a d} ≤ d by rw [← hfl]; exact h3)
      simp only [Set.mem_ofPred_eq] at hmem
      omega
    · intro h
      refine ⟨by omega, ?_⟩
      by_contra h3
      push Not at h3
      have : sInf {d | j + 1 ≤ a d} ≤ d := Nat.sInf_le (by simp only [Set.mem_ofPred_eq]; omega)
      omega
  rw [this, Finset.card_range]

theorem fl_mono (a : ℕ → ℕ) {N D0 : ℕ} (hD0 : N ≤ a D0) {j : ℕ} (hj : j < N) :
    fl a j ≤ fl a (j + 1) := by
  by_cases h0 : j = 0
  · subst h0; simp [fl]
  · simp only [fl, if_neg h0, if_neg (Nat.succ_ne_zero j)]
    have hne : ({d | j + 1 ≤ a d} : Set ℕ).Nonempty := ⟨D0, by simp only [Set.mem_ofPred_eq]; omega⟩
    have hmem := Nat.sInf_mem hne
    exact Nat.sInf_le (by simp only [Set.mem_ofPred_eq] at hmem ⊢; omega)

/-- The layer-cake identity:
`∑_{d < D0} (p ^ (N - a d) - 1) = ∑_{j < N} (fl(j+1) - fl j) (p ^ (N - j) - 1)`. -/
theorem layer_cake (a : ℕ → ℕ) (ha : Monotone a) {N D0 : ℕ} (hle : ∀ d, a d ≤ N)
    (hD0 : N ≤ a D0) (q : ℕ) (hq : 1 ≤ q) :
    ∑ d ∈ Finset.range D0, (q ^ (N - a d) - 1)
      = ∑ j ∈ Finset.range N, (fl a (j + 1) - fl a j) * (q ^ (N - j) - 1) := by
  set g : ℕ → ℤ := fun j => (q : ℤ) ^ (N - j) - 1 with hg
  have hgN : g N = 0 := by simp [hg]
  have hcast : ∀ j, ((q ^ (N - j) - 1 : ℕ) : ℤ) = g j := fun j => by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hq)]; simp [hg]
  -- `g i = ∑_{j < N} [i ≤ j] (g j - g (j + 1))` for `i ≤ N`
  have htel : ∀ i, i ≤ N → g i = ∑ j ∈ Finset.range N, if i ≤ j then g j - g (j + 1) else 0 := by
    intro i hi
    rw [← Finset.sum_filter]
    have : (Finset.range N).filter (fun j => i ≤ j) = Finset.Ico i N := by
      ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [this, Finset.sum_Ico_eq_sum_range]
    have := Finset.sum_range_sub' (fun k => g (i + k)) (N - i)
    simp only [← add_assoc] at this
    rw [this]
    simp only [add_zero, Nat.add_sub_cancel' hi, hgN, sub_zero]
  apply Nat.cast_injective (R := ℤ)
  push_cast [Nat.cast_sum]
  simp only [hcast]
  rw [Finset.sum_congr rfl fun d _ => htel (a d) (hle d), Finset.sum_comm]
  have hL : ∀ j ∈ Finset.range N, ∑ d ∈ Finset.range D0, (if a d ≤ j then g j - g (j + 1) else 0)
      = (fl a (j + 1) : ℤ) * (g j - g (j + 1)) := by
    intro j hj
    rw [← Finset.sum_filter, Finset.sum_const, card_filter_le_eq_fl a ha hD0 (Finset.mem_range.1 hj),
      nsmul_eq_mul]
  rw [Finset.sum_congr rfl hL]
  have hR : ∀ j ∈ Finset.range N, (((fl a (j + 1) - fl a j : ℕ) : ℤ) * g j)
      = (fl a (j + 1) : ℤ) * g j - (fl a j : ℤ) * g j := by
    intro j hj
    rw [Nat.cast_sub (fl_mono a hD0 (Finset.mem_range.1 hj))]; ring
  rw [Finset.sum_congr rfl hR, Finset.sum_sub_distrib]
  have hshift : ∑ j ∈ Finset.range N, (fl a j : ℤ) * g j
      = ∑ j ∈ Finset.range N, (fl a (j + 1) : ℤ) * g (j + 1) := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0; simp
    · obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
      simp [fl, hgN]
  rw [hshift, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end Count


section TopFlag

variable (p : ℕ) [hp : Fact p.Prime] {n : ℕ}

/-- `∑_{φ ≠ 0} charDep u φ = ∑_{j < r} (d(j+1) - d(j)) (p ^ (r - j) - 1)`. -/
theorem sum_charDep (u : MvPowerSeries (Fin n) ℤ) :
    ∑ φ ∈ Finset.univ.erase (0 : Module.Dual (ZMod p) (fullSpace p u)), charDep p u φ
      = ∑ j ∈ Finset.range (rankF p u), flagJump p u j * (p ^ (rankF p u - j) - 1) := by
  obtain ⟨D0, hD0⟩ := exists_depth_full p u (not_pow_dvd_int_series p)
  set a : ℕ → ℕ := fun d => Module.finrank (ZMod p) (depthSpace p u d) with ha
  have hamono : Monotone a := fun d d' h => Submodule.finrank_mono (depthSpace_mono p u h)
  have hale : ∀ d, a d ≤ rankF p u := fun d =>
    Submodule.finrank_mono (depthSpace_le_fullSpace p u d)
  have haD0 : rankF p u ≤ a D0 := Submodule.finrank_mono hD0
  have hbound : ∀ φ ∈ Finset.univ.erase (0 : Module.Dual (ZMod p) (fullSpace p u)),
      charDep p u φ ≤ D0 := by
    intro φ hφ
    have hφ0 := (Finset.mem_erase.1 hφ).1
    by_contra hlt
    push Not at hlt
    have hann := (lt_charDep_iff p hφ0 D0).1 hlt
    apply hφ0
    ext w
    rw [Submodule.mem_dualAnnihilator] at hann
    exact hann w (by simp only [Submodule.mem_comap, Submodule.subtype_apply]; exact hD0 w.2)
  rw [sum_eq_sum_card _ _ D0 hbound]
  simp only [card_lt_charDep]
  have := layer_cake a hamono hale haD0 p hp.out.one_lt.le
  simp only [ha] at this
  rw [this]
  rfl

theorem div_pow_sub_one {q N b : ℕ} (hq : 1 ≤ q) (hb : b ≤ N) :
    (q ^ N - 1) / q ^ b = q ^ (N - b) - 1 := by
  have hP : 1 ≤ q ^ b := Nat.one_le_pow _ _ hq
  have hQ : 1 ≤ q ^ (N - b) := Nat.one_le_pow _ _ hq
  have hN : q ^ N = q ^ (N - b) * q ^ b := by rw [← pow_add, Nat.sub_add_cancel hb]
  rw [hN]
  have hX : q ^ b ≤ q ^ (N - b) * q ^ b := Nat.le_mul_of_pos_left _ (by omega)
  apply Nat.div_eq_of_lt_le
  · rw [Nat.sub_one_mul]; omega
  · rw [Nat.sub_add_cancel hQ]; omega

theorem digit_top {N b : ℕ} (hb : b < N) : digit p b (p ^ N - 1) = p - 1 := by
  have hp1 := hp.out.one_lt
  rw [digit, div_pow_sub_one hp1.le hb.le]
  obtain ⟨c, hc⟩ : ∃ c, N - b = c + 1 := ⟨N - b - 1, by omega⟩
  rw [hc, pow_succ]
  have hY : 1 ≤ p ^ c := Nat.one_le_pow _ _ (by omega)
  have : p ^ c * p - 1 = (p - 1) + p * (p ^ c - 1) := by
    rw [Nat.mul_sub, mul_one, mul_comm]
    have : p ≤ p * p ^ c := Nat.le_mul_of_pos_right p (by omega)
    omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem topVal_eq_digitVal (N : ℕ) (γ : ℕ → ℕ) : topVal p N γ = digitVal p N γ (p ^ N - 1) := by
  rw [topVal, digitVal]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [digit_top p (Finset.mem_range.1 hb)]

/-- **R-083's top bound for every `u ∈ ℤ[[x_1..x_n]]`** (no unit hypothesis is needed here): a
monic `P ∈ B[X]` of degree `p ^ r - 1` with `p ^ k ∣ P(u)` has `k ≤ ∑_{b<r} (p - 1) γ_b`, where `r`
and `γ` come from the depth flag of `u`. Proved by the trace over the characters of `W`. -/
theorem topBound_flag_int (u : MvPowerSeries (Fin n) ℤ) :
    TopBound p (frob p) (rankF p u) (flagGamma p (flagJump p u)) u := by
  intro k hk
  set N := rankF p u
  have h1 := top_bound_int p (G := Module.Dual (ZMod p) (fullSpace p u))
    (by rw [card_dual]; rfl) (secM p (fullSpace p u)).toAddMonoidHom (charDep p u)
    (fun h hh m hm => charDep_hdiv p hh m hm) (fun h hh => charDep_hstar p hh) hk
  rw [sum_charDep] at h1
  rw [topVal_eq_digitVal, digitVal_flagGamma _ (Nat.sub_lt (Nat.one_le_pow _ _ hp.out.pos) one_pos)]
  have hdiv : ∀ j ∈ Finset.range N, flagJump p u j * ((p ^ N - 1) / p ^ j)
      = flagJump p u j * (p ^ (N - j) - 1) := fun j hj => by
    rw [div_pow_sub_one hp.out.one_lt.le (Finset.mem_range.1 hj).le]
  rw [Finset.sum_congr rfl hdiv]
  have hleg := legendre_split p N (p ^ N - 1) 0 (by have := Nat.one_le_pow N p hp.out.pos; omega)
  simp only [Nat.factorial_zero, padicValNat_one_right, add_zero] at hleg
  set S := ∑ j ∈ Finset.range N, flagJump p u j * (p ^ (N - j) - 1)
  set v := padicValNat p (p ^ N - 1).factorial
  have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
  have h2 : (p - 1) * (k + N) ≤ (p - 1) * (v + S + N) := by
    have e : (p - 1) * (v + S + N) = (p - 1) * v + N * (p - 1) + (p - 1) * S := by ring
    omega
  have := Nat.le_of_mul_le_mul_left h2 hp1
  omega

end TopFlag

end FrobLevel
